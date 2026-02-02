Require Import bedrock2.NotationsCustomEntry.

Import Syntax Syntax.Coercions BinInt String List List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition cswap_spec {T} (c : nat) (x y : T) :=
  match c with
    | 0%nat => (x, y)
    | _ => (y, x)
  end.

(* LLVM compilers may optimize this and make it non-constant time, try to use csel and nonconditional swap instead. *)
Definition cswap := func! (c, x, y, n) {
  c = $0 - c;
  while n {
    vx = load1(x);
    vy = load1(y);

    v = vx ^ vy;
    v = v & c;

    vx = v ^ vx;
    vy = v ^ vy;
    store1(x, vx);
    store1(y, vy);

    x = x + $1;
    y = y + $1;
    n = n - $1;

    $(cmd.unset "vx");
    $(cmd.unset "vy");
    $(cmd.unset "v")
  }
}.

Require Import bedrock2.WeakestPrecondition bedrock2.Semantics bedrock2.ProgramLogic.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface bedrock2.Map.SeparationLogic.
Require Import bedrock2.ZnWords.
Import Coq.Init.Byte coqutil.Byte.
Local Notation string := String.string.

Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").

Section WithParameters.
  Context {width} {BW: Bitwidth width}.
  Context {word: word.word width} {mem: map.map word byte}.
  Context {ext_spec: ExtSpec}.
  Import ProgramLogic.Coercions.

  #[local] Instance locals: Interface.map.map String.string word := SortedListString.map _.

  Global Instance spec_of_cswap : spec_of "cswap" :=
    fnspec! "cswap" (c x y n : word) / (xs ys : list byte) (R : mem -> Prop),
    { requires t m := m =* xs$@x * ys$@y * R /\
                      length xs = n :> Z /\ length ys = n :> Z
                      /\ (c = word.of_Z 0%nat \/ c = word.of_Z 1%nat) ;
      ensures t' m :=
        let (nxs, nys) := cswap_spec (Z.to_nat (word.unsigned c)) xs ys in
        m =* nxs$@x * nys$@y * R /\ t=t' }.

  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {locals_ok : map.ok locals}
    {ext_spec_ok : ext_spec.ok ext_spec}.

  Import coqutil.Tactics.letexists coqutil.Tactics.Tactics coqutil.Tactics.autoforward.
  Import coqutil.Word.Properties coqutil.Map.Properties.

  (* This is a ZnWords version with destructing width in the middle, which helps solving goals here. *)
  Local Ltac lia_width := destruct width_cases as [J|J]; symmetry in J; ZnWords_pre; destruct J; better_lia.

  Lemma cswap_ok : program_logic_goal_for_function! cswap.
  Proof.
    repeat straightline.

    refine ((Loops.tailrec
      (HList.polymorphic_list.cons _
      (HList.polymorphic_list.cons _
      (HList.polymorphic_list.cons _
      HList.polymorphic_list.nil)))
      ["c";"x";"y";"n"])
      (fun (v:nat) xs ys R t m c' x y n => PrimitivePair.pair.mk (
        m =* xs$@x * ys$@y * R /\ length xs = n :>Z /\ length ys = n :>Z /\ v = n :>Z /\ c' = c)
      (fun                 T M (C X Y N : word) => t = T /\
                              let (nxs, nys) := cswap_spec (Z.to_nat (word.unsigned c14)) xs ys in
                                  M =* nxs$@x * nys$@y * R))
      lt
      _ _ _ _ _ _ _ _); Loops.loop_simpl.
      { cbv [Loops.enforce]; cbn. split; exact eq_refl. }
      { eapply Wf_nat.lt_wf. }
      { repeat straightline. ssplit; try ecancel_assumption; eauto. }
      { intros ?v ?xs ?ys ?R ?t ?m ?c ?x ?y ?n.
        repeat straightline.

        2: {
          cbv [cswap_spec].
          destruct xs0, ys0; rewrite ?List.length_cons in *; try Lia.lia.
          destruct (Z.to_nat c14); ecancel_assumption.
        }

        cbn in localsmap.
        destruct xs0 as [|hxs xs0] in *, ys0 as [|hys ys0] in *;
        cbn [length Array.array] in *; try (exfalso; lia_width).

        eapply WeakestPreconditionProperties.dexpr_expr.
        do 69 straightline.

        (* At the moment, straightline takes very long to solve the Loops.Enforce goal so we do it manually. *)
        eexists _, _, _, _.
        split.
        {
          cbv [Loops.enforce]. cbn. split; exact eq_refl.
        }

        repeat straightline.

        eexists _, _, _, _.
        split; split; ssplit; try ecancel_assumption; try lia_width.
        { instantiate (1:= (Nat.pred (Z.to_nat (word.unsigned n0)))). lia_width. }
        1: lia_width.

        repeat straightline. cbv [cswap_spec] in *.

        epose proof (byte.unsigned_range hxs).
        epose proof (byte.unsigned_range hys).
        subst c vx vy v v0 vy'0 v'1.

        (* Destruct if c is one or zero. *)
        destruct H2 as [Hc14|Hc14]; rewrite Hc14 in *.

        {
          replace (Z.to_nat (word.of_Z 0%nat)) with 0%nat in * by lia_width.
          rewrite !word.sub_0_r, !word.and_0_r, !word.unsigned_xor_nowrap, !word.unsigned_of_Z_nowrap, !Z.lxor_0_l,
            !byte.of_Z_unsigned in *; try lia_width; try exact eq_refl.

          do 2 SeparationLogic.seprewrite (Array.array_cons (width:=width) (mem:=mem) ptsto (word.of_Z 1)).
          ecancel_assumption.
        }
        {
          replace (Z.to_nat (word.of_Z 1%nat)) with 1%nat in * by lia_width.
          replace (word.sub (word.of_Z 0) (word.of_Z 1%nat)) with ((word.of_Z (width:=width)(-1))) in * by lia_width.
          rewrite word.and_m1_r in *.
          rewrite <- word.xor_assoc in *.
          rewrite (word.xor_eq_0_iff (word.of_Z (byte.unsigned hys)) (word.of_Z (byte.unsigned hys))) in *; try exact eq_refl.
          rewrite (word.xor_comm _ (word.of_Z (byte.unsigned hys))) in *.
          rewrite <- word.xor_assoc in *.
          rewrite (word.xor_eq_0_iff (word.of_Z (byte.unsigned hxs)) (word.of_Z (byte.unsigned hxs))) in *; try exact eq_refl.
          rewrite !word.unsigned_xor_nowrap, !word.unsigned_of_Z_nowrap,
            !Z.lxor_0_r, !byte.of_Z_unsigned in *; try lia_width; try exact eq_refl.

          do 2 SeparationLogic.seprewrite (Array.array_cons (width:=width) (mem:=mem) ptsto (word.of_Z 1)).
          ecancel_assumption.
        }
      }
      (* postcondition *)
      repeat straightline.
      destruct (cswap_spec (Z.to_nat c14) xs ys).
      split; [assumption|exact eq_refl].
  Qed.
End WithParameters.
