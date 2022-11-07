Require Import bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition uint128_add := func! (s, a, b) ~> c {
    a0 = load4(a); a = a+$4;
    b0 = load4(b); b = b+$4;
    s0 = a0 + b0;
        a1 = load4(a); a = a+$4;
        b1 = load4(b); b = b+$4;
        c1 = s0 < a0;
        s1 = a1 + b1;
            a2 = load4(a);
            c2 = s1 < a1;
        s1 = c1 + s1;
                           a = a+$4;
            c2p = s1 < c1;
            b2 = load4(b); b = b+$4;
            c2 = c2 + c2p;
            s2 = a2 + b2;
                a3 = load4(a);
                b3 = load4(b);
                c3 = s2 < a2;
            s2 = c2 + s2;
    store4(s, s0); s = s+$4;
                c3p = s2 < c2;
                c3 = c3 + c3p;
                s3 = a3 + b3;
        store4(s, s1); s = s+$4;
                    c = s3 < a3;
                s3 = c3 + s3;
            store4(s, s2); s = s+$4;
                    c4p = s3 < c3;
                store4(s, s3);
                    c = c + c4p
}.

Require Import bedrock2.FE310CSemantics bedrock2.Semantics .
Require Import bedrock2.WeakestPrecondition bedrock2.ProgramLogic.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface bedrock2.Map.SeparationLogic.
Require Import bedrock2.Array bedrock2.Scalars.
Require Import bedrock2.ZnWords.
Require Import coqutil.Tactics.Tactics.
Local Ltac invert H := inversion H; clear H.

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing) (* experiment*).
  Local Notation "m =*> P" := (exists R, (sep P R) m) (at level 70, only parsing) (* experiment*).
  Import ProgramLogic.Coercions.
  Local Number Notation nat Nat.of_num_uint Nat.to_num_hex_uint (abstract after 5001) : core_scope.
  Local Number Notation nat Nat.of_num_uint Nat.to_num_uint (abstract after 5001) : core_scope.
  Local Open Scope core_scope.
  Local Notation array32 := (array scalar32 (word.of_Z 4)).

  Definition eval : list word -> Z :=
    List.fold_right (fun a s => word.unsigned a + 2^32*s) 0.

  Instance spec_of_swap : spec_of "uint128_add" :=
    fnspec! "uint128_add" ps pa pb / a b s R ~> c,
    { requires t m :=
        m =*> array32 pa a     /\ length a = 4 /\
        m =*> array32 pb b     /\ length b = 4 /\
        m =*  array32 ps s * R /\ length s = 4;
      ensures T M := exists s,
        M =*  array32 ps s * R /\ length s = 4 /\
        T = t /\ 2^128*c + eval s = eval a + eval b }.

  Lemma ltu_as_carry (a b : word)
    (s : word := word.add a b)
    (c : word := if word.ltu s a then word.of_Z 1 else word.of_Z 0)
    : word.unsigned c = (a + b) /  2 ^ 32.
  Proof.
    subst s c. rewrite word.unsigned_ltu. destr (word.add a b <? a); ZnWords.
  Qed.

  Lemma uint128_add_ok : program_logic_goal_for_function! uint128_add.
  Proof.
    straightline; repeat straightline_cleanup.

    repeat match goal with
    | H : length ?l = _ |- _ =>
        let x := fresh l "_0" in destruct l as [(*nil*)|x l]; invert H
    end; unfold array in *.

    repeat straightline; fwd_uniq.
    (* exfalso; clear dependent mem. *)
    clear dependent pa; clear dependent pb. clear -H5 mem_ok word_ok.

    exists [s0; s1; s2; s3]; ssplit; try ecancel_assumption; trivial.

    (* repeat match goal with x := _ |- _ => subst x end. *)

    repeat match goal with
    | c := if word.ltu ?s _ then _ else _ |- _ =>
        let H := fresh "H" c in
        pose proof (ltu_as_carry _ _ : word.unsigned c = _) as H;
        move H before c; clearbody c; move c before word_ok
    end.
    clear dependent ps; clear dependent mem.

    unfold eval, List.fold_right; ZnWords.
  Qed.
End WithParameters.
