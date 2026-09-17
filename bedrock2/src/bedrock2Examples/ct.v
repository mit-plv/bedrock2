Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations ZArith.
Require Import coqutil.Z.Lia.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition div3329_vartime := func! (x) ~> ret {
  ret = $(expr.op bopname.divu "x" 3329)
}.

Definition div3329 := func! (x) ~> ret {
  ret = (x * $989558401) >> $32;
  ret = (ret + (x - ret >> $1)) >> $11
}.

From coqutil Require Import Word.Properties Word.Bitwidth Tactics.letexists.
Import Coq.Lists.List List.ListNotations.
From bedrock2 Require Import Semantics LeakageSemantics FE310CSemantics LeakageWeakestPrecondition LeakageProgramLogic.
Import LeakageProgramLogic.Coercions.
Section WithParameters.
  Local Notation word := (bits 32).
  Context {mem: Interface.map.map word Byte.byte}.
  Context {mem_ok : Interface.map.ok mem}.
  Context {pick_sp: PickSp}.

#[global] Instance ctspec_of_div3329 : spec_of "div3329" :=
    fnspec! exists f, "div3329" x ~> ret,
      { requires k t m := True ; ensures k' t' m' := t' = t /\ m' = m /\ k' = f k }.

Lemma div3329_ct : program_logic_goal_for_function! div3329.
Proof.
  repeat (straightline || eexists).
  { (* no leakag -- 3 minutes *) cbn. exact eq_refl. }
Qed.

#[global] Instance vtspec_of_div3329 : spec_of "div3329_vartime" :=
  fnspec! "div3329_vartime" x ~> ret,
    { requires k t m := True ;
      ensures k' t' m' := t' = t /\ m' = m /\
                            k' = [leak_word (bits.of_Z 32 3329); leak_word x]++k }.

Lemma div3329_vt : program_logic_goal_for_function! div3329_vartime.
Proof.
  repeat (straightline || eexists).
Qed.

(* Mon Jul  1 14:14:15 EDT 2024 *)

Import Byte.
Definition getchar_event c : LogItem :=
  ((Interface.map.empty, "getchar", []), (Interface.map.empty, [bits.of_Z 32 (byte.unsigned c)])).
#[global] Instance ctspec_of_getchar : spec_of "getchar" :=
  fnspec! exists f, "getchar" ~> ret,
    { requires k t m := True ; ensures k' t' m' :=
        exists c, ret = bits.of_Z 32 (byte.unsigned c) /\
               k' = f ++ k /\ m' = m /\ t' = cons (getchar_event c) t }.

Definition getline := func! (dst, n) ~> n {
  i = $0;
  c = $0;
  while (i < n) {
    unpack! c = getchar();
    if (c == $0x0a) { n = i }
    else { store1(dst + i, c); i = i + $1 }
  }
}.

Local Notation "xs $@ a" := (Array.array Separation.ptsto (bits.of_Z 32 1) a xs) (at level 10, format "xs $@ a").
Local Infix "*" := Separation.sep.
Local Infix "*" := Separation.sep : type_scope.

Definition getline_io n bs :=
  let chars := map getchar_event (rev bs) in
  let newline := if n =? length bs then nil else [getchar_event Byte.x0a] in
  newline ++ chars.

Local Fixpoint getline_leakage f dst n (bs : nat) (i : word) :=
  if i =? n then leak_bool false :: nil else
  match bs with
  | S bs => getline_leakage f dst n bs (Zmod.add i (bits.of_Z 32 1)) ++ (leak_word (Zmod.add dst i) :: leak_bool false :: f ++ leak_unit :: leak_bool true :: nil)
  | O => leak_bool false :: leak_bool true :: f ++ leak_unit :: leak_bool true :: nil
  end.

#[global] Instance ctspec_of_getline : spec_of "getline" :=
  fnspec! exists f, "getline" (dst n : word) / d R ~> l,
    { requires k t m := (d$@dst * R) m /\ length d = n :> Z ;
      ensures k' t' m' := exists bs es,
        k' = f dst n l ++ k /\
        (bs$@dst * es$@(Zmod.add dst l) * R) m' /\
        length bs = l :> Z /\
        length bs + length es = n :> Z /\
        t' = getline_io n bs ++ t 
        (* /\ ~ In Byte.x0a bs *) }.

(* Mon Jul  1 14:24:28 EDT 2024 *)

Require Coq.Program.Wf.
Import Separation SeparationLogic.

Lemma getline_ct : program_logic_goal_for_function! getline.
Proof.
  repeat straightline.

  refine ((LeakageLoops.tailrec_earlyout
    (HList.polymorphic_list.cons (list byte)
    (HList.polymorphic_list.cons (_ -> Prop)
    HList.polymorphic_list.nil))
    ["dst";"n";"i";"c"])
    (fun (v:Z) es R k t m  dst_ n_ i c => PrimitivePair.pair.mk (
      n_ = n /\ dst_ = dst /\ v = i :> Z /\
      i <= n /\
      (es$@(Zmod.add dst i) * R) m /\ length es = Zmod.sub n i :> Z
    )
    (fun                K T M DST N I C => DST = dst /\
      exists bs ES, (bs$@(Zmod.add dst i) * ES$@(Zmod.add dst I) * R) M /\ I = N /\
      length bs = Zmod.sub I i :> Z /\
      length ES = Zmod.sub n I :> Z /\
      i <= N <= n /\
      T = getline_io (n-i) bs ++ t /\
      K = getline_leakage f dst n (length bs) i ++ k
    ))
    (fun i j => j < i <= n)
    _ _ _ _ _ _ _);
    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *;
    repeat straightline.
    { eapply Z.gt_wf. }
    { split. { subst i. rewrite Zmod.unsigned_0. lia. }
      subst i; rewrite Zmod.add_0_r; split; [ecancel_assumption|]. rewrite Zmod.sub_0_r; auto. }

    { 
      pose proof (bits.unsigned_range n width_nonneg).
      pose proof (bits.unsigned_range x3 width_nonneg) as Hx3.
      subst br. case Z.ltb eqn:? in H2; 
          rewrite ?bits.unsigned_1, ?Zmod.unsigned_0, ?(word.unsigned_sub_nowrap _ _ width_pos)  in *; try lia; [].
      eapply LeakageWeakestPreconditionProperties.Proper_call; repeat intro; cycle 1.
      { eapply H. exact I. }
      repeat straightline.
      eexists _, _; repeat straightline.
      split; repeat straightline.
      split; repeat straightline.
      { left; repeat straightline.
        { subst br. rewrite Z.ltb_irrefl. apply Zmod.unsigned_0. }
        eexists _, _; repeat straightline.
        eapply word.if_nonzero, Zmod.eqb_eq in H4.
        instantiate (1:=nil); cbn [Array.array]; split.
        { ecancel_assumption. }
        { 
          split; trivial.
          split. { rewrite (word.unsigned_sub_nowrap _ _ width_pos); simpl length; lia. }
          split. { rewrite (word.unsigned_sub_nowrap _ _ width_pos); lia. }
          split. { lia. }
          split. { (* I/O *)
            cbv [getline_io]. cbn [map rev List.app length]. case (Z.eqb_spec (n'0-x3) 0%nat) as []; try lia.
            rewrite app_nil_r. subst a0. simpl.
            eapply f_equal2; f_equal; trivial.
            progress change 10 with (byte.unsigned Byte.x0a) in H4.
            pose proof byte.unsigned_range x2.
            pose proof byte.unsigned_range Byte.x0a.
            subst x1; eapply bits.of_Z_inj in H4; rewrite 2 Z.mod_small in H4 by lia.
            eapply byte.unsigned_inj in H4; trivial. }
          (* leakage *)
          subst k'''. cbn [getline_leakage leak_binop "++" length].
          rewrite (proj2 (Z.eqb_neq _ _)) by lia; trivial. simpl. rewrite <- app_assoc. reflexivity. } }

      (* store *)
      destruct x as [|x_0 x]. { cbn [length] in *; lia. }
      cbn [Array.array] in *.
      repeat straightline.
      right; repeat straightline.
      eexists _, _, _; repeat straightline.
      { instantiate (1:=x).
        subst i.
        rewrite Zmod.add_assoc.
        split. { rewrite (word.unsigned_add_nowrap _ _ width_pos); rewrite ?bits.unsigned_1; try lia. }
        split; [ecancel_assumption|].
        cbn [length] in *.
        pose proof (bits.unsigned_of_Z_small (n := 32) 1 ltac:(lia)).
        pose proof (word.unsigned_add_nowrap x3 (bits.of_Z 32 1) width_pos).
        pose proof (word.unsigned_sub_nowrap n (Zmod.add x3 (bits.of_Z 32 1)) width_pos).
        lia. }
      { split.
        { subst i.
          pose proof (bits.unsigned_of_Z_small (n := 32) 1 ltac:(lia)).
          pose proof (word.unsigned_add_nowrap x3 (bits.of_Z 32 1) width_pos).
          pose proof (word.unsigned_sub_nowrap n (Zmod.add x3 (bits.of_Z 32 1)) width_pos).
          lia. }
        repeat straightline.
        (* subroutine return *)
        subst i.

        rename x9 into bs.
        rename x10 into es.
        rename x6 into I.
        rename x3 into _i.
        rewrite Zmod.add_assoc in H10.

        eexists (byte.of_Z x1 :: bs), (es).
        cbn ["$@" "++"].
        split. { ecancel_assumption. }
        split; trivial.
        split. { cbn [length]. rewrite Nat2Z.inj_succ, H15.
          pose proof (bits.unsigned_of_Z_small (n := 32) 1 ltac:(lia)).
          pose proof (word.unsigned_add_nowrap _i (bits.of_Z 32 1) width_pos ltac:(lia)).
          rewrite 2 (word.unsigned_sub_nowrap _ _ width_pos); lia. }
        split; trivial.
        split. {
          pose proof (bits.unsigned_of_Z_small (n := 32) 1 ltac:(lia)).
          pose proof (word.unsigned_add_nowrap _i (bits.of_Z 32 1) width_pos ltac:(lia)).
          lia. }
        split. { (* I/O *)
          subst T a0.
          cbv [getline_io]; cbn [rev List.map].
          repeat rewrite ?map_app, <-?app_comm_cons, <-?app_assoc; f_equal.
          { pose proof (bits.unsigned_of_Z_small (n := 32) 1 ltac:(lia)) as H_1.
            rewrite (word.unsigned_add_nowrap _i (bits.of_Z 32 1) width_pos ltac:(lia)), H_1; cbn [length].
            case Z.eqb eqn:? at 1; case Z.eqb eqn:? at 1; trivial; try lia.
            { (* WHY manual? does zify do a bad job here? *) eapply Z.eqb_neq in Heqb1. lia. }
            { (* WHY manual? does zify do a bad job here? *) eapply Z.eqb_eq in Heqb1. lia. } }
          f_equal.
          cbn [map List.app].
          f_equal.
          f_equal.
          subst x1.
          pose proof byte.unsigned_range x2.
          rewrite bits.unsigned_of_Z_small, byte.of_Z_unsigned; trivial; lia. }
        (* leakage *)
        subst K a1; cbn [getline_leakage leak_binop length].
        rewrite (proj2 (Z.eqb_neq _ _)) by lia; trivial.
        repeat (simpl || rewrite <- app_assoc). reflexivity. } }

    { (* buffer full *)
      replace x3 with n in *; cycle 1.
      { subst br; eapply (word.if_zero _ width_pos), Z.ltb_nlt in H2.
        apply Zmod.unsigned_inj. lia. }
      exists x, nil; cbn [Array.array].
      split. { ecancel_assumption. }
      split. { trivial. }
      split. { trivial. }
      rewrite (word.unsigned_sub_nowrap _ _ width_pos), Z.sub_diag in H7 by lia.
      split. { rewrite (word.unsigned_sub_nowrap _ _ width_pos), Z.sub_diag by lia; trivial. }
      split. { lia. }
      split. { destruct x; cbn [length] in *; try lia; cbn.
        rewrite Z.sub_diag; reflexivity. }
      destruct x; try (cbn in *; lia).
      cbn [getline_leakage length]; rewrite Z.eqb_refl; trivial. }

    do 2 eexists. split. { subst k0 i. rewrite Zmod.sub_0_r in *.
      assert (length x3 = Z.to_nat (Zmod.unsigned x0)) as -> by lia. reflexivity. }
    subst i.
    rewrite Zmod.add_0_r in *.
    split.
    { ecancel_assumption. }
    split.
    { rewrite H5. rewrite Zmod.sub_0_r. trivial. }
    split.
    { rewrite H5, H6, Zmod.sub_0_r, (word.unsigned_sub_nowrap _ _ width_pos); lia. }
    subst t0.
    rewrite Zmod.unsigned_0, Z.sub_0_r.
    trivial.

(* Tue Jul  2 14:26:41 EDT 2024 *)
Qed.
(* Mon Jul  8 17:03:59 EDT 2024 *)

Require Import bedrock2Examples.memequal.

Definition password_checker := func! (password) ~> ret {
                                   stackalloc 8 as x; (*password is 8 characters*)
                                   unpack! n = getline(x, $8);
                                   unpack! ok = memequal(x, password, $8);
                                   ret = (n == $8) & ok
                                 }.

#[global] Instance ctspec_of_password_checker : spec_of "password_checker" :=
  fnspec! exists f, "password_checker" password_addr / R password ~> ret (*bs =? password*),
    { requires k t m := length password = 8 :> Z /\ (password$@password_addr * R) m ;
      ensures k' t' m' := exists bs (l : word),
        (password$@password_addr * R) m' /\
          t' = getline_io 8 bs ++ t /\
          length bs = l :> Z /\
          (k' = f k password_addr l) /\
          (Zmod.unsigned ret = 1 <-> bs = password) }.

Fail Lemma password_checker_ct : program_logic_goal_for_function! password_checker. (*Why*)
Global Instance spec_of_memequal : spec_of "memequal" := spec_of_memequal.

Require Import coqutil.Word.SimplWordExpr.

Lemma password_checker_ct : program_logic_goal_for_function! password_checker.
Proof.
  repeat straightline.
  eapply LeakageWeakestPreconditionProperties.Proper_call; repeat intro; cycle 1.
  { eapply H. split. 2: rewrite bits.unsigned_of_Z; eassumption. ecancel_assumption. }
  repeat straightline.
  seprewrite_in_by @Array.bytearray_index_merge H9 ltac:(lia).
  eapply LeakageWeakestPreconditionProperties.Proper_call; repeat intro; cycle 1.
  { eapply H0. split.
    { ecancel_assumption. } split.
    { ecancel_assumption. }
    split.
    { rewrite ?app_length; lia. }
    { rewrite H1. rewrite bits.unsigned_of_Z. reflexivity. } }
  assert (length ((x0 ++ x1)) = 8%nat).
  { rewrite ?app_length. rewrite bits.unsigned_of_Z_small in H11; lia. }
  repeat straightline.
  do 2 eexists. split. { ecancel_assumption. }
  split. { subst a0. rewrite bits.unsigned_of_Z. exact eq_refl. }
  split. { eassumption. }
  split. { (* leakage *)
    subst a0. subst a. subst a2. instantiate (1 := fun _ _ => _). simpl. reflexivity. }
  { (* functional correctness *)
    subst ret.
    destruct (Zmod.eqb_spec x 8) as [->|?]; cycle 1.
    { rewrite bits.unsigned_and, Zmod.unsigned_0, Z.land_0_l; split; try discriminate.
      intros X%(f_equal (@length _)). case H13; clear H13; apply Zmod.unsigned_inj.
      rewrite <-H10, X, bits.unsigned_of_Z_small; lia. }
    rewrite bits.unsigned_and, bits.unsigned_1 by lia.
    destruct x1; cycle 1.
    { cbn [length] in *. lia. }     { rewrite ?app_nil_r in *. rewrite <-H16.
      case H15 as [->|]; intuition try congruence. rewrite H15. trivial. } }
Qed.

Definition output_event x : LogItem :=
  ((Interface.map.empty, "output", [x]), (Interface.map.empty, [])).
#[global] Instance ctspec_of_output : spec_of "output" :=
  fnspec! exists f, "output" x,
    { requires k t m := True ;
      ensures k' t' m' := k' = f ++ k /\ m' = m /\ t' = cons (output_event x) t }.

Definition getprime_event p : LogItem :=
  ((Interface.map.empty, "getprime", []), (Interface.map.empty, [p])).
#[global] Instance ctspec_of_getprime : spec_of "getprime" :=
  fnspec! exists f, "getprime" ~> p,
    { requires k t m := True ;
      ensures k' t' m' := k' = f ++ k /\ m' = m /\ t' = cons (getprime_event p) t }.

Definition semiprime := func! () ~> (p, q) {
  unpack! p = getprime();
  unpack! q = getprime();
  n = p * q;
  output(n)
}.

#[global] Instance ctspec_of_semiprime : spec_of "semiprime" :=
  fnspec! exists f, "semiprime" ~> p q,
    { requires k t m := True ;
      ensures k' t' m' :=
        k' = f ++ k /\ m' = m
        /\ t' = [output_event (Zmod.mul p q); getprime_event q; getprime_event p]++ t }.

Lemma semiprime_ct : program_logic_goal_for_function! semiprime.
Proof.
  repeat straightline.
  eapply LeakageWeakestPreconditionProperties.Proper_call; repeat intro; [|eapply H]; repeat straightline.
  eapply LeakageWeakestPreconditionProperties.Proper_call; repeat intro; [|eapply H]; repeat straightline.
  eapply LeakageWeakestPreconditionProperties.Proper_call; repeat intro; [|eapply H0]; repeat straightline.
  Tactics.ssplit; trivial; simpl in *; align_trace.
Qed.

Definition maskloop := func! (a) {
  i = $0;
  while (i < $2) {
    mask = $0-((load1(a+i)>>i)&$1);
    store1(a+i, mask & $123);
    i = i + $1
  }
}.

Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

(*#[global] Instance ctspec_of_maskloop : spec_of "maskloop" :=
  fun functions => forall k a, exists k_, forall a0 a1 R t m,
      m =* ptsto a a0 * ptsto (Zmod.add a (bits.of_Z 32 1)) a1 * R ->
      LeakageWeakestPrecondition.call functions "maskloop" k t m [a]
        (fun k' t' m' rets => rets = [] /\ k' = k_).

Lemma maskloop_ct : program_logic_goal_for_function! maskloop.
Proof.
  enter maskloop. eapply LeakageWeakestPreconditionProperties.start_func.
  enter maskloop.

         match goal with
         | H:map.get ?functions ?fname = Some _
           |- _ =>
               eapply LeakageWeakestPreconditionProperties.start_func;
                [ exact H | clear H ]
         end; cbv beta match delta [func].
  intros. eexists. intros.
  repeat straightline.
  eexists nat, lt, (fun i k _ (m : mem) (l : locals) =>
    map.get l "a" = Some a /\
    map.get l "i" = Some (bits.of_Z 32 (Z.of_nat i)) /\ (
    i = 0%nat /\ m =* ptsto a a0 * ptsto (Zmod.add a (bits.of_Z 32 1)) a1 * R \/
    i = 1%nat /\ False \/
    i = 2%nat /\ False)).
  Tactics.ssplit; auto using lt_wf.
  { exists 0%nat; Tactics.ssplit.
    { subst l0 l; rewrite map.get_put_diff, map.get_put_same; congruence. }
    { subst l0 l v. rewrite map.get_put_same; trivial. }
    left; Tactics.ssplit; trivial; ecancel_assumption. }
  intuition subst.
Abort.*)
End WithParameters.
