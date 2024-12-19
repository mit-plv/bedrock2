Require Import Coq.ZArith.ZArith coqutil.Z.div_mod_to_equations.
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

From coqutil Require Import Word.Properties Word.Interface Tactics.letexists.
Import Interface.word Coq.Lists.List List.ListNotations.
From bedrock2 Require Import Semantics LeakageSemantics BasicC32Semantics LeakageWeakestPrecondition LeakageProgramLogic.
Import LeakageProgramLogic.Coercions.
Section WithOracle.
Context {pick_sp: PickSp}.

#[global] Instance ctspec_of_div3329 : spec_of "div3329" :=
  fun functions => forall k, exists k_, forall t m x,
      LeakageWeakestPrecondition.call functions "div3329" k t m [x]
        (fun k' t' m' rets => exists ret, rets = [ret]
        /\ t' = t /\ m' = m /\ k' = k_
        (*x < 2^32 -> ret = x / 3329 :> Z*) ).

Lemma div3329_ct : program_logic_goal_for_function! div3329.
Proof.
  repeat (straightline || eexists).
  { (* no leakag -- 3 minutes *) cbv [k' k'0]. cbn. exact eq_refl. }
Qed.

#[global] Instance vtspec_of_div3329 : spec_of "div3329_vartime" :=
  fun functions => forall k, forall t m x,
      LeakageWeakestPrecondition.call functions "div3329_vartime" k t m [x]
        (fun k' t' m' rets => exists ret, rets = [ret]
        /\ t' = t /\ m' = m /\ k' = [leak_word (word.of_Z 3329); leak_word x]++k
        (*x < 2^32 -> ret = x / 3329 :> Z*) ).

Lemma div3329_vt : program_logic_goal_for_function! div3329_vartime.
Proof.
  repeat (straightline || eexists).
Qed.

(* Mon Jul  1 14:14:15 EDT 2024 *)

Import Byte.
Definition getchar_event c : LogItem :=
  ((Interface.map.empty, "getchar", []), (Interface.map.empty, [word.of_Z (byte.unsigned c)])).
#[global] Instance ctspec_of_getchar : spec_of "getchar" :=
  fun functions => exists f, forall k t m,
      LeakageWeakestPrecondition.call functions "getchar" k t m []
        (fun k' t' m' rets => exists c, rets = [word.of_Z (byte.unsigned c)] /\ k' = f ++ k /\ m' = m /\
        t' = cons (getchar_event c) t ).

Definition getline := func! (dst, n) ~> n {
  i = $0;
  c = $0;
  while (i < n) {
    unpack! c = getchar();
    if (c == $0x0a) { n = i }
    else { store1(dst + i, c); i = i + $1 }
  }
}.

Local Notation "xs $@ a" := (Array.array Separation.ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").
Local Infix "*" := Separation.sep.
Local Infix "*" := Separation.sep : type_scope.

Definition getline_io n bs :=
  let chars := map getchar_event (rev bs) in
  let newline := if n =? length bs then nil else [getchar_event Byte.x0a] in
  newline ++ chars.

Local Fixpoint getline_leakage f dst n (bs : nat) (i : word) :=
  if i =? n then leak_bool false :: nil else
  match bs with
  | S bs => getline_leakage f dst n bs (add i (of_Z 1)) ++ (leak_word (add dst i) :: leak_bool false :: f ++ leak_unit :: leak_bool true :: nil)
  | O => leak_bool false :: leak_bool true :: f ++ leak_unit :: leak_bool true :: nil
  end.

#[global] Instance ctspec_of_getline : spec_of "getline" :=
  fun functions => exists f, forall k (dst n : word) d t m R,
  (d$@dst * R) m -> length d = n :> Z ->
      LeakageWeakestPrecondition.call functions "getline" k t m [dst; n]
        (fun k' t' m' rets => exists bs es l, rets = [l] /\ k' = f dst n l ++ k /\
        (bs$@dst * es$@(word.add dst l) * R) m' /\
        length bs = l :> Z /\
        length bs + length es = n :> Z /\
        t' = getline_io n bs ++ t 
        (* /\ ~ In Byte.x0a bs *)
        ).

(* Mon Jul  1 14:24:28 EDT 2024 *)

Require Coq.Program.Wf.
Import Separation SeparationLogic.

Lemma getline_ct : program_logic_goal_for_function! getline.
Proof.
  enter getline. destruct H as [f H]. Print straightline.
  intros;
         match goal with
         | |- call _ _ _ _ _ _ _ => idtac
         | |- exists _, _ => eexists
         end; intros;
         match goal with
         | H:Interface.map.get ?functions ?fname = Some _
           |- _ =>
               eapply LeakageWeakestPreconditionProperties.start_func;
                [ exact H | clear H ]
         end; cbv beta match delta [func].
  repeat straightline.

  refine ((LeakageLoops.tailrec_earlyout
    (HList.polymorphic_list.cons (list byte)
    (HList.polymorphic_list.cons (_ -> Prop)
    HList.polymorphic_list.nil))
    ["dst";"n";"i";"c"])
    (fun (v:Z) es R k t m  dst_ n_ i c => PrimitivePair.pair.mk (
      n_ = n /\ dst_ = dst /\ v = i :> Z /\
      i <= n /\
      (es$@(word.add dst i) * R) m /\ length es = word.sub n i :> Z
    )
    (fun                K T M DST N I C => DST = dst /\
      exists bs ES, (bs$@(word.add dst i) * ES$@(word.add dst I) * R) M /\ I = N /\
      length bs = word.sub I i :> Z /\
      length ES = word.sub n I :> Z /\
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
    { split. { subst v. rewrite word.unsigned_of_Z_0. blia. }
      subst v; rewrite word.add_0_r; split; [ecancel_assumption|]. rewrite word.sub_0_r; auto. }

    { 
      pose proof word.unsigned_range n.
      pose proof word.unsigned_range x3 as Hx3.
      subst br. rewrite unsigned_ltu in H2; case Z.ltb eqn:? in H2; 
          rewrite ?word.unsigned_of_Z_1, ?word.unsigned_of_Z_0, ?word.unsigned_sub_nowrap  in *; try blia; [].
      eapply LeakageWeakestPreconditionProperties.Proper_call; repeat intro; cycle 1.
      { eapply H. }
      repeat straightline.
      eexists _, _; repeat straightline.
      split; repeat straightline.
      split; repeat straightline.
      { left; repeat straightline.
        { subst br. rewrite unsigned_ltu, Z.ltb_irrefl; trivial. }
        eexists _, _; repeat straightline.
        eapply word.if_nonzero, word.eqb_true in H4.
        instantiate (1:=nil); cbn [Array.array]; split.
        { ecancel_assumption. }
        { 
          split; trivial.
          split. { rewrite word.unsigned_sub_nowrap; simpl length; blia. }
          split. { rewrite word.unsigned_sub_nowrap; blia. }
          split. { blia. }
          split. { (* I/O *)
            cbv [getline_io]. cbn [map rev List.app length]. case (Z.eqb_spec (n-x3) 0%nat) as []; try blia.
            rewrite app_nil_r. subst a0. simpl.
            eapply f_equal2; f_equal; trivial.
            progress change 10 with (byte.unsigned Byte.x0a) in H4.
            pose proof byte.unsigned_range x1.
            pose proof byte.unsigned_range Byte.x0a.
            eapply word.of_Z_inj_small, byte.unsigned_inj in H4; trivial; blia. }
          (* leakage *)
          subst k'. subst k'''. cbn [getline_leakage leak_binop "++" length].
          rewrite (proj2 (Z.eqb_neq _ _)) by blia; trivial. simpl. rewrite <- app_assoc. reflexivity. } }

      (* store *)
      destruct x as [|x_0 x]. { cbn [length] in *; blia. }
      cbn [Array.array] in *.
      repeat straightline.
      right; repeat straightline.
      eexists _, _, _; repeat straightline.
      { instantiate (1:=x).
        subst v3.
        rewrite word.add_assoc.
        split. { rewrite word.unsigned_add_nowrap; rewrite ?word.unsigned_of_Z_1; try blia. }
        split; [ecancel_assumption|].
        cbn [length] in *.
        pose proof word.unsigned_of_Z_1.
        pose proof word.unsigned_add_nowrap x3 (word.of_Z 1).
        pose proof word.unsigned_sub_nowrap n (add x3 (of_Z 1)).
        blia. }
      { split.
        { subst  v3.
          pose proof word.unsigned_of_Z_1.
          pose proof word.unsigned_add_nowrap x3 (word.of_Z 1).
          pose proof word.unsigned_sub_nowrap n (add x3 (of_Z 1)).
          blia. }
        repeat straightline.
        (* subroutine return *)
        subst v3.

        rename x9 into bs.
        rename x10 into es.
        rename x5 into I.
        rename x3 into _i.
        rewrite word.add_assoc in H10.

        eexists (byte.of_Z v2::bs), (es).
        cbn ["$@" "++"].
        split. { ecancel_assumption. }
        split; trivial.
        split. { cbn [length]. rewrite Nat2Z.inj_succ, H15.
          pose proof word.unsigned_of_Z_1.
          pose proof word.unsigned_add_nowrap _i (of_Z 1) ltac:(blia).
          rewrite 2 word.unsigned_sub_nowrap; blia. }
        split; trivial.
        split. {
          pose proof word.unsigned_of_Z_1.
          pose proof word.unsigned_add_nowrap _i (of_Z 1) ltac:(blia).
          blia. }
        split. { (* I/O *)
          subst T a0.
          cbv [getline_io]; cbn [rev List.map].
          repeat rewrite ?map_app, <-?app_comm_cons, <-?app_assoc; f_equal.
          { pose proof word.unsigned_of_Z_1 as H_1.
            rewrite (word.unsigned_add_nowrap _i (of_Z 1) ltac:(blia)), H_1; cbn [length].
            case Z.eqb eqn:? at 1; case Z.eqb eqn:? at 1; trivial; try blia.
            { (* WHY manual? does zify do a bad job here? *) eapply Z.eqb_neq in Heqb1. blia. }
            { (* WHY manual? does zify do a bad job here? *) eapply Z.eqb_eq in Heqb1. blia. } }
          f_equal.
          cbn [map List.app].
          f_equal.
          f_equal.
          subst v2.
          pose proof byte.unsigned_range x1.
          rewrite word.unsigned_of_Z_nowrap, byte.of_Z_unsigned; trivial; blia. }
        (* leakage *)
        subst K k'0 k'' k' a1; cbn [getline_leakage leak_binop length].
        rewrite (proj2 (Z.eqb_neq _ _)) by blia; trivial.
        repeat (simpl || rewrite <- app_assoc). reflexivity. } }

    { (* buffer full *)
      replace x3 with n in *; cycle 1.
      { subst br; rewrite unsigned_ltu in *; eapply word.if_zero, Z.ltb_nlt in H2.
        apply word.unsigned_inj. blia. }
      exists x, nil; cbn [Array.array].
      split. { ecancel_assumption. }
      split. { trivial. }
      split. { trivial. }
      rewrite word.unsigned_sub_nowrap, Z.sub_diag in H7 by blia.
      split. { rewrite word.unsigned_sub_nowrap, Z.sub_diag by blia; trivial. }
      split. { blia. }
      split. { destruct x; cbn [length] in *; try blia; cbn.
        rewrite Z.sub_diag; reflexivity. }
      destruct x; try (cbn in *; blia).
      cbn [getline_leakage length]; rewrite Z.eqb_refl; trivial. }

    split. { subst k0 v0 v. rewrite word.sub_0_r in *.
      assert (length x3 = Z.to_nat (word.unsigned x0)) as -> by blia. reflexivity. }
    subst v.
    rewrite word.add_0_r in *.
    split.
    { ecancel_assumption. }
    split.
    { rewrite H5. rewrite word.sub_0_r. trivial. }
    split.
    { rewrite H5, H6, word.sub_0_r, word.unsigned_sub_nowrap; blia. }
    subst t0.
    rewrite word.unsigned_of_Z_0, Z.sub_0_r.
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
Print getline_io.

#[global] Instance ctspec_of_password_checker : spec_of "password_checker" :=
  fun functions => exists f, forall (username password_addr : word), forall R t m password,
      length password = 8 :> Z ->
      (password$@password_addr * R) m ->
      LeakageWeakestPrecondition.call functions "password_checker" [] t m [password_addr]
        (fun k' t' m' rets =>
           exists bs ret (l : word),
             rets = [ret (*bs =? password*)] /\
               (password$@password_addr * R) m' /\
               t' = getline_io 8 bs ++ t /\
               length bs = l :> Z /\
               (k' = f password_addr l) /\
               (word.unsigned ret = 1 <-> bs = password)).

Fail Lemma password_checker_ct : program_logic_goal_for_function! password_checker. (*Why*)
Global Instance spec_of_memequal : spec_of "memequal" := spec_of_memequal.

Lemma password_checker_ct : program_logic_goal_for_function! password_checker.
Proof.
  enter password_checker. destruct H as [f H]. destruct H0 as [g H0].
         match goal with
         | |- call _ _ _ _ _ _ _ => idtac
         | |- exists _, _ => eexists
         end; intros;
         match goal with
         | H:Interface.map.get ?functions ?fname = Some _
           |- _ =>
               eapply LeakageWeakestPreconditionProperties.start_func;
                [ exact H | clear H ]
         end; cbv beta match delta [func].
  
  repeat straightline.
  eapply LeakageWeakestPreconditionProperties.Proper_call; repeat intro; cycle 1.
  { eapply H. 2: eassumption. ecancel_assumption. }
  repeat straightline.
  seprewrite_in_by @Array.bytearray_index_merge H9 ltac:(blia).
  eapply LeakageWeakestPreconditionProperties.Proper_call; repeat intro; cycle 1.
  { eapply H0. split.
    { ecancel_assumption. } split.
    { ecancel_assumption. }
    split.
    { rewrite ?app_length; blia. }
    { rewrite H1. reflexivity. } }
  assert (length ((x ++ x0)) = 8%nat).
  { rewrite ?app_length. rewrite word.unsigned_of_Z_nowrap in H11; blia. }
  repeat straightline.
  split. { ecancel_assumption. }
  split. { exact eq_refl. }
  split. { eassumption. }
  split. { (* leakage *)
    subst a0. subst a. subst k'0. subst k'. reflexivity. }
  { (* functional correctness *)
    subst v.
    destruct (word.eqb_spec x1 (of_Z 8)) as [->|?]; cycle 1.
    { rewrite word.unsigned_and_nowrap, word.unsigned_of_Z_0, Z.land_0_l; split; try discriminate.
      intros X%(f_equal (@length _)). case H13; clear H13; apply word.unsigned_inj.
      rewrite <-H10, X, word.unsigned_of_Z_nowrap; blia. }
    rewrite word.unsigned_and_nowrap, word.unsigned_of_Z_1.
    destruct x0; cycle 1.
    { cbn [length] in *. rewrite word.unsigned_of_Z_nowrap in H10, H11; blia. }
    { rewrite ?app_nil_r in *. rewrite <-H16.
      case H15 as [->|]; intuition try congruence. rewrite H15. trivial. } }
  Unshelve.
  all: assumption || exact nil.
Qed.

Definition output_event x : LogItem :=
  ((Interface.map.empty, "output", [x]), (Interface.map.empty, [])).
#[global] Instance ctspec_of_output : spec_of "output" :=
  fun functions => exists f, forall k t m x,
      LeakageWeakestPrecondition.call functions "output" k t m [x]
        (fun k' t' m' rets => rets = [] /\ k' = f ++ k /\ m' = m /\
        t' = cons (output_event x) t ).

Definition getprime_event p : LogItem :=
  ((Interface.map.empty, "getprime", []), (Interface.map.empty, [p])).
#[global] Instance ctspec_of_getprime : spec_of "getprime" :=
  fun functions => exists f, forall k t m,
      LeakageWeakestPrecondition.call functions "getprime" k t m []
        (fun k' t' m' rets => exists p, rets = [p] /\ k' = f ++ k /\ m' = m /\
        t' = cons (getprime_event p) t ).

Definition semiprime := func! () ~> (p, q) {
  unpack! p = getprime();
  unpack! q = getprime();
  n = p * q;
  output(n)
}.

#[global] Instance ctspec_of_semiprime : spec_of "semiprime" :=
  fun functions => exists f, forall t m k,
      LeakageWeakestPrecondition.call functions "semiprime" k t m []
      (fun k' t' m' rets => exists p q, rets = [p;q] /\ k' = f ++ k /\ m' = m
        /\ t' = [output_event (word.mul p q); getprime_event q; getprime_event p]++t).

Lemma semiprime_ct : program_logic_goal_for_function! semiprime.
Proof.
  enter semiprime. destruct H as [f H]. destruct H0 as [g H0]. destruct H1 as [h H1].
  match goal with
         | |- call _ _ _ _ _ _ _ => idtac
         | |- exists _, _ => eexists
         end; intros;
         match goal with
         | H:Interface.map.get ?functions ?fname = Some _
           |- _ =>
               eapply LeakageWeakestPreconditionProperties.start_func;
                [ exact H | clear H ]
         end; cbv beta match delta [func].
  repeat straightline.
  eapply LeakageWeakestPreconditionProperties.Proper_call; repeat intro; [|eapply H]; repeat straightline.
  eapply LeakageWeakestPreconditionProperties.Proper_call; repeat intro; [|eapply H]; repeat straightline.
  eapply LeakageWeakestPreconditionProperties.Proper_call; repeat intro; [|eapply H1]; repeat straightline.
  Tactics.ssplit; trivial; align_trace.
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
      m =* ptsto a a0 * ptsto (word.add a (word.of_Z 1)) a1 * R ->
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
    map.get l "i" = Some (word.of_Z (Z.of_nat i)) /\ (
    i = 0%nat /\ m =* ptsto a a0 * ptsto (word.add a (word.of_Z 1)) a1 * R \/
    i = 1%nat /\ False \/
    i = 2%nat /\ False)).
  Tactics.ssplit; auto using lt_wf.
  { exists 0%nat; Tactics.ssplit.
    { subst l0 l; rewrite map.get_put_diff, map.get_put_same; congruence. }
    { subst l0 l v. rewrite map.get_put_same; trivial. }
    left; Tactics.ssplit; trivial; ecancel_assumption. }
  intuition subst.
Abort.*)
