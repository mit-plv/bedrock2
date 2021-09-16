Require Import Coq.ZArith.ZArith.
Require Import compiler.FlatImp.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.simpl_rewrite.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.Utility.
Require Import coqutil.Z.Lia.
Require Import coqutil.Macros.unique.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Solver.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Map.TestLemmas.
Require Import bedrock2.Syntax.
Require Import coqutil.Datatypes.ListSet.
Require Import coqutil.Tactics.Simp.
Require Import coqutil.Tactics.autoforward.
Require Import compiler.Simulation.

Open Scope Z_scope.

Local Notation srcvar := String.string (only parsing).
Local Notation impvar := Z (only parsing).
Local Notation stmt  := (@FlatImp.stmt srcvar). (* input type *)
Local Notation stmt' := (@FlatImp.stmt impvar). (* output type *)
Local Notation bcond  := (@FlatImp.bcond srcvar).
Local Notation bcond' := (@FlatImp.bcond impvar).

Axiom TODO_sam: False.

Definition accessed_vars_bcond(c: bcond): list srcvar :=
  match c with
  | CondBinary _ x y => list_union String.eqb [x] [y]
  | CondNez x => [x]
  end.

Fixpoint live(s: stmt)(used_after: list srcvar): list srcvar :=
  match s with
  | SSet x y
  | SLoad _ x y _
  | SInlinetable _ x _ y =>
    list_union String.eqb [y] (list_diff String.eqb used_after [x])
  | SStore _ a x _ => list_union String.eqb [a; x] used_after
  | SStackalloc x _ body => list_diff String.eqb (live body used_after) [x]
  | SLit x _ => list_diff String.eqb used_after [x]
  | SOp x _ y z => list_diff String.eqb (list_union String.eqb [y; z] used_after) [x]
  | SIf c s1 s2 => list_union String.eqb
                              (list_union String.eqb (live s1 used_after) (live s2 used_after))
                              (accessed_vars_bcond c)
  | SSeq s1 s2 => live s1 (live s2 used_after)
  | SLoop s1 c s2 =>
    live s1 (list_union String.eqb (accessed_vars_bcond c) (list_union String.eqb used_after (live s2 [])))
  | SSkip => used_after
  | SCall binds _ args
  | SInteract binds _ args => list_union String.eqb args (list_diff String.eqb used_after binds)
  end.

(* old RegAlloc files:
https://github.com/mit-plv/bedrock2/tree/7cbae1a1caf7d19270d0fb37199f86eb8ea5ce4f/compiler/src/compiler
*)

Declare Scope option_monad_scope. Local Open Scope option_monad_scope.

Notation "' pat <- c1 ;; c2" :=
  (match c1 with
   | Some pat => c2
   | None => None
   end)
  (at level 61, pat pattern, c1 at next level, right associativity) : option_monad_scope.

Notation "x <- c1 ;; c2" :=
  (match c1 with
   | Some x => c2
   | None => None
   end)
  (at level 61, c1 at next level, right associativity) : option_monad_scope.

Notation "c1 ;; c2" :=
  (match c1 with
   | Some _ => c2
   | None => None
   end)
  (at level 61, right associativity) : option_monad_scope.

Scheme Equality for Syntax.access_size. (* to create access_size_beq *)
Scheme Equality for bopname. (* to create bopname_beq *)
Scheme Equality for bbinop. (* to create bbinop_beq *)

Instance access_size_beq_spec: EqDecider access_size_beq.
Proof. intros. destruct x; destruct y; simpl; constructor; congruence. Qed.

Instance bopname_beq_spec: EqDecider bopname_beq.
Proof. intros. destruct x; destruct y; simpl; constructor; congruence. Qed.

Instance bbinop_beq_spec: EqDecider bbinop_beq.
Proof. intros. destruct x; destruct y; simpl; constructor; congruence. Qed.

(* TODO List.list_eqb should not require an EqDecider instance *)
(* TODO move *)
Module Byte.
  Instance eqb_spec: EqDecider Byte.eqb.
  Proof.
    intros. destruct (Byte.eqb x y) eqn: E; constructor.
    - apply Byte.byte_dec_bl. assumption.
    - apply Byte.eqb_false. assumption.
  Qed.
End Byte.
Existing Instance List.list_eqb_spec.

Section PairList.
  Context {A B: Type}.

  Definition remove_by_fst(aeqb: A -> A -> bool)(key: A): list (A * B) -> list (A * B) :=
    List.filter (fun '(a, b) => negb (aeqb a key)).

  Definition remove_by_snd(beqb: B -> B -> bool)(key: B): list (A * B) -> list (A * B) :=
    List.filter (fun '(a, b) => negb (beqb b key)).

  Lemma In_remove_by_fst{aeqb: A -> A -> bool}{aeqb_spec: EqDecider aeqb}: forall a a' b l,
      In (a, b) (remove_by_fst aeqb a' l) ->
      In (a, b) l /\ a <> a'.
  Proof.
    unfold remove_by_fst. intros. eapply filter_In in H. destruct H.
    destr (aeqb a a'). 1: discriminate. auto.
  Qed.

  Lemma not_In_remove_by_snd{beqb: B -> B -> bool}{beqb_spec: EqDecider beqb}: forall a b l,
      ~ In (a, b) (remove_by_snd beqb b l).
  Proof.
    unfold remove_by_snd, not. intros. eapply filter_In in H. apply proj2 in H.
    destr (beqb b b). 1: discriminate. apply E. reflexivity.
  Qed.

  Lemma In_remove_by_snd{beqb: B -> B -> bool}{beqb_spec: EqDecider beqb}: forall a b b' l,
      In (a, b) (remove_by_snd beqb b' l) ->
      In (a, b) l /\ b <> b'.
  Proof.
    unfold remove_by_snd. intros. eapply filter_In in H. destruct H.
    destr (beqb b b'). 1: discriminate. auto.
  Qed.
End PairList.

Section IntersectLemmas.
  Context {A: Type}(aeqb: A -> A -> bool){aeqb_spec: EqDecider aeqb}.

  Lemma intersect_max_length_l: forall l1 l2,
      (length (list_intersect aeqb l1 l2) <= length l1)%nat.
  Proof.
    intros.
    induction l1; intros.
    - simpl. reflexivity.
    - unfold list_intersect in *. cbn [fold_right]. destruct_one_match.
      + cbn [length]. eapply Peano.le_n_S. apply IHl1.
      + cbn [length]. eapply Nat.le_trans. 1: apply IHl1. constructor. reflexivity.
  Qed.

  Lemma intersect_same_length: forall l1 l2,
      length (list_intersect aeqb l1 l2) = length l1 ->
      list_intersect aeqb l1 l2 = l1.
  Proof.
    induction l1; intros.
    - reflexivity.
    - simpl in *. destruct_one_match; simpl in *.
      + f_equal. eapply IHl1. congruence.
      + pose proof (intersect_max_length_l l1 l2) as P.
        rewrite H in P. exfalso. eapply Nat.nle_succ_diag_l. exact P.
  Qed.
End IntersectLemmas.

#[export] Hint Resolve Byte.eqb_spec : typeclass_instances.

Definition assert(b: bool): option unit := if b then Some tt else None.

Definition mapping_eqb: srcvar * impvar -> srcvar * impvar -> bool :=
  fun '(x, x') '(y, y') => andb (String.eqb x y) (Z.eqb x' y').

Definition assert_in(y: srcvar)(y': impvar)(m: list (srcvar * impvar)): option unit :=
  _ <- List.find (mapping_eqb (y, y')) m;; Some tt.

Definition assert_ins(args: list srcvar)(args': list impvar)(m: list (srcvar * impvar)): option unit :=
  assert (Nat.eqb (List.length args) (List.length args'));;
  assert (List.forallb (fun p => if List.find (mapping_eqb p) m then true else false)
                       (List.combine args args')).

Definition check_bcond(m: list (srcvar * impvar))(c: bcond)(c': bcond'): option unit :=
  match c, c' with
  | CondBinary op y z, CondBinary op' y' z' =>
    assert_in y y' m;; assert_in z z' m;; assert (bbinop_beq op op')
  | CondNez y, CondNez y' =>
    assert_in y y' m
  | _, _ => None
  end.

Definition assignment(m: list (srcvar * impvar))(x: srcvar)(x': impvar): list (srcvar * impvar) :=
  (x, x') :: (remove_by_snd Z.eqb x' (remove_by_fst String.eqb x m)).

Fixpoint assignments(m: list (srcvar * impvar))(xs: list srcvar)(xs': list impvar):
  option (list (srcvar * impvar)) :=
  match xs, xs' with
  | x :: xs0, x' :: xs0' => assignments (assignment m x x') xs0 xs0'
  | nil, nil => Some m
  | _, _ => None
  end.

Section LoopInv.
  Context (check: list (srcvar * impvar) -> stmt -> stmt' -> option (list (srcvar * impvar)))
          (s1 s2: stmt)(s1' s2': stmt').

  (* Probably one iteration to compute the invariant, and another one to check that it
     doesn't change any more, ie 2 iterations, is enough, but that might be hard to prove.
     `List.length m` is enough fuel because the size can decrease at most that many times
     before we get to an empty invariant. *)
  Fixpoint loop_inv'(fuel: nat)(m: list (srcvar * impvar)): option (list (srcvar * impvar)) :=
    match fuel with
    | O => None
    | S fuel' =>
      m1 <- check m s1 s1';;
      m2 <- check m1 s2 s2';;
      let cand := list_intersect mapping_eqb m m2 in
      if Nat.eqb (List.length m) (List.length cand)
      then Some cand
      else loop_inv' fuel' cand
    end.
End LoopInv.

(* does 2 things at once: checks that the correct variables are read and computes the bindings
   that hold after executing the statement *)
(* m: conservative underapproximation of which impvar stores which srcvar *)
Fixpoint check(m: list (srcvar * impvar))(s: stmt)(s': stmt'){struct s}: option (list (srcvar * impvar)) :=
  match s, s' with
  | SLoad sz x y ofs, SLoad sz' x' y' ofs' =>
    assert_in y y' m;;
    assert (Z.eqb ofs ofs');;
    assert (access_size_beq sz sz');;
    Some (assignment m x x')
  | SStore sz x y ofs, SStore sz' x' y' ofs' =>
    assert_in x x' m;;
    assert_in y y' m;;
    assert (Z.eqb ofs ofs');;
    assert (access_size_beq sz sz');;
    Some m
  | SInlinetable sz x bs y, SInlinetable sz' x' bs' y' =>
    assert_in y y' m;;
    (* FlatToRiscv uses x' as a tmp register, and that should not overwrite y' *)
    assert (negb (Z.eqb x' y'));;
    assert (access_size_beq sz sz');;
    assert (List.list_eqb Byte.eqb bs bs');;
    Some (assignment m x x')
  | SStackalloc x n body, SStackalloc x' n' body' =>
    assert (Z.eqb n n');;
    check (assignment m x x') body body'
  | SLit x z, SLit x' z' =>
    assert (Z.eqb z z');;
    Some (assignment m x x')
  | SOp x op y z, SOp x' op' y' z' =>
    assert_in y y' m;;
    assert_in z z' m;;
    assert (bopname_beq op op');;
    Some (assignment m x x')
  | SSet x y, SSet x' y' =>
    assert_in y y' m;; Some (assignment m x x')
  | SIf c s1 s2, SIf c' s1' s2' =>
    check_bcond m c c';;
    m1 <- check m s1 s1';;
    m2 <- check m s2 s2';;
    Some (list_intersect mapping_eqb m1 m2)
  | SLoop s1 c s2, SLoop s1' c' s2' =>
    inv <- loop_inv' check s1 s2 s1' s2' (S (List.length m)) m;;
    m1 <- check inv s1 s1';;
    check_bcond m1 c c';;
    m2 <- check m1 s2 s2';;
    Some m1
  | SSeq s1 s2, SSeq s1' s2' =>
    m1 <- check m s1 s1';;
    check m1 s2 s2'
  | SSkip, SSkip =>
    Some m
  | SCall binds f args, SCall binds' f' args'
  | SInteract binds f args, SInteract binds' f' args' =>
    assert (String.eqb f f');;
    assert_ins args args' m;;
    assignments m binds binds'
  | _, _ => None
  end.

Definition loop_inv(corresp: list (srcvar * impvar))(s1 s2: stmt)(s1' s2': stmt'): list (srcvar * impvar) :=
  match loop_inv' check s1 s2 s1' s2' (S (List.length corresp)) corresp with
  | Some inv => inv
  | None => []
  end.

Definition extends(m1 m2: list (srcvar * impvar)): Prop :=
  forall x x', assert_in x x' m2 = Some tt -> assert_in x x' m1 = Some tt.

Lemma extends_refl: forall m, extends m m.
Proof. unfold extends. eauto. Qed.

Lemma extends_nil: forall m, extends m [].
Proof. unfold extends, assert_in. simpl. intros. discriminate. Qed.

Lemma extends_trans: forall m1 m2 m3, extends m1 m2 -> extends m2 m3 -> extends m1 m3.
Proof. unfold extends. eauto. Qed.

Lemma extends_cons: forall a l1 l2,
    extends l1 l2 ->
    extends (a :: l1) (a :: l2).
Proof.
  unfold extends, assert_in. simpl. intros. simp.
  destruct_one_match_hyp. 1: reflexivity.
  eapply H. rewrite E. reflexivity.
Qed.

Lemma extends_cons_l: forall a l,
    extends (a :: l) l.
Proof.
  unfold extends, assert_in. simpl. intros. simp.
  destruct_one_match. 1: reflexivity.
  destruct_one_match_hyp; discriminate.
Qed.

Lemma extends_cons_r: forall a l1 l2,
    In a l1 ->
    extends l1 l2 ->
    extends l1 (a :: l2).
Proof.
  unfold extends, assert_in. simpl. intros. simp.
  destruct_one_match_hyp. 2: {
    eapply H0. rewrite E. reflexivity.
  }
  destruct_one_match. 1: reflexivity.
  eapply find_none in E1. 2: eassumption.
  simpl in E1. exfalso. congruence.
Qed.

Lemma extends_intersect_l: forall l1 l2,
    extends l1 (list_intersect mapping_eqb l1 l2).
Proof.
  intros. induction l1; simpl.
  - apply extends_refl.
  - destruct_one_match.
    + eapply extends_cons. apply IHl1.
    + eapply extends_trans. 2: apply IHl1. apply extends_cons_l.
Qed.

Lemma extends_intersect_r: forall l1 l2,
    extends l2 (list_intersect mapping_eqb l1 l2).
Proof.
  induction l1; intros.
  - simpl. apply extends_nil.
  - simpl. unfold mapping_eqb. destruct a as [x x']. destruct_one_match.
    + destruct p as [z z']. eapply find_some in E. destruct E as [E1 E2].
      apply Bool.andb_true_iff in E2. destruct E2 as [E2 E3].
      autoforward with typeclass_instances in E2.
      autoforward with typeclass_instances in E3.
      subst z z'.
      eapply extends_cons_r. 1: assumption. apply IHl1.
    + apply IHl1.
Qed.

Lemma extends_loop_inv': forall s1 s2 s1' s2' fuel corresp1 corresp2,
    loop_inv' check s1 s2 s1' s2' fuel corresp1 = Some corresp2 ->
    extends corresp1 corresp2.
Proof.
  induction fuel; simpl; intros.
  - discriminate.
  - simp. destruct_one_match_hyp.
    + simp. symmetry in E1. eapply intersect_same_length in E1.
      rewrite E1. eapply extends_refl.
    + eapply IHfuel in H. eapply extends_trans.
      2: exact H. apply extends_intersect_l.
Qed.

Lemma extends_loop_inv: forall corresp s1 s2 s1' s2',
    extends corresp (loop_inv corresp s1 s2 s1' s2').
Proof.
  intros. unfold loop_inv. destruct_one_match. 2: {
    unfold extends. unfold assert_in. simpl. intros. discriminate.
  }
  eapply extends_loop_inv'. eassumption.
Qed.

Lemma defuel_loop_inv': forall fuel corresp inv m1 m2 s1 s2 s1' s2',
    loop_inv' check s1 s2 s1' s2' fuel corresp = Some inv ->
    check inv s1 s1' = Some m1 ->
    check m1 s2 s2' = Some m2 ->
    inv = list_intersect mapping_eqb inv m2.
Proof.
  induction fuel; intros; simpl in *.
  - discriminate.
  - simp. destruct_one_match_hyp.
    + simp. symmetry in E1. eapply intersect_same_length in E1. rewrite E1 in H0.
      rewrite E in H0. simp.
      rewrite E0 in H1. simp.
      rewrite <- E1 at 1. reflexivity.
    + eapply IHfuel; eassumption.
Qed.

(* Similar effect as unfolding loop_inv where loop_inv's definition does not involve fuel,
   ie this lemma allows us to prove `inv = intersect inv (update inv loop_body)` *)
Lemma defuel_loop_inv: forall corresp inv m1 m2 s1 s2 s1' s2',
    inv = loop_inv corresp s1 s2 s1' s2' ->
    check inv s1 s1' = Some m1 ->
    check m1 s2 s2' = Some m2 ->
    inv = list_intersect mapping_eqb inv m2.
Proof.
  unfold loop_inv. intros. subst. destruct_one_match. 2: reflexivity.
  eapply defuel_loop_inv'; eassumption.
Qed.

Section RegAlloc.

  Context {width} {BW: Bitwidth width} {word: word.word width} {word_ok: word.ok word}.
  Context {mem: map.map word byte}.
  Context {srcLocals: map.map srcvar word}.
  Context {impLocals: map.map impvar word}.
  Context {srcLocalsOk: map.ok srcLocals}.
  Context {impLocalsOk: map.ok impLocals}.
  Context {srcEnv: map.map String.string (list srcvar * list srcvar * stmt)}.
  Context {impEnv: map.map String.string (list impvar * list impvar * stmt')}.
  Context {ext_spec: Semantics.ExtSpec}.

  Definition states_compat(st: srcLocals)(corresp: list (srcvar * impvar))(st': impLocals) :=
    forall (x: srcvar) (x': impvar),
      assert_in x x' corresp = Some tt ->
      forall w,
        map.get st x = Some w ->
        map.get st' x' = Some w.

  Definition precond(corresp: list (srcvar * impvar))(s: stmt)(s': stmt'): list (srcvar * impvar) :=
    match s, s' with
    | SLoop s1 c s2, SLoop s1' c' s2' => loop_inv corresp s1 s2 s1' s2'
    | _, _ => corresp
    end.

  Lemma states_compat_eval_bcond: forall lH lL c c' b corresp,
      check_bcond corresp c c' = Some tt ->
      eval_bcond lH c = Some b ->
      states_compat lH corresp lL ->
      eval_bcond lL c' = Some b.
  Proof.
    intros. rename H1 into C. unfold states_compat in C.
    destruct c; cbn in *; simp;
      repeat match goal with
             | u: unit |- _ => destruct u
             end;
      unfold assert in *;
      cbn; simp;
      repeat match goal with
             | H: @eq bool _ _ |- _ => autoforward with typeclass_instances in H
             end;
      subst;
      erewrite ?C by eauto; reflexivity.
  Qed.

  Lemma states_compat_eval_bcond_None: forall lH lL c c' corresp,
      check_bcond corresp c c' = Some tt ->
      eval_bcond lH c <> None ->
      states_compat lH corresp lL ->
      eval_bcond lL c' <> None.
  Proof.
    intros. destr (eval_bcond lH c). 2: congruence.
    erewrite states_compat_eval_bcond; eassumption.
  Qed.

  Lemma states_compat_eval_bcond_bw: forall lH lL c c' b corresp,
      check_bcond corresp c c' = Some tt ->
      eval_bcond lL c' = Some b ->
      states_compat lH corresp lL ->
      eval_bcond lH c <> None ->
      eval_bcond lH c = Some b.
  Proof.
    intros. destr (eval_bcond lH c). 2: congruence.
    symmetry. rewrite <- H0. eapply states_compat_eval_bcond; eassumption.
  Qed.

  Lemma states_compat_extends: forall lH m1 m2 lL,
      extends m1 m2 ->
      states_compat lH m1 lL ->
      states_compat lH m2 lL.
  Proof.
    unfold states_compat, extends. intros. eauto.
  Qed.

  Lemma states_compat_precond: forall lH corresp lL s s',
      states_compat lH corresp lL ->
      states_compat lH (precond corresp s s') lL.
  Proof.
    intros.
    destruct s; cbn; try assumption.
    destruct s'; cbn; try assumption.
    eapply states_compat_extends. 2: eassumption.
    eapply extends_loop_inv.
  Qed.
  Hint Resolve states_compat_precond : states_compat.

  Lemma states_compat_get: forall corresp lL lH y y' v,
      states_compat lH corresp lL ->
      assert_in y y' corresp = Some tt ->
      map.get lH y = Some v ->
      map.get lL y' = Some v.
  Proof. unfold states_compat. eauto. Qed.

  Lemma states_compat_getmany: forall corresp lL lH ys ys' vs,
      states_compat lH corresp lL ->
      assert_ins ys ys' corresp = Some tt ->
      map.getmany_of_list lH ys = Some vs ->
      map.getmany_of_list lL ys' = Some vs.
  Proof.
    induction ys; intros.
    - unfold assert_ins in *. cbn in *. simp. destruct ys'. 2: discriminate. reflexivity.
    - cbn in *. unfold assert_ins, assert in H0. simp.
      autoforward with typeclass_instances in E3. destruct ys' as [|a' ys']. 1: discriminate.
      inversion E3. clear E3.
      cbn in *. simp. simpl in E2.
      erewrite states_compat_get; try eassumption. 2: {
        unfold assert_in. unfold mapping_eqb. rewrite E1. reflexivity.
      }
      unfold map.getmany_of_list in *.
      erewrite IHys; eauto.
      unfold assert_ins. rewrite H1. rewrite Nat.eqb_refl. simpl.
      unfold assert. rewrite E2. reflexivity.
  Qed.

  Lemma states_compat_put: forall lH corresp lL x x' v,
      states_compat lH corresp lL ->
      states_compat (map.put lH x v) (assignment corresp x x') (map.put lL x' v).
  Proof.
    intros. unfold states_compat in *. intros k k'. intros.
    rewrite map.get_put_dec. rewrite map.get_put_dec in H1.
    unfold assert_in, assignment in H0. simp. simpl in E.
    rewrite String.eqb_sym, Z.eqb_sym in E.
    destr (Z.eqb x' k').
    - subst k'.
      destr (String.eqb x k).
      + assumption.
      + simpl in E. eapply find_some in E. destruct E as [E F].
        destruct p. eapply Bool.andb_true_iff in F. destruct F as [F1 F2].
        eapply String.eqb_eq in F1. subst s.
        eapply Z.eqb_eq in F2. subst z.
        exfalso. eapply not_In_remove_by_snd in E. exact E.
    - rewrite Bool.andb_false_r in E.
      eapply find_some in E. destruct E as [E F].
      destruct p. eapply Bool.andb_true_iff in F. destruct F as [F1 F2].
      eapply String.eqb_eq in F1. subst s.
      eapply Z.eqb_eq in F2. subst z.
      eapply In_remove_by_snd in E. apply proj1 in E.
      eapply In_remove_by_fst in E. destruct E.
      destr (String.eqb x k).
      + exfalso. congruence.
      + eapply H. 2: eassumption. unfold assert_in.
        destruct_one_match. 1: reflexivity.
        eapply find_none in E1. 2: eassumption.
        simpl in E1. rewrite String.eqb_refl, Z.eqb_refl in E1. discriminate.
  Qed.

  Lemma putmany_of_list_zip_states_compat: forall binds binds' resvals lL lH l' corresp corresp',
      map.putmany_of_list_zip binds resvals lH = Some l' ->
      assignments corresp binds binds' = Some corresp' ->
      states_compat lH corresp lL ->
      exists lL',
        map.putmany_of_list_zip binds' resvals lL = Some lL' /\
        states_compat l' corresp' lL'.
  Proof.
    induction binds; intros.
    - simpl in H. simp. destruct binds'. 2: discriminate.
      simpl in *. simp. eauto.
    - simpl in *. simp.
      specialize IHbinds with (1 := H).
      rename l' into lH'.
      edestruct IHbinds as (lL' & P & C). 1: eassumption. 1: eapply states_compat_put. 1: eassumption.
      simpl. rewrite P. eauto.
  Qed.

  Hint Constructors exec.exec : checker_hints.
  Hint Resolve states_compat_get : checker_hints.
  Hint Resolve states_compat_put : checker_hints.

  Lemma checker_correct: forall (e: srcEnv) (e': impEnv) s t m lH mc post,
      (forall f argnames retnames body,
          map.get e f = Some (argnames, retnames, body) ->
          exists args binds body' corresp,
            map.get e' f = Some (map snd args, map snd binds, body') /\
            argnames = map fst args /\
            retnames = map fst binds /\
            check args body body' = Some corresp /\
            extends corresp binds (* TODO maybe just invoke check_fun instead? *)) ->
      exec e s t m lH mc post ->
      forall lL corresp corresp' s',
      check corresp s s' = Some corresp' ->
      states_compat lH (precond corresp s s') lL ->
      exec e' s' t m lL mc (fun t' m' lL' mc' =>
        exists lH', states_compat lH' corresp' lL' /\ post t' m' lH' mc').
  Proof.
    induction 2; intros;
      match goal with
      | H: check _ _ _ = Some _ |- _ => pose proof H as C; move C at top; cbn [check] in H
      end;
      simp;
      repeat match goal with
             | u: unit |- _ => destruct u
             end;
      unfold assert in *;
      simp;
      repeat match goal with
             | H: negb _ = false |- _ => apply Bool.negb_false_iff in H
             | H: negb _ = true  |- _ => apply Bool.negb_true_iff in H
             | H: @eq bool _ _ |- _ => autoforward with typeclass_instances in H
             end;
      subst;
      cbn [precond] in *.

    - (* Case exec.interact *)
      eapply exec.interact; eauto using states_compat_getmany.
      intros. edestruct H3 as (l' & P & F). 1: eassumption.
      eapply putmany_of_list_zip_states_compat in P. 2-3: eassumption. destruct P as (lL' & P & SC).
      eexists. split. 1: eassumption. intros. eauto.
    - (* Case exec.call *)
      rename binds0 into binds'.
      (*
      pose proof @map.putmany_of_list_zip_sameLength as L1. specialize L1 with (1 := H2).
      pose proof @map.getmany_of_list_length as L2. specialize L2 with (1 := H1).
      pose proof E0 as A.
      unfold assert_ins, assert in A. simp. autoforward with typeclass_instances in E2.
      rewrite E2 in L2.
      eapply map.sameLength_putmany_of_list in L2.
      destruct L2 as (lL' & P).
      pose proof H2 as Q.
      eapply putmany_of_list_zip_states_compat in Q. 2-3: case TODO_sam. destruct Q as (st' & Q & SC).
      eapply exec.call.
      + case TODO_sam.
      + eauto using states_compat_getmany.
      + exact Q.
      + eapply IHexec. 2: exact SC. case TODO_sam.
      + cbv beta. intros. simp. edestruct H4. 1: eassumption. simp.
        do 2 eexists. ssplit.
        * eapply states_compat_getmany. 1: eassumption. 2: eassumption. case TODO_sam.
        * case TODO_sam.
        * eexists. split. 2: eassumption. case TODO_sam.
      *)
      case TODO_sam.
    - (* Case exec.load *)
      eauto 10 with checker_hints.
    - (* Case exec.store *)
      eauto 10 with checker_hints.
    - (* Case exec.inlinetable *)
      eauto 10 with checker_hints.
    - (* Case exec.stackalloc *)
      eapply exec.stackalloc. 1: assumption.
      intros. eapply exec.weaken.
      + eapply H2; try eassumption.
        eapply states_compat_precond. eapply states_compat_put. assumption.
      + cbv beta. intros. simp. eauto 10 with checker_hints.
    - (* Case exec.lit *)
      eauto 10 with checker_hints.
    - (* Case exec.op *)
      eauto 10 with checker_hints.
    - (* Case exec.set *)
      eauto 10 with checker_hints.
    - (* Case exec.if_true *)
      eapply exec.if_true. 1: eauto using states_compat_eval_bcond.
      eapply exec.weaken.
      + eapply IHexec. 1: eassumption.
        eapply states_compat_precond. eassumption.
      + cbv beta. intros. simp. eexists. split. 2: eassumption.
        eapply states_compat_extends. 2: eassumption. eapply extends_intersect_l.
    - (* Case exec.if_false *)
      eapply exec.if_false. 1: eauto using states_compat_eval_bcond.
      eapply exec.weaken.
      + eapply IHexec. 1: eassumption.
        eapply states_compat_precond. eassumption.
      + cbv beta. intros. simp. eexists. split. 2: eassumption.
        eapply states_compat_extends. 2: eassumption. eapply extends_intersect_r.
    - (* Case exec.loop *)
      rename H4 into IH2, IHexec into IH1, H6 into IH12.
      match goal with
      | H: states_compat _ _ _ |- _ => rename H into SC
      end.
      pose proof SC as SC0.
      unfold loop_inv in SC.
      rewrite E in SC.
      eapply exec.loop.
      + eapply IH1. 1: eassumption. eapply states_compat_precond. exact SC.
      + cbv beta. intros. simp. eauto using states_compat_eval_bcond_None.
      + cbv beta. intros. simp. eexists. split. 2: eauto using states_compat_eval_bcond_bw. assumption.
      + cbv beta. intros. simp. eapply IH2; eauto using states_compat_eval_bcond_bw.
        eapply states_compat_precond. assumption.
      + cbv beta. intros. simp. eapply IH12. 1: eassumption. 1: eassumption.
        rename l0 into inv.
        eapply states_compat_extends. 2: eassumption.
        pose proof defuel_loop_inv as P.
        specialize P with (2 := E0).
        specialize P with (2 := E2).
        specialize (P corresp).
        unfold loop_inv in P|-*.
        rewrite E in P. rewrite E.
        specialize (P eq_refl).
        rewrite P.
        eapply extends_intersect_r.
    - (* Case exec.seq *)
      rename H2 into IH2, IHexec into IH1.
      eapply exec.seq.
      + eapply IH1. 1: eassumption.
        eapply states_compat_precond. assumption.
      + cbv beta. intros. simp.
        eapply IH2. 1: eassumption. 1: eassumption.
        eapply states_compat_precond. assumption.
    - (* Case exec.skip *)
      eapply exec.skip. eauto.
  Qed.

End RegAlloc.

(* Print Assumptions checker_correct. *)
