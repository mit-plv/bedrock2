Require Export bedrock2.Map.Separation.

Require Import Coq.Classes.Morphisms.
Require Import bedrock2.Lift1Prop.
Require Coq.Lists.List.
Require Import coqutil.sanity coqutil.Decidable coqutil.Tactics.destr.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.ltac_list_ops.
Import Map.Interface.map Map.Properties.map.


(*TODO: use hintdb or user-provided tactic?
  Study performance implications
*)
Create HintDb ecancel_impl discriminated.
Lemma impl1_refl{T: Type}: forall {P: T -> Prop}, Lift1Prop.impl1 P P.
Proof. intros. reflexivity. Qed.
#[global] Hint Resolve impl1_refl : ecancel_impl.

Lemma iff1_refl{A: Type}(P: A -> Prop): iff1 P P. Proof. reflexivity. Qed.
Lemma iff1_sym{A: Type}{P Q: A -> Prop}: iff1 P Q -> iff1 Q P.
Proof. intros. symmetry. assumption. Qed.

Ltac iff1_syntactic_reflexivity :=
  lazymatch goal with
  | |- iff1 ?x ?y => first [is_evar x | is_evar y | constr_eq x y]
  end;
  exact (iff1_refl _).

Ltac impl1_syntactic_reflexivity :=
  lazymatch goal with
  | |- impl1 ?x ?y => first [is_evar x | is_evar y | constr_eq x y]
  end;
  exact impl1_refl.

Section SepProperties.
  Context {key value} {map : map key value} {ok : ok map}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.
  Local Open Scope sep_scope.

  Global Instance Proper_sep_iff1 : Proper (@iff1 map ==> iff1 ==> iff1) sep. firstorder idtac. Qed.
  Global Instance Proper_sep_impl1 : Proper (@impl1 map ==> impl1 ==> impl1) sep. firstorder idtac. Qed.

  Ltac t :=
    repeat match goal with
    | _ => progress subst
    | H:_ /\ _ |- _ => destruct H
    | H:exists _, _ |- _ => destruct H
    | H:disjoint (putmany _ _) _ |- _ => eapply disjoint_putmany_l in H; destruct H
    | H:disjoint _ (putmany _ _) |- _ => eapply disjoint_putmany_r in H; destruct H
    | _ => progress intuition idtac
    end.

  Implicit Types (p q r : map -> Prop) (k : key) (v : value) (m : map).

  (* sep and sep *)
  Lemma sep_comm p q : iff1 (p*q) (q*p).
  Proof. cbv [iff1 sep split]; t; eauto 10 using putmany_comm, (fun m1 m2 => proj2 (disjoint_comm m1 m2)). Qed.
  Lemma sep_assoc p q r : iff1 ((p*q)*r) (p*(q*r)).
  Proof. cbv [iff1 sep split]; t; eauto 15 using eq_sym, putmany_assoc, ((fun m1 m2 m3 => proj2 (disjoint_putmany_l m1 m2 m3))), ((fun m1 m2 m3 => proj2 (disjoint_putmany_r m1 m2 m3))). Qed.

  Lemma get_ptsto k v m (H : ptsto k v m) : get m k = Some v.
  Proof. rewrite H, get_put_same; trivial. Qed.
  Lemma get_sep k v R m (H : sep (ptsto k v) R m) : get m k = Some v.
  Proof.
    destruct H as (mk&mR&H&Hp&HR); eapply get_ptsto in Hp; subst.
    destruct (get_split k _ _ _ H) as [[]|[]]; congruence.
  Qed.
  Lemma sep_get k v m (H : get m k = Some v) :
    sep (ptsto k v) (eq (map.remove m k)) m.
  Proof.
    unfold sep. exists (map.put map.empty k v).
    eexists. repeat split.
    - apply map_ext. intros.
      rewrite get_putmany_dec.
      rewrite get_remove_dec.
      destr (key_eqb k k0).
      + subst. rewrite get_put_same. assumption.
      + rewrite get_put_diff by congruence. rewrite get_empty.
        destruct (get m k0); reflexivity.
    - unfold disjoint. intros.
      destr (key_eqb k k0).
      + subst. rewrite get_remove_same in H1. discriminate.
      + rewrite get_put_diff in H0 by congruence. rewrite get_empty in H0. discriminate.
  Qed.
  Lemma sep_put k v m v_old R (H : sep (ptsto k v_old) R m) : sep (ptsto k v) R (put m k v).
  Proof.
    eapply sep_comm in H; eapply sep_comm.
    destruct H as (mR&mk&[Heq Hd]&HR&Hp); cbv [ptsto] in Hp; subst mk; subst m.
    exists mR, (put empty k v); split; [|solve[repeat split; trivial]]; split.
    { eapply map_ext; intro k'; destruct (key_eq_dec k' k); try subst k';
        rewrite ?get_put_same, ?get_put_diff by trivial.
      { erewrite get_putmany_right; trivial. rewrite get_put_same; trivial. }
      { rewrite 2get_putmany_left; trivial. all:rewrite get_put_diff, get_empty; trivial. } }
    { intros k' ? ? ? Hget; intros; destruct (key_eq_dec k' k); try subst k'.
      { eapply Hd; eauto using get_put_same. }
      { rewrite get_put_diff, get_empty in Hget by trivial; inversion Hget. } }
  Qed.

  Lemma sepeq_on_undef_put: forall m addr b,
      map.get m addr = None ->
      (sep (ptsto addr b) (eq m)) (map.put m addr b).
  Proof.
    intros. unfold sep. exists (map.put map.empty addr b). exists m.
    split; [|split; reflexivity].
    apply map.split_undef_put. assumption.
  Qed.

  Lemma sep_on_undef_put: forall m addr b (R: _ -> Prop),
      map.get m addr = None ->
      R m ->
      (sep (ptsto addr b) R) (map.put m addr b).
  Proof.
    intros. unfold sep. exists (map.put map.empty addr b). exists m.
    split; [|split; reflexivity || trivial].
    apply split_undef_put. assumption.
  Qed.

  Lemma sep_eq_putmany (a b : map) (H : disjoint a b)
    : Lift1Prop.iff1 (eq (putmany a b)) (sep (eq a) (eq b)).
  Proof.
    split.
    { intros; subst. eexists _, _; eauto using Properties.map.split_disjoint_putmany. }
    { intros (?&?&(?&?)&?&?); subst; trivial. }
  Qed.

  Lemma iff1_sep_cancel p q1 q2 (H : iff1 q1 q2) : iff1 (p * q1) (p * q2).
  Proof. exact (Proper_sep_iff1 _ _ (reflexivity _) _ _ H). Qed.

  (* More Conntectives *)
  Global Instance Proper_emp_iff : Proper (iff ==> @iff1 map) emp. firstorder idtac. Qed.
  Global Instance Proper_emp_impl : Proper (Basics.impl ==> @impl1 map) emp. firstorder idtac. Qed.

  (* sep and and *)

  Lemma sep_and_l_fwd P Q R m : sep (fun m => P m /\ Q m) R m -> sep P R m /\ sep Q R m.
  Proof. cbv [sep]. intros (?&?&?&(?&?)&?); eauto 10. Qed.
  Lemma sep_and_r_fwd P Q R m : sep R (fun m => P m /\ Q m) m -> sep R P m /\ sep R Q m.
  Proof. cbv [sep]. intros (?&?&?&?&(?&?)); eauto 10. Qed.

  (* sep and emp *)
  Lemma sep_emp_emp P Q : @iff1 map (sep (emp P) (emp Q)) (emp (P /\ Q)).
  Proof. cbv [iff1 sep emp split]; t; intuition eauto 20 using putmany_empty_l, disjoint_empty_l. Qed.
  Lemma sep_comm_emp_r p Q : iff1 (p * emp Q) (emp Q * p). eapply sep_comm. Qed.
  Lemma sep_emp_2 p Q r : iff1 (p * (emp Q * r)) (emp Q * (p * r)).
  Proof. rewrite <-sep_assoc. rewrite (sep_comm p). rewrite sep_assoc. reflexivity. Qed.
  Lemma sep_emp_12 P Q r : iff1 (emp P * (emp Q * r)) (emp (P /\ Q) * r).
  Proof. rewrite <-sep_assoc. rewrite sep_emp_emp. reflexivity. Qed.

  Lemma sep_emp_l a b m : sep (emp a) b m <-> a /\ b m.
  Proof.
    split.
    { intros (?&?&(?&?)&(?&?)&?); subst; rewrite putmany_empty_l; auto. }
    { intros (?&?). exists empty, m.
      cbv [emp]; edestruct split_empty_l; intuition eauto. }
  Qed.
  Lemma sep_emp_r a b m : sep a (emp b) m <-> a m /\ b.
  Proof.
    setoid_rewrite (and_comm _ b).
    setoid_rewrite sep_comm || (etransitivity; [eapply sep_comm|]). (* WHY? *)
    eapply sep_emp_l.
  Qed.
  Lemma sep_emp_True_l p : iff1 (sep (emp True) p) p.
  Proof. intros m; rewrite sep_emp_l; intuition idtac. Qed.
  Lemma sep_emp_True_r p : iff1 (sep p (emp True)) p.
  Proof. intros m; rewrite sep_emp_r; intuition idtac. Qed.

  (* sep and ex1 *)
  Lemma sep_ex1_r {T} p (q:T->_) : iff1 (p * ex1 q) (ex1 (fun h => p * q h)).
  Proof. firstorder idtac. Qed.
  Lemma sep_ex1_l {T} p (q:T->_) : iff1 (ex1 q * p) (ex1 (fun h => q h * p)).
  Proof. rewrite sep_comm. rewrite sep_ex1_r. setoid_rewrite (sep_comm p). reflexivity. Qed.

  (* impl1 and emp *)
  Lemma impl1_l_sep_emp (a:Prop) r c : impl1 (emp a * r) c <-> (a -> impl1 r c).
  Proof. cbv [impl1 emp sep split]; t; rewrite ?putmany_empty_l; eauto 10 using putmany_empty_l, disjoint_empty_l. Qed.
  Lemma impl1_r_sep_emp p b c : (b /\ impl1 p c) -> impl1 p (emp b * c).
  Proof. cbv [impl1 emp sep split]; t; eauto 10 using putmany_empty_l, disjoint_empty_l. Qed.

(** shallow reflection from a list of predicates for faster cancellation proofs *)
  Fixpoint seps' (xs : list (map -> Prop)) : map -> Prop :=
    match xs with
    | cons x xs => sep x (seps' xs)
    | nil => emp True
    end.
  Remark seps'_fold_right: seps' = List.fold_right sep (emp True). reflexivity. Qed.
  Lemma seps'_iff1_seps xs : iff1 (seps' xs) (seps xs).
  Proof.
    induction xs; [exact (reflexivity _)|].
    destruct xs; [solve[eauto using sep_emp_True_r]|].
    eapply Proper_sep_iff1, IHxs.
    exact (reflexivity _).
  Qed.
  Lemma seps_cons(P: map -> Prop)(Ps: list (map -> Prop)):
    iff1 (seps (P :: Ps)) (sep P (seps Ps)).
  Proof. rewrite <-! seps'_iff1_seps. reflexivity. Qed.
  Lemma seps_app(Ps Qs: list (map -> Prop)):
    iff1 (seps (Ps ++ Qs)) (sep (seps Ps) (seps Qs)).
  Proof.
    induction Ps.
    - simpl. symmetry. apply sep_emp_True_l.
    - rewrite <- List.app_comm_cons. rewrite! seps_cons. rewrite IHPs.
      symmetry. apply sep_assoc.
  Qed.

  Definition hd {T} := Eval cbv delta in @List.hd T.
  Definition tl {T} := Eval cbv delta in @List.tl T.
  Definition firstn {T} := Eval cbv delta in @List.firstn T.
  Definition skipn {T} := Eval cbv delta in @List.skipn T.
  Definition app {T} := Eval cbv delta in @List.app T.

  Local Infix "++" := app. Local Infix "++" := app : list_scope.
  Let nth n xs := hd (emp(map:=map) True) (skipn n xs).
  Let remove_nth n (xs : list (map -> Prop)) :=
    (firstn n xs ++ tl (skipn n xs)).
  Let replace_nth n (P: map -> Prop) (xs : list (map -> Prop)) :=
    (firstn n xs ++ P :: tl (skipn n xs)).

  Lemma seps_nth_to_head n xs : iff1 (sep (nth n xs) (seps (remove_nth n xs))) (seps xs).
  Proof.
    cbv [nth remove_nth].
    pose proof (List.firstn_skipn n xs : (firstn n xs ++ skipn n xs) = xs).
    set (xsr := skipn n xs) in *; clearbody xsr.
    set (xsl := firstn n xs) in *; clearbody xsl.
    subst xs.
    setoid_rewrite <-seps'_iff1_seps.
    destruct xsr.
    { cbn [seps']; rewrite sep_emp_True_l, 2List.app_nil_r; exact (reflexivity _). }
    cbn [hd tl].
    induction xsl; cbn; [exact (reflexivity _)|].
    rewrite <-IHxsl; clear IHxsl.
    rewrite (sep_comm _ (seps' _)), <-(sep_assoc _ (seps' _)), <-(sep_comm _ (_ * seps' _)).
    exact (reflexivity _).
  Qed.

  Lemma cancel_emps_at_indices i j xs ys P Q
        (Hi : nth i xs = emp P)
        (Hj : nth j ys = emp Q)
        (HPQ : P <-> Q)
        (Hrest : iff1 (seps (remove_nth i xs)) (seps (remove_nth j ys)))
    : iff1 (seps xs) (seps ys).
  Proof.
    rewrite <-(seps_nth_to_head i xs), <-(seps_nth_to_head j ys), Hi, Hj, Hrest.
    unfold iff1 in *. intro m. do 2 rewrite sep_emp_l. intuition idtac.
  Qed.

  (* iff1 instead of eq as a hyp would be a more general lemma, but eq is more convenient to use *)
  Lemma cancel_seps_at_indices i j xs ys
        (Hij : nth i xs = nth j ys)
        (Hrest : iff1 (seps (remove_nth i xs)) (seps (remove_nth j ys)))
    : iff1 (seps xs) (seps ys).
  Proof.
    rewrite <-(seps_nth_to_head i xs), <-(seps_nth_to_head j ys), Hij, Hrest.
    exact (reflexivity _).
  Qed.

  (* Analogous to cancel_seps_at_indices, but works with implication rather than eq.
     TODO: If this lemma's dependencies become general enough, should we deprecate cancel_seps_at_indices?
   *)
  Lemma cancel_seps_at_indices_by_implication i j xs ys
        (Hij : Lift1Prop.impl1 (nth i xs) (nth j ys))
        (Hrest : Lift1Prop.impl1 (seps (remove_nth i xs)) (seps (remove_nth j ys)))
    : Lift1Prop.impl1 (seps xs) (seps ys).
  Proof.
    rewrite <-(seps_nth_to_head i xs), <-(seps_nth_to_head j ys).
    rewrite Hij, Hrest.
    exact (reflexivity _).
  Qed.

  Lemma cancel_emp_at_index_l i xs ys
        (Hi : nth i xs = emp True)
        (Hrest : iff1 (seps (remove_nth i xs)) (seps ys))
    : iff1 (seps xs) (seps ys).
  Proof.
    rewrite <-(seps_nth_to_head i xs), Hi, Hrest. exact (sep_emp_True_l _).
  Qed.
  Lemma cancel_emp_at_index_r j xs ys
        (Hj : nth j ys = emp True)
        (Hrest : iff1 (seps xs) (seps (remove_nth j ys)))
    : iff1 (seps xs) (seps ys).
  Proof.
    rewrite <-(seps_nth_to_head j ys), Hj, Hrest, sep_emp_True_l.
    exact (reflexivity _).
  Qed.

  Lemma cancel_emp_at_index_impl j xs ys
        (Hj : nth j ys = emp True)
        (Hrest : impl1 (seps xs) (seps (remove_nth j ys)))
    : impl1 (seps xs) (seps ys).
  Proof.
    rewrite <-(seps_nth_to_head j ys), Hj, Hrest, sep_emp_True_l.
    exact (reflexivity _).
  Qed.

  Lemma extract_emp_in_hyp_at_index i xs m P
        (Hi : nth i xs = emp P)
        (H : seps xs m)
    : P /\ seps (remove_nth i xs) m.
  Proof.
    eapply (seps_nth_to_head i xs) in H. rewrite Hi in H.
    eapply sep_emp_l in H. exact H.
  Qed.

  Lemma extract_emp_in_goal_at_index i xs m P
        (Hi : nth i xs = emp P)
        (NewGoal : seps (remove_nth i xs) m /\ P)
    : seps xs m.
  Proof.
    eapply (seps_nth_to_head i xs). rewrite Hi.
    eapply sep_comm. eapply sep_emp_r. exact NewGoal.
  Qed.

  Lemma extract_emp_in_goal_with_and_at_index i xs m P C
        (Hi : nth i xs = emp P)
        (NewGoal : seps (remove_nth i xs) m /\ P /\ C)
    : seps xs m /\ C.
  Proof.
    destruct NewGoal as (HN & HP & HC). split; [|exact HC].
    eapply (extract_emp_in_goal_at_index i); eauto.
  Qed.

  Lemma replace_nth_sep_remove_nth i P xs :
      iff1 (seps (replace_nth i P xs))
           (sep P (seps (remove_nth i xs))).
  Proof.
    unfold replace_nth, remove_nth.
    rewrite ?seps_app, ?seps_cons.
    rewrite <-?sep_assoc.
    rewrite (sep_comm P).
    reflexivity.
  Qed.

  Lemma extract_ex1_in_hyp_at_index{A : Type} i xs m (P: A -> map -> Prop)
        (Hi : nth i xs = ex1 P)
        (H : seps xs m)
    : exists a, seps (replace_nth i (P a) xs) m.
  Proof.
    eapply (seps_nth_to_head i xs) in H. rewrite Hi in H.
    eapply sep_ex1_l in H. unfold ex1 in H. destruct H as [a H]. exists a.
    eapply replace_nth_sep_remove_nth. exact H.
  Qed.

  Lemma extract_ex1_in_goal_at_index{A : Type} i xs m (P: A -> map -> Prop) a
        (Hi : nth i xs = ex1 P)
        (NewGoal : seps (replace_nth i (P a) xs) m)
    : seps xs m.
  Proof.
    eapply (seps_nth_to_head i xs). rewrite Hi.
    eapply sep_ex1_l. unfold ex1. exists a.
    eapply replace_nth_sep_remove_nth. exact NewGoal.
  Qed.

  Lemma extract_ex1_in_goal_with_and_at_index{A : Type} i xs m (P: A -> map -> Prop) a C
        (Hi : nth i xs = ex1 P)
        (NewGoal : seps (replace_nth i (P a) xs) m /\ C)
    : seps xs m /\ C.
  Proof.
    destruct NewGoal as (HN & HC). split; [|exact HC].
    eapply (extract_ex1_in_goal_at_index i); eauto.
  Qed.
End SepProperties.

Require Import coqutil.Tactics.syntactic_unify coqutil.Tactics.rdelta.

Notation "X '========' 'seps' 'iff' '========' Y" :=
  (Lift1Prop.iff1 (seps X) (seps Y))
    (at  level 200, no associativity,
     format "X '//' '========'  'seps'  'iff'  '========' '//' Y").

Module Tree.
  Inductive Tree(A: Type): Type :=
  | Leaf(a: A)
  | Node(left right: Tree A).
  Arguments Leaf {A} _.
  Arguments Node {A} _ _.
  Section Interp.
    Context {A B: Type}.
    Context (interp_Leaf: A -> B).
    Context (interp_Node: B -> B -> B).
    Fixpoint interp(t: Tree A): B :=
      match t with
      | Leaf a => interp_Leaf a
      | Node t1 t2 => interp_Node (interp t1) (interp t2)
      end.
  End Interp.

  Definition flatten{A: Type}: Tree A -> list A := interp (fun a => cons a nil) (@app A).

  Section WithMap.
    Context {key value} {map : map key value} {ok : ok map}.
    Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.

    Definition to_sep: Tree (map -> Prop) -> map -> Prop := interp (fun x => x) sep.

    Lemma flatten_iff1_to_sep(t : Tree.Tree (map -> Prop)):
      Lift1Prop.iff1 (seps (flatten t)) (to_sep t).
    Proof.
      induction t; [reflexivity|].
      simpl. rewrite seps_app. rewrite IHt1, IHt2. reflexivity.
    Qed.

    Lemma iff1_to_sep_of_iff1_flatten(LHS RHS : Tree (map -> Prop)):
      Lift1Prop.iff1 (seps (flatten LHS)) (seps (flatten RHS)) ->
      Lift1Prop.iff1 (to_sep LHS) (to_sep RHS).
    Proof. rewrite! flatten_iff1_to_sep. exact id. Qed.

    Lemma impl1_to_sep_of_impl1_flatten(LHS RHS : Tree (map -> Prop)):
      Lift1Prop.impl1 (seps (flatten LHS)) (seps (flatten RHS)) ->
      Lift1Prop.impl1 (to_sep LHS) (to_sep RHS).
    Proof. rewrite! flatten_iff1_to_sep. exact id. Qed.

    Lemma flatten_to_sep_with_and(t : Tree.Tree (map -> Prop))(m: map)(C: Prop):
      seps (flatten t) m /\ C -> to_sep t m /\ C.
    Proof.
      intros (H & HC). refine (conj _ HC). eapply flatten_iff1_to_sep. exact H.
    Qed.
  End WithMap.
End Tree.

Ltac reify e :=
  lazymatch e with
  | @sep ?key ?value ?map ?a ?b =>
    let a := reify a in
    let b := reify b in
    uconstr:(@Tree.Node (@map.rep key value map -> Prop) a b)
  | ?a => uconstr:(Tree.Leaf a)
  end.

Ltac reify_goal :=
  lazymatch goal with
  | |- Lift1Prop.iff1 ?LHS ?RHS =>
    let LHS := reify LHS in
    let RHS := reify RHS in
    change (Lift1Prop.iff1 (Tree.to_sep LHS) (Tree.to_sep RHS));
    eapply Tree.iff1_to_sep_of_iff1_flatten
  | |- Lift1Prop.impl1 ?LHS ?RHS =>
    let LHS := reify LHS in
    let RHS := reify RHS in
    change (Lift1Prop.impl1 (Tree.to_sep LHS) (Tree.to_sep RHS));
    eapply Tree.impl1_to_sep_of_impl1_flatten
  end;
  cbn [Tree.flatten Tree.interp app].

(* Given `H: seplogformula m`, first cbns away all occurrences of `seps` in H,
   and then flattens the formula into a list of sep clauses, resulting in an
   `H: seps [...] m` *)
Ltac flatten_seps_in H :=
  lazymatch type of H with
  | ?nested ?m =>
    let tmem := type of m in
    let E := fresh "E" in
    eassert (@iff1 tmem nested _) as E;
    [ (* from `nested` to `Tree.to_sep tree` *)
      let stars := eval cbn[seps] in nested in
      let tree := reify stars in
      transitivity (Tree.to_sep tree); [
        cbn [seps Tree.to_sep Tree.interp]; iff1_syntactic_reflexivity
      |];
      (* from `Tree.to_sep tree` to `seps (Tree.flatten tree)` *)
      transitivity (seps (Tree.flatten tree)); [
        exact (iff1_sym (Tree.flatten_iff1_to_sep tree))
      |];
      (* from `seps (Tree.flatten tree)` to `seps clauses` *)
      cbn [SeparationLogic.Tree.flatten SeparationLogic.Tree.interp SeparationLogic.app];
      iff1_syntactic_reflexivity
    | let HNew := fresh in pose proof (proj1 (E m) H) as HNew;
      move HNew before H;
      clear E H;
      rename HNew into H ]
  end.

(* Given a goal of shape `seplogformula m`, first cbns away all occurrences of
   `seps` in H, and then flattens the formula into a list of sep clauses, resulting
   in a goal of shape `seps [...] m` *)
Ltac flatten_seps_in_goal :=
  cbn [seps];
  lazymatch goal with
  | |- ?nested ?m /\ ?C =>
      let xs := reify nested in
      change (Tree.to_sep xs m /\ C);
      eapply Tree.flatten_to_sep_with_and
  | |- ?nested ?m =>
      let xs := reify nested in
      change (Tree.to_sep xs m);
      eapply Tree.flatten_iff1_to_sep
  end;
  cbn [Tree.flatten Tree.interp app].

Ltac cancel_emp_l :=
  lazymatch goal with
  | |- Lift1Prop.iff1 (@seps ?K ?V ?M ?LHS) (seps ?RHS) =>
    let i := find_constr_eq LHS constr:(@emp K V M True) in
    simple refine (cancel_emp_at_index_l i LHS RHS _ _);
    cbn [firstn skipn app hd tl];
    [syntactic_exact_deltavar (@eq_refl _ _)|]
  end.

Ltac cancel_emp_r :=
  lazymatch goal with
  | |- Lift1Prop.iff1 (seps ?LHS) (@seps ?K ?V ?M ?RHS) =>
    let j := find_constr_eq RHS constr:(@emp K V M True) in
    simple refine (cancel_emp_at_index_r j LHS RHS _ _);
    cbn [firstn skipn app hd tl];
    [syntactic_exact_deltavar (@eq_refl _ _)|]
  end.

(* TODO: should this eventually subsume the one above?*)
Ltac cancel_emp_impl :=
  lazymatch goal with
  | |- Lift1Prop.impl1 (seps ?LHS) (@seps ?K ?V ?M ?RHS) =>
    let j := find_constr_eq RHS constr:(@emp K V M True) in
    (*TODO: replace lemma*)
    simple refine (cancel_emp_at_index_impl j LHS RHS _ _);
    cbn [firstn skipn app hd tl];
    (*TODO: use more complicated solver here?*)
    [syntactic_exact_deltavar (@eq_refl _ _)|]
  end.

(* leaves two open goals:
   1) equality between left sep clause #i and right sep clause #j
   2) updated main goal *)
Ltac cancel_seps_at_indices i j :=
  lazymatch goal with
  | |- Lift1Prop.iff1 (seps ?LHS) (seps ?RHS) =>
    simple refine (cancel_seps_at_indices i j LHS RHS _ _);
    cbn [firstn skipn app hd tl]
  end.


(* Analogous to cancel_seps_at_indices, but works with implication rather than eq.
   TODO: If this tactic's dependencies become general enough, should we deprecate cancel_seps_at_indices?
 *)
(* leaves two open goals:
   1) implication between left sep clause #i and right sep clause #j
   2) updated main goal *)
Ltac cancel_seps_at_indices_by_implication i j :=
  lazymatch goal with
  | |- Lift1Prop.impl1 (seps ?LHS) (seps ?RHS) =>
    simple refine (cancel_seps_at_indices_by_implication i j LHS RHS _ _);
    cbn [firstn skipn app hd tl]
  end.

(*TODO: performance*)
Ltac find_implication xs y :=
  multimatch xs with
  | cons ?x _ => constr:(O)
  | cons _ ?xs => let i := find_implication xs y in constr:(S i)
  end.


Ltac cancel_step := once (
      let RHS := lazymatch goal with |- Lift1Prop.iff1 _ (seps ?RHS) => RHS end in
      let jy := index_and_element_of RHS in (* <-- multi-success! *)
      let j := lazymatch jy with (?i, _) => i end in
      let y := lazymatch jy with (_, ?y) => y end in
      assert_fails (has_evar y); (* <-- different from ecancel_step *)
      let LHS := lazymatch goal with |- Lift1Prop.iff1 (seps ?LHS) _ => LHS end in
      let i := find_constr_eq LHS y in (* <-- different from ecancel_step *)
      cancel_seps_at_indices i j; [syntactic_exact_deltavar (@eq_refl _ _)|]).

Ltac ecancel_step :=
      let RHS := lazymatch goal with |- Lift1Prop.iff1 _ (seps ?RHS) => RHS end in
      let jy := index_and_element_of RHS in (* <-- multi-success! *)
      let j := lazymatch jy with (?i, _) => i end in
      let y := lazymatch jy with (_, ?y) => y end in
      assert_fails (idtac; let y := rdelta_var y in is_evar y);
      let LHS := lazymatch goal with |- Lift1Prop.iff1 (seps ?LHS) _ => LHS end in
      let i := find_syntactic_unify_deltavar LHS y in (* <-- multi-success! *)
      cancel_seps_at_indices i j; [syntactic_exact_deltavar (@eq_refl _ _)|].

(* TODO: eventually replace ecancel_step? Probably not since implication is too agressive.*)
(*TODO: performance. I've replaced the deltavar stuff with heavier operations  *)
Ltac ecancel_step_by_implication :=
      let RHS := lazymatch goal with |- Lift1Prop.impl1 _ (seps ?RHS) => RHS end in
      let jy := index_and_element_of RHS in (* <-- multi-success! *)
      let j := lazymatch jy with (?i, _) => i end in
      let y := lazymatch jy with (_, ?y) => y end in
      assert_fails (idtac; let y := rdelta_var y in is_evar y);
      let LHS := lazymatch goal with |- Lift1Prop.impl1 (seps ?LHS) _ => LHS end in
      let i := find_implication LHS y in (* <-- multi-success! *)
      cancel_seps_at_indices_by_implication i j; [solve [auto 1 with nocore ecancel_impl]|].

Ltac ecancel_done :=
  cbn [seps];
  syntactic_exact_deltavar
    (@RelationClasses.reflexivity _ _
        (@RelationClasses.Equivalence_Reflexive _ _ (@Equivalence_iff1 _)) _).

(* might be slightly less efficient than ecancel_done because it uses [exact] instead of
   [exact_no_check], but it gives better error messages in case of evar scoping problems,
   because [syntactic_exact_deltavar] calls [unify], which gives no details about evar
   scoping problems, while the [exact] called below does give details *)
Ltac ecancel_done' :=
  cbn [seps];
  match goal with
  | |- iff1 ?x ?y => first [is_evar x | is_evar y | constr_eq x y]
  end;
  exact
    (@RelationClasses.reflexivity _ _
       (@RelationClasses.Equivalence_Reflexive _ _ (@Equivalence_iff1 _)) _).

Ltac cancel_done :=
  lazymatch goal with
  | |- iff1 (seps (cons _ nil)) _ => idtac
  | |- iff1 _ (seps (cons _ nil )) => idtac
  | |- ?g => assert_fails (has_evar g)
  end;
  ecancel_done.

Ltac cancel_seps :=
  repeat cancel_step;
  repeat cancel_emp_l;
  repeat cancel_emp_r;
  repeat cancel_emp_impl;
  try solve [ cancel_done ].

Ltac cancel := reify_goal; cancel_seps.

Ltac ecancel :=
  cancel;
  lazymatch goal with
  | [|- impl1 _ _] =>
     repeat ecancel_step_by_implication;
     (solve [ cbn [seps]; exact impl1_refl ])
  | [|- iff1 _ _] =>
    repeat ecancel_step;
    solve [ ecancel_done ]
  end.


Ltac ecancel_assumption :=
  multimatch goal with
  | |- _ ?m1 =>
    multimatch goal with
    | H: _ ?m2 |- _ =>
      syntactic_unify_deltavar m1 m2;
      refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H;
      solve [ecancel]
    end
  end.

 Ltac ecancel_assumption_impl :=
    multimatch goal with
    | |- ?PG ?m1 =>
      multimatch goal with
      | H: ?PH ?m2
        |- _ =>
        syntactic_unify_deltavar m1 m2;
        (*TODO: can I just revert H?*)
        refine (Morphisms.subrelation_refl Lift1Prop.impl1 PH PG _ m1 H);
        clear H;
        solve[ecancel]
      end
    end.

 (* To use the implication-based ecancel assumption in existing tactics in a proof, add this line:

    Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

    The implication-based tactic should in theory solve a strict superset of goals,
    but its performance may be worse, especially when it fails.
  *)

Ltac use_sep_assumption :=
  match goal with
  | |- _ ?m1 =>
    match goal with
    | H: _ ?m2 |- _ =>
      unify m1 m2;
      refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H
    end
  end.

Ltac seplog :=
  use_sep_assumption;
  cancel;
  try solve [ repeat ecancel_step; cbn [seps]; exact (RelationClasses.reflexivity _) ].

Ltac seprewrite0_in Hrw H :=
  let lemma_lhs := lazymatch type of Hrw with @Lift1Prop.iff1 _ ?lhs _ => lhs end in
  let Psep := lazymatch type of H with ?P _ => P end in
  let mem := lazymatch type of Psep with ?mem -> _ => mem end in
  lazymatch mem with
  | @map.rep _ _ _ => idtac
  | _ => fail "hypothesis must be of form 'P m'"
  end;
  let pf := fresh in
  (* COQBUG(faster use ltac:(...) here if that was multi-success *)
  eassert (@Lift1Prop.iff1 mem Psep (sep lemma_lhs _)) as pf
      by (ecancel || fail "failed to find" lemma_lhs "in" Psep "using ecancel");
  let H' := fresh H in (* rename H into H' (* COGBUG(9937) *) *)
  epose proof (proj1 (Proper_sep_iff1 _ _ Hrw _ _ (RelationClasses.reflexivity _) _) (proj1 (pf _) H)) as H';
  clear H pf; rename H' into H.


Ltac seprewrite_in Hrw H :=
  multimatch constr:(Set) with
  | _ => unshelve
           (let Hrw := open_constr:(Hrw _) in seprewrite_in Hrw H);
         shelve_unifiable
  | _ => seprewrite0_in Hrw H
  end.

(* last side-condition is solved first *)
Ltac seprewrite_in_by Hrw H tac :=
  multimatch constr:(Set) with
  | _ => unshelve
           (let Hrw := open_constr:(Hrw _) in seprewrite_in_by Hrw H tac);
         shelve_unifiable;
         [solve [tac].. | ]
  | _ => seprewrite0_in Hrw H
  end.


(* the same (but slightly different) for rewriting in the goal
   TODO can we do with less duplication, but without unreadable abstraction? *)

Ltac seprewrite0 Hrw :=
  let lemma_lhs := lazymatch type of Hrw with @Lift1Prop.iff1 _ ?lhs _ => lhs end in
  let Psep := lazymatch goal with |- ?P _ => P end in
  let mem := lazymatch type of Psep with ?mem -> _ => mem end in
  lazymatch mem with
  | @map.rep _ _ _ => idtac
  | _ => fail "goal must be of form 'P m'"
  end;
  let pf := fresh in
  (* COQBUG(faster use ltac:(...) here if that was multi-success *)
  eassert (@Lift1Prop.iff1 mem Psep (sep lemma_lhs _)) as pf
      by (ecancel || fail "failed to find" lemma_lhs "in" Psep "using ecancel");
  eapply (fun m => (proj2 (pf m))); clear pf; (* <-- note: proj2 instead of proj1 *)
  eapply (Proper_sep_iff1 _ _ Hrw _ _ (RelationClasses.reflexivity _) _).

Ltac seprewrite Hrw :=
  multimatch constr:(Set) with
  | _ => unshelve
           (let Hrw := open_constr:(Hrw _) in seprewrite Hrw);
         shelve_unifiable
  | _ => seprewrite0 Hrw
  end.

(* last side-condition is solved first *)
Ltac seprewrite_by Hrw tac :=
  multimatch constr:(Set) with
  | _ => unshelve
           (let Hrw := open_constr:(Hrw _) in seprewrite_by Hrw tac);
         shelve_unifiable;
         [solve [tac].. | ]
  | _ => seprewrite0 Hrw
  end.

(* a convenient way to turn iff1 into eq, so that it can be used with our own equality-based
   (rather than Morphism-based) rewriters. *)
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Lemma iff1ToEq{T: Type}{P Q: T -> Prop}(H: iff1 P Q): P = Q.
Proof.
  unfold iff1 in *. extensionality x.
  eapply propositional_extensionality.
  eapply H.
Qed.

Ltac is_emp P :=
  lazymatch P with
  | emp _ => constr:(true)
  | _ => constr:(false)
  end.

Ltac is_ex1 P :=
  lazymatch P with
  | ex1 _ => constr:(true)
  | _ => constr:(false)
  end.

Ltac extract_ex1_step_in H :=
  match type of H with
  | seps ?xs _ =>
      lazymatch find_in_list ltac:(is_ex1) xs with
      | (?j, ex1 ?Q) =>
          apply extract_ex1_in_hyp_at_index with (i := j) (P := Q) in H;
          [ cbn [firstn skipn app hd tl] in H
          | cbn [firstn skipn app hd tl]; syntactic_exact_deltavar (@eq_refl _ _) ];
          let name := lazymatch Q with
                      | fun e => _ => e
                      | _ => fresh "e"
                      end in
          destruct H as [name H]
      end
  end.

Ltac extract_emp_step_in H :=
  match type of H with
  | seps ?xs _ =>
      lazymatch find_in_list ltac:(is_emp) xs with
      | (?j, emp ?Q) =>
          apply extract_emp_in_hyp_at_index with (i := j) (P := Q) in H;
          [ cbn [firstn skipn app hd tl] in H
          | cbn [firstn skipn app hd tl]; syntactic_exact_deltavar (@eq_refl _ _) ];
          let name := fresh H "_emp0" in
          destruct H as [name H]
      end
  end.

Ltac extract_ex1_and_emp_in0 H :=
  repeat first [ extract_ex1_step_in H
               | extract_emp_step_in H
               | flatten_seps_in H ].

Ltac extract_ex1_and_emp_in H :=
  extract_ex1_and_emp_in0 H; cbn [seps] in H.

Ltac extract_ex1_and_emp_in_hyps :=
  repeat match goal with
         | H: _ |- _ => progress extract_ex1_and_emp_in H
         end.

Ltac extract_ex1_step_in_goal :=
  match goal with
  | |- seps ?xs _ /\ _ =>
      lazymatch find_in_list ltac:(is_ex1) xs with
      | (?j, ex1 _) =>
          eapply (extract_ex1_in_goal_with_and_at_index j);
          cbn [firstn skipn app hd tl];
          [ syntactic_exact_deltavar (@eq_refl _ _) | ]
      end
  | |- seps ?xs _ =>
      lazymatch find_in_list ltac:(is_ex1) xs with
      | (?j, ex1 _) =>
          eapply (extract_ex1_in_goal_at_index j);
          cbn [firstn skipn app hd tl];
          [ syntactic_exact_deltavar (@eq_refl _ _) | ]
      end
  end.

Ltac extract_emp_step_in_goal :=
  lazymatch goal with
  | |- seps ?xs _ =>
      lazymatch find_in_list_bw ltac:(is_emp) xs with
      | (?j, emp _) =>
          eapply (extract_emp_in_goal_at_index j);
          cbn [firstn skipn app hd tl];
          [ syntactic_exact_deltavar (@eq_refl _ _) | ]
      end
  | |- seps ?xs _  /\ _ =>
      lazymatch find_in_list_bw ltac:(is_emp) xs with
      | (?j, emp _) =>
          eapply (extract_emp_in_goal_with_and_at_index j);
          cbn [firstn skipn app hd tl];
          [ syntactic_exact_deltavar (@eq_refl _ _) | ]
      end
  end.

Ltac extract_ex1_and_emp_in_goal0 :=
  repeat first [extract_ex1_step_in_goal | flatten_seps_in_goal];
  repeat extract_emp_step_in_goal.

Ltac extract_ex1_and_emp_in_goal :=
   extract_ex1_and_emp_in_goal0; cbn [seps].

Section Tests.
  Context {key value} {map : map key value} {ok : ok map}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.
  Local Open Scope sep_scope.
  Import List.ListNotations.

  Goal forall (a1 a2: key) (v1 v1': value) (m: map)
      (H: (ptsto a1 v1 * ex1 (fun y => emp (0 < y)%nat * ex1 (fun v => ptsto a2 v)))%sep m)
      (OtherH: v1 = v1'),
      (ex1 (fun z => ex1 (fun y => ptsto a2 y) * emp (0 < z)%nat) *
       ptsto a1 v1 * emp (v1 = v1'))%sep m.
  Proof.
    intros.
    extract_ex1_and_emp_in H.
    extract_ex1_and_emp_in_goal.
    eapply sep_comm in H.
    eauto.
    all: fail.
  Abort.

  Goal forall (a1 a2: key) (v1 v1': value) (m: map)
      (H: (ptsto a1 v1 * ex1 (fun y => emp (0 < y)%nat * ex1 (fun v => ptsto a2 v)))%sep m)
      (OtherH: v1 = v1'),
      (ex1 (fun z => ex1 (fun y => ptsto a2 y) * emp (0 < z)%nat) *
       ptsto a1 v1 * emp (v1 = v1'))%sep m /\ v1 = v1'.
  Proof.
    intros.
    extract_ex1_and_emp_in H.
    extract_ex1_and_emp_in_goal.
    eapply sep_comm in H.
    eauto.
    all: fail.
  Abort.
End Tests.
