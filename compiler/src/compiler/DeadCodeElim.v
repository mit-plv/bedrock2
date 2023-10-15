Require Import compiler.FlatImp.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.fwd.
Require Import String.
Require Import coqutil.Map.MapEauto.
Open Scope Z_scope.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Datatypes.ListSet.
Local Notation var := String.string (only parsing).
Require Import compiler.util.Common.
Require Import bedrock2.MetricLogging.
Require Import coqutil.Tactics.fwd.
(*  below only for of_list_list_diff *)
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.

Section WithArguments0.
  Context {env: map.map String.string (list var * list var * stmt var) }.

  Local Notation bcond := (@FlatImp.bcond var).

  Definition accessed_vars_bcond(c: bcond): list var :=
    match c with
    | CondBinary _ x y => list_union String.eqb [x] [y]
    | CondNez x => [x]
    end.

  Fixpoint accessed_vars_stmt(s: stmt var) : list var :=
    match s with
    | SInteract _ _ argvars => argvars
    | SCall _ _ args => args
    | SLoad _ _ a _ => [a]
    | SStore _ a v _ => list_union String.eqb [a] [v]
    | SInlinetable _ _ _ i => [i]
    | SStackalloc _ _ body => accessed_vars_stmt body
    | SLit _ _ => []
    | SOp _ _ y oz =>
        match oz with
        | Const _ => [y]
        | Var z => list_union String.eqb [y] [z]
        end
    | SSet _ y => [y]
    | SIf cond bThen bElse => list_union String.eqb
                                (accessed_vars_bcond cond)
                                (list_union String.eqb
                                   (accessed_vars_stmt bThen)
                                   (accessed_vars_stmt bElse))
    | SLoop body1 cond body2 =>
        list_union String.eqb
          (accessed_vars_bcond cond)
          (list_union String.eqb
             (accessed_vars_stmt body1)
             (accessed_vars_stmt body2))
    | SSeq s1 s2 =>
        list_union String.eqb
          (accessed_vars_stmt s1)
          (accessed_vars_stmt s2)
    | SSkip => []
    end.

  Fixpoint defined_vars_stmt(s: stmt var) : list var :=
    match s with
    | SInteract _ _ _ => []
    | SCall binds _ _ => binds
    | SLoad _ x _ _ => [x]
    | SStore _ _ _ _ => []
    | SInlinetable _ x _ _ => [x]
    | SStackalloc _ _ body => defined_vars_stmt body
    | SLit x _ => [x]
    | SOp x _ _ _ => [x]
    | SSet x _ => [x]
    | SIf cond bThen bElse => list_intersect String.eqb
                                (defined_vars_stmt bThen)
                                (defined_vars_stmt bElse)
    | SLoop body1 cond body2 =>
        defined_vars_stmt body1
    | SSeq s1 s2 =>
        list_union String.eqb
          (defined_vars_stmt s1)
          (defined_vars_stmt s2)
    | SSkip => []
    end.

  (* Increasing fixpoint, i.e.
     stop when the newest result is a subset of the old result *)

  Definition is_list_subset (x: list var) (x': list var)
    := forallb (fun v => (existsb (eqb v) x')) x.

  Lemma is_list_subset_refl :
    forall l, is_list_subset l l = true.
  Proof.
    induction l.
    - simpl. reflexivity.
    - unfold is_list_subset.
      simpl.
      rewrite eqb_refl.
      simpl.
      eapply forallb_forall.
      intros.
      replace (existsb (eqb x) l) with true%bool.
      2: { symmetry. rewrite existsb_exists.
           exists x; auto.
           propositional idtac.
           eapply eqb_refl.
      }
      eapply Bool.orb_true_r.
  Qed.

  Fixpoint fixpoint_inc'
    (fuel: nat)
    (x: list var)
    (default: list var)
    (F: list var -> list var) :=
    match fuel with
    | O => default
    | S fuel' => let x' := F x
             in if is_list_subset x' x then x else
                  fixpoint_inc' fuel' x' default F
    end.

  Lemma fixpoint_inc'_convergence:
    forall fuel x default F,
      let retval := fixpoint_inc' fuel x default F
      in is_list_subset (F retval) retval = true \/
           retval = default.
  Proof.
    induction fuel.
    - simpl. intros. auto.
    - simpl. intros.
      destr (is_list_subset (F x) x).
      + rewrite E in *. auto.
      + eapply IHfuel.
  Qed.

  Definition fix_fuel := 8%nat.
  Definition fixpoint_inc := fixpoint_inc' fix_fuel [].

  Lemma fixpoint_inc'_bounded':
    forall fuel default F,
      (forall x', is_list_subset x' default = true
                  -> is_list_subset (F x') default = true)
      -> forall x,
        is_list_subset x default = true ->
        let retval := fixpoint_inc' fuel x default F in
        is_list_subset retval default = true.
  Proof.
    induction fuel.
    - intros. simpl in *.
      eapply is_list_subset_refl.
    - intros. simpl in *.
      destr (is_list_subset (F x) x).
      + eapply H0.
      + assert (is_list_subset (F retval) retval = true \/
                  retval = default).  {
          eapply fixpoint_inc'_convergence.
        }
        destr H1.
        * eapply IHfuel in H.
          2: { eapply H. }
          2: { eapply H0. }
          eapply H.
        * rewrite H1. eapply is_list_subset_refl.
  Qed.


  Lemma fixpoint_inc'_bounded:
    forall fuel default F,
      (forall x', is_list_subset x' default = true
                  -> is_list_subset (F x') default = true)
      ->
        let retval := fixpoint_inc' fuel [] default F in
        is_list_subset retval default = true.
  Proof.
    intros.
    eapply fixpoint_inc'_bounded'.
    2: { simpl. reflexivity. }
    eapply H.
  Qed.

  Fixpoint live(s: stmt var)(l: list var): list var :=
    match s with
    | SInteract resvars _ argvars  =>
          list_union String.eqb
            (argvars) (list_diff String.eqb l resvars)
    | SCall binds _ args =>
        list_union String.eqb args (list_diff String.eqb l binds)
    | SLoad _ x a _ =>
        list_union String.eqb [a] (list_diff String.eqb l [x])
    | SStore _ a v _ =>
        list_union String.eqb (list_union String.eqb [a] [v]) l
    | SInlinetable _ x _ i =>
        list_union String.eqb [i] (list_diff String.eqb l [x])
    | SStackalloc x _ body =>
        list_diff String.eqb (live body l) [x]
    | SLit x v =>
        list_diff String.eqb l [x]
    | SOp x _ y oz =>
        match oz with
        | Const _ => list_union String.eqb [y] (list_diff String.eqb l [x])
        | Var z => list_union String.eqb (list_union String.eqb [y] [z]) (list_diff String.eqb l [x])
        end
    | SSet x y =>
        list_union String.eqb [y] (list_diff String.eqb l [x])
    | SIf c s1 s2 =>
        list_union String.eqb
          (list_union String.eqb (live s1 l) (live s2 l))
          (accessed_vars_bcond c)
    | SSeq s1 s2 => live s1 (live s2 l)
    | SSkip => l
    | SLoop s1 c s2 =>
        let default := list_union String.eqb (accessed_vars_stmt (SLoop s1 c s2)) l in
        fixpoint_inc default
          (fun x => (live s1 (list_union String.eqb
                                (live s2 x)
                                (list_union String.eqb
                                  (accessed_vars_bcond c)
                                  l))))
    end.

  Lemma existsb_eqb_in:
    forall x (l: list string),
      In x l <-> (existsb (eqb x) l = true).
  Proof.
    intros.
    unfold iff.
    split.
    - intros.
      induction l.
      + simpl in *.
        auto.
      + simpl.
        eapply in_inv in H.
        destr H.
        * rewrite H in *. rewrite eqb_refl. eapply Bool.orb_true_l.
        * eapply IHl in H.
          rewrite H. eapply Bool.orb_true_r.
    - intros.
      induction l.
      + simpl in *.
        inversion H.
      + simpl in H.
        eapply Bool.orb_prop in H.
        destr H.
        * eapply eqb_eq in H.
          rewrite H in *.
          eapply in_eq.
        * eapply IHl in H.
          eapply in_cons.
          assumption.
  Qed.

  Lemma subset_of_list_cons:
    forall h t l,
      PropSet.subset (PropSet.of_list (h::t)) (PropSet.of_list l) <->
      existsb (eqb h) l = true /\ PropSet.subset (PropSet.of_list t) (PropSet.of_list l).
  Proof.
    intros.
    unfold iff.
    split.
    - split.
        + unfold PropSet.subset in H.
          pose proof H as H'.
          specialize (H' h).
          assert (PropSet.elem_of h (PropSet.of_list (h :: t))).
          { unfold PropSet.elem_of.
            unfold PropSet.of_list.
            eapply in_eq.
          }
          eapply H' in H0.
          unfold PropSet.elem_of in H0.
          unfold PropSet.of_list in H0.
          eapply existsb_exists.
          exists h.
          split; simpl; auto.
          eapply eqb_eq.
          reflexivity.

        + unfold PropSet.subset in *.
          unfold PropSet.elem_of in *.
          intros.
          unfold PropSet.of_list in *.
          eapply in_cons in H0.
          eapply H in H0.
          assumption.
    - intros. destr H.
      unfold PropSet.subset.
      intros.
      unfold PropSet.elem_of in H1.
      unfold PropSet.of_list in H1.
      eapply in_inv in H1.
      destr H1.
      + eapply existsb_eqb_in in H.
        unfold PropSet.elem_of, PropSet.of_list.
        rewrite H1 in *.
        assumption.
      + unfold subset in H0.
        unfold PropSet.elem_of, PropSet.of_list in *.
        eapply H0, H1.
  Qed.

  Lemma is_list_subset_of_list:
    forall l1 l2,
      PropSet.subset (PropSet.of_list l1) (PropSet.of_list l2) <->
      is_list_subset l1 l2 = true.
  Proof.
    unfold iff.
    split.
    - induction l1.
      + simpl. intros. reflexivity.
      + intros. eapply subset_of_list_cons in H.
        simpl.
        destr H. eapply IHl1 in H0.
        rewrite H, H0 in *.
        simpl.
        reflexivity.
    - induction l1.
      + simpl. intros.
        unfold subset, of_list.
        intros.
        unfold PropSet.elem_of in *.
        inversion H0.
      + intros. simpl in H.
        eapply andb_prop in H.
        destr H.
        eapply subset_of_list_cons.
        rewrite H.
        propositional idtac.
        reflexivity.
  Qed.


  Lemma subset_of_list_removeb:
    forall (l: list string) s,
      PropSet.subset (PropSet.of_list (List.removeb eqb s l))
        (PropSet.of_list (l)).
  Proof.
    intros. rewrite of_list_removeb.
    unfold PropSet.subset.
    intros.
    unfold PropSet.elem_of in H.
    unfold PropSet.diff in H.
    destr H.
    eapply H.
  Qed.
  Lemma subset_of_list_diff:
    forall  l' (l: list string),
      PropSet.subset (PropSet.of_list (list_diff eqb l l'))
        (PropSet.of_list l).
  Proof.
    intros.
    unfold subset.
    intros.
    unfold elem_of in *.
    unfold of_list in *.
    eapply In_list_diff_weaken.
    eapply H.
  Qed.


  Lemma superset_of_list_cons:
    forall h t l,
      PropSet.subset (PropSet.of_list l) (PropSet.of_list (h :: t)) <->
      forallb (fun x => ((eqb h x) || (existsb (eqb x) t))%bool) l = true.
  Proof.
    intros.
    unfold iff.
    split.
    - induction l.
      + simpl in *. eauto.
      + simpl in *. intros.
        apply subset_of_list_cons in H.
        destr H.
        simpl in H.
        apply andb_true_intro.
        split.
        * rewrite eqb_sym. eapply H.
        * eauto.
    - induction l.
      + simpl in *. intro. unfold PropSet.subset.
        intros.
        unfold PropSet.elem_of, PropSet.of_list in H0.
        inversion H0.
      + simpl. intros.
        apply andb_prop in H.
        destr H.
        apply subset_of_list_cons.
        split.
        * simpl. rewrite eqb_sym. eapply H.
        * eauto.
  Qed.

  Lemma forallb_implies:
    forall (l: list string) (f: string -> bool) (g: string -> bool),
      forallb f l = true ->
      (forall s, f s = true -> g s = true) ->
      forallb g l = true.
  Proof.
    induction l.
    - simpl. auto.
    - simpl. intros.
      apply andb_prop in H.
      destr H.
      apply andb_true_intro.
      split.
      + eauto.
      + eauto.
  Qed.



  Lemma superset_of_list_tail:
    forall h t (l: list string),
      PropSet.subset (PropSet.of_list l) (PropSet.of_list (t))
      -> PropSet.subset (PropSet.of_list l) (PropSet.of_list (h :: t)).
  Proof.
    intros.
    apply superset_of_list_cons.
    eapply forallb_implies.
    - assert (is_list_subset l t = true). { eapply is_list_subset_of_list. assumption. }
      unfold is_list_subset in H0.
      eapply H0.
    - simpl.
      intros. rewrite H0.
      eapply Bool.orb_true_r.
  Qed.

  Lemma subset_of_list_tail:
    forall h (l1 l2: list string),
      PropSet.subset (PropSet.of_list l1) (PropSet.of_list l2) ->
      PropSet.subset (PropSet.of_list (h :: l1)) (PropSet.of_list (h :: l2)).
  Proof.
    intros.
    apply subset_of_list_cons.
    split.
    - simpl. rewrite eqb_refl.
      apply Bool.orb_true_l.
    - apply superset_of_list_cons.
      eapply forallb_implies.
      + apply is_list_subset_of_list in H.
        unfold is_list_subset in H.
        eapply H.
      + simpl; intros. rewrite H0.
        apply Bool.orb_true_r.
  Qed.

  Lemma find_eqb:
    forall (l: list string) s s',
      find (eqb s) l = Some s' -> s = s'.
  Proof.
    induction l; simpl in *.
    - intros.
      inversion H.
    - intros. destr ((s =? a)%string).
      + inversion H. reflexivity.
      + eapply IHl in H. eapply H.
  Qed.

  Lemma existsb_find_some:
    forall (l: list string) s s',
      (find (eqb s) l = Some s') -> existsb (eqb s) l = true.
  Proof.
    intros.
    induction l.
    + simpl in *.
      inversion H.
    + simpl in H.
      destr (s =? a)%string.
      * inversion H. simpl in *.
        rewrite eqb_refl. eapply Bool.orb_true_l.
      * apply IHl in H. simpl.
        rewrite H.
        eapply Bool.orb_true_r.
  Qed.

  Lemma subset_of_list_split_union:
    forall s1 s1' s2 s2',
      subset (of_list s1) (of_list s1')
      -> subset (of_list s2) (of_list s2')
      -> subset (of_list (list_union eqb s1 s2)) (of_list (list_union eqb s1' s2')).
  Proof.
    intros. repeat rewrite of_list_list_union.
    eapply subset_union_l.
    - eapply subset_union_rl. assumption.
    - eapply subset_union_rr. assumption.
  Qed.

  Lemma subset_of_list_union:
    forall s1a s1b s2,
      subset (of_list s1a) (of_list s2) ->
      subset (of_list s1b) (of_list s2) ->
      subset (of_list (list_union eqb s1a s1b)) (of_list s2).
  Proof.
    intros. rewrite of_list_list_union.
    eapply subset_union_l; assumption.
  Qed.

  Lemma subset_of_list_union_inv:
    forall s1a s1b s2,
      subset (of_list (list_union eqb s1a s1b)) (of_list s2) ->
      subset  (of_list s1a) (of_list s2) /\
        subset (of_list s1b) (of_list s2).
  Proof.
    intros.
    rewrite of_list_list_union in H.
    split.
    - unfold subset, union in *.
      unfold elem_of in *.
      intros. eapply H.
      eauto.
    - unfold subset, union in *.
      unfold elem_of in *.
      intros. eapply H.
      eauto.
  Qed.

  Lemma superset_of_list_union_l:
    forall s1 s2a s2b,
      subset (of_list s1) (of_list s2a) ->
      subset (of_list s1) (of_list (list_union eqb s2a s2b)).
  Proof.
    intros. rewrite of_list_list_union. eapply subset_union_rl; assumption.
  Qed.

  Lemma superset_of_list_union_r:
    forall s1 s2a s2b,
      subset (of_list s1) (of_list s2b) ->
      subset (of_list s1) (of_list (list_union eqb s2a s2b)).
  Proof.
    intros. rewrite of_list_list_union. eapply subset_union_rr; assumption.
  Qed.

  Lemma superset_of_list_union_comm:
    forall s1 s2a s2b,
      subset (of_list s1) (of_list (list_union eqb s2a s2b)) ->
      subset (of_list s1) (of_list (list_union eqb s2b s2a)).
  Proof.
    intros.
    rewrite of_list_list_union in *.
    eapply subset_trans.
    - eassumption.
    - eapply union_comm.
  Qed.


  Lemma superset_of_list_union_assoc:
    forall s1 s2a s2b s2c,
      subset (of_list s1) (of_list (list_union eqb (list_union eqb s2a s2b) s2c)) ->
      subset (of_list s1) (of_list (list_union eqb s2a (list_union eqb s2b s2c))).
  Proof.
    intros.
    repeat rewrite of_list_list_union in *.
    eapply subset_trans.
    - eassumption.
    - eapply union_assoc.
  Qed.

  Lemma subset_of_list_find_removeb:
    forall a x l,
      subset
        (of_list
           (if find (eqb a) (List.removeb eqb x l)
            then List.removeb eqb x l
            else a :: List.removeb eqb x l))
        (of_list (if find (eqb a) l then l else a :: l)).
  Proof.
    intros.
    destr (find (eqb a) l).
    - destr (find (eqb a) (List.removeb eqb x l)).
      + eapply subset_of_list_removeb.
      + eapply subset_of_list_cons.
        split.
        * eapply existsb_find_some.
          eassumption.
        * eapply subset_of_list_removeb.
    - destr (find (eqb a) (List.removeb eqb x l)).
      + eapply superset_of_list_tail.
        eapply subset_of_list_removeb.
      + eapply subset_of_list_tail.
        eapply subset_of_list_removeb.
  Qed.



  Lemma In_list_diff_spec:
   forall {E : Type} {eeq : E -> E -> bool},
     EqDecider eeq ->
     forall (l1 l2 : list E) (x : E),
       In x (list_diff eeq l1 l2) <-> In x l1 /\ (~ In x l2).
  Proof.
    induction l1.
    - simpl.
      intros.
      rewrite list_diff_empty_l.
      unfold iff.
      propositional idtac.
    - simpl. intros.
      rewrite list_diff_cons.
      destr (find (eeq a) l2).
      + unfold iff.
        split.
        * intros. eapply IHl1 in H0.
          propositional idtac.
        * intros.
          propositional idtac.
          2: { eapply IHl1.
               propositional idtac. }
          eapply find_some in E0.
          propositional idtac.
          destr (eeq x e).
          -- exfalso; auto.
          -- inversion E0_r.
      + unfold iff.
        split.
        * intros. specialize (find_none (eeq a) l2).
          intros.
          assert (forall x : E, In x l2 -> eeq a x = false).
          { eauto. }
          inversion H0.
          -- propositional idtac; eauto.
             eapply H1 in H3.
             destr (eeq x x).
             ++ inversion H3.
             ++ eapply E1. reflexivity.
          -- eapply IHl1 in H3.
             propositional idtac.
        * intros.
          propositional idtac.
          -- eapply in_eq.
          -- eapply in_cons. eapply IHl1. propositional idtac.
  Qed.

  Lemma of_list_list_diff :
    forall {E : Type} {eeq : E -> E -> bool},
      EqDecider eeq ->
      forall l1 l2 : list E,
        of_list (list_diff eeq l1 l2) = diff (of_list l1) (of_list l2).
  Proof.
    intros.
    extensionality e. apply propositional_extensionality.
    unfold of_list, diff, elem_of.
    eapply In_list_diff_spec.
    assumption.
  Qed.
  Ltac subset_union_solve :=
    match goal  with
    | |- subset (union _ _) _  => eapply subset_union_l; subset_union_solve
    | |- subset _ (union _ _)  =>
        try solve [ eapply subset_union_rl; subset_union_solve ]; try solve [ eapply subset_union_rr; subset_union_solve ]; idtac
    | |- subset ?x ?x => solve [ eapply subset_refl ]
    | |- _ => fail
    end.


  Ltac listset_to_set :=
    match goal with
    | H: context[of_list (ListSet.list_union _ _ _)] |- _ => rewrite ListSet.of_list_list_union in H
    | H: context[of_list (ListSet.list_diff _ _ _)] |- _ =>
        rewrite of_list_list_diff in H;
        try match goal with
          | |- EqDecider String.eqb => eapply String.eqb_spec
          end
    | H: context[of_list (List.removeb _ _ _)] |- _ =>
        rewrite ListSet.of_list_removeb in H
    end.

  Lemma live_upper_bound':
    forall s l,
      subset (of_list (live s l)) (of_list (list_union String.eqb (accessed_vars_stmt s) l)).
  Proof.
    intro.
    induction s.
    - simpl. eapply subset_of_list_find_removeb.
    - simpl. intros.  eapply sameset_ref.
    - simpl. eapply subset_of_list_find_removeb.
    - simpl. intro.
      eapply subset_trans.
      + eapply subset_of_list_removeb.
      + eauto.
    - simpl. intro.
      eapply subset_of_list_removeb.
    - simpl.
      destr z.
      + destr ((y =? v)%string); intro.
        * eapply subset_of_list_split_union.
          -- eapply subset_refl.
          -- eapply subset_of_list_removeb.
        * eapply subset_of_list_split_union.
          -- eapply subset_refl.
          -- eapply subset_of_list_removeb.
      + simpl. eapply subset_of_list_find_removeb.
    - simpl. eapply subset_of_list_find_removeb.
    - simpl; intro. eapply subset_of_list_union.
      + eapply subset_of_list_union.
        * eapply subset_trans.
          -- eapply IHs1.
          -- repeat rewrite of_list_list_union.
             subset_union_solve.
        * eapply subset_trans.
          -- eapply IHs2.
          -- repeat rewrite of_list_list_union.
             subset_union_solve.
      + repeat rewrite of_list_list_union.
        subset_union_solve.
    - simpl.
      intros.
      eapply subset_trans.
      + unfold fixpoint_inc.
        eapply is_list_subset_of_list.
        eapply fixpoint_inc'_bounded.
        intros.
        eapply is_list_subset_of_list in H.
        eapply is_list_subset_of_list.
        repeat listset_to_set.
        repeat rewrite of_list_list_union.
        * eapply subset_trans; [ eapply IHs1 | ].
          repeat rewrite of_list_list_union.
          eapply subset_union_l; [ subset_union_solve | ].
          eapply subset_union_l; [ eapply subset_trans; [ eapply IHs2 | ] | ].
          -- repeat rewrite of_list_list_union.
             eapply subset_union_l; [ subset_union_solve | ].
             eassumption.
          -- subset_union_solve.
      + eapply subset_refl.
    - simpl.
      intros.
      eapply subset_trans.
      + eapply IHs1.
      + eapply subset_of_list_union.
        * repeat rewrite of_list_list_union.
          subset_union_solve.
        * eapply subset_trans.
          -- eapply IHs2.
          -- repeat rewrite of_list_list_union.
             subset_union_solve.
    - simpl. intros. eapply subset_refl.
    - simpl.
      intros.
      eapply subset_of_list_split_union.
      + eapply subset_refl.
      + eapply subset_of_list_diff.
    - simpl. intros. eapply subset_refl.
      eapply subset_of_list_split_union.
      + eapply subset_refl.
      + eapply subset_of_list_diff.
  Qed.

  Lemma live_while:
    forall s1 c s2 l,
      let l' := live (SLoop s1 c s2) l in
      subset (of_list (live s1
                         (list_union eqb


                            (live s2 l')
                            (list_union eqb (accessed_vars_bcond c) l)))) (of_list l').
  Proof.
    intros.
    cbn -[fixpoint_inc' list_union]   in l'.
    unfold fixpoint_inc in l'.

    let Heq := fresh in
    specialize
      (fixpoint_inc'_convergence
         fix_fuel []
          (list_union eqb
             (list_union eqb (accessed_vars_bcond c)
                (list_union eqb (accessed_vars_stmt s1)
                   (accessed_vars_stmt s2))) l)
          (fun x : list string =>
           live s1
             (list_union eqb
                (live s2 x)
                (list_union eqb (accessed_vars_bcond c) l)))) as Heq.
    cbn zeta in H; destr H.
    - eapply is_list_subset_of_list in H.
      replace (fixpoint_inc' fix_fuel []
              (list_union eqb
                 (list_union eqb (accessed_vars_bcond c)
                    (list_union eqb (accessed_vars_stmt s1)
                       (accessed_vars_stmt s2))) l)
              (fun x : list string =>
               live s1
                 (list_union eqb
                    (live s2 x)
                    (list_union eqb (accessed_vars_bcond c) l)
                    ))) with l' in *.
      2: { auto. }
      assumption.
    -  replace (fixpoint_inc' fix_fuel []
              (list_union eqb
                 (list_union eqb (accessed_vars_bcond c)
                    (list_union eqb (accessed_vars_stmt s1)
                       (accessed_vars_stmt s2))) l)
              (fun x : list string =>
               live s1
                 (list_union eqb
                     (live s2 x)(list_union eqb (accessed_vars_bcond c) l)
                   ))) with l' in *.
       2: { auto. }
       eapply subset_trans; [ eapply live_upper_bound' | ].
       rewrite H.
       repeat rewrite of_list_list_union.
       eapply subset_union_l; [ subset_union_solve | ].
       eapply subset_union_l; [  | subset_union_solve ].
       eapply subset_trans; [ eapply live_upper_bound' | ].
       repeat rewrite of_list_list_union.
       subset_union_solve.
  Qed.

  Fixpoint dce(s: stmt var)(u: list var)  : stmt var :=
    match s with
    | SInteract _ _ _ => s
    | SCall _ _ _ => s
    | SLoad _ x _ _ => (* maybe unsound optimization? *)
        if (existsb (eqb x) u) then
          s
        else
          SSkip
    | SStore _ _ _ _ => s
    | SInlinetable _ x _ _ => (* maybe unsound? *)
        if (existsb (eqb x) u) then
          s
        else
          SSkip
    | SStackalloc x _ _ => (* maybe unsound? *)
        if (existsb (eqb x) u) then
          s
        else
          SSkip
    | SLit x _ =>
        if (existsb (eqb x) u) then
          s
        else
          SSkip
    | SOp x _ _ _ =>
        if (existsb (eqb x) u) then
          s
        else
          SSkip
    | SSet x _ =>
         if (existsb (eqb x) u) then
          s
        else
          SSkip
    | SIf c s1 s2 => SIf c (dce s1 u) (dce s2 u)
    | SLoop s1 c s2 =>
        let live_before :=  (live (SLoop s1 c s2) u) in
        SLoop
          (dce s1 (list_union String.eqb
                     (live s2 live_before)
                      (list_union
                         eqb
                         (accessed_vars_bcond c)
                         u)))
          c
          (dce s2 (live_before))
    | SSeq s1 s2 => SSeq (dce s1 (live s2 u)) (dce s2 u)
    | SSkip => SSkip
    end.

  Definition dce_function: (list string *
                              list string *
                              stmt string ) ->
                           result (list string
                                   * list string
                                   * stmt string
                             ) :=
    fun '(argnames, retnames, body) =>
      let body' := dce body retnames in
      Success (argnames, retnames, body').

  Definition dce_functions : env -> result env :=
    map.try_map_values dce_function.

End WithArguments0.

Section WithArguments1.
  Context {width: Z}.
  Context {BW: Bitwidth.Bitwidth width }.
  Context {word : word width } { word_ok : word.ok word }.
  Context {env: map.map string (list var * list var * stmt var) } { env_ok : map.ok env }.
  Context {mem: map.map word (Init.Byte.byte : Type) } {mem_ok : map.ok mem } .
  Context {locals: map.map string word } {locals_ok : map.ok locals }.
  Context {ext_spec : Semantics.ExtSpec } {ext_spec_ok: Semantics.ext_spec.ok ext_spec } .

  (* Duplicated from previous section: when
     reorganizing, decide which one to keep *)
  Ltac subset_union_solve :=
    match goal  with
    | |- subset (union _ _) _  => eapply subset_union_l; subset_union_solve
    | |- subset _ (union _ _)  =>
        try solve [ eapply subset_union_rl; subset_union_solve ]; try solve [ eapply subset_union_rr; subset_union_solve ]; idtac
    | |- subset ?x ?x => solve [ eapply subset_refl ]
    | |- _ => fail
    end.


  Definition compile_post
    used_after
    (postH: Semantics.trace -> mem -> locals -> MetricLog -> Prop)
    :
    Semantics.trace -> mem -> locals -> MetricLog -> Prop
    :=
    (fun t' m' lL' mcL' =>
       exists lH' mcH',
         map.agree_on (PropSet.of_list used_after) lH' lL'
         /\ postH t' m' lH' mcH').

  Local Hint Constructors exec: core.


   Lemma sameset_union:
    forall (s1 s2 s1' s2': set string),
      sameset s1 s1' ->
      sameset s2 s2' ->
      sameset (union s1 s2) (union s1' s2').
  Proof.
    intros.
    unfold sameset, union.
    split.
    - unfold sameset, subset in *.
      propositional idtac.
      assert (x \in s1 \/ x \in s2) by auto.
      cut (x \in s1' \/ x \in s2'); [ auto |  ].
      destr H.
      + left; eauto.
      + right; eauto.
    - unfold sameset, subset in *.
      propositional idtac.
      assert (x \in s1' \/ x \in s2') by auto.
      cut (x \in s1 \/ x \in s2); [ auto |  ].
      destr H.
      + left; eauto.
      + right; eauto.
  Qed.

  Lemma agree_on_cons:
    forall k ks (m1 m2: locals),
      map.agree_on (of_list (k :: ks)) m1 m2 <->
        map.agree_on (of_list ks) m1 m2 /\
          map.get m1 k = map.get m2 k.
  Proof.
    unfold iff.
    propositional idtac.
    - unfold map.agree_on in *.
      intros.
      eapply Hyp.
      unfold of_list, elem_of in *.
      eauto using in_cons.
    - unfold map.agree_on in *.
      intros.
      eapply Hyp.
      unfold of_list, elem_of in *.
      eauto using in_eq.
    - unfold map.agree_on in *.
      intros.
      unfold of_list, elem_of in *.
      inversion H.
      + rewrite H0 in *.  assumption.
      + eapply Hyp_l. assumption.
  Qed.

  Lemma agree_on_getmany:
    forall ks (m1 m2: locals),
      map.agree_on (of_list ks) m1 m2 ->
      map.getmany_of_list m1 ks =
        map.getmany_of_list m2 ks.
  Proof.
    intros.
    unfold map.getmany_of_list, map.agree_on.
    induction ks.
    - simpl. reflexivity.
    - simpl.
      pose proof H as H'.
      unfold map.agree_on in H.
      assert (map.get m1 a = map.get m2 a).
      { eapply H. unfold elem_of. unfold of_list.
        eauto using in_eq. }
      rewrite H0.
      rewrite IHks.
      + reflexivity.
      + eapply agree_on_cons in H'.  propositional idtac.
  Qed.


  Lemma agree_on_subset:
    forall ks ks' (m1 m2: locals),
      subset ks' ks ->
      map.agree_on ks m1 m2 ->
      map.agree_on ks' m1 m2.
  Proof.
    intros.
    unfold map.agree_on, subset in *.
    intros.
    eapply H0.
    eapply H.
    eassumption.
  Qed.

  Lemma agree_on_comm :
    forall ks (m1 m2: locals),
      map.agree_on ks m1 m2 ->
      map.agree_on ks m2 m1.
  Proof.
    intros.
    unfold map.agree_on in *.
    intros.
    symmetry.
    eauto.
  Qed.

  Ltac agree_on_solve :=
    match goal with
    | H: map.agree_on ?s ?x ?y |-
        map.agree_on _ ?x ?y =>
        eapply agree_on_subset with (ks := s);
        [ subset_union_solve | eapply H]
    | H: map.agree_on ?s ?x ?y |-
        map.agree_on _ ?y ?x =>
        eapply agree_on_comm; agree_on_solve
    | _ => idtac
    end.

  Lemma agree_on_union:
    forall (s0 s1: set string) (m0 m1: locals),
      map.agree_on (union s0 s1) m0 m1
      <-> map.agree_on s0 m0 m1 /\ map.agree_on s1 m0 m1.
  Proof.
    intros.
    unfold iff; split; unfold map.agree_on in *.
    - split; intros; cut (s0 k \/ s1 k); auto.
    - intros; destr H; cut (s0 k \/ s1 k); auto.
      intros; destr H0; auto.
  Qed.

  Lemma agree_on_sameset:
    forall s1 s2 (m1 m2: locals),
      map.agree_on s2 m1 m2 ->
      sameset s1 s2 ->
      map.agree_on s1 m1 m2.
  Proof.
    intros.
    eapply agree_on_subset; eauto; eapply H0.
  Qed.


  Lemma sameset_union_diff_of_list:
    forall (l1 l2: list string),
      sameset (union (of_list l1) (of_list l2)) (union (diff (of_list l1) (of_list l2) ) (of_list l2)).
  Proof.
    intros.
    unfold sameset, of_list, subset, union, diff.

    assert (forall x, In x l2 \/ ~ (In x l2)).
    { intro. eapply ListDec.In_decidable. unfold ListDec.decidable_eq.
      intros. destr (eqb x0 y).
      - unfold Decidable.decidable. left. reflexivity.
      - unfold Decidable.decidable. right. eassumption.
    }

    split.
    - intros.
      cut ((fun x : string =>
              x \in (fun e : string => In e l1) \/
                      x \in (fun e : string => In e l2)) x); [ simpl; intro | auto ].
      cut ((In x l1) \/ (In x l2)); [ simpl; intro | auto ].
      cut ((fun x0 : string =>
              x0 \in
              (fun x1 : string =>
                 x1 \in (fun e : string => In e l1) /\
                          ~ x1 \in (fun e : string => In e l2)) \/
                x0 \in (fun e : string => In e l2)) x); [ simpl; intro; auto | ].
      simpl.
      assert (In x l2 \/ ~ In x l2) by eapply H.
      destr H3.
      + right. auto.
      + propositional idtac. left.
        cut ((fun x1 : string =>
   x1 \in (fun e : string => In e l1) /\
            ~ x1 \in (fun e : string => In e l2)) x); [ simpl; intro; auto | ].
        simpl.
        split; auto.
    - intros.
      cut ((fun x : string =>
        x \in
        (fun x0 : string =>
         x0 \in (fun e : string => In e l1) /\
         ~ x0 \in (fun e : string => In e l2)) \/
          x \in (fun e : string => In e l2)) x); [ | auto ].
      simpl. intro.
      destr H1.
      + cut ((fun x0 : string =>
        x0 \in (fun e : string => In e l1) /\
                 ~ x0 \in (fun e : string => In e l2)) x); [ simpl; intro | auto ].
        cut ((fun x0 : string =>
   x0 \in (fun e : string => In e l1) \/
            x0 \in (fun e : string => In e l2)) x); [ simpl; intro; auto | ].
        simpl.
        destr H2. left. assumption.
      + cut ((fun x0 : string =>
   x0 \in (fun e : string => In e l1) \/
            x0 \in (fun e : string => In e l2)) x); [ simpl; intro; auto | ].
        simpl.
        right. assumption.
  Qed.

    Lemma agree_on_put:
    forall a r s (mH mL: locals)  mH' mL',
      map.agree_on s mH mL ->
      map.put mH a r = mH' ->
      map.put mL a r = mL' ->
      map.agree_on (union s (singleton_set a)) mH' mL'.
  Proof.
    intros.
    apply agree_on_union.
    split.
    - unfold map.agree_on in *.
      intros.
      eapply H in H2.
      subst.
      destr (eqb a k).
      + repeat rewrite map.get_put_same; reflexivity.
      + repeat rewrite map.get_put_diff; eauto.
    - unfold map.agree_on.
      intros.
      cut (a = k).
      + intros. subst.
        repeat rewrite map.get_put_same; reflexivity.
      + assert (singleton_set a k) by auto.
        unfold singleton_set in *; assumption.
  Qed.

   Lemma agree_on_diff_put:
    forall a r s (mH mL: locals),
      map.agree_on (diff (of_list s) (singleton_set a)) mH mL ->
                    map.agree_on (of_list s)  (map.put mH a r) (map.put mL a r).
   Proof.
     intros.
     eapply agree_on_subset.
     2: {
      eapply agree_on_put.
      2-3: reflexivity.
      eapply H.
     }

     replace (singleton_set a) with (of_list [a]).

     2: { erewrite singleton_set_eq_of_list. reflexivity. }
     eapply subset_trans.
     2: eapply sameset_union_diff_of_list.
     subset_union_solve.
   Qed.
  Lemma agree_on_putmany_of_list_zip:
    forall (lk0: list string) lv s (mH mL: locals) mH' mL',
      map.agree_on s mH mL ->
      map.putmany_of_list_zip lk0 lv mH = Some mH' ->
      map.putmany_of_list_zip lk0 lv mL = Some mL' ->
      map.agree_on (union s (of_list lk0)) mH' mL'.
  Proof.
    induction lk0.
    - intros. simpl in *.
      destr lv; [ | discriminate ].
      apply agree_on_union.
      split.
      + inversion H0.
        inversion H1.
        subst; eauto.
      + unfold map.agree_on.
        intros.
        cut (of_list [] k).
        * unfold of_list.
          intros.
          exfalso.
          eauto using in_nil.
        * auto.
    - intros. destr lv; [ discriminate | ].
      simpl in *.
      cut (map.agree_on (union s (singleton_set a))
             (map.put mH a r) (map.put mL a r)).
      + intros.
        eapply IHlk0 in H2.
        2-3: eassumption.
        eapply agree_on_sameset.
        * eassumption.
        * eapply sameset_trans.
          2: { eapply union_assoc. }
          apply sameset_union;
            [ eapply sameset_ref | eapply of_list_cons ].
      + eapply agree_on_put.
        2-3: reflexivity.
        eassumption.
  Qed.


  Lemma agree_on_diff_putmany_of_list_zip :
    forall o1 o2 v (l l': locals) lL lL',
      map.agree_on (diff (of_list o1) (of_list o2)) l lL
      -> map.putmany_of_list_zip o2 v l = Some l'
      -> map.putmany_of_list_zip o2 v lL = Some lL'
      -> map.agree_on (of_list o1) l' lL'.
  Proof.
    intros.
    eapply agree_on_subset.
    2: {
      eapply agree_on_putmany_of_list_zip.
      2-3: eassumption.
      eapply H.
    }
    eapply subset_trans.
    2: { eapply sameset_union_diff_of_list. }
    subset_union_solve.
  Qed.
  Lemma agree_on_find:
    forall s l (m1 m2: locals),
      map.agree_on (of_list (if (find (eqb s) l)
                    then l
                    else s :: l)) m1 m2
      -> map.agree_on (of_list [s]) m1 m2 /\
           map.agree_on (of_list l) m1 m2.
  Proof.
    intros.
    destr (find (eqb s) l).
    - split.
      + unfold map.agree_on.
        intros.
        inversion H0.
        2: { inversion H1. }
        rewrite H1 in *.
        apply find_some in E.
        destr E.
        apply eqb_eq in H3.
        rewrite H3 in *.
        eauto.
      + assumption.
    - apply agree_on_cons in H.
      destr H.
      propositional idtac.
      unfold map.agree_on.
      intros.

      inversion H1.
      2: { inversion H2. }
      rewrite H2 in *.
      assumption.
  Qed.

  Ltac listset_to_set :=
    match goal with
    | H: context[of_list (ListSet.list_union _ _ _)] |- _ => rewrite ListSet.of_list_list_union in H
    | H: context[of_list (ListSet.list_diff _ _ _)] |- _ =>
        rewrite of_list_list_diff in H;
        try match goal with
          | |- EqDecider String.eqb => eapply String.eqb_spec
          end
    | H: context[of_list (List.removeb _ _ _)] |- _ =>
        rewrite ListSet.of_list_removeb in H
    end.

  Lemma agree_on_refl :
    forall keySet (m : locals),
      map.agree_on keySet m m.
  Proof.
    intros.
    unfold map.agree_on.
    intros.
    reflexivity.
  Qed.

Lemma existsb_of_list :
    forall k keySet,
      existsb (eqb k) keySet = true <-> k \in of_list keySet.
  Proof.
    intros.
    simpl.
    unfold iff.
    propositional idtac.
    - induction keySet.
      + simpl in Hyp. discriminate.
      + simpl in Hyp.
        apply Bool.orb_prop in Hyp.
        destr Hyp.
        * eapply of_list_cons.
          unfold add.
          eapply in_union_l.
          eapply eqb_eq in H.
          rewrite H.
          unfold singleton_set.
          constructor.
        * eapply of_list_cons.
          unfold add.
          eapply in_union_r.
          eauto.
    - induction keySet.
      +  unfold of_list in Hyp. simpl in Hyp.
         auto.
      + simpl.
        inversion Hyp.
        * rewrite H.
          rewrite eqb_refl.
          eapply Bool.orb_true_l.
        * rewrite IHkeySet.
          -- eapply Bool.orb_true_r.
          -- assumption.
  Qed.


   Lemma agree_on_not_in:
    forall keySet (m: locals) x,
      existsb (String.eqb x) keySet = false ->
      forall y,
        map.agree_on (PropSet.of_list keySet) (map.put m x y) m.
  Proof.
    intros.
    unfold map.agree_on.
    intros.
    rewrite map.get_put_dec.
    destr (x =? k)%string.
    - apply existsb_of_list in H0.
      rewrite H in H0. discriminate.
    - reflexivity.
  Qed.

  Lemma agree_on_put_not_in :
    forall x l (m1 m2: locals),
      map.agree_on (of_list l) m1 m2
      -> existsb (eqb x) l = false
      -> forall v,
          map.agree_on (of_list l) (map.put m1 x v) m2.
  Proof.
    intros.
    unfold map.agree_on.
    intros.
    rewrite <- H.
    2: eassumption.
    erewrite agree_on_not_in.
    3: eassumption.
    2: eassumption.
    reflexivity.
  Qed.


  Lemma agree_on_sym:
    forall s (m1 m2: locals),
      map.agree_on s m1 m2 ->
      map.agree_on s m2 m1.
  Proof.
    intros; unfold map.agree_on in *.
    intros. eapply H in H0.
    symmetry.
    assumption.
  Qed.

  Lemma agree_on_eval_bcond:
    forall cond (m1 m2: locals),
      map.agree_on (of_list (accessed_vars_bcond cond)) m1 m2 ->
      eval_bcond m1 cond = eval_bcond m2 cond.
  Proof.
    intros.
    induction cond.
    - simpl in *.
      destr ((x =? y)%string).
      + unfold map.agree_on in H.
        repeat rewrite H.
        * reflexivity.
        * unfold of_list; simpl.
          cut ((fun e : string => y = e \/ False) y);
            [ auto |
              simpl; propositional idtac; left; reflexivity ].
      + unfold map.agree_on in H.
        repeat rewrite H.
        * reflexivity.
        *  unfold of_list; simpl.
          cut ((fun e : string => x = e \/ y = e \/ False) y);
            [ auto |
              simpl; propositional idtac; right; left; reflexivity ].

        *  unfold of_list; simpl.
          cut ((fun e : string => x = e \/ y = e \/ False) x);
            [ auto |
              simpl; propositional idtac;  left; reflexivity ].
    - simpl in *.
      repeat rewrite H.
      + reflexivity.
      + cut ((fun e : string => x = e \/ False) x);
            [ auto |
              simpl; propositional idtac; left; reflexivity ].
  Qed.

  Lemma dce_correct_aux :
    forall eH eL,
      dce_functions eH = Success eL ->
      forall sH t m mcH lH postH,
        exec eH sH t m lH mcH postH ->
        forall used_after lL mcL,
          map.agree_on (of_list (live sH used_after)) lH lL ->
          exec eL (dce sH used_after) t m lL mcL (compile_post used_after postH).
  Proof.
    induction 2.
    (* - simpl.
      intros.
      do 2 listset_to_set.
      eapply @exec.interact; eauto.
      + erewrite agree_on_getmany.
        * eassumption.
        * eapply agree_on_sym.
          eapply agree_on_subset.
          2: { eapply H4. }
          subset_union_solve.
      + intros.
        eapply H3 in H5.
        destr H5. *)
    12: {
      intros.
      cbn - [live].
      rename IHexec into IH1.
      rename H6 into IH12.
      rename H4 into IH2.
      cbn - [live] in IH12.
      eapply @exec.loop with (mid2 := compile_post (live (SLoop body1 cond body2) used_after) mid2).
      { eapply IH1.
        eapply agree_on_subset.
        - let Heq := fresh in
          specialize (live_while body1 cond body2 used_after) as Heq; cbn zeta in Heq.
          eapply H4.
        - eapply H7.
      }
      { intros.
        unfold compile_post in *.
        repeat destr H4.
        eapply H1 in H6.
        erewrite agree_on_eval_bcond; [ eassumption | ].
        eapply agree_on_sym.
        repeat listset_to_set.
        eapply agree_on_subset; [ | eapply H4 ].
        subset_union_solve.
      }
      { intros.
        unfold compile_post in *.
        repeat destr H4.
        eapply H2 in H8.
        - exists x.
          eexists.
          split.
          + repeat listset_to_set.
            eapply agree_on_subset; [ | eapply H4 ].
            subset_union_solve.
          + eapply H8.
        -  erewrite agree_on_eval_bcond; [ eassumption | ].

           repeat listset_to_set.
           eapply agree_on_subset; [ | eapply H4 ].
           subset_union_solve.
      }
      {
        intros.
        unfold compile_post in *.
        repeat destr H4.
        eapply IH2.
        - eapply H8.
        - erewrite agree_on_eval_bcond; [ eassumption | ].

           repeat listset_to_set.
           eapply agree_on_subset; [ | eapply H4 ].

           subset_union_solve.
        - repeat listset_to_set.
          eapply agree_on_subset; [ | eapply H4 ].
          subset_union_solve.
      }
      {
        intros.
        unfold compile_post in *.
        repeat destr H4.
        eapply IH12.
        - eapply H6.
        - eapply H4.

      }
        eapply H2.
        eapply H1.

      2: { intros.
           unfold compile_post in *.
           repeat destr H4.
           exists x.
           eexists.
           split.
           - admit.  (* trivial *)
           - eapply H2.
             + eapply H8.
             + admit.
      }
      3: { intros.
           unfold compile_post in *.
           repeat destr H4.
           eapply IH12.
           - eapply H6.
           - eapply H4.
      }
      4: {
      intros.

      cbn zeta.
      let Heq := fresh in pose proof live_while as Heq.
      specialize (H8 body1 cond body2 used_after).
      simpl.
      replace ( (fixpoint_inc
             (list_union eqb
                (list_union eqb (accessed_vars_bcond cond)
                   (list_union eqb (accessed_vars_stmt body1)
                      (accessed_vars_stmt body2)))
                (live body1
                   (list_union eqb (accessed_vars_bcond cond)
                      used_after)))
             (fun x : list string =>
              list_union eqb
                (live body1
                   (list_union eqb (accessed_vars_bcond cond)
                      used_after)) (live body2 x)))) with (live (SLoop body1 cond body2) used_after).
      2: { simpl in *. reflexivity. }
      assert ( subset
         (of_list
            (live body1
               (list_union eqb (accessed_vars_bcond cond)
                  used_after))) (of_list (live (SLoop body1 cond body2) used_after)) /\
                 subset (of_list (live body2 ( live (SLoop body1 cond body2) used_after))) (of_list ( live (SLoop body1 cond body2) used_after))).
      { eapply H8. }
      destr H9.
      eapply @exec.loop.
      + eapply IHexec.
        eapply agree_
      Print live.
      (* how do I unfold the let expression without opening everything *)
      simpl in *.
      remember (live (SLoop body1 cond body2) used_after) as l' in *.
      eapply live_while in Heql'.
      About live_while.
      eapply agree_on_subset in H7.
      2: { eapply live_while. }
      About agree_on_subset.
      Search agree_on_subset.
      Search live SLoop.


  Lemma dce_correct_aux' :
    forall eH eL,
      dce_functions eH = Success eL ->
      forall sH t m mcH lH postH,
        exec eH sH t m lH mcH postH ->
        forall used_after lL mcL,
          map.agree_on (of_list (live (dce sH used_after) used_after)) lH lL ->
          exec eL (dce sH used_after) t m lL mcL (compile_post used_after postH).
  Proof.
    induction 2.
    - simpl.
      intros.
      eapply @exec.interact; fwd.
      + match goal with
        | |- map.split _ _ _ => eassumption
        end.
      + match goal with
        | H: map.getmany_of_list ?l ?argvars = Some ?argvals,
            H1: map.agree_on _ ?l ?lL |-
            map.getmany_of_list ?lL ?argvars = Some _ =>
            repeat rewrite of_list_list_union, of_list_list_diff in *;
            [rewrite agree_on_getmany with (m2 := l);
             [ eassumption | agree_on_solve ]
            |
              eapply String.eqb_spec]
        end.
      + match goal with
        | |- ext_spec _ _ _ _ _ => eassumption
        end.
      + intros.
        match goal with
        | H: ?outcome ?mReceive ?resvals,
          H1: forall mReceive resvals,
            ?outcome mReceive resvals ->
            exists l', _ |- _ =>
            eapply H1 in H; fwd;
            match goal with
            | |- exists l'0, map.putmany_of_list_zip _ _ _ = Some l'0 /\ _ => idtac
            end
        end.

        match goal with
        | H: map.putmany_of_list_zip ?resvars ?resvals ?l = _
          |- exists l'0, map.putmany_of_list_zip ?resvars ?resvals ?lL = Some l'0 /\ _ =>
            let Heq := fresh in
            pose proof H as Heq;
            eapply map.putmany_of_list_zip_sameLength in Heq;
            eapply map.sameLength_putmany_of_list in Heq; destr Heq
        end.

        match goal with
        | H: map.putmany_of_list_zip ?resvars ?resvals _ = Some ?x
          |- exists l'0, map.putmany_of_list_zip ?resvars ?resvals ?lL = Some l'0 /\ _
          => exists x; split; [ eapply H | ]
        end.

        match goal with
        | |- forall m', map.split m' ?mKeep ?mReceive -> _
          =>  intros
        end; match goal with
             | H': map.split ?m' ?mKeep ?mReceive,
                 H: forall m',
                   map.split m' ?mKeep ?mReceive -> _
        |- _ => eapply H in H'
        end.

        match goal with
        | |- context[compile_post] => unfold compile_post
        end.

        match goal with
        | H: post ?t ?m' ?x _ |-
            exists lH' mcH', map.agree_on _ lH' _ /\
                                 (post _ _ lH' _) =>
            exists x; eexists; split; [ | eapply H]
        end.
        listset_to_set.
        listset_to_set.
        2: {  eapply String.eqb_spec. }
        match goal with
        | H: map.agree_on (union _ _) ?l ?lL
          |- _ => apply agree_on_union in H; destr H
        end.
         match goal with
          | H: map.agree_on (diff (of_list ?used_after) (of_list ?binds)) ?l ?lL,
              H1: map.putmany_of_list_zip ?binds ?retvs l = Some ?l',
                H2:  map.putmany_of_list_zip ?binds ?retvs lL = Some ?x
            |- map.agree_on (of_list used_after) l' x
            => eapply agree_on_diff_putmany_of_list_zip; [ eapply H | eapply H1 | eapply H2 ]
         end.
    - simpl.
      intros.
      eapply @exec.call; fwd.
      + match goal with
        | H: dce_functions ?eH = Success ?eL,
          H1: map.get ?eH ?fname = Some ?x |-
            map.get eL fname = Some _ =>
            unfold dce_functions in H;
            unfold dce_function in H;
            eapply map.try_map_values_fw in H; [ | eapply H1 ];
            repeat (destr H; simpl in H)
        end.
        match goal with
        | H: Success _ = Success ?x,
            H1: map.get ?eL ?fname = Some x
          |- map.get eL fname = Some _
          => inversion H; fwd; eapply H1
        end.
      + match goal with
        | H: map.getmany_of_list ?l ?args = Some ?argvs
          |- map.getmany_of_list lL args = Some _ => erewrite agree_on_getmany;  [ eapply H | ]
        end.
        listset_to_set.
        agree_on_solve.

      + match goal with
        | |- map.putmany_of_list_zip _ _ _ = Some _ => eassumption
        end.
      + match goal with
        | H: forall used_after lL mcL,
            map.agree_on _ ?st0 lL ->
            exec ?eL (dce ?fbody ?rets) _ _ lL  _ _
            |- exec ?eL (dce fbody rets) _  _ _ _ _ =>
            eapply H; eapply agree_on_refl
        end.
      + match goal with
        | |- forall t' m' mc' st1,
            compile_post ?rets ?outcome t' m' st1 mc' -> _
          => unfold compile_post; intros; fwd
        end.

        match goal with
        | H: outcome _ _ _ _,
            H1: forall t' m' mc' st1,
              outcome _ _ _ _ ->
              exists retvs l',
                map.getmany_of_list st1 ?rets = Some retvs /\ _
                |- _ => eapply H1 in H; fwd
        end.

        match goal with
        | H: map.getmany_of_list ?lH' ?rets = Some ?retvs,
            H1: map.agree_on (of_list ?rets) ?lH' ?st1,

  H2 : map.putmany_of_list_zip ?binds ?retvs _ = Some _ |-
            exists retvs0 l'0,
              map.getmany_of_list ?st1 ?rets = Some retvs0 /\ _
          =>
            let Heq := fresh in
            pose proof H2 as Heq;
            eapply map.putmany_of_list_zip_sameLength in Heq;
            eapply map.sameLength_putmany_of_list in Heq; destr Heq
        end.


        match goal with
        | H: map.agree_on (of_list ?rets) ?lH' ?st1,
            H1: map.getmany_of_list ?lH' ?rets = Some ?retvs,
          H2: map.putmany_of_list_zip ?binds ?retvs _ = Some ?x |-
            exists retvs0 l'0,
              map.getmany_of_list st1 rets = Some retvs0 /\ _
          => exists retvs; exists x; repeat split; [ | eapply H2 | ]
        end.
        * match goal with
          | H: map.agree_on (of_list ?rets) ?lH' ?st1,
              H1: map.getmany_of_list ?lH' ?rets = Some ?retvs
            |- map.getmany_of_list ?st1 ?rets = Some ?retvs
            => apply agree_on_getmany in H; rewrite <- H; eapply H1
          end.
        * match goal with
          | H: post ?t' ?m' ?l' _
            |- exists lH'0 mcH'0,
              map.agree_on (of_list ?used_after) lH'0 ?x /\
                post ?t' ?m' lH'0 mcH'0
            => exists l'; eexists; split; [ | eapply H ]
          end.
          do 2 listset_to_set.
          2: { eapply String.eqb_spec. }
          match goal with
          | H: map.agree_on (union _ _) ?l ?lL
            |- _ => apply agree_on_union in H; destr H
          end.

         match goal with
          | H: map.agree_on (diff (of_list ?used_after) (of_list ?binds)) ?l ?lL,
              H1: map.putmany_of_list_zip ?binds ?retvs l = Some ?l',
                H2:  map.putmany_of_list_zip ?binds ?retvs lL = Some ?x
            |- map.agree_on (of_list used_after) l' x
            => eapply agree_on_diff_putmany_of_list_zip; [ eapply H | eapply H1 | eapply H2 ]
         end.
    - simpl.
      intros.
      match goal with
      | |- context[if ?c then _ else _] => destr c
      end.
      + simpl in *. match goal with
      | H: map.agree_on (of_list (if _ then _ else _)) _ _ |- _ =>
          apply agree_on_find in H; destr H
        end. eapply @exec.load; simpl in *; fwd.

        * match goal with
          | H: map.agree_on (of_list [?a]) ?l ?lL,
            H1: map.get ?l ?a = Some ?addr |-
            map.get ?lL ?a = Some _ => rewrite <- H; [ eassumption | ]
        end.
        match goal with
        | |- ?s \in of_list [?s] => cut (of_list [s] s); [ simpl; intro; auto | unfold of_list; simpl; auto ]
        end.
      * match goal with
        | H: Memory.load _ _ _ = Some _ |- Memory.load _ _ _ = Some _ => eapply H
        end.
      * match goal with
        | |- compile_post _ _ _ _ _ _ => unfold compile_post
        end.
        match goal with
        | H: post ?t m (map.put ?l ?x ?v) _,
            H1: map.agree_on (of_list (List.removeb eqb ?x ?used_after)) ?l ?lL
          |- exists lH' mcH',
            map.agree_on (of_list used_after) lH'
              (map.put lL x v) /\
              post t m lH' mcH'
          => exists (map.put l x v); eexists; split; [ | ] ;
             match goal with
             | H: post ?t ?m (map.put ?l ?x ?v) _ |- post t m (map.put l x v) _ => eapply H
             | |- _ => idtac
             end
        end.
        listset_to_set.
        match goal with
          | H: map.agree_on
                 (diff (of_list ?used_after) (singleton_set ?x)) ?l ?lL |-
              map.agree_on (of_list ?used_after) (map.put ?l ?x ?v)
                (map.put ?lL ?x ?v) => eapply agree_on_diff_put; eapply H
        end.
      + simpl in *.
        eapply @exec.skip.
        unfold compile_post.
        match goal with
        | H: post ?t ?m (map.put ?l ?x ?v) _,
            H2: map.agree_on (of_list ?used_after) ?l ?lL,
          H3: existsb (eqb ?x) ?used_after = false |-
            exists lH' mcH',
              map.agree_on (of_list ?used_after) lH' ?lL /\
                post ?t ?m lH' mcH' =>
            exists (map.put l x v); eexists; split; [ eapply agree_on_put_not_in; [ eapply H2 | eapply H3 ] | eapply H]
        end.
    - simpl; intros.
      listset_to_set.
      match goal with
      | H: map.agree_on (union _ _) ?l ?lL |- _ =>
          eapply agree_on_union in H; destr H
      end.
      replace (of_list (if
              if
               (a =? v)%string
              then Some v
              else None
             then [v]
                else [a; v])) with
        (of_list (if (find (eqb a) [v]) then
           [v] else [a; v])) in *.
      2: {
        simpl.
        repeat match goal with
          | H: context[if ?c then _ else _] |- _ => destr c
          end.
        - reflexivity.
        - inversion E.
        - inversion E.
        - reflexivity.
      }
      repeat match goal with
             | H: map.agree_on (of_list (if _ then _ else _)) _ _ |- _
               => apply agree_on_find in H; destr H
             end.
      eapply @exec.store.
       + match goal with
        | H: map.get ?l ?a = Some _,
          H1: map.agree_on (of_list [?a]) ?l ?lL|- map.get ?lL ?a = Some _ =>
            rewrite <- H1; [ eapply H | ]; cut (of_list [a] a); [ auto | constructor; reflexivity ]
        end.
      + match goal with
        | H: map.get ?l ?a = Some _,
          H1: map.agree_on (of_list [?a]) ?l ?lL|- map.get ?lL ?a = Some _ =>
            rewrite <- H1; [ eapply H | ]; cut (of_list [a] a); [ auto | constructor; reflexivity ]
        end.
      + match goal with
        | |- Memory.store _ _ (word.add _ _) _ = Some _ => eassumption
        end.
      + match goal with
        | |- context[compile_post] => unfold compile_post
        end.
        match goal with
        | H: map.agree_on ?s ?l ?lL,
            H1: post ?t ?m' ?l ?mcH'
          |- exists lH' mcH',
            map.agree_on ?s lH' ?lL /\
              post ?t ?m' lH' mcH'
          => exists l; eexists; split; [ eapply H | eapply H1 ]
        end.
    - intros.
      simpl in *.
      repeat match goal with
      | |- context[if ?c then _ else _] => destr c; simpl in *
      end.
      +  match goal with
         | H: map.agree_on (of_list (if _ then _ else _)) _ _ |- _ =>
             apply agree_on_find in H; destr H
         end.
         eapply @exec.inlinetable; try solve [assumption].
         * match goal with
           | H: map.get ?l ?a = Some _,
            H1: map.agree_on (of_list [?a]) ?l ?lL|- map.get ?lL ?a = Some _ =>
            rewrite <- H1; [ eapply H | ]; cut (of_list [a] a); [ auto | constructor; reflexivity ]
           end.
         *  match goal with
        | |- Memory.load _ (OfListWord.map.of_list_word _) _ = Some _ => eassumption
            end.
         * match goal with
        | |- context[compile_post] => unfold compile_post
           end.
           listset_to_set.
           match goal with
           | H: map.agree_on
                  (diff (of_list ?used_after) (singleton_set ?x)) ?l ?lL,
            H1: post ?t ?m (map.put ?l ?x ?v) ?mcH'
          |- exists lH' mcH',
            map.agree_on (of_list ?used_after) lH' (map.put ?lL ?x ?v) /\
              post ?t ?m' lH' mcH'
          => exists (map.put l x v); eexists; split; [ eapply agree_on_diff_put; eapply H | eapply H1 ]
           end.
    + eapply @exec.skip.
        unfold compile_post.
        match goal with
        | H: post ?t ?m (map.put ?l ?x ?v) _,
            H2: map.agree_on (of_list ?used_after) ?l ?lL,
          H3: existsb (eqb ?x) ?used_after = false |-
            exists lH' mcH',
              map.agree_on (of_list ?used_after) lH' ?lL /\
                post ?t ?m lH' mcH' =>
            exists (map.put l x v); eexists; split; [ eapply agree_on_put_not_in; [ eapply H2 | eapply H3 ] | eapply H]
        end.
        - admit.
        - admit.
        - admit.
        - admit.
        - admit.
        - admit.
        - Search  SLoop. intros. unfold dce. simpl in *.
           8: {
           eapply agree_on
     eauto.

      c
            constructor.
        Search map.agree_on.
           exists ((map.put l x v)).
           eexists.
           split.
           2: { eapply H2. }
           eapply agree_on_put_not_in.
           + eassumption.
           + eassumption.
      intros.
      match goal with
      | H: map.agree_on (of_list (if _ then _ else _)) _ _ |- _ =>
          apply agree_on_find in H; destr H
      end.
      eapply @exec.load; fwd.
        match goal with
        | H: map.putmany_of_list_zip ?binds ?x1 ?l = Some ?x2,
            H1: map.agree_on _ l ?lL
          |- context[map.putmany_of_list_zip ?binds _ ?lL] =>
            let Heq := fresh in
            pose proof H as Heq; eapply putmany_Some in H; destr H; fwd
        end.
        match goal with
        | |- forall t' m' mc' st1,
            compile_post ?rets ?outcome t' m' st1 mc' -> _
          => unfold compile_post; intros; fwd
        end.


        erewrite agree_on_getmany; eassumption. match goal with
        | H: map.getmany_of_list ?l ?args = Some ?argvs
          |- map.getmany_of_list lL args = Some _ =>
            replace (map.getmany_of_list lL args)  with (map.getmany_of_list l args); [ eapply H | ]
        end.


        Search agree_on_getmany.
        apply agree_on_union in H4.
        Search agree_on_put.
        Search map.agree_on map.putmany_of_list_zip.




  Search map.putmany_of_list_zip.
  (* map.putmany_of_list_zip_sameLength *)
  Lemma putmany_of_list
    forall (lk: list string) lv (m: locals),
      (exists m', map.putmany_of_list_zip lk lv m = Some m'


        fwd. match goal with


        match goal with


          unfold compile_post.
        intros.
        eapply H3 in H5.
        destr H5.
        destr H5.
        eexists.
        split.




        eassumption.



          Search (EqDecider eqb).  eqb. unfold eqb. Search eqb.   eauto.
