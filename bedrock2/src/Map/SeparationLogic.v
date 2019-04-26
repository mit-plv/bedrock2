Require Import Coq.Classes.Morphisms.
Require Import bedrock2.Lift1Prop bedrock2.Map.Separation.
Require Coq.Lists.List.
Require Import coqutil.sanity coqutil.Map.Interface coqutil.Map.Properties.
Import Map.Interface.map Map.Properties.map.

Section SepProperties.
  Context {key value} {map : map key value} {ok : ok map}.
  Local Infix "*" := sep.

  Global Instance Proper_sep_iff1 : Proper (iff1 ==> iff1 ==> iff1) sep. firstorder idtac. Qed.
  Global Instance Proper_sep_impl1 : Proper (impl1 ==> impl1 ==> impl1) sep. firstorder idtac. Qed.

  Ltac t :=
    repeat match goal with
    | _ => progress subst
    | H:_ /\ _ |- _ => destruct H
    | H:exists _, _ |- _ => destruct H
    | H:disjoint (putmany _ _) _ |- _ => eapply disjoint_putmany_l in H; destruct H
    | H:disjoint _ (putmany _ _) |- _ => eapply disjoint_putmany_r in H; destruct H
    | _ => progress intuition idtac
    end.

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
  Lemma sep_get{keq: Decidable.DecidableEq key} k v m (H : get m k = Some v) :
    sep (ptsto k v) (eq (map.remove m k)) m.
  Proof.
    unfold sep. exists (map.put map.empty k v).
    eexists. repeat split.
    - apply map_ext. intros.
      rewrite get_putmany_dec.
      rewrite get_remove_dec.
      destruct (Decidable.dec (k = k0)).
      + subst. rewrite get_put_same. assumption.
      + rewrite get_put_diff by congruence. rewrite get_empty.
        destruct (get m k0); reflexivity.
    - unfold disjoint. intros.
      destruct (Decidable.dec (k = k0)).
      + subst. rewrite get_remove_same in H1. discriminate.
      + rewrite get_put_diff in H0 by congruence. rewrite get_empty in H0. discriminate.
  Qed.
  Lemma sep_put (key_eq_dec : forall k1 k2 : key, k1 = k2 \/ k1 <> k2)
        k v m v_old R (H : sep (ptsto k v_old) R m) : sep (ptsto k v) R (put m k v).
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

  Lemma sepeq_on_undef_put{keq: Decidable.DecidableEq key}: forall m addr b,
      map.get m addr = None ->
      (sep (ptsto addr b) (eq m)) (map.put m addr b).
  Proof.
    intros. unfold sep. exists (map.put map.empty addr b). exists m.
    split; [|split; reflexivity].
    apply map.split_undef_put. assumption.
  Qed.

  Lemma sep_on_undef_put{keq: Decidable.DecidableEq key}:
    forall m addr b (R: _ -> Prop),
      map.get m addr = None ->
      R m ->
      (sep (ptsto addr b) R) (map.put m addr b).
  Proof.
    intros. unfold sep. exists (map.put map.empty addr b). exists m.
    split; [|split; reflexivity || trivial].
    apply split_undef_put. assumption.
  Qed.

  Lemma iff1_sep_cancel P Q1 Q2 (H : iff1 Q1 Q2) : iff1 (P * Q1) (P * Q2).
  Proof. exact (Proper_sep_iff1 _ _ (reflexivity _) _ _ H). Qed.

  (* More Conntectives *)
  Global Instance Proper_emp_iff : Proper (iff ==> iff1) emp. firstorder idtac. Qed.
  Global Instance Proper_emp_impl : Proper (Basics.impl ==> impl1) emp. firstorder idtac. Qed.

  (* sep and emp *)
  Lemma sep_emp_emp p q : iff1 (sep (emp p) (emp q)) (emp (p /\ q)).
  Proof. cbv [iff1 sep emp split]; t; intuition eauto 20 using putmany_empty_l, disjoint_empty_l. Qed.
  Lemma sep_comm_emp_r a b : iff1 (a * emp b) (emp b * a). eapply sep_comm. Qed.
  Lemma sep_emp_2 a b c : iff1 (a * (emp b * c)) (emp b * (a * c)).
  Proof. rewrite <-sep_assoc. rewrite (sep_comm a). rewrite sep_assoc. reflexivity. Qed.
  Lemma sep_emp_12 a b c : iff1 (emp a * (emp b * c)) (emp (a /\ b) * c).
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
  Lemma impl1_l_sep_emp (a:Prop) b c : impl1 (emp a * b) c <-> (a -> impl1 b c).
  Proof. cbv [impl1 emp sep split]; t; rewrite ?putmany_empty_l; eauto 10 using putmany_empty_l, disjoint_empty_l. Qed.
  Lemma impl1_r_sep_emp a b c : (b /\ impl1 a c) -> impl1 a (emp b * c).
  Proof. cbv [impl1 emp sep split]; t; eauto 10 using putmany_empty_l, disjoint_empty_l. Qed.

  (* shallow reflection from a list of predicates *)
  Fixpoint seps' (xs : list (rep -> Prop)) : rep -> Prop :=
    match xs with
    | cons x xs => sep x (seps' xs)
    | nil => emp True
    end.
  Lemma seps'_iff1_seps xs : iff1 (seps' xs) (seps xs).
  Proof.
    induction xs; [exact (reflexivity _)|].
    destruct xs; [solve[eauto using sep_emp_True_r]|].
    eapply Proper_sep_iff1, IHxs.
    exact (reflexivity _).
  Qed.
  Lemma seps_cons(P: rep -> Prop)(Ps: list (rep -> Prop)):
    iff1 (seps (P :: Ps)) (sep P (seps Ps)).
  Proof. rewrite <-! seps'_iff1_seps. reflexivity. Qed.
  Lemma seps_app(Ps Qs: list (rep -> Prop)):
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
  Let nth n xs := hd (emp True) (skipn n xs).
  Let remove_nth n (xs : list (rep -> Prop)) :=
    (firstn n xs ++ tl (skipn n xs)).

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

  (* iff1 instead of eq as a hyp would be a more general lemma, but eq is more convenient to use *)
  Lemma cancel_seps_at_indices i j xs ys
        (Hij : nth i xs = nth j ys)
        (Hrest : iff1 (seps (remove_nth i xs)) (seps (remove_nth j ys)))
    : iff1 (seps xs) (seps ys).
  Proof.
    rewrite <-(seps_nth_to_head i xs), <-(seps_nth_to_head j ys), Hij, Hrest.
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

    Definition to_sep: Tree (map -> Prop) -> map -> Prop := interp id sep.

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

Ltac index_and_element_of xs :=
  multimatch xs with
  | cons ?x _ => constr:((0%nat, x))
  | cons _ ?xs =>
    let r := index_and_element_of xs in
    multimatch r with
    | (?i, ?y) => constr:((S i, y))
    end
  end.

Ltac find_syntactic_unify_deltavar xs y :=
  multimatch xs with
  | cons ?x _ =>
    let __ := match constr:(Set) with _ => syntactic_unify_deltavar x y end in
    constr:(O)
  | cons _ ?xs => let i := find_syntactic_unify_deltavar xs y in constr:(S i)
  end.

Ltac find_constr_eq xs y :=
  multimatch xs with
  | cons ?x _ => constr:(ltac:(constr_eq x y; exact 0%nat))
  | cons _ ?xs => let i := find_constr_eq xs y in constr:(S i)
  end.

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

(* leaves two open goals:
   1) equality between left sep clause #i and right sep clause #j
   2) updated main goal *)
Ltac cancel_seps_at_indices i j :=
  lazymatch goal with
  | |- Lift1Prop.iff1 (seps ?LHS) (seps ?RHS) =>
    simple refine (cancel_seps_at_indices i j LHS RHS _ _);
    cbn [firstn skipn app hd tl]
  end.

Ltac cancel_step :=
      let RHS := lazymatch goal with |- Lift1Prop.iff1 _ (seps ?RHS) => RHS end in
      let jy := index_and_element_of RHS in
      let j := lazymatch jy with (?i, _) => i end in
      let y := lazymatch jy with (_, ?y) => y end in
      assert_fails (has_evar y); (* <-- different from ecancel_step *)
      let LHS := lazymatch goal with |- Lift1Prop.iff1 (seps ?LHS) _ => LHS end in
      let i := find_constr_eq LHS y in (* <-- different from ecancel_step *)
      cancel_seps_at_indices i j; [syntactic_exact_deltavar (@eq_refl _ _)|].

Ltac ecancel_step :=
      let RHS := lazymatch goal with |- Lift1Prop.iff1 _ (seps ?RHS) => RHS end in
      let jy := index_and_element_of RHS in
      let j := lazymatch jy with (?i, _) => i end in
      let y := lazymatch jy with (_, ?y) => y end in
      assert_fails (idtac; let y := rdelta_var y in is_evar y);
      let LHS := lazymatch goal with |- Lift1Prop.iff1 (seps ?LHS) _ => LHS end in
      let i := find_syntactic_unify_deltavar LHS y in
      cancel_seps_at_indices i j; [syntactic_exact_deltavar (@eq_refl _ _)|].

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

Ltac cancel :=
  reify_goal;
  repeat cancel_step;
  repeat cancel_emp_l;
  repeat cancel_emp_r;
  try solve [ ecancel_done ].

Ltac ecancel :=
  cancel;
  repeat ecancel_step;
  solve [ ecancel_done ].

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
  let pf := fresh in
  (* COQBUG(faster use ltac:(...) here if that was multi-success *)
  eassert (@Lift1Prop.iff1 mem Psep (sep lemma_lhs _)) as pf
      by (ecancel || fail "failed to find" lemma_lhs "in" Psep "using ecancel");
  let H' := fresh H in (* rename H into H' (* COGBUG(9937) *) *)
  epose proof (proj1 (Proper_sep_iff1 _ _ Hrw _ _ (RelationClasses.reflexivity _) _) (proj1 (pf _) H)) as H';
  clear H pf.


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
