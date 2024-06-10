(* The seppapp operator: separating append, useful for contiguous memory regions *)
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import coqutil.Tactics.Tactics coqutil.Tactics.fwd.
Require Import coqutil.Byte.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.is_emp.
Require Import bedrock2.SepLib.
Require Import bedrock2.PurifySep.

Definition sepapp{width: Z}{BW: Bitwidth width}{word: word.word width}
  {mem: map.map word Byte.byte}
  (P1 P2: word -> mem -> Prop){P1size: PredicateSize P1}: word -> mem -> Prop :=
  fun addr => sep (P1 addr) (P2 (word.add addr (word.of_Z P1size))).

Declare Scope sepapp_scope. Local Open Scope sepapp_scope.
Infix "*+" := sepapp (at level 36, left associativity) : sepapp_scope.

#[export] Hint Extern 1 (PredicateSize (sepapp ?P1 ?P2)) =>
  lazymatch constr:(_: PredicateSize P1) with
  | ?sz1 => lazymatch constr:(_: PredicateSize P2) with
            | ?sz2 => exact (Z.add sz1 sz2)
            end
  end
: typeclass_instances.

(* Placeholder for use with sepapp.
   After removing one clause out of a series of sepapps, we get
   (stuffBefore start_addr * stuffAfter (start_addr + size_of_stuffBefore + size_of_hole))
   Using `hole`, we can write it more concisely:
   (stuffBefore *+ hole size_of_hole *+ stuffAfter) start_addr *)
Definition hole{key value}{mem: map.map key value}(n: Z)(addr: key): mem -> Prop :=
  emp True.
#[export] Hint Extern 1 (PredicateSize (hole ?n)) => exact n : typeclass_instances.
#[export] Hint Opaque hole : typeclass_instances.

Definition emp_at_addr{key value}{mem: map.map key value}
  (P: Prop)(ignored_addr: key): mem -> Prop := emp P.
#[export] Hint Extern 1 (PredicateSize (emp_at_addr _)) => exact 0 : typeclass_instances.

(* pair of a predicate and its size, used as tree leaves *)
Inductive sized_predicate{width: Z}{BW: Bitwidth width}{word: word.word width}
  {mem: map.map word Byte.byte}: Type :=
| mk_sized_predicate(p: word -> mem -> Prop)(sz: Z).

(* We could also mark the sz argument of mk_sized_predicate as having type (PredicateSize p),
   but then mk_sized_predicate looks more dependently-typed than it actually is, and
   rewriting in its p argument leads to typing problems (eg in using f_equal in
   bottom_up_simpl). *)
Notation mk_inferred_size_predicate p := (mk_sized_predicate p (sizeof p%function)).

Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {word_ok: word.ok word}
    {mem: map.map word byte} {mem_ok: map.ok mem}.

  Import List.ListNotations. Local Open Scope list_scope.

  Goal True.
    pose (mk_inferred_size_predicate (uint 32 42)) as p.
    lazymatch goal with
    | _ := mk_sized_predicate _ 4 |- _ => idtac
    end.
  Abort.

  Lemma sepapp_assoc(P1 P2 P3: word -> mem -> Prop)
    {sz1: PredicateSize P1}{sz2: PredicateSize P2}:
    sepapp (sepapp P1 P2) P3 = sepapp P1 (sepapp P2 P3).
  Proof.
    unfold sepapp. extensionality addr.
    rewrite sep_assoc_eq. rewrite <- word.add_assoc, word.ring_morph_add.
    reflexivity.
  Qed.

  Definition sized_emp := mk_sized_predicate (fun a => emp True) 0.

  Definition sepapp_sized_predicates(sp1 sp2: sized_predicate): sized_predicate :=
    match sp1, sp2 with
    | mk_sized_predicate p1 sz1, mk_sized_predicate p2 sz2 =>
        mk_sized_predicate (@sepapp _ _ _ mem p1 p2 sz1) (sz1 + sz2)
    end.

  Definition proj_predicate(sp: sized_predicate): word -> mem -> Prop :=
    match sp with
    | mk_sized_predicate p _ => p
    end.

  Definition proj_size(sp: sized_predicate): Z :=
    match sp with
    | mk_sized_predicate _ sz => sz
    end.

  Definition sepapps(l: list sized_predicate): word -> mem -> Prop :=
    proj_predicate (List.fold_right sepapp_sized_predicates sized_emp l).

  Lemma purify_sepapp: forall a p1 P1 {sz: PredicateSize p1} p2 P2,
      purify (p1 a) P1 ->
      purify (p2 (word.add a (word.of_Z sz))) P2 ->
      purify (sepapp p1 p2 a) (P1 /\ P2).
  Proof. unfold sepapp. intros. eapply purify_sep; assumption. Qed.

  Lemma purify_sepapps_nil: forall a, purify (sepapps nil a) True.
  Proof. unfold purify. intros. constructor. Qed.

  Lemma purify_sepapps_cons: forall p P Q sz l a,
      purify (p a) P ->
      purify (sepapps l (word.add a (word.of_Z sz))) Q ->
      purify (sepapps (cons (mk_sized_predicate p sz) l) a) (P /\ Q).
  Proof.
    unfold purify. intros. unfold sepapps in H1. simpl in H1.
    destruct_one_match_hyp. simpl in H1. unfold sepapp, sep in H1.
    fwd. split.
    - eapply H. eassumption.
    - eapply H0. unfold sepapps. rewrite E. simpl. eassumption.
  Qed.

  Definition sepapps_size(l: list sized_predicate): Z :=
    List.fold_right Z.add 0 (List.map proj_size l).

  Lemma sepapps_nil: forall a, sepapps nil a = emp True.
  Proof. intros. reflexivity. Qed.

  Lemma sepapps_cons: forall p l a,
      sepapps (cons p l) a = sep (proj_predicate p a)
                                 (sepapps l (word.add a (word.of_Z (proj_size p)))).
  Proof.
    intros. unfold sepapps. destruct p as [P sz]. simpl.
    destruct (List.fold_right sepapp_sized_predicates sized_emp l). simpl.
    unfold sepapp. reflexivity.
  Qed.

  Lemma sepapps_app: forall l1 l2 a,
      sepapps (l1 ++ l2) a = sep (sepapps l1 a)
                                 (sepapps l2 (word.add a (word.of_Z (sepapps_size l1)))).
  Proof.
    induction l1; intros; simpl.
    - rewrite sepapps_nil. eapply iff1ToEq. rewrite sep_emp_True_l.
      change (sepapps_size nil) with 0. rewrite word.add_0_r. reflexivity.
    - rewrite 2sepapps_cons. rewrite IHl1.
      rewrite sep_assoc_eq.
      f_equal. f_equal. f_equal.
      change (sepapps_size (a :: l1)) with (proj_size a + sepapps_size l1).
      rewrite word.ring_morph_add.
      symmetry. apply word.add_assoc.
  Qed.

  Lemma expose_nth_sepapp: forall l n a P sz,
      List.nth_error l n = Some (mk_sized_predicate P sz) ->
      sepapps l a = sep (P (word.add a (word.of_Z (sepapps_size (List.firstn n l)))))
                        (sepapps (List.firstn n l ++
                                  cons (mk_sized_predicate (hole sz) sz)
                                  (List.skipn (S n) l)) a).
  Proof.
    intros. rewrite (List.nth_error_expose _ _ _ H) at 1.
    rewrite ?sepapps_app, ?sepapps_cons. eapply iff1ToEq.
    cbn [proj_predicate proj_size]. unfold hole. cancel.
  Qed.

  Lemma merge_back_nth_sepapp: forall l n a P sz,
      List.nth_error l n = Some (mk_sized_predicate (hole sz) sz) ->
      sep (P (word.add a (word.of_Z (sepapps_size (List.firstn n l))))) (sepapps l a) =
        (sepapps (List.firstn n l ++ cons (mk_sized_predicate P sz) (List.skipn (S n) l)) a).
  Proof.
    intros. rewrite (List.nth_error_expose _ _ _ H) at 2.
    rewrite ?sepapps_app, ?sepapps_cons. eapply iff1ToEq.
    cbn [proj_predicate proj_size]. unfold hole. cancel.
  Qed.

(* Not sure if needed at all
  Definition interp_sepapp_tree(t: Tree.Tree sized_predicate): word -> mem -> Prop :=
    proj_predicate (Tree.interp id sepapp_sized_predicates t).

  Lemma flatten_eq_interp_sepapp_tree_aux(t: Tree.Tree sized_predicate):
    forall sp0: sized_predicate,
      match List.fold_left sepapp_sized_predicates (Tree.flatten t) sp0,
        sepapp_sized_predicates sp0 (Tree.interp id sepapp_sized_predicates t) with
      | mk_sized_predicate p1 sz1, mk_sized_predicate p2 sz2 =>
          p1 = p2 /\ sz1 = sz2
      end.
  Proof.
    induction t; intros.
    - simpl. destruct sp0. destruct a. simpl. auto.
    - simpl. change @app with @List.app.
      rewrite List.fold_left_app.
      specialize (IHt1 sp0).
      specialize (IHt2 (List.fold_left sepapp_sized_predicates (Tree.flatten t1) sp0)).
      destruct_one_match.
      destr sp0.
      destr (List.fold_left sepapp_sized_predicates (Tree.flatten t1)
               (mk_sized_predicate p0 sz0)).
      destr (Tree.interp id sepapp_sized_predicates t1).
      destr (Tree.interp id sepapp_sized_predicates t2).
      simpl in *.
      fwd. subst. rewrite <- sepapp_assoc. rewrite Z.add_assoc. split; reflexivity.
  Qed.

  Lemma flatten_eq_interp_sepapp_tree(t : Tree.Tree sized_predicate):
    sepapps (Tree.flatten t) = interp_sepapp_tree t.
  Proof.
    unfold sepapps, interp_sepapp_tree, proj_predicate.
    pose proof (flatten_eq_interp_sepapp_tree_aux t sized_emp) as P.
    unfold sized_emp in *. do 2 destruct_one_match. simpl in P. apply proj1 in P.
    subst.
    extensionality a. unfold sepapp. eapply iff1ToEq.
    rewrite word.add_0_r. eapply sep_emp_True_l.
  Qed.

  Lemma interp_sepapp_tree_eq_of_flatten_eq(LHS RHS : Tree.Tree sized_predicate):
    Tree.flatten LHS = Tree.flatten RHS ->
    interp_sepapp_tree LHS = interp_sepapp_tree RHS.
  Proof. intros. rewrite <-2flatten_eq_interp_sepapp_tree. f_equal. assumption. Qed.
*)

  Lemma sepapps_is_emp: forall l a,
      List.map (fun '(mk_sized_predicate _ sz) => mk_sized_predicate (hole sz) sz) l = l ->
      is_emp (sepapps l a) True.
  Proof.
    induction l; cbn; intros.
    - unfold is_emp. reflexivity.
    - rewrite sepapps_cons. destruct a. simpl.
      fwd. specialize IHl with (1 := H0).
      eapply weaken_is_emp; cycle 1.
      + eapply sep_is_emp.
        * unfold hole, is_emp. reflexivity.
        * apply IHl.
      + auto.
  Qed.

End WithParams.

#[export] Hint Resolve purify_sepapp: purify.
#[export] Hint Resolve purify_sepapps_nil: purify.
#[export] Hint Resolve purify_sepapps_cons: purify.

Ltac is_ground_Z x :=
  lazymatch x with
  | ?op ?a ?b =>
      lazymatch (lazymatch op with
                 | Z.add => constr:(true)
                 | Z.mul => constr:(true)
                 | _ => constr:(false)
                 end) with
      | true => lazymatch is_ground_Z a with
                | true => lazymatch is_ground_Z b with
                          | true => constr:(true)
                          | false => constr:(false)
                          end
                | false => constr:(false)
                end
      | false => constr:(false)
      end
  | _ => isZcst x
  end.

Ltac sized_predicate_list_size l :=
  lazymatch l with
  | cons (mk_sized_predicate _ ?sz) nil => sz
  | cons (mk_sized_predicate _ ?sz) ?rest =>
      let sz' := sized_predicate_list_size rest in
      constr:(Z.add sz sz')
  | nil => Z0
  end.

(* Often, only the last field of a record is of variable size,
   so computing the size left-associatively and adding up all
   the constant sizes can simplify the expressions *)
Ltac sepapps_size_with_ground_acc acc l :=
  lazymatch l with
  | cons (mk_sized_predicate _ ?sz) ?rest =>
      lazymatch is_ground_Z sz with
      | true => let acc' := eval cbv in (Z.add acc sz) in
                  sepapps_size_with_ground_acc acc' rest
      | false => lazymatch sized_predicate_list_size rest with
                 | Z0 => constr:(Z.add acc sz)
                 | ?sz' => constr:(Z.add acc (Z.add sz sz'))
                 end
      end
  | nil => acc
  end.

#[export] Hint Extern 1 (PredicateSize (sepapps ?l)) =>
  let sz := sepapps_size_with_ground_acc Z0 l in exact sz
: typeclass_instances.

Ltac only_holes l :=
  lazymatch l with
  | cons (mk_sized_predicate (hole _) _) ?rest => only_holes rest
  | nil => idtac
  end.

#[export] Hint Extern 10 (is_emp (sepapps ?l _) _) =>
    only_holes l;
    eapply sepapps_is_emp;
    reflexivity
: is_emp.
