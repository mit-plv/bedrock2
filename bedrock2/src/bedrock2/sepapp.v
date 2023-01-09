(* The seppapp operator: separating append, useful for contiguous memory regions *)
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import coqutil.Tactics.Tactics coqutil.Tactics.fwd.
Require Import coqutil.Byte.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.SepLib.

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

Section Reassociate_sepapp.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {word_ok: word.ok word}
    {mem: map.map word byte} {mem_ok: map.ok mem}.

  Lemma sep_assoc_eq: forall (p q r: mem -> Prop),
      sep (sep p q) r = sep p (sep q r).
  Proof.
    intros. eapply iff1ToEq. eapply sep_assoc.
  Qed.

  Lemma sepapp_assoc(P1 P2 P3: word -> mem -> Prop)
    {sz1: PredicateSize P1}{sz2: PredicateSize P2}:
    sepapp (sepapp P1 P2) P3 = sepapp P1 (sepapp P2 P3).
  Proof.
    unfold sepapp. extensionality addr.
    rewrite sep_assoc_eq. rewrite <- word.add_assoc, word.ring_morph_add.
    reflexivity.
  Qed.

  (* pair of a predicate and its size, used as tree leaves *)
  Inductive sized_predicate: Type :=
  | mk_sized_predicate(p: word -> mem -> Prop)(sz: PredicateSize p).

  Definition sized_emp := mk_sized_predicate (fun a => emp True) 0.

  Definition sepapp_sized_predicates(sp1 sp2: sized_predicate): sized_predicate :=
    match sp1, sp2 with
    | mk_sized_predicate p1 sz1, mk_sized_predicate p2 sz2 =>
        mk_sized_predicate (@sepapp _ _ _ mem p1 p2 sz1) (sz1 + sz2)
    end.

  Definition proj_sized_predicate(sp: sized_predicate): word -> mem -> Prop :=
    match sp with
    | mk_sized_predicate p _ => p
    end.

  Definition sepapps(l: list sized_predicate): word -> mem -> Prop :=
    proj_sized_predicate (List.fold_left sepapp_sized_predicates l sized_emp).

  Definition interp_sepapp_tree(t: Tree.Tree sized_predicate): word -> mem -> Prop :=
    proj_sized_predicate (Tree.interp id sepapp_sized_predicates t).

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
    unfold sepapps, interp_sepapp_tree, proj_sized_predicate.
    pose proof (flatten_eq_interp_sepapp_tree_aux t sized_emp) as P.
    unfold sized_emp in *. do 2 destruct_one_match. simpl in P. apply proj1 in P.
    subst. (* TODO *)
  Admitted.

  Lemma interp_sepapp_tree_eq_of_flatten_eq(LHS RHS : Tree.Tree sized_predicate):
    Tree.flatten LHS = Tree.flatten RHS ->
    interp_sepapp_tree LHS = interp_sepapp_tree RHS.
  Proof. intros. rewrite <-2flatten_eq_interp_sepapp_tree. f_equal. assumption. Qed.

End Reassociate_sepapp.
