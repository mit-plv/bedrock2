Require Import lib.LibTactics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalFacts.
Require Import compiler.Axioms.
Require Import compiler.Common.
Require Import compiler.set_lemmas.
Require Import lib.fiat_crypto_tactics.Not.
Require Import lib.fiat_crypto_tactics.UniquePose.

Section StateCalculus.

  Context {var: Type}. (* variable name (key) *)
  Context {dec_eq_var: DecidableEq var}.
  Context {val: Type}. (* value *)
  Context {dec_eq_val: DecidableEq val}.
  Context {state: Type}.
  Context {stateMap: Map state var val}.

  (* models a set of vars *)
  Definition vars := var -> Prop.

  (* definitions which need to know that sets are modeled as functions and access elements
     (don't unfold) *)

  Definition dom(s: state): vars := fun x => get s x <> None.

  (* the domain on which s1 and s2 differ *)
  Definition domdiff(s1 s2: state): vars := fun x => get s1 x <> get s2 x.

  Definition is_empty(v: vars) := forall x, ~ x \in v.
  (*Definition is_empty(v: vars) := v = empty_set.*)

  Axiom excluded_middle: forall P, P \/ ~ P.
  Axiom proof_irrelev: forall (A : Prop) (a1 a2 : A), a1 = a2.

  Lemma is_empty_spec: forall v, is_empty v <-> v = empty_set.
  Proof.
    split; cbv in *; intros.
    - extensionality x. destruct (prop_degen (v x)).
      + exfalso. apply (H x). rewrite H0. constructor.
      + assumption.
    - rewrite H in H0. assumption.
  Qed.

  (* derived definitions *)

  Definition subset(vs1 vs2: vars) := is_empty (diff vs1 vs2).

  Definition extends(s1 s2: state) := is_empty (intersect (domdiff s1 s2) (dom s2)).

  Definition only_differ(s1: state)(vs: vars)(s2: state) :=
    subset (domdiff s1 s2) vs.

  Definition undef(s: state)(vs: vars) := is_empty (intersect (dom s) vs).

  Hint Unfold subset extends only_differ undef : unfold_state_calculus.

  Ltac unf := repeat autounfold with unfold00 unfold_state_calculus.

  Ltac unf1 := repeat autounfold with unfold_state_calculus.

  Ltac state_calc := repeat autounfold with unfold_state_calculus; firstorder.

  Axiom notnot: forall P, ~ ~ P -> P.

  Lemma domdiff_spec: forall s1 s2,
    subset (diff (union (dom s1) (dom s2)) (domdiff s1 s2)) (intersect (dom s1) (dom s2)).
  Proof.
    intros s1 s2.
    unfold subset, diff, intersect, Function_Set.
    unfold is_empty, empty_set. 
    intros x. intro H.
    unfold contains, Function_Set, id in H.
    destruct H as [[A B] C].
    unfold dom in *.
    unfold domdiff in *.
    apply notnot in B. (* <-- TODO can we do without this? *)
    simpl in A.
    rewrite <- B in *.
    apply C.
    split; destruct A; assumption.
  Qed.

  Lemma extends_refl: forall s, extends s s.
  Proof. state_calc. Qed.

(* should be part of typeclass (spec)
  Lemma in_union: forall x A B, x \in union A B <-> x \in A \/ x \in B.
  Proof. intros; split; cbv. unfold union.
*)

  Lemma only_differ_union_l: forall s1 s2 r1 r2,
    only_differ s1 r1 s2 ->
    only_differ s1 (union r1 r2) s2.
  Proof. state_calc. Qed.

  Lemma only_differ_union_r: forall s1 s2 r1 r2,
    only_differ s1 r2 s2 ->
    only_differ s1 (union r1 r2) s2.
  Proof. state_calc. Qed.

  Lemma domdiff_put_general: forall s1 s2 x v,
    domdiff s1 (put s2 x v) =
      union (domdiff s1 s2 ) (if dec (get s1 x = Some v) then empty_set else singleton_set x).
  Proof.
    cbv -[get put dec]. intros. destruct_one_match; extensionality y; apply prop_ext; split;
      (destruct (dec (x = y)); [subst; rewrite get_put_same | rewrite get_put_diff by assumption]).
  Abort.

  Lemma domdiff_put: forall s1 x v,
    domdiff s1 (put s1 x v) = if dec (get s1 x = Some v) then empty_set else singleton_set x.
  Proof.
    cbv -[get put dec]. intros. destruct_one_match; extensionality y; apply prop_ext; split;
      destruct (dec (x = y)); subst; try rewrite get_put_same; auto;
      rewrite get_put_diff by assumption; auto.
    intro H. exfalso. auto.
  Qed.

  (* TODO make this nicer *)
  Lemma only_differ_one: forall s x v,
    only_differ s (singleton_set x) (put s x v).
  Proof. unf1.
    intros.
    replace (domdiff s (put s x v))
       with (if dec (get s x = Some v) then empty_set else singleton_set x).
    - destruct_one_match; firstorder.
    - symmetry. apply domdiff_put. 
  Qed. (*
    cbv [only_differ vars_one]. intros. destruct (dec (x = x0)); [ auto | ].
    right. symmetry. apply get_put_diff. assumption.
  Qed.*)

  Lemma only_differ_refl: forall s1 r,
    only_differ s1 r s1.
  Proof. state_calc. Qed.

  Lemma only_differ_sym: forall s1 s2 r,
    only_differ s1 r s2 ->
    only_differ s2 r s1.
  Proof. state_calc. Qed.

  Lemma elim_impl: forall P Q,
    ~ P \/ Q -> P -> Q.
  Proof. firstorder. Qed.
  Lemma elim_impl2: forall P Q R,
    ~ P \/ ~ Q \/ R -> P -> Q -> R.
  Proof. firstorder. Qed.

(*
  Lemma not_forall: forall {T: Type} (x: T) (P: T -> Prop),
    (~ forall x, ~ P x) <-> exists x, P x.
  Proof. split. *)
  Lemma non_empty_classical: forall v,
    ~ is_empty v <-> exists x, x \in v. Admitted.

  Lemma nonempty_or: forall v1 v2,
    (~ is_empty v1) \/ (~ is_empty v2) <-> ~ is_empty (union v1 v2).
  Proof.
    split; [cbv|]; intros.
    - destruct H.
      + apply H. intros. eapply H0. eauto.
      + apply H. intros. eapply H0. eauto.
    - rewrite! non_empty_classical in *. destruct H as [x H]. cbv in H.
      destruct H; eauto.
  Qed.

(*  Lemma non_empty_complement: forall v,
    (~ is_empty v) *)

  Lemma only_differ_trans: forall s1 s2 s3 r,
    only_differ s1 r s2 ->
    only_differ s2 r s3 ->
    only_differ s1 r s3.
  Proof.
    unf1. intros s1 s2 s3 r. apply elim_impl2.
    match goal with |- ?P \/ ?Q \/ ?R => cut ((P \/ Q) \/ R); [tauto|] end.
    rewrite nonempty_or.
  Abort. (*
    unfold only_differ. introv E1 E2. intro x.
    specialize (E1 x). specialize (E2 x).
    destruct E1; [auto|]. destruct E2; [auto|]. right. congruence.
  Qed.*)

  Lemma undef_shrink: forall st vs1 vs2,
    undef st vs1 ->
    subset vs2 vs1 ->
    undef st vs2.
  Proof. unfold undef, subset. firstorder. Qed.

  Lemma only_differ_subset: forall s1 s2 r1 r2,
    subset r1 r2 ->
    only_differ s1 r1 s2 ->
    only_differ s1 r2 s2.
  Proof.
    unfold subset, only_differ. intros. firstorder.
  Qed.

  Axiom not_forall: forall (T: Type) (P: T -> Prop),
    (~ forall x, P x) <-> (exists x, ~ P x).

  Axiom not_exists: forall (T: Type) (P: T -> Prop),
    (~ exists x, P x) <-> (forall x, ~ P x).

  Lemma neq_sym: forall (T: Type) (a b: T), a <> b -> b <> a.
  Proof. clear. firstorder. Qed.

  Lemma get_elem_from_nonempty: forall (vs: vars), vs <> empty_set -> exists x, x \in vs.
  Proof.
    intros. rewrite <- is_empty_spec in H. unfold is_empty in H. rewrite not_forall in H.
    destruct H as [x H]. exists x. apply notnot. assumption.
  Qed.

  Lemma get_elem_from_nonempty': forall (vs: vars), empty_set <> vs -> exists x, x \in vs.
  Proof. intros. apply neq_sym in H. apply get_elem_from_nonempty. assumption. Qed.

  Lemma demorgan1: forall P Q, ~ (P \/ Q) <-> ~P /\ ~Q.
  Proof.
    split; intros.
    - destruct (excluded_middle P) as [p|p];
      destruct (excluded_middle Q) as [q|q];
      try (assert (P \/ Q) by auto; contradiction); auto.
    - destruct H. intro E. destruct E as [p|q]; contradiction.
  Qed.

  Lemma demorgan2: forall P Q, ~ (P /\ Q) <-> ~P \/ ~Q.
  Proof.
    split; intros.
    - destruct (excluded_middle P) as [p|p];
      destruct (excluded_middle Q) as [q|q];
      try (assert (P \/ Q) by auto; contradiction); auto.
    - destruct H; intro E; destruct E as [p q]; contradiction.
  Qed.

  (* generalization: *)
  Lemma get_neq_witness: forall (vs1 vs2: vars),
    vs1 <> vs2 ->
    (exists x, x \in vs1 /\ ~ x \in vs2) \/ (exists x, ~ x \in vs1 /\ x \in vs2).
  Proof.
    intros.
    match goal with
    | |- ?P1 \/ ?P2 => destruct (excluded_middle P1) as [p1|np1];
                       destruct (excluded_middle P2) as [p2|np2]
    end;
    auto.
    exfalso. apply H. extensionality x.
    rewrite not_exists in np1. rewrite not_exists in np2.
    cbv -[not] in np1, np2.
    specialize (np1 x). specialize (np2 x).
    rewrite demorgan2 in np1. rewrite demorgan2 in np2.
    destruct np1 as [np1 | np1]; destruct np2 as [np2 | np2].
    - contradiction.
    - destruct (prop_degen (vs1 x)) as [E1 | E1]; rewrite E1 in *; [contradiction|].
      destruct (prop_degen (vs2 x)) as [E2 | E2]; rewrite E2 in *; [contradiction|].
      reflexivity.
    - apply notnot in np1. apply notnot in np2.
      destruct (prop_degen (vs1 x)) as [E1 | E1]; rewrite E1 in *; [|contradiction].
      destruct (prop_degen (vs2 x)) as [E2 | E2]; rewrite E2 in *; [|contradiction].
      reflexivity.
    - contradiction.
  Qed.

Ltac ensure_literal P :=
  match type of P with
  | _ = _ => idtac
  | _ <> _ => idtac
  | _ \in _ => idtac
  | ~ _ \in _ => idtac
  end.

Ltac saturate_equalities :=
  repeat match goal with
  | E: ?t1 = ?t2 |- _ =>
    match goal with
    (* called "literal" *)
    | L: _ |- _ =>
      let tE := type of E in
      let tL := type of L in
      not (unify tE tL);
      ensure_literal L;
      let H' := fresh in
      match tL with
      | context C[t1] => let G := context C[t2] in
          assert G as H' by (rewrite E; assumption)
      | context C[t2] => let G := context C[t1] in
          assert G as H' by (rewrite E; assumption)
      end;
      ensure_new H'
    end
  end.
  (* TODO 3rd rule *)


Ltac saturate_union_intersect_diff_contains :=
  repeat match goal with
  | H: _ |- _ => unique pose proof (in_intersect_l _ _ _ H)
  | H: _ |- _ => unique pose proof (in_intersect_r _ _ _ H)
  | H: ~ ?s \in ?t1 |- _ => match goal with
    | _: context [intersect t1 ?t2] |- _ => unique pose proof (notin_intersect_l _ _ _ H)
    end
  | H: ~ ?s \in ?t2 |- _ => match goal with
    | _: context [intersect ?t1 t2] |- _ => unique pose proof (notin_intersect_r _ _ _ H)
    end
  | H1: ~ ?s \in (intersect ?t1 ?t2), H2: ?s \in ?t1 |- _ =>
     unique pose proof (notin_intersect_other_l _ _ _ H1 H2)
  | H1: ~ ?s \in (intersect ?t1 ?t2), H2: ?s \in ?t1 |- _ =>
     unique pose proof (notin_intersect_other_r _ _ _ H1 H2)
  | H1: ?s \in ?t1, H2: ?s \in ?t2 |- _ => match goal with
    | _: context [intersect t1 t2] |- _ => unique pose proof (in_intersect _ _ _ H1 H2)
    end
  | H: _ |- _ => unique pose proof (notin_union_l _ _ _ H)
  | H: _ |- _ => unique pose proof (notin_union_r _ _ _ H)
  | H: ?s \in ?t1 |- _ => match goal with
    | _: context [union t1 ?t2] |- _ => unique pose proof (in_union_l _ _ _ H)
    end
  | H: ?s \in ?t2 |- _ => match goal with
    | _: context [union ?t1 t2] |- _ => unique pose proof (in_union_r _ _ _ H)
    end
  | H1: ?s \in (union ?t1 ?t2), H2: ~ ?s \in ?t1 |- _ =>
      unique pose proof (in_union_other_l _ _ _ H1 H2)
  | H1: ?s \in (union ?t1 ?t2), H2: ~ ?s \in ?t2 |- _ =>
      unique pose proof (in_union_other_r _ _ _ H1 H2)
  | H1: ~ ?s \in ?t1, H2: ~ ?s \in ?t2 |- _ => match goal with
    | _: context [union t1 t2] |- _ => unique pose proof (notin_union _ _ _ H1 H2)
    end
  | H: _ |- _ => unique pose proof (invert_in_diff_l _ _ _ H)
  | H: _ |- _ => unique pose proof (invert_in_diff_r _ _ _ H)
  | H: ~ ?s \in ?t1 |- _ => match goal with
    | _: context [diff t1 ?t2] |- _ => unique pose proof (notin_diff_l _ _ _ H)
    end
  | H: ?s \in ?t2 |- _ => match goal with
    | _: context [diff ?t1 t2] |- _ => unique pose proof (notin_diff_r _ _ _ H)
    end
  | H1: ~ ?s \in (diff ?t1 ?t2), H2: ?s \in ?t1 |- _ =>
      unique pose proof (notin_diff_other_l _ _ _ H1 H2)
  | H1: ~ ?s \in (diff ?t1 ?t2), H2: ~ ?s \in ?t2 |- _ =>
      unique pose proof (notin_diff_other_r _ _ _ H1 H2)
  | H1: ?s \in ?t1, H2: ~ ?s \in ?t2 |- _ => match goal with
    | _: context [diff t1 t2] |- _ => unique pose proof (in_diff _ _ _ H1 H2)
    end
  end.

(* bad: if applied again later, it will redo the same with a different new var *)
Ltac fulfill_nonempty_linear_bad :=
  repeat match goal with
  | H: ?t <> empty_set |- _ => (* TODO also treat "empty_set <> ?t" *)
      let H' := fresh in pose proof (get_elem_from_nonempty _ H) as H'; ensure_new H'
  end;
  repeat match goal with
  | H: exists x, _ |- _ => destruct H
  end.

Ltac fulfill_nonempty_linear :=
  repeat match goal with
  | H: ?t <> empty_set |- _ => match goal with
    | _: ?x \in t |- _ => fail 1
    | _ => destruct (get_elem_from_nonempty _ H) as [? ?]
    end
  | H: empty_set <> ?t |- _ => match goal with
    | _: ?x \in t |- _ => fail 1
    | _ => destruct (get_elem_from_nonempty' _ H) as [? ?]
    end
  end.

Ltac fulfill :=
  match goal with
  | H1: ?s \in (union ?t1 ?t2) |- _ => match goal with
    | _: s \in t1 |- _ => fail 1
    | _: ~ s \in t1 |- _ => fail 1
    | _ => destruct (excluded_middle (s \in t1))
    end
  | H1: ?s \in (union ?t1 ?t2) |- _ => match goal with
    | _: s \in t2 |- _ => fail 1
    | _: ~ s \in t2 |- _ => fail 1
    | _ => destruct (excluded_middle (s \in t2))
    end
  | H1: ?s \in ?t1, H2: context [intersect ?t1 ?t2] |- _ => match goal with
    | _: s \in t2 |- _ => fail 1
    | _: ~ s \in t2 |- _ => fail 1
    | _ => destruct (excluded_middle (s \in t2))
    end
  | H1: ?s \in ?t2, H2: context [intersect ?t1 ?t2] |- _ => match goal with
    | _: s \in t1 |- _ => fail 1
    | _: ~ s \in t1 |- _ => fail 1
    | _ => destruct (excluded_middle (s \in t1))
    end
  | H1: ?s \in ?t1, H2: context [diff ?t1 ?t2] |- _ => match goal with
    | _: s \in t2 |- _ => fail 1
    | _: ~ s \in t2 |- _ => fail 1
    | _ => destruct (excluded_middle (s \in t2))
    end
  (* TODO why does it say precondition t1,t2 in T_phi, isn't this always true?
     Probably just for consistency with the other rules where the precondition is
     sometimes needed to make sure we don't make up an aribtrary t2 *)
  | IE: ?t1 <> ?t2 |- _ => match goal with
    | _:   ?x \in t1, _: ~ ?x \in t2 |- _ => fail 1
    | _: ~ ?x \in t1, _:   ?x \in t2 |- _ => fail 1
    | _ => (* if one of t1,t2 is empty set, it should rather be treated fulfill_nonempty_linear *)
           match t1 with
           | empty_set => fail 1
           | _ => idtac
           end;
           match t2 with
           | empty_set => fail 1
           | _ => idtac
           end;
           destruct (get_neq_witness _ _ IE) as [[? [? ?]] | [? [? ?]]]
    end
  (* TODO more rules *)
  end.

(*
A branch is closed if one of these holds:
a) it has ~P and P
b) it has a membership cycle
c) it has t1 <> t1
d) it has x \in empty_set
Coq's typesystem excludes b), and "contradiction" solves a) and c), and if the definition of
sets is transparent, it also solves d), so "contradiction" is enough to check if a branch is closed
*)
Ltac close_branch := contradiction.

Goal forall (x: var), False. intro.
assert (x \in empty_set) by admit. simpl in H. cbv in H. contradiction.

  Lemma extends_if_only_differ_in_undef: forall s1 s2 s vs,
    extends s1 s ->
    undef s vs ->
    only_differ s1 vs s2 ->
    extends s2 s.
  Proof.
    unfold extends, undef, only_differ.
    introv E U O.
    pose proof (domdiff_spec s1 s) as P1.
    pose proof (domdiff_spec s1 s2) as P12.
    pose proof (domdiff_spec s2 s) as P2.
    remember (domdiff s1 s) as Ds1s.
    remember (domdiff s2 s) as Ds2s.
    remember (domdiff s1 s2) as Ds1s2.
    remember (dom s1) as A1.
    remember (dom s2) as A2.
    remember (dom s) as A.
    (*clear - E U O P1 P12 P2 dec_eq_var dec_eq_val val.*)
    unfold subset in *.
    rewrite is_empty_spec in *.
    (* start proof by contradiction *)
    apply notnot. intro H.

    saturate_equalities.
    fulfill_nonempty_linear.
    saturate_union_intersect_diff_contains.
    close_branch || fulfill.
    {
    repeat (saturate_equalities; fulfill_nonempty_linear; saturate_union_intersect_diff_contains).
    close_branch || fulfill.
    }
    {
    repeat (saturate_equalities; fulfill_nonempty_linear; saturate_union_intersect_diff_contains).
    close_branch || fulfill.
    {
    repeat (saturate_equalities; fulfill_nonempty_linear; saturate_union_intersect_diff_contains).
    close_branch || fulfill.
    {
    repeat (saturate_equalities; fulfill_nonempty_linear; saturate_union_intersect_diff_contains).
    close_branch || fulfill.
    {
    repeat (saturate_equalities; fulfill_nonempty_linear; saturate_union_intersect_diff_contains).
    close_branch || fulfill.
    }
    {
    repeat (saturate_equalities; fulfill_nonempty_linear; saturate_union_intersect_diff_contains).
    close_branch || fulfill.
    {
    repeat (saturate_equalities; fulfill_nonempty_linear; saturate_union_intersect_diff_contains).
    close_branch || fulfill.
    {
    repeat (saturate_equalities; fulfill_nonempty_linear; saturate_union_intersect_diff_contains).
    close_branch || fulfill.
    {
    repeat (saturate_equalities; fulfill_nonempty_linear; saturate_union_intersect_diff_contains).
    close_branch || fulfill.
    {
    repeat (saturate_equalities; fulfill_nonempty_linear; saturate_union_intersect_diff_contains).
    close_branch || fulfill.
    }
    {
    repeat (saturate_equalities; fulfill_nonempty_linear; saturate_union_intersect_diff_contains).
    close_branch || fulfill. (* fails, why? *)


match goal with
| H1: ?P, H2: ~?P |- _ => idtac H1 H2
end.
contradiction.
assert (x \in empty_set).
    fulfill.
    {
    repeat (saturate_equalities; fulfill_nonempty_linear; saturate_union_intersect_diff_contains).
    fulfill.
    {
    repeat (saturate_equalities; fulfill_nonempty_linear; saturate_union_intersect_diff_contains).
    fulfill.

  Fail match goal with
  | H2: context [diff ?t1 ?t2] |- _ => idtac t1; fail
  end. 

  match goal with
  | H1: ?s \in ?t1 |- _ => idtac H1 t1; fail
  end. 


  match goal with
  | H1: ?s \in ?t1, H2: context [diff ?t1 ?t2] |- _ => idtac
  end. 

  match goal with
  | H1: ?s \in ?t1, H2: context [diff ?t1 ?t2] |- _ => idtac "try" H1 H2; match goal with
    | F: s \in t2 |- _ => idtac "no because of" F; fail 1
    | F: ~ s \in t2 |- _ => idtac "no because of" F; fail 1
    | _ => destruct (excluded_middle (s \in t2))
    end
  end.   
    fulfill. (* TODO fulfill fails because its rules are not yet all implemented. *)
(* fulfill-debug code: *)
     match goal with
  (* TODO why does it say precondition t1,t2 in T_phi, isn't this always true? *)
  | IE: ?t1 <> ?t2 |- _ => idtac IE; let m := type of IE in idtac m; match goal with
    | F1:   ?x \in t1, F2: ~ ?x \in t2 |- _ => idtac "ff>"; idtac F1; idtac F2; idtac "<ff"; fail 1
    | F1: ~ ?x \in t1, F2:   ?x \in t2 |- _ => idtac "ff>"; idtac F1; idtac F2; idtac "<ff"; fail 1
    | _ => (* if one of t1,t2 is empty set, it should rather be treated fulfill_nonempty_linear *)
           idtac "hh2";
           match t1 with
           | empty_set => fail 1
           | _ => idtac
           end;
           idtac "hh3";
           match t2 with
           | empty_set => fail 1
           | _ => idtac
           end;
           idtac "hh4";
           destruct (get_neq_witness _ _ IE) as [[? [? ?]] | [? [? ?]]]
    end
  (* TODO more rules *)
  end.
    fulfill.
    saturate_equalities.
    fulfill_nonempty_linear.
    saturate_union_intersect_diff_contains.


    
    
    specialize (O x). destruct O as [O | O].
    - specialize (U _ O). congruence. (* contradiction *)
    - rewrite <- O. apply E. assumption.
  Qed.

  Lemma extends_if_only_differ_is_undef: forall s1 s2 vs,
    undef s1 vs ->
    only_differ s1 vs s2 ->
    extends s2 s1.
  Proof.
    intros. eapply extends_if_only_differ_in_undef; [eapply extends_refl | eassumption..].
  Qed.

  Lemma extends_put_same: forall s1 s2 x v,
    extends s2 s1 ->
    extends (put s2 x v) (put s1 x v).
  Proof.
    unfold extends. introv E G.
    destruct (dec (x = x0)).
    - subst x0. rewrite get_put_same in G. inversion G. subst v0; clear G.
      apply get_put_same.
    - rewrite get_put_diff by assumption.
      rewrite get_put_diff in G by assumption. auto.
  Qed.

  Lemma only_differ_get_unchanged: forall s1 s2 x v d,
    get s1 x = v ->
    only_differ s1 d s2 ->
    ~ x \in d ->
    get s2 x = v.
  Proof.
    introv G D N.
    unfold only_differ in D. destruct (D x); congruence.
  Qed.

  Lemma only_differ_put: forall s (d: vars) x v,
    x \in d ->
    only_differ s d (put s x v).
  Proof.
    unfold only_differ. intros.
    destruct (dec (x = x0)).
    - subst x0. left. assumption.
    - right. rewrite get_put_diff; auto.
  Qed.

End StateCalculus.
