From coqutil Require Import
     Decidable Map.Interface.
From bedrock2 Require Import
     Lift1Prop Map.Separation.
From Coq Require Import
     Classes.Morphisms List.
From Rupicola Require Import Core.

Import ListNotations.
Open Scope list_scope.

Module SepRefl.
Section Reflection.
  Context {key value} {map : map.map key value} {map_ok : map.ok map}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.

  Notation unseps := (unseps (map := map)).

  Inductive expr :=
    | Pred (p: map -> Prop)
    | Sep (s1 s2: expr)
    | Unsep (s1 s2: expr).

  Fixpoint denote (e: expr) : map -> Prop :=
    match e with
    | Pred p => p
    | Sep s1 s2 => sep (denote s1) (denote s2)
    | Unsep s1 s2 => unsep (denote s1) (denote s2)
    end.

  Fixpoint unsep_normal_form' (e: expr) : list expr :=
    match e with
    | Pred p => [Pred p]
    | Sep s1 s2 =>
      map2 Sep (product (unsep_normal_form' s1)
                        (unsep_normal_form' s2))
    | Unsep s1 s2 =>
      unsep_normal_form' s1 ++ unsep_normal_form' s2
    end.

  Fixpoint Unseps (es: list expr) :=
    match es with
    | [] => Pred (pure True)
    | [e] => e
    | e :: es => Unsep e (Unseps es)
    end.

  Definition unsep_normal_form (e: expr) :=
    Unseps (unsep_normal_form' e).

  Lemma denote_Unseps :
    forall es, denote (Unseps es) = unseps (List.map denote es).
  Proof.
    induction es as [| e [|] IHes]; simpl in *; congruence.
  Qed.

  Lemma product_map {A B A' B'} (fA: A -> A') (fB: B -> B'):
    forall As Bs,
      product (List.map fA As) (List.map fB Bs) =
      map2 (fun a b => (fA a, fB b)) (product As Bs).
  Proof.
    unfold map2, product; intros.
    rewrite !flat_map_concat_map, !concat_map, !map_map.
    f_equal; apply map_ext; intros; rewrite !map_map.
    reflexivity.
  Qed.

  Lemma denote_map2_Sep :
    forall es1 es2,
      List.map denote (map2 Sep (product es1 es2)) =
      map2 sep (product (List.map denote es1)
                        (List.map denote es2)).
  Proof.
    intros.
    rewrite product_map, map2_map2, map_map2.
    reflexivity.
  Qed.

  Lemma unsep_normal_form_sound :
    forall e, impl1 (denote e) (denote (unsep_normal_form e)).
  Proof.
    unfold unsep_normal_form; induction e; simpl; intros;
      rewrite ?IHe1, ?IHe2,
        ?denote_Unseps, ?denote_map2_Sep,
        ?unseps_distr_sep, ?map_app,
        ?unseps_app in *; reflexivity.
  Qed.

  Fixpoint denote_unseps_as_conj (es: list expr) m :=
    match es with
    | [] => True
    | [e] => denote e m
    | e :: es => denote e m /\ denote_unseps_as_conj es m
    end.

  Lemma unsep_normal_form_sound' e m:
    denote e m ->
    denote_unseps_as_conj (unsep_normal_form' e) m.
  Proof.
    intros H%unsep_normal_form_sound;
      unfold unsep_normal_form in H;
      rewrite denote_Unseps in H.
    induction (unsep_normal_form' e) as [| p [|] IHps];
      simpl in *; unfold unsep in *; auto.
    intuition.
  Qed.
End Reflection.

  Ltac reify e :=
    let rec loop e :=
        match e with
        | sep ?s1 ?s2 =>
          let ur1 := loop s1 in let ur2 := loop s2 in uconstr:(Sep ur1 ur2)
        | unsep ?s1 ?s2 =>
          let ur1 := loop s1 in let ur2 := loop s2 in uconstr:(Unsep ur1 ur2)
        | ?p => uconstr:(Pred p)
        end in
    let ur := loop e in
    type_term ur.
End SepRefl.

Module Tactics.
  Ltac decompose_one_unsep H :=
    unfold unsep in H; cbv beta in H; decompose [and] H; clear H.

  Ltac decompose_all_unsep :=
    repeat match goal with
           | [ H: (unsep _ _) ?m |- _ ] => decompose_one_unsep H
           end.

  Ltac decompose_relevant_unsep :=
    repeat match goal with
           | [ H: (unsep _ _) ?m |- (sep _ _) ?m ] => decompose_one_unsep H
           end.

  Ltac normalize_relevant_sep :=
    match goal with
    | [ H: ?P ?m |- (sep _ _) ?m ] =>
      lazymatch P with
      | context[unsep] =>
        lazymatch type of H with
        | P m => fail "No progress"
        | _ => idtac
        end
      end
    | _ => fail "No hypothesis to normalize"
    end.

  Ltac normalize_decompose_relevant_sep :=
    match goal with
    | [ H: ?P ?m |- (sep _ _) ?m ] =>
      lazymatch P with
      | context[unsep] =>
        let r := SepRefl.reify P in
        change P with (SepRefl.denote r) in H;
        apply SepRefl.unsep_normal_form_sound' in H;
        simpl in H; decompose [and] H; clear H
      end
    | _ => fail "No hypothesis to normalize"
    end.
End Tactics.

Export Tactics.

(** The hint below is only a heuristic: it works well for stack allocation, for
    example, but it does not work in all cases.

    The separation logic problems that Rupicola needs to solve fall into two
    categories: *in* parameters and *(in-)out* parameters.  Consider this
    function and its spec::

        void add(bignum* p1, bignum* p2, bignum* pout)

        requires := p1 ↦ o1 * R1 &&& p2 ↦ o2 * R2 &&& pout ↦ out * Rout

        ensures := pout ↦ sum(op1, op2) * Rout

    Here `p1` and `p2` are *in* parameters: they (the pointers) are only read.
    `pout` is an out parameter: it is used for writing.  The spec of the
    function shows that:

    This peculiar spec allows `p1`, `p2`, and `out` to overlap in arbitrary
    ways: for example, calling `add(x, y, x)` will increment `x` by `y` in
    place. Assuming a memory `x ↦ X * y ↦ Y`, this corresponds to invoking `add`
    with `p1 == pout == x`, `p2 == y`, `R1 == Rout == y ↦ Y`, and `R2 == x ↦ X`.


    To infer the values of `R1`, `R2`, and `Rout`, Rupicola uses Bedrock2's
    cancellation.  This works well for formulae with a single non-separating
    conjunct, but there is a subtle issue when there is more than one such
    parameter.  Consider a call to `add(x, y, z)`:

    - If memory is described by `z ↦ Z * (x ↦ X &&& y ↦ Y)`, then traditional
      cancellation will infer `Rout == x ↦ X &&& y ↦ Y`, which is good.
    - But if we have `(z ↦ Z * x ↦ X) &&& (z ↦ Z * y ↦ Y)` instead (this is
      the same formula, written differently), then naive cancellation will yield
      either `Rout == x ↦ X` or `Rout == y ↦ Y`, and the postcondition will lose
      information about one of the two input variables… which is bad.

    Note that in both cases the problem is only with *out* parameters: for *in*
    parameters we only need to show that there is some pointer pointing to the
    right object.


    The heuristic that Rupicola implements is to first try unification against
    the original formula, and then if this fails to expand to the second form by
    normalizing and try canceling again.

    Concretely, the unification would succeed for `z` in the first case but fail
    for `x` and `y`, and subsequently succeed for `x` and `y` against the
    expanded, normalized form.

    But since Rupicola only ever expands, and never factors, starting with the
    second form will cause the wrong thing to be inferred for `z` in the example
    above.

    Stepping through IndirectAdd.v can also be very informative. **)
#[export] Hint Extern 1 ((sep _ _) _) =>
  normalize_decompose_relevant_sep; shelve : compiler_side_conditions.
