From coqutil Require Import
     Decidable Map.Interface.
From bedrock2 Require Import
     Lift1Prop Map.Separation.
From Coq Require Import
     Classes.Morphisms List.
From Rupicola Require Import Core.

Import ListNotations.
Open Scope list_scope.

Module SepReif.
Section Reification.
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
End Reification.

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
End SepReif.

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
        let r := SepReif.reify P in
        change P with (SepReif.denote r) in H;
        apply SepReif.unsep_normal_form_sound' in H;
        simpl in H; decompose [and] H; clear H
      end
    | _ => fail "No hypothesis to normalize"
    end.
End Tactics.

Export Tactics.

#[export] Hint Extern 1 ((sep _ _) _) =>
  normalize_decompose_relevant_sep; shelve : compiler_side_conditions.
