Require Export bedrock2.Map.SeparationLogic.

Require Import Coq.Classes.Morphisms.
Require Import bedrock2.Lift1Prop.
Require Coq.Lists.List.
Require Import coqutil.sanity coqutil.Decidable coqutil.Tactics.destr.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.fwd.
Import Map.Interface.map Map.Properties.map.

Section SepProperties.
  Context {key value} {map : map key value} {ok : ok map}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.
  Local Open Scope sep_scope.

  (* C: common, already cancelled clauses
     Ps: LHS clauses to pick from
     Qs: RHS clauses to cancel
     U: uncancelable clauses in Qs *)
  Definition cancelling(C Ps Qs U: map -> Prop)(m: map): Prop :=
    sep C Ps m -> sep C (sep Qs U) m.

  Lemma start_cancelling: forall (Ps Qs: map -> Prop) m,
      (Ps m -> Qs m) = cancelling (emp True) Ps Qs (emp True) m.
  Proof.
    unfold cancelling.
    intros. apply PropExtensionality.propositional_extensionality. split; intros.
    - rewrite sep_emp_l. rewrite sep_emp_l in H0. rewrite sep_emp_r. apply proj2 in H0. auto.
    - rewrite 2sep_emp_l in H. rewrite sep_emp_r in H. apply H. auto.
  Qed.

  Lemma done_cancelling: forall C m,
      cancelling C (emp True) (emp True) (emp True) m.
  Proof.
    unfold cancelling. intros. apply sep_assoc. rewrite sep_emp_r. auto.
  Qed.

  Lemma cancelling_step: forall C P Ps Q Qs U m,
      P = Q ->
      cancelling C (sep P Ps) (sep Q Qs) U m = cancelling (sep P C) Ps Qs U m.
  Proof.
    intros. subst Q.
    apply PropExtensionality.propositional_extensionality. unfold cancelling.
    split; intros.
    - seprewrite_in (sep_comm P C) H0. eapply sep_assoc in H0. specialize (H H0).
      clear H0. ecancel_assumption.
    - eapply sep_assoc in H0. seprewrite_in (sep_comm C P) H0. specialize (H H0).
      clear H0. ecancel_assumption.
  Qed.

  Lemma uncancellable_step: forall C Ps Q Qs U m,
      cancelling C Ps (sep Q Qs) U m = cancelling C Ps Qs (sep Q U) m.
  Proof.
    intros.
    apply PropExtensionality.propositional_extensionality. unfold cancelling.
    split; intros.
    - specialize (H H0). clear H0. ecancel_assumption.
    - specialize (H H0). clear H0. ecancel_assumption.
  Qed.

(*
  (* without stash of uncancellable conjuncts: *)

  Definition cancelling(C Ps Qs: map -> Prop)(m: map): Prop :=
    sep C Ps m -> sep C Qs m.

  Lemma start_cancelling: forall (Ps Qs: map -> Prop) m,
      (Ps m -> Qs m) = cancelling (emp True) Ps Qs m.
  Proof.
    unfold cancelling.
    intros. apply PropExtensionality.propositional_extensionality. split; intros.
    - rewrite sep_emp_l. rewrite sep_emp_l in H0. apply proj2 in H0. auto.
    - rewrite 2sep_emp_l in H. apply H. auto.
  Qed.

  Lemma done_cancelling: forall C m,
      cancelling C (emp True) (emp True) m.
  Proof.
    unfold cancelling. intros. assumption.
  Qed.

  Lemma cancelling_step: forall C P Ps Q Qs m,
      P = Q ->
      cancelling C (sep P Ps) (sep Q Qs) m = cancelling (sep P C) Ps Qs m.
  Proof.
    intros. subst Q.
    apply PropExtensionality.propositional_extensionality. unfold cancelling.
    split; intros.
    - seprewrite_in (sep_comm P C) H0. eapply sep_assoc in H0. specialize (H H0).
      eapply sep_assoc in H. seprewrite_in (sep_comm C P) H. exact H.
    - eapply sep_assoc in H0. seprewrite_in (sep_comm C P) H0. specialize (H H0).
      seprewrite_in (sep_comm P C) H. eapply sep_assoc in H. exact H.
  Qed.
*)
End SepProperties.
