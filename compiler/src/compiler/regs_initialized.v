Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Local Open Scope Z_scope.

Section WithParameters.
  Context {width: Z} {T: Type} {locals: map.map Z T} {locals_ok: map.ok locals}.

  Definition regs_initialized(regs: locals): Prop :=
    forall r : Z, 0 < r < 32 -> exists v : T, map.get regs r = Some v.

  Lemma regs_initialized_put: forall l x v,
      regs_initialized l ->
      regs_initialized (map.put l x v).
  Proof.
    unfold regs_initialized in *.
    intros.
    rewrite map.get_put_dec.
    destruct_one_match; eauto.
  Qed.

  Lemma regs_initialized_putmany: forall l l',
      regs_initialized l ->
      regs_initialized (map.putmany l l').
  Proof.
    unfold regs_initialized. intros. specialize (H _ H0). destruct H as [v H].
    rewrite map.get_putmany_dec. destruct_one_match; eauto.
  Qed.

  Lemma preserve_regs_initialized_after_put: forall regs var val,
      regs_initialized regs ->
      regs_initialized (map.put regs var val).
  Proof.
    unfold regs_initialized. intros. specialize (H _ H0).
    rewrite map.get_put_dec. destruct_one_match; subst; eauto.
  Qed.

  Lemma preserve_regs_initialized_after_putmany_of_list_zip: forall vars vals (regs regs': locals),
      regs_initialized regs ->
      map.putmany_of_list_zip vars vals regs = Some regs' ->
      regs_initialized regs'.
  Proof.
    induction vars; intros.
    - simpl in H0. destruct vals; try discriminate.
      replace regs' with regs in * by congruence. assumption.
    - simpl in H0.
      destruct vals; try discriminate.
      eapply IHvars. 2: eassumption.
      eapply preserve_regs_initialized_after_put.
      eassumption.
  Qed.

End WithParameters.
