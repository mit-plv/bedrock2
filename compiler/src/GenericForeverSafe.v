Require Import riscv.Utility.runsToNonDet.


Section ForeverSafe.

  Context {State: Type}.

  Variable step: State -> (State -> Prop) -> Prop.

  Variables safe1 safe2: State -> Prop.

  Hypothesis exclusive: forall state, ~ (safe1 state /\ safe2 state).

  Hypothesis step_weaken: forall (post1 post2: State -> Prop),
    (forall s, post1 s -> post2 s) ->
    forall s, step s post1 -> step s post2.

  Hypothesis run_1_2: forall state,
      safe1 state -> runsTo step state safe2.

  Hypothesis run_2_1: forall state,
      safe2 state -> runsTo step state safe1.

  Lemma run_ping: forall state,
      runsTo step state safe1 ->
      runsTo step state safe2.
  Proof.
    induction 1; rename P into safe1.
    - eauto.
    - eapply runsToStep. 1: eassumption.
      intros.
      eapply H1; eauto.
  Qed.

  Lemma run_pong: forall state,
      runsTo step state safe2 ->
      runsTo step state safe1.
  Proof.
    induction 1; rename P into safe2.
    - eauto.
    - eapply runsToStep. 1: eassumption.
      intros.
      eapply H1; eauto.
  Qed.

  (* extract the "head" of a "runsTo safe1",
     making the runsToDone case disappear by going from safe1 to safe2 and back to safe1 *)
  Lemma runsTo_safe1_head: forall (st: State),
      runsTo step st safe1 ->
      step st (fun st' => runsTo step st' safe1).
  Proof.
    intros st R. destruct R.
    - pose proof (run_1_2 _ H) as P. inversion P.
      + exfalso. eapply exclusive; eauto.
      + eapply step_weaken. 2: eassumption.
        intros. specialize (H1 _ H2).
        eapply run_pong. assumption.
    - eapply step_weaken. 2: eassumption.
      intros. eapply H0. assumption.
  Qed.

End ForeverSafe.
