(*
Simulations usually talk about single executions:
"All low-level executions have a high-level explanation".
Our simulations, however, talk about all executions at once and about single states:
"All states in the low-level outcome set have a corresponding state in the high-level outcome set".

This one is like Simulation.v, but Params can hold state which doesn't change during execution
and can be shared between "exec" and "related".
*)

Require compiler.Simulation.

Definition simulation{Params1 Params2 State1 State2: Type}
           (exec1: Params1 -> State1 -> (State1 -> Prop) -> Prop)
           (exec2: Params2 -> State2 -> (State2 -> Prop) -> Prop)
           (related: Params1 -> Params2 -> State1 -> State2 -> Prop): Prop :=
  forall p1 p2, Simulation.simulation (exec1 p1) (exec2 p2) (related p1 p2).

Definition compile_inv{Params1 State1 Params2 State2: Type}
           (related: Params1 -> Params2 -> State1 -> State2 -> Prop)
           (inv: Params1 -> State1 -> Prop)
           (p1: Params1)(p2: Params2): State2 -> Prop :=
  Simulation.compile_inv (related p1 p2) (inv p1).

Lemma compile_inv_is_inv{Params1 State1 Params2 State2: Type}
      (exec1: Params1 -> State1 -> (State1 -> Prop) -> Prop)
      (exec2: Params2 -> State2 -> (State2 -> Prop) -> Prop)
      (related: Params1 -> Params2 -> State1 -> State2 -> Prop)
      (Sim: simulation exec1 exec2 related)
      (inv1: Params1 -> State1 -> Prop)
      (p1: Params1)(p2: Params2)
      (inv1_is_inv: forall s1, (inv1 p1) s1 -> exec1 p1 s1 (inv1 p1)):
  forall s2, (compile_inv related inv1 p1 p2) s2 -> exec2 p2 s2 (compile_inv related inv1 p1 p2).
Proof.
  unfold compile_inv, simulation in *.
  eapply Simulation.compile_inv_is_inv.
  - eapply Sim.
  - eapply inv1_is_inv.
Qed.

Definition compose_relation{Params1 Params2 Params3 State1 State2 State3: Type}
           (R12: Params1 -> Params2 -> State1 -> State2 -> Prop)
           (R23: Params2 -> Params3 -> State2 -> State3 -> Prop):
  Params1 -> Params3 -> State1 -> State3 -> Prop :=
  fun p1 p3 s1 s3 => exists p2, (Simulation.compose_relation (R12 p1 p2) (R23 p2 p3)) s1 s3.

Definition weakening{Params State: Type}(exec: Params -> State -> (State -> Prop) -> Prop): Prop :=
  forall p, Simulation.weakening (exec p).

Lemma compose_simulation{Params1 Params2 Params3 State1 State2 State3: Type}
      (exec1: Params1 -> State1 -> (State1 -> Prop) -> Prop)
      (exec2: Params2 -> State2 -> (State2 -> Prop) -> Prop)
      (exec3: Params3 -> State3 -> (State3 -> Prop) -> Prop)
      (W3: weakening exec3)
      (R12: Params1 -> Params2 -> State1 -> State2 -> Prop)
      (R23: Params2 -> Params3 -> State2 -> State3 -> Prop)
      (S12: simulation exec1 exec2 R12)
      (S23: simulation exec2 exec3 R23):
  simulation exec1 exec3 (compose_relation R12 R23).
Proof.
  unfold simulation, compose_relation, weakening in *.
  intros p1 p3.
  pose proof @Simulation.compose_simulation as P.
  specialize P with (exec1 := (exec1 p1)).
  specialize P with (exec3 := (exec3 p3)).
  specialize P with (1 := (W3 p3)).
  unfold Simulation.compose_relation in *.

  unfold Simulation.simulation.
  intros s1 s3 post1 (p2 & s2 & HR12 & HR23) E1.
  specialize P with (1 := (S12 p1 p2)).
  specialize P with (1 := (S23 p2 p3)).
  unfold Simulation.simulation in P.
  specialize P with (2 := E1).
  eapply W3; cycle 1.
  - eapply P. eexists. split; eassumption.
  - cbv beta. intros s3' A.
    firstorder idtac.
Qed.
