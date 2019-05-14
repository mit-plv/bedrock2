(*
Simulations usually talk about single executions:
"All low-level executions have a high-level explanation".
Our simulations, however, talk about all executions at once and about single states:
"All states in the low-level outcome set have a corresponding state in the high-level outcome set".
*)

Definition simulation{State1 State2: Type}
           (exec1: State1 -> (State1 -> Prop) -> Prop)
           (exec2: State2 -> (State2 -> Prop) -> Prop)
           (related: State1 -> State2 -> Prop): Prop :=
  forall s1 s2 post1,
    related s1 s2 ->
    exec1 s1 post1 ->
    exec2 s2 (fun s2' => exists s1', related s1' s2' /\ post1 s1').

Definition compose_relation{State1 State2 State3: Type}
           (R12: State1 -> State2 -> Prop)(R23: State2 -> State3 -> Prop):
  State1 -> State3 -> Prop :=
  fun s1 s3 => exists s2, R12 s1 s2 /\ R23 s2 s3.

Definition weakening{State: Type}(exec: State -> (State -> Prop) -> Prop): Prop :=
  forall (post1 post2: State -> Prop),
    (forall s, post1 s -> post2 s) ->
    forall s, exec s post1 -> exec s post2.

Lemma compose_simulation{State1 State2 State3: Type}
      (exec1: State1 -> (State1 -> Prop) -> Prop)
      (exec2: State2 -> (State2 -> Prop) -> Prop)
      (exec3: State3 -> (State3 -> Prop) -> Prop)
      (W3: weakening exec3)
      (R12: State1 -> State2 -> Prop)
      (R23: State2 -> State3 -> Prop)
      (S12: simulation exec1 exec2 R12)
      (S23: simulation exec2 exec3 R23):
  simulation exec1 exec3 (compose_relation R12 R23).
Proof.
  unfold simulation, compose_relation in *.
  intros s1 s3 post1 (s2 & HR12 & HR23) E1.
  specialize S12 with (1 := HR12) (2 := E1).
  specialize S23 with (1 := HR23) (2 := S12).
  simpl in S23.
  eapply W3. 2: exact S23.
  simpl. intros s3' (s2' & HR23' & s1' & HR12' & P1).
  eauto.
Qed.
