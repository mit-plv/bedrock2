Ltac ltac_identity x := x.

(* It is important that we don't pass `tt` or any other constr to `f`,
   because constructing a constr requires to be focused on a goal,
   and Ltac1 auto-focuses as soon as a constr needs to be constructed,
   so if this tactic runs after a tactic that leaves n<>1 open subgoals,
   passing `tt` would cause the logger to be called n times instead of once. *)
Ltac run_logger_thunk f := f ltac_identity.

Ltac ignore_logger_thunk f := idtac.

Local Ltac sample_step_tactic logger :=
  match goal with
  | x: ?T |- _ =>
      lazymatch type of T with
      | Prop => fail
      | _ => idtac
      end;
      clear x;
      logger ltac:(fun _ => idtac "clear unused non-Prop" x)
  | H: _ \/ _ |- _ =>
      (* NOTE: if you uncomment H, the message will be printed twice! *)
      destruct H; logger ltac:(fun _ => idtac "destruct \/" (* H *))
  | H: _ /\ _ |- _ =>
      destruct H; logger ltac:(fun _ => idtac "destruct /\ in")
  | |- _ => assumption; logger ltac:(fun _ => idtac "assumption")
  | |- _ => congruence; logger ltac:(fun _ => idtac "congruence")
  end.

(* Local Ltac step := sample_step_tactic run_logger_thunk. *)
Local Ltac step := sample_step_tactic ignore_logger_thunk.

Goal forall a b c: nat, a = b \/ b = a -> a = b.
  intros.
  step. step. step. step.
  Unshelve. all: fail.
Abort.
