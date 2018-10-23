Ltac log_goal :=
  idtac "---begin-goal---";
  try match reverse goal with
      | H: ?T |- _ => idtac H ":" T; fail
      end;
  idtac "===============";
  match goal with
  | |- ?G => idtac G
  end;
  idtac "---end-goal---".
