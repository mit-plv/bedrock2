Require Import compiler.util.Tactics.

Ltac log_goal_no_names :=
  idtac "---begin-goal---";
  repeat match goal with
         | H: _ |- _ => revert H
         end;
  match goal with
  | |- ?G => idtac G
  end;
  intros;
  idtac "---end-goal---".


Ltac log_goal_reversed :=
  idtac "---begin-reversed-goal---";
  match goal with
  | |- ?G => idtac G
  end;
  idtac "===============";
  repeat match goal with
         | H: ?T |- _ => revert H; idtac H ":" T
         end;
  intros;
  idtac "---end-reversed-goal---".


Inductive Mark{T: Type}(x: T): Type := doMark.

Ltac log_goal_slow :=
  idtac "---begin-goal---";
  repeat match goal with
         | H: ?T |- _ =>
           lazymatch T with
           | Mark _ => fail
           | _ => let H' := fresh "M_" H in unique pose proof (doMark _: Mark H) as H'
           end
         end;
  repeat match goal with
         | H: ?T, M: Mark ?H' |- _ => unify H H'; idtac H ":" T; clear M
         end;
  idtac "===============";
  match goal with
  | |- ?G => idtac G
  end;
  idtac "---end-goal---".


Ltac log_goal := log_goal_reversed.
