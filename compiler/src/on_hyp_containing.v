Tactic Notation "on" "hyp" "[" constr(t1) "]" "do" tactic(f) :=
  match goal with
  | H: _ |- _ =>
    lazymatch type of H with
    | context[t1] => f H
    end
  end.

Tactic Notation "on" "hyp" "[" constr(t1) ";" constr(t2) "]" "do" tactic(f) :=
  match goal with
  | H: _ |- _ =>
    lazymatch type of H with
    | context[t1] =>
      lazymatch type of H with
      | context[t2] => f H
      end
    end
  end.

Tactic Notation "on" "hyp" "[" constr(t1) ";" constr(t2) ";" constr(t3) "]" "do" tactic(f) :=
  match goal with
  | H: _ |- _ =>
    lazymatch type of H with
    | context[t1] =>
      lazymatch type of H with
      | context[t2] =>
        lazymatch type of H with
        | context[t3] => f H
        end
      end
    end
  end.
