Require Import Ltac2.Ltac2. Set Default Proof Mode "Classic".
Require Import coqutil.Word.Interface.

Ltac2 Type exn ::= [ Undo ].

(* run t and undo its effects (except for its print output), but if it fails,
   turn the failure into an uncatchable panic *)
Ltac2 undo(t: unit -> unit): unit :=
  match Control.case (fun _ => t (); Control.zero Undo) with
  | Val _ => Control.throw Assertion_failure
  | Err e => match e with
             | Undo => ()
             | _ => Control.throw e
             end
  end.

Ltac ltac1Unit x := x.

Ltac _undo := ltac2:(t |- undo (fun _ => ltac1:(tac |- tac ltac1Unit) t)).
Tactic Notation "undo" tactic0(t) := _undo t.

Goal forall x: nat, x = x + x.
  intros.
  undo (fun _ => revert x;
                 match goal with
                 | |- ?g => (* idtac g; *) unify g (forall a : nat, a = a + a)
                 end).
  Fail undo (fun _ => revert x;
                 match goal with
                 | |- ?g => unify g (forall a : nat, a = a)
                 end).
Abort.

Class SidecondIrrelevant(P: Prop) := {}.

Ltac log_sidecond :=
  repeat lazymatch goal with
    | H: ?t |- _ =>
        lazymatch t with
        | word.word _ => fail (* arrived at top (section vars), exit repeat *)
        | word.ok _ => fail (* arrived at top (section vars), exit repeat *)
        | _ => first [ let _ := constr:(_ : SidecondIrrelevant t) in clear H
                     | lazymatch type of t with
                       | Prop => revert H
                       | _ => clear H || revert H
                       end ]
        end
    end;
  lazymatch goal with
  | |- ?g => idtac "Goal" g ".";
             idtac "Proof. t. Qed."
  end.
