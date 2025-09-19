Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.SeparationLogic.
From coqutil Require Import Map.Interface Decidable.
Import map.

Section straightline_test.
    Context {key value} {map : map key value} {ok : ok map}.
    Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.
    Context (p q r : map -> Prop) (m : map).

    Ltac assert_goal_is P := match goal with
            | |- P => idtac
            | |- ?G => idtac "expected " P " but got " G; fail
        end.
    Ltac assert_hyp_ex P := match goal with
            | H : P |- _ => idtac
            | _ => fail
        end.

    (* Apply associativity to move brackets to the right. *)
    Goal (((p * q) * r)%sep m).
        straightline.
        assert_goal_is ((p * (q * r))%sep m).
    Abort.
    Goal False.
        assert (((p * q) * r)%sep m).
        1: admit.
        straightline.
        assert_hyp_ex ((p * (q * r))%sep m).
    Abort.

    (* Do nothing when already seps are already right-associative. *)
    Goal ((p * (q * r))%sep m).
        Fail straightline.
    Abort.
    Goal False.
        assert ((p * (q * r))%sep m).
        1: admit.
        Fail straightline.
    Abort.

    (* Do not destruct context variables with exists and /\. *)
    Section ex_context.
        Context {ex: exists q : map -> Prop, p m}.
        Goal False.
            Fail straightline.
            Fail assert_hyp_ex (p m).
        Abort.
    End ex_context.
    Section conj_context.
        Context {conj : p m /\ q m}.
        Goal False. 
            Fail straightline.
            Fail assert_hyp_ex (p m).
        Abort.
    End conj_context.
End straightline_test.