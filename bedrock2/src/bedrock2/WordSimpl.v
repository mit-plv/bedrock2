Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import bedrock2.groundcbv.
Require Import Coq.setoid_ring.Ring.

Ltac word_simpl_step_in_hyps :=
  match goal with
  | H: ?x = ?y |- _ => is_var x; is_var y; subst x
  | H: context[@word.add ?wi ?wo ?x ?y] |- _ =>
      progress (ring_simplify (@word.add wi wo x y) in H)
  | H: context[@word.sub ?wi ?wo ?x ?y] |- _ =>
      progress (ring_simplify (@word.sub wi wo x y) in H)
  | H: context[@word.opp ?wi ?wo ?x   ] |- _ =>
      progress (ring_simplify (@word.opp wi wo x  ) in H)
  | H: context[@word.mul ?wi ?wo ?x ?y] |- _ =>
      progress (ring_simplify (@word.mul wi wo x y) in H)
  | H: context[word.unsigned (word.of_Z _)] |- _ =>
    rewrite word.unsigned_of_Z_nowrap in H by Lia.lia
  | _ => progress groundcbv_in_all
  end.

Ltac word_simpl_step_in_goal :=
  match goal with
  | |- context[@word.add ?wi ?wo ?x ?y] => progress (ring_simplify (@word.add wi wo x y))
  | |- context[@word.sub ?wi ?wo ?x ?y] => progress (ring_simplify (@word.sub wi wo x y))
  | |- context[@word.opp ?wi ?wo ?x   ] => progress (ring_simplify (@word.opp wi wo x  ))
  | |- context[@word.mul ?wi ?wo ?x ?y] => progress (ring_simplify (@word.mul wi wo x y))
  | |- context[word.unsigned (word.of_Z _)] =>
    rewrite word.unsigned_of_Z_nowrap by Lia.lia
  | _ => progress groundcbv_in_goal
  end.
