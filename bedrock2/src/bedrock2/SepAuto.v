(* More separation logic automation, independent of the programming language semantics,
   and intended to be usable both for concrete programs and simulation proofs.

   Note: If after importing this file, you import coqutil.Tactics.fwd_core or another
   file which exports coqutil.Tactics.fwd_core (eg coqutil.Tactics.fwd), that will
   undo the `Ltac fwd_rewrites ::= fwd_rewrite_db_in_star.` patching, so `fwd` and
   tactics using `fwd` will do fewer simplifications than intended *)

Require Export Coq.ZArith.ZArith. Open Scope Z_scope.
Require Export coqutil.Byte.
Require Export coqutil.Datatypes.Inhabited.
Require Export coqutil.Tactics.Tactics.
Require Export coqutil.Tactics.autoforward.
Require Export coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.OfListWord.
Require Export coqutil.Word.Interface coqutil.Word.Properties.
Require Export coqutil.Tactics.fwd.
Require Export bedrock2.Lift1Prop.
Require Export bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.Array.
Require Export bedrock2.ZnWords.
Require Import bedrock2.groundcbv.
Export List.ListNotations. Open Scope list_scope.
Require Export bedrock2.SepCalls.
Require Export bedrock2.TransferSepsOrder.
Require Export bedrock2.SepAddrLast. (* goes last because it redefines "array" and others *)

Ltac fwd_rewrites ::= fwd_rewrite_db_in_star.

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

(* Note: It would be nice to have a notation for this pattern, eg

Tactic Notation "ebind" tactic3(t1) ";;" tactic3(t2) :=
  t1; match goal with
      | _: tactic_error _ |- _ => idtac
      | |- _ => idtac; t2
      end.

but if t2 is a match and not prefixed with idtac, it's evaluated too early *)
Ltac after_mem_modifying_lemma :=
  after_sep_call;
  match goal with
  | _: tactic_error _ |- _ => idtac
  | |- _ => transfer_sep_order
  end.
