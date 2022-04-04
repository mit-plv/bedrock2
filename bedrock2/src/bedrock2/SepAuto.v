(* More separation logic automation, independent of the programming language semantics,
   and intended to be usable both for concrete programs and simulation proofs.

   Note: If after importing this file, you import coqutil.Tactics.fwd_core or another
   file which exports coqutil.Tactics.fwd_core (eg coqutil.Tactics.fwd), that will
   undo the `Ltac fwd_rewrites ::= fwd_rewrite_db_in_star.` patching, so `fwd` and
   tactics using `fwd` will do fewer simplifications than intended *)

Require Import Coq.ZArith.ZArith. Open Scope Z_scope. (* TODO remove *)
Require Import coqutil.Byte.
Require Import coqutil.Datatypes.Inhabited.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.autoforward.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.OfListWord.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.fwd.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.Array.
Require Import bedrock2.ZnWords.
Require Import bedrock2.WordSimpl.
Import List.ListNotations. Open Scope list_scope. (* TODO remove *)
Require Import bedrock2.SepCalls.
Require Import bedrock2.TransferSepsOrder.

Ltac fwd_rewrites ::= fwd_rewrite_db_in_star.

(* Note: It would be nice to have a notation for this pattern, eg

Tactic Notation "ebind" tactic3(t1) ";;" tactic3(t2) :=
  t1; match goal with
      | _: tactic_error _ |- _ => idtac
      | |- _ => idtac; t2
      end.

but if t2 is a match and not prefixed with idtac, it's evaluated too early *)
Ltac after_mem_modifying_lemma :=
  scancel_asm;
  match goal with
  | _: bedrock2.TacticError.tactic_error _ |- _ => idtac
  | |- _ => intro_new_mem; transfer_sep_order
  end.
