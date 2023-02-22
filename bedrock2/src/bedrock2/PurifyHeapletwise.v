Require Import Ltac2.Ltac2.
Require Import Coq.micromega.Lia.
Require Import coqutil.Tactics.fold_hyps coqutil.Tactics.foreach_hyp.
Require Import bedrock2.PurifySep.
Require Import bedrock2.HeapletwiseHyps.
Require Import bedrock2.ident_starts_with.
Require Import bedrock2.unzify.

Ltac purify_heapletwise_pred H pred m :=
  let HP := fresh "__pure_" H in eassert (purify pred _) as HP by eauto with purify;
  specialize (HP m H).

Ltac purify_heapletwise_hyp_of_type H t :=
  match t with
  | ?R ?m => purify_heapletwise_pred H R m
  | with_mem ?m ?R => purify_heapletwise_pred H R m
  | _ => idtac
  end.

Ltac purify_heapletwise_hyps := foreach_hyp purify_heapletwise_hyp_of_type.

Inductive derivability_test_marker: Prop := mk_derivability_test_marker.

Ltac clear_pure_hyp_if_derivable h tp :=
  tryif ident_starts_with __pure_ h then
    tryif assert_succeeds (idtac; assert tp by (zify_goal; xlia zchecker))
    then clear h else idtac
  else idtac.

Ltac unpurify :=
  pose proof mk_derivability_test_marker;
  purify_heapletwise_hyps;
  zify_hyps_upto_marker derivability_test_marker;
  foreach_hyp_downto_marker derivability_test_marker clear_pure_hyp_if_derivable;
  clear_upto_marker derivability_test_marker.
