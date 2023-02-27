Require Import Ltac2.Ltac2.
Require Import Coq.micromega.Lia.
Require Import coqutil.Tactics.fold_hyps coqutil.Tactics.foreach_hyp.
Require Import bedrock2.PurifySep.
Require Import bedrock2.HeapletwiseHyps.
Require Import coqutil.Tactics.ident_ops.
Require Import bedrock2.unzify.

Ltac purify_heapletwise_pred_cont k H pred m :=
  let pf := constr:(ltac:(eauto with purify) : purify pred _) in
  lazymatch type of pf with
  | purify pred True => idtac
  | purify pred ?P =>
      let HP := fresh "__pure_" H in pose proof (pf m H) as HP; k HP P
  end.

Ltac purify_heapletwise_hyp_of_type_cont k H t :=
  match t with
  | ?R ?m => purify_heapletwise_pred_cont k H R m
  | with_mem ?m ?R => purify_heapletwise_pred_cont k H R m
  | _ => idtac
  end.

Ltac purify_heapletwise_hyps :=
  foreach_hyp (purify_heapletwise_hyp_of_type_cont ltac:(fun h tp => idtac)).

Inductive derivability_test_marker: Prop := mk_derivability_test_marker.

Ltac clear_pure_hyp_if_derivable h tp :=
  tryif ident_starts_with __pure_ h then
    try (clear h; assert_succeeds (idtac; assert tp by (zify_goal; xlia zchecker)))
  else idtac.

Ltac clear_upto_marker marker :=
  lazymatch goal with
  | H: marker |- _ =>
      repeat lazymatch goal with
        | A: ?T |- _ => lazymatch T with
                        | marker => fail (* done *)
                        | _ => clear A
                        end
        end;
      clear H
  | |- _ => fail "marker not found found"
  end.

Ltac unpurify :=
  pose proof mk_derivability_test_marker;
  purify_heapletwise_hyps;
  zify_hyps_upto_marker derivability_test_marker;
  foreach_hyp_downto_marker derivability_test_marker clear_pure_hyp_if_derivable;
  clear_upto_marker derivability_test_marker.
