Require Import Ltac2.Ltac2.
Require Import coqutil.Tactics.fold_hyps coqutil.Tactics.foreach_hyp.
Require Import bedrock2.PurifySep.
Require Import bedrock2.HeapletwiseHyps.

Ltac purify_heapletwise_pred H pred m :=
  let HP := fresh H "P" in eassert (purify pred _) as HP by eauto with purify;
  specialize (HP m H).

Ltac purify_heapletwise_hyp_of_type H t :=
  match t with
  | ?R ?m => purify_heapletwise_pred H R m
  | with_mem ?m ?R => purify_heapletwise_pred H R m
  | _ => idtac
  end.

Ltac purify_heapletwise_hyps := foreach_hyp purify_heapletwise_hyp_of_type.

Ltac2 purified_type_of_pred(p: constr) :=
  let pf := constr:(ltac:(eauto with purify) : purify $p _) in
  lazy_match! Constr.type pf with
  | purify _ ?t => t
  end.

Ltac2 purified_type t :=
  match! t with
  | ?r ?m => [ purified_type_of_pred r ]
  | with_mem ?m ?r => [ purified_type_of_pred r ]
  | _ => []
  end.

Ltac2 collect_purified_hyp_types () :=
  fold_hyps_upwards (fun (l: constr list) h tp => List.append (purified_type tp) l) [].

(* clears all hypotheses that are derivable by purify_heapletwise_hyps *)
Ltac2 unpurify () :=
  let l := collect_purified_hyp_types () in
  foreach_hyp (fun h tp => if List.exist (Constr.equal tp) l then clear $h else ()).
