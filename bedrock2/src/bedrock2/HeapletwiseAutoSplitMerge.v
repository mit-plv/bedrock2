Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Byte.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import coqutil.Datatypes.ZList.
Require Import coqutil.Datatypes.Inhabited.
Require Import bedrock2.Lift1Prop bedrock2.Map.Separation.
Require Import bedrock2.PurifySep.
Require Import bedrock2.SepLib.
Require Import bedrock2.ZnWords.
Require Import bedrock2.HeapletwiseHyps.
Require Import bedrock2.bottom_up_simpl_ltac1.

Import ZList.List.ZIndexNotations.
Local Open Scope zlist_scope.
Local Open Scope Z_scope.

Section SepLog.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma split_off_elem_from_array{E: Type}{inh: inhabited E}:
    forall a a' elem {elemSize: PredicateSize elem} n i,
      (word.unsigned (word.sub a' a)) mod elemSize = 0 ->
      word.unsigned (word.sub a' a) / elemSize = i ->
      (forall (vs: list E) m,
          array elem n vs a m ->
          sep (elem vs[i] a')
              (sep (array elem i vs[:i] a)
                   (array elem (n-i-1) vs[i+1:]
                      (word.add a' (word.of_Z elemSize)))) m) /\
      (forall vs1 vs2 v m,
          sep (array elem i vs1 a)
              (sep (elem v a')
                   (array elem (n-i-1) vs2
                      (word.add a' (word.of_Z elemSize)))) m ->
          array elem n (vs1 ++ [|v|] ++ vs2) a m).
  Proof.
  Admitted.

(* alternative way of expressing "1 past a'":
  Lemma split_off_elem_from_array{E: Type}{inh: inhabited E}:
    forall a a' elem {elemSize: PredicateSize elem} n i,
      (word.unsigned (word.sub a' a)) mod elemSize = 0 ->
      word.unsigned (word.sub a' a) / elemSize = i ->
      (forall (vs: list E) m,
          array elem n vs a m ->
          sep (elem vs[i] a')
              (sep (array elem i vs[:i] a)
                   (array elem (n-i-1) vs[i+1:]
                      (word.add a (word.of_Z (elemSize * (i + 1)))))) m) /\
      (forall vs1 vs2 v m,
          sep (array elem i vs1 a)
              (sep (elem v a')
                   (array elem (n-i-1) vs2
                      (word.add a (word.of_Z (elemSize * (i + 1)))))) m ->
          array elem n (vs1 ++ [|v|] ++ vs2) a m).
  Proof.
  Admitted.
*)
End SepLog.


Definition find_superrange_hyp{word: Type}(start: word)(size: Z)(tGoal: Prop) := tGoal.
Definition split_range_from_hyp{word: Type}(start: word)(size: Z)(tHyp: Prop)
  (H: tHyp)(tGoal: Prop) := tGoal.

Definition merge_step(P: Prop) := P.

(* Is start..start+size a subrange of start'..start'+size' ?
   Assumes 0<=size<2^width and 0<=size'<2^width.
   Both ranges may wrap around. *)
Ltac is_subrange start size start' size' :=
  (* we do the comparison in a different coordinate system, namely relative to start',
     ie we shift (with wrapping) all points so that start' corresponds to zero *)
  assert_succeeds (idtac;
    assert (word.unsigned (word.sub start start') + size <= size') by ZnWords).

Ltac find_superrange_hyp start size :=
  match goal with
  | H: with_mem _ (?P' ?start') |- _ =>
      let size' := lazymatch constr:(_: PredicateSize P') with ?s => s end in
      let __ := match constr:(Set) with _ => is_subrange start size start' size' end in H
  end.

Ltac split_range_from_hyp_default :=
  lazymatch goal with
  | |- split_range_from_hyp ?start ?size (with_mem ?m ?P) ?H ?g =>
      let pf := fresh in
      lazymatch P with
      | array ?elem ?n ?vs ?start' =>
          unshelve epose proof (split_off_elem_from_array start' start elem n _ _ _) as pf;
          [ (* i *)
          | ZnWords
          | bottom_up_simpl_in_goal; reflexivity
          | (* remaining goal *) ]
      end;
      change g;
      eapply (proj1 pf) in H;
      eapply proj2 in pf;
      let t := type of pf in change (merge_step t) in pf
  end.

Ltac split_range_from_hyp_hook := split_range_from_hyp_default.

Ltac split_merge_step :=
  lazymatch goal with
  | |- canceling (cons (?P ?start) _) ?m _ =>
      let size := lazymatch constr:(_: PredicateSize P) with ?s => s end in
      let g := lazymatch goal with |- ?x => x end in
      change (find_superrange_hyp start size g)
  | |- find_superrange_hyp ?start ?size ?g =>
      let H := find_superrange_hyp start size in
      change (split_range_from_hyp start size _ H g)
  | |- split_range_from_hyp ?start ?size ?tH ?H ?g => split_range_from_hyp_hook
  end.
