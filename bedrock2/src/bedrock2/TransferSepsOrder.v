(* Applying the order of sep clauses from an old hypothesis onto a new hypothesis: *)

Require Export Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import coqutil.Z.Lia.
Require Export coqutil.Byte.
Require Import coqutil.Datatypes.HList.
Require Import coqutil.Datatypes.PropSet.
Require Export coqutil.Datatypes.Inhabited.
Require Import coqutil.Tactics.rewr coqutil.Tactics.rdelta.
Require Import Coq.Program.Tactics.
Require Export coqutil.Tactics.Tactics.
Require Export coqutil.Tactics.autoforward.
Require Export coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.OfListWord.
Require Export coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Sorting.OrderToPermutation.
Require Export coqutil.Tactics.fwd.
Require Import coqutil.Tactics.ltac_list_ops.
Require Export bedrock2.Lift1Prop.
Require Export bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.Array.
Require Export bedrock2.ZnWords.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Require Export bedrock2.SepClause.
Export List.ListNotations. Open Scope list_scope.

Section TransferSepsOrder.
  Context {width : Z} {word : Word.Interface.word width} {word_ok: word.ok word}
          {mem : map.map word byte} {mem_ok: map.ok mem}.

  Lemma reorder_is_iff1: forall (order: list nat) (l: list (mem -> Prop)),
      List.length order = List.length l ->
      iff1 (seps l) (seps (reorder order l)).
  Proof.
    intros. rewrite <-2seps'_iff1_seps. rewrite seps'_fold_right.
    rewrite reorder_comm_fold_right.
    - reflexivity.
    - intros. eapply iff1ToEq. cancel.
    - assumption.
  Qed.
End TransferSepsOrder.

(* If the second-to-last argument of a predicate is a word, we assume it's the address.
   Could be made more flexible and accurate using typeclasses, but that would require
   adding an instance for each predicate. *)
Ltac get_addr clause :=
  lazymatch clause with
  | _ ?a _ => lazymatch type of a with
              | @word.rep _ _ => constr:(a)
              end
  end.

Ltac clause_index clause clauses start_index default_index :=
  match clauses with
  | cons clause _ => constr:(start_index)
  | cons ?otherclause _ =>
      let a := get_addr clause in
      lazymatch get_addr otherclause with
      | a => constr:(start_index)
      end
  | cons _ ?tail => clause_index clause tail (S start_index) default_index
  | nil => constr:(default_index)
  end.

Ltac get_order_rec old_clauses new_clauses default_index :=
  lazymatch new_clauses with
  | nil => constr:(@nil nat)
  | cons ?clause ?tail =>
    let priority := clause_index clause old_clauses 0%nat default_index in
    let rest := get_order_rec old_clauses tail priority in
    constr:(priority :: rest)
  end.

Ltac get_order old_clauses new_clauses :=
  (* if the first clause is not found in old_clauses, we put it at the end;
     if a non-first clause is not found, we put it after the clause that's
     to the left of it in new_clauses, so we give it the same priority value,
     so the returned order might have duplicate priority values, and we rely
     on mergesort being stable to keep the order between clauses of the same priority *)
  let n := list_length old_clauses in
  get_order_rec old_clauses new_clauses n.

Ltac is_fresh x := assert_succeeds (pose proof tt as x).

Ltac make_fresh x :=
  tryif is_fresh x then idtac else let x' := fresh x "_0" in rename x into x'.

(* Given an old and a new sep hyp, transfers the order of the sepclauses from the old one
   to the new one *)
Ltac transfer_sep_order_from_to HOld HNew :=
  flatten_seps_in HNew;
  flatten_seps_in HOld;
  lazymatch type of HOld with
  | seps ?old_clauses ?mOld =>
    lazymatch type of HNew with
    | seps ?new_clauses ?mNew =>
      let tmem := type of mNew in
      let E := fresh "E" in
      eassert (@iff1 tmem (seps new_clauses) _) as E;
      [ (* from `seps new_clauses` to `seps (reorder order new_clauses)` *)
        let order := get_order old_clauses new_clauses in
        etransitivity; [
          eapply (reorder_is_iff1 order new_clauses); reflexivity
        |];
        (* from `seps (reorder order new_clauses)` to cbv'd version of it *)
        cbv [reorder];
        let r := eval vm_compute in (order_to_permutation order) in
            change (order_to_permutation order) with r;
        cbv [apply_permutation apply_permutation_with_default my_list_map my_list_nth];
        cbn [seps];
        reflexivity
      | let HNewNew := fresh in pose proof (proj1 (E mNew) HNew) as HNewNew;
        clear E HOld HNew;
        rename HNewNew into HOld;
        try clear mOld;
        (* won't work if mNew or mOld is not a variable *)
        try (make_fresh mOld; rename mNew into mOld) ]
    end
  end.

Ltac transfer_sep_order :=
  lazymatch goal with
  | HOld: sep _ _ _, HNew: sep _ _ _ |- _ =>
      transfer_sep_order_from_to HOld HNew
  end.

Section TestTransferSepsOrder.
  Context {width : Z} {word : Word.Interface.word width} {word_ok: word.ok word}
          {mem : map.map word byte} {mem_ok: map.ok mem}.

  Lemma reordering_test: forall addr1 addr2 addr3 addr4 v1_old v1_new v2 v3 v4 R (m m': mem),
    seps [scalar addr1 v1_old; scalar addr2 v2; scalar addr3 v3; R] m ->
    (* value at addr1 was updated, addr2 was consumed, addr4 was added, and order changed: *)
    seps [R; seps [scalar addr3 v3; scalar addr4 v4]; scalar addr1 v1_new] m' ->
    True ->
    True.
  Proof.
    intros *. intros M M2 ExtraHyp.
    (*            0                    1                2                3
       M  : seps [scalar addr1 v1_old; scalar addr2 v2; scalar addr3 v3; R] m
       M2 : seps [R; seps [scalar addr3 v3; scalar addr4 v4]; scalar addr1 v1_new] m'
       order :=  [3; 2;                     2;                0                  ] *)
    transfer_sep_order_from_to M M2.
    flatten_seps_in M.
    lazymatch type of M with
    | seps [scalar addr1 v1_new; scalar addr3 v3; scalar addr4 v4; R] m =>
        idtac
    end.
  Abort.
End TestTransferSepsOrder.
