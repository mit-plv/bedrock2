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

Lemma iff1_refl{A: Type}(P: A -> Prop): iff1 P P. Proof. reflexivity. Qed.
Lemma iff1_sym{A: Type}{P Q: A -> Prop}: iff1 P Q -> iff1 Q P.
Proof. intros. symmetry. assumption. Qed.

Ltac iff1_syntactic_reflexivity :=
  lazymatch goal with
  | |- iff1 ?x ?y => first [is_evar x | is_evar y | constr_eq x y]
  end;
  exact (iff1_refl _).

Ltac impl1_syntactic_reflexivity :=
  lazymatch goal with
  | |- impl1 ?x ?y => first [is_evar x | is_evar y | constr_eq x y]
  end;
  exact impl1_refl.

Ltac clause_index clause clauses start_index default_index :=
  lazymatch clauses with
  | cons (sepcl _ _ ?a) ?tail =>
    lazymatch clause with
    | sepcl _ _ a => constr:(start_index)
    | _ => clause_index clause tail (S start_index) default_index
    end
  | cons clause _ => constr:(start_index)
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

(* Given `H: seplogformula m`, first cbns away all occurrences of `seps` in H,
   and then flattens the formula into a list of sep clauses, resulting in an
   `H: seps [...] m` *)
Ltac flatten_seps_in H :=
  lazymatch type of H with
  | ?nested ?m =>
    let tmem := type of m in
    let E := fresh "E" in
    eassert (@iff1 tmem nested _) as E;
    [ (* from `nested` to `Tree.to_sep tree` *)
      let stars := eval cbn[seps] in nested in
      let tree := reify stars in
      transitivity (Tree.to_sep tree); [
        cbn [seps Tree.to_sep Tree.interp]; iff1_syntactic_reflexivity
      |];
      (* from `Tree.to_sep tree` to `seps (Tree.flatten tree)` *)
      transitivity (seps (Tree.flatten tree)); [
        exact (iff1_sym (Tree.flatten_iff1_to_sep tree))
      |];
      (* from `seps (Tree.flatten tree)` to `seps clauses` *)
      cbn [SeparationLogic.Tree.flatten SeparationLogic.Tree.interp SeparationLogic.app];
      iff1_syntactic_reflexivity
    | let HNew := fresh in pose proof (proj1 (E m) H) as HNew;
      move HNew before H;
      clear E H;
      rename HNew into H ]
  end.

(* Given an old and a new sep hyp, transfers the order of the sepclauses from the old one
   to the new one *)
Ltac transfer_sep_order_from_to HOld HNew :=
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
  let mNew := lazymatch goal with mNew: @map.rep (@word.rep _ _) _ _ |- _ => mNew end in
  lazymatch goal with
  | HOld: seps _ ?mOld, HNew: _ mNew |- _ =>
      flatten_seps_in HNew;
      transfer_sep_order_from_to HOld HNew
  end.

Section TestTransferSepsOrder.
  Context {width : Z} {word : Word.Interface.word width} {word_ok: word.ok word}
          {mem : map.map word byte} {mem_ok: map.ok mem}.

  Lemma reordering_test: forall addr1 addr2 addr3 addr4 v1_old v1_new v2 v3 v4 R (m m': mem),
    seps [addr1 :-> v1_old : scalar; addr2 :-> v2 : scalar; addr3 :-> v3 : scalar; R] m ->
    (* value at addr1 was updated, addr2 was consumed, addr4 was added, and order changed: *)
    seps [R; seps [addr3 :-> v3 : scalar; addr4 :-> v4 : scalar];
          addr1 :-> v1_new : scalar] m' ->
    True ->
    True.
  Proof.
    intros *. intros M M2 ExtraHyp.
    (*            0                        1                    2                    3
       M  : seps [addr1 |-> scalar v1_old; addr2 |-> scalar v2; addr3 |-> scalar v3; R] m0
       M2 : seps [R; addr3 |-> scalar v3; addr4 |-> scalar v4; addr1 |-> scalar v1_new] m1
       order :=  [3; 2;                   2;                   0                      ] *)
    flatten_seps_in M2.
    transfer_sep_order_from_to M M2.
    lazymatch type of M with
    | seps [addr1 :-> v1_new : scalar; addr3 :-> v3 : scalar; addr4 :-> v4 : scalar; R] m =>
        idtac
    end.
  Abort.
End TestTransferSepsOrder.
