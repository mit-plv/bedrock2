(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)

Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.fwd.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.Lists.List.
Require Import coqutil.Datatypes.ZList.
Import List.ZIndexNotations. Local Open Scope zlist_scope.

Section List_TODO_move.
  Context [A: Type].

  Lemma NoDup_singleton: forall (a: A), NoDup (cons a nil).
  Proof. intros; repeat constructor. intro C. inversion C. Qed.
End List_TODO_move.

Section ZList_TODO_move.
  Context [A: Type].

  Section MapWithIndex.
    Context [B: Type] (f: Z -> A -> B).
    Fixpoint map_with_index_from(start: Z)(l: list A): list B :=
      match l with
      | nil => nil
      | cons h t => cons (f start h) (map_with_index_from (start+1) t)
      end.

    Definition map_with_index: list A -> list B := map_with_index_from 0.
  End MapWithIndex.

End ZList_TODO_move.

Section LexicographicListOrder.
  Context [A: Type] (comp: A -> A -> comparison).

  Fixpoint lexicographic(l1 l2: list A): comparison :=
    match l1, l2 with
    | nil, nil => Eq
    | nil, cons _ _  => Lt
    | cons _ _ , nil => Gt
    | cons h1 t1, cons h2 t2 =>
        match comp h1 h2 with
        | Eq => lexicographic t1 t2
        | ne => ne
        end
    end.
End LexicographicListOrder.

Section PropSet_TODO_move. Local Set Default Proof Using "All".
  Context {E: Type}.

  Definition size(s: set E)(n: Z): Prop :=
    exists l, NoDup l /\ sameset s (of_list l) /\ len l = n.

  Lemma singleton_size: forall (e: E), size (singleton_set e) 1.
  Proof.
    intros. unfold size, singleton_set.
    exists [|e|]. ssplit.
    - apply NoDup_singleton.
    - unfold sameset, subset, of_list, elem_of.
      split; intros.
      + subst. constructor. reflexivity.
      + inversion H. 1: assumption. inversion H0.
    - reflexivity.
  Qed.

  Lemma size_eq: forall (s1 s2: set E) (sz: Z), s1 = s2 -> size s1 sz -> size s2 sz.
  Proof. intros. subst. assumption. Qed.

  Import PropExtensionality FunctionalExtensionality.
  Lemma sameset_ext: forall (s1 s2: set E), sameset s1 s2 -> s1 = s2.
  Proof.
    unfold elem_of, sameset, subset.
    intros. extensionality y. apply propositional_extensionality.
    split; intros; apply H; assumption.
  Qed.

  Lemma set_ext: forall (s1 s2: set E), (forall x, s1 x <-> s2 x) -> s1 = s2.
  Proof. intros. eapply sameset_ext. eapply sameset_iff. assumption. Qed.

  Lemma invert_size_0: forall (s: set E), size s 0 -> s = empty_set.
  Proof.
    unfold size. intros. fwd. destruct l. 2: discriminate.
    eapply sameset_ext in Hp1. assumption.
  Qed.

  Lemma size_empty_set: size empty_set 0.
  Proof. unfold size. exists nil. ssplit; try reflexivity. constructor. Qed.

  Definition map_set[R: Type](f: E -> R)(s: set E): set R :=
    fun r => exists e, f e = r.

End PropSet_TODO_move.

Definition queen: Type := Z * Z.

Definition row: queen -> Z := fun '(r, _) => r.
Definition col: queen -> Z := fun '(_, c) => c.
Definition ascDiag q := row q - col q.
Definition descDiag q := row q + col q.

Definition noConfl(f: queen -> Z)(qs: set queen) :=
  forall q1 q2, q1 \in qs -> q2 \in qs -> q1 <> q2 -> f q1 <> f q2.

Definition noConfls(qs: set queen) :=
  noConfl row qs /\ noConfl col qs /\ noConfl ascDiag qs /\ noConfl descDiag qs.

Definition board(nRows nCols: Z): set queen :=
  fun q => 0 <= row q < nRows /\ 0 <= col q < nCols.

Definition validConfigs(nRows nCols: Z): set (set queen) :=
  fun qs => noConfls qs /\ subset qs (board nRows nCols) /\ size qs nRows.

Definition queensSpec(nRows nCols result: Z) :=
  size (validConfigs nRows nCols) result.

Lemma noConfl_empty_set f: noConfl f empty_set.
Proof. unfold noConfl, empty_set, elem_of. intros. contradiction. Qed.

Lemma noConfls_empty_set: noConfls empty_set.
Proof. unfold noConfls. eauto using noConfl_empty_set. Qed.

Lemma queensSpec_base: forall nCols, queensSpec 0 nCols 1.
Proof.
  intros.
  unfold queensSpec.
  eapply (size_eq (singleton_set empty_set)). 2: eapply singleton_size.
  eapply set_ext.
  unfold elem_of, singleton_set, validConfigs. split; intros.
  - subst. eauto using noConfls_empty_set, subset_empty_l, size_empty_set.
  - fwd. eapply invert_size_0 in Hp2. congruence.
Qed.

Definition cols_to_set(cols: list Z): set queen := of_list (map_with_index pair cols).

Definition allLt(bound: list Z): set (list Z) :=
  fun cols => lexicographic Z.compare cols bound = Lt.

Require Import LiveVerif.LiveVerifLib. Load LiveVerif.

#[export] Instance spec_of_nqueens: fnspec :=                                   .**/

uintptr_t nqueens(uintptr_t n, uintptr_t buf) /**#
  ghost_args := (R: mem -> Prop) grb;
  requires t m := 0 < \[n] < 32 /\
                  <{ * array (uint 32) \[n] grb buf
                     * R }> m;
  ensures t' m' r := queensSpec \[n] \[n] \[r] /\ t' = t /\ exists grb',
            <{ * array (uint 32) \[n] grb' buf
               * R }> m' #**/                                              /**.
Derive nqueens SuchThat (fun_correct! nqueens) As nqueens_ok.                   .**/
{                                                                          /**. .**/
  uintptr_t res = 1;                                                       /**. .**/
  uintptr_t row = 0;                                                       /**.

  pose (exploredUpto := @nil Z).
  swap grb with (exploredUpto ++ grb) in #(array (uint 32)). 1: reflexivity.
  assert (size (intersect (validConfigs \[n] \[n])
                          (map_set cols_to_set (allLt exploredUpto))) \[res]). {
    admit.
  }
  clearbody exploredUpto.

(*
  available columns, ascending/descending diagonals
  avCols, avAsc, avDesc

  backtrack until intersection becomes nonempty


  assert (queensSpec \[row] \[n] \[res]). {
    bottom_up_simpl_in_goal. eapply queensSpec_base.
  }
  assert (0 <= \[row] < \[n]) by steps.
  delete #(res = ??).
  delete #(row = ??).
  loop invariant above res.
                                                                                .**/
  while (row < n) /* decreases (\[n] - \[row]) */ {                        /**. .**/
*)

(* bugs/mis-specifications avoided while coding:
   - what if n=0? (0 <= \[row] < \[n]) didn't hold
 *)

Abort.

End LiveVerif. Comments .**/ //.
