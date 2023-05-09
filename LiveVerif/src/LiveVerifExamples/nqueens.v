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

Definition noConfl(r1 c1 r2 c2: Z) :=
  r1 <> r2 /\ c1 <> c2 /\ r1 - c1 <> r2 - c2 /\ r1 + c1 <> r2 + c2.

Definition noConfls(qcols: list Z) :=
  forall r1 r2, 0 <= r1 -> r1 < r2 -> r2 < len qcols -> noConfl r1 qcols[r1] r2 qcols[r2].

Definition colsBounded(nCols: Z)(qcols: list Z) :=
  forall r, 0 <= r < len qcols -> 0 <= qcols[r] < nCols.

Definition partialSol(nRows nCols: Z)(qcols: list Z) :=
  len qcols = nRows /\
  noConfls qcols /\
  colsBounded nCols qcols.

Definition isSol(n: Z): list Z -> Prop := partialSol n n.

Require Import LiveVerif.LiveVerifLib. Load LiveVerif.

#[export] Instance spec_of_nqueens: fnspec :=                                   .**/

uintptr_t find_nqueens_sol(uintptr_t n, uintptr_t sol) /**#
  ghost_args := (R: mem -> Prop) grb;
  requires t m := 0 < \[n] < 32 /\
                  <{ * array (uint 8) \[n] grb sol
                     * R }> m;
  ensures t' m' r := t' = t /\ exists qcols,
            <{ * array (uint 8) \[n] qcols sol
               * R }> m' /\
            (r <> /[0] /\ isSol \[n] qcols \/
             r = /[0] /\ forall qcols, ~ isSol \[n] qcols) #**/            /**.
Derive find_nqueens_sol SuchThat (fun_correct! find_nqueens_sol)
  As find_nqueens_sol_ok.                                                       .**/
{                                                                          /**. .**/
  uintptr_t depth = 0;                                                     /**. .**/
  uintptr_t explored = 0;                                                  /**.

(*
  // TODO must not forget any bits when lshifting beyond 32 or rshifting beyond 0

  depth := 1 // length of current search branch
  sol[0] := 0
  explored := repeat false n
  avCols := {1..n-1}
  usedAsc := {0}
  usedDesc := {0}
  while 0 < depth && depth < n:
    if explored[depth]: // fully explored for current sol[depth], go to sibling or parent
      c := sol[depth]
      usedAsc := usedAsc - {c}
      usedDesc := usedDesc - {c}
      avCols := avCols + {c}
      match minElemAbove c avCols with // go to sibling
      | Some s =>
        avCols := avCols - {s}
        usedAsc := usedAsc + {s}
        usedDesc := usedDesc + {s}
        sol[depth] := s
        explored[depth] := false
      | None => // go to parent
        depth--
        explored[depth] := true
        usedAsc := decrAll(usedAsc)
        usedDesc := incrAll(usedDesc)
      end
    else: // go to child
      match minElem avCols with
      | Some s
      c := minElem avCols
      avCols := avCols + {c}
      usedAsc := incrAll(usedAsc) + {c}
      usedDesc := decrall(usedDesc) + {c}

  return depth == n // depth back to 0 means nothing found, depth n means found


  TODO termination?

*)
Abort.

End LiveVerif. Comments .**/ //.
