Require Import coqutil.Sorting.Permutation.
Require Import LiveVerif.LiveVerifLib.
Require Import List Lia.

Load LiveVerif.

(* Any implementation of `sort` works as long as it is correct. *)
(* Specifications copied from SF Vol 3 (VFA). *)
Inductive sorted : list Z -> Prop :=
| sorted_nil :
    sorted nil
| sorted_1 : forall x,
    sorted [| x |]
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).
Parameter sort : list Z -> list Z.
Axiom sort_sorted : forall l l', sort l = l' -> sorted l'.
Axiom sort_perm : forall l l', sort l = l' -> Permutation l l'.
Axiom sort_nil : sort (@nil Z) = (@nil Z).
Axiom sort_preserves_length : forall l, len l = len (sort l).
Axiom sort_app_preserves_length : forall l1 l2,
  len (sort (l1 ++ l2)) = len (sort l1) + len (sort l2).

Axiom sort_can_split : forall l l1 l2,
  sorted l -> l = l1++l2 -> sorted l1 /\ sorted l2.
Axiom sort_can_split' : forall l l1 l2,
  sort l = l1++l2 -> sort l = sort l1 ++ sort l2.

(* Insertion function for insertion sort *)
(* insert(p, n, i) assumes A[0..(i-1)] is sorted and try to insert A[i],
   so ultimately A[0..i] is sorted. *)
#[export] Instance spec_of_insert: fnspec :=                                   .**/
void insert(uintptr_t p, uintptr_t n, uintptr_t i) /**#
  ghost_args := (R: mem -> Prop) (l1 l2 : list Z) (x : Z);
  requires t m := len (sort l1) = \[i] /\
                sep (array (uint 32) \[n] ((sort l1 ++ [|x|]) ++ l2) p) R m;
  ensures t' m' := t' = t /\
                   sep (array (uint 32) \[n] (sort (l1 ++ [|x|]) ++ l2) p) R m' /\
                   len (sort (l1 ++ [|x|])) = \[i]+1
            #**/ /**.

Parameter insert : function_with_callees.
Parameter insert_ok : program_logic_goal_for "insert" insert.

(* Derive insert SuchThat (fun_correct! insert) As insert_ok.
.**/ { /**.
  .**/ uintptr_t j = i; /**.
  rewrite <- sort_nil in H2.
  ltac1:(set (arrL := (sort l1)) in H2).
  ltac1:(set (arrR := (sort nil)) in H2).
  assert (sort l1 = arrL ++ arrR).
  { subst arrL arrR. rewrite sort_nil. rewrite List.app_nil_r. auto. }
  assert (len arrL = \[j]).
  { ltac1:(bottom_up_simpl_in_goal). assumption. }
  assert (len arrR = \[i]-\[j]).
  { ltac1:(bottom_up_simpl_in_goal). subst arrR. rewrite sort_nil. auto. }
  assert (Forall (fun v => x < v) arrR).
  { subst arrR. rewrite sort_nil. auto. }

  ltac1:(loop invariant above arrL).
  Std.clearbody [ @j; @arrL; @arrR ].
  rewrite List.assoc_app_cons in H2.

  .**/ while (j > 0 && load32(p+j-1) > load32(p+j))  /* decreases j */ { /**.

  .**/ } /**.

  (* after this loop, we'll know that x fits right in between *)
  (* therefore sort arrL ++ [|x|] ++ arrR should be sorted. *)
Qed. *)


(* Insertion sort *)
#[export] Instance spec_of_insertion_sort: fnspec :=                                   .**/
void insertion_sort(uintptr_t p, uintptr_t n) /**#
  ghost_args := (R: mem -> Prop) (arr : list Z);
  requires t m := sep (array (uint 32) \[n] arr p) R m;
  ensures t' m' := t' = t /\ 
            sep (array (uint 32) \[n] (sort arr) p) R m' #**/ /**.
Derive insertion_sort SuchThat (fun_correct! insertion_sort) As insertion_sort_ok.
(* open function *)
.**/ { /**.

  .**/ uintptr_t i = 0; /**.

  (* invariants - true at the beginning of the loop *)
  assert (0 <= \[i] <= \[n]) by ltac1:(ZnWords).
  assert (len arr = \[n]-\[i]) as lenArrR by
    ltac1:(bottom_up_simpl_sidecond_hook).
  assert (len (sort nil) = \[i]) as lenArrL by (
    ltac1:(bottom_up_simpl_in_goal);
    rewrite sort_nil; auto).
  ltac1:(replace arr with ((sort nil) ++ arr) in H1 by
    (rewrite sort_nil;
    rewrite List.app_nil_l;
    auto)).

  (* assign some names so we can generalize *)
  ltac1:(set (arrL := nil) in * |-);
  ltac1:(set (arrR := arr) in * |-);
  assert (arr = arrL ++ arrR) as HarrSplit by (subst arrL arrR; auto).

  (* generalize *)
  ltac1:(loop invariant above arrL);
  Std.clearbody [ @i; @arrL; @arrR ].

  .**/ while (i < n) /* decreases (n ^- i) */ { /**.

    (* target goal 1 only *) {

    (* claim: if we're in the loop, the array is not empty,
       so we can pull an element *)
    destruct arrR as [ | x arrR' ].
    { simpl in *; ltac1:(exfalso; ZnWords). }

    (* structure it so we can call insert *)
    rewrite List.assoc_app_cons in *.
    .**/ insert(p,n,i); /**.
    { assumption. }

    .**/ i = i+1; /**.
    assert (len arrR' = \[n]-\[i]) by (
      rewrite ? List.len_app in *;
      rewrite <- ? sort_preserves_length in *;
      rewrite ? List.len_app in *;
      rewrite <- ? sort_preserves_length in *;
      ltac1:(ZnWords)).

  (* at this point we can now close the loop *)
  (* because the lengths of left side and right side have been established *)
  .**/ } /**.

(* close goal 1 *) }

(* at the end of the loop now. arrR should be empty. *)
  assert (len arrR = 0) by ltac1:(ZnWords).
  assert (arrR = nil) by (destruct arrR; try discriminate; auto).
  subst.

(* close the function *)
.**/ } /**.
Qed.

End LiveVerif. Comments .**/ //.
