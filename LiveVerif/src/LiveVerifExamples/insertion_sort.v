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

(* Insertion function for insertion sort *)
(* insert(p, n, i) assumes A[0..(i-1)] is sorted and try to insert A[i],
   so ultimately A[0..i] is sorted. *)

#[export] Instance spec_of_real_insert: fnspec :=                                   .**/
void real_insert(uintptr_t p, uintptr_t i) /**#
  ghost_args := (R: mem -> Prop) (l1 : list Z) (x : Z);
  requires t m := sep (array (uint 32) (\[i]+1) (sort l1 ++ [|x|]) p) R m;
  ensures t' m' := t' = t /\
                   sep (array (uint 32) (\[i]+1) (sort (l1 ++ [|x|])) p) R m'
            #**/ /**.
Parameter real_insert : function_with_callees.
Parameter real_insert_ok : program_logic_goal_for "real_insert" real_insert.

#[export] Instance spec_of_insert: fnspec :=                                   .**/
void insert(uintptr_t p, uintptr_t n, uintptr_t i) /**#
  ghost_args := (R: mem -> Prop) (l1 l2 : list Z) (x : Z);
  requires t m := len (sort l1) = \[i] /\
                sep (array (uint 32) \[n] ((sort l1 ++ [|x|]) ++ l2) p) R m;
  ensures t' m' := t' = t /\
                   sep (array (uint 32) \[n] (sort (l1 ++ [|x|]) ++ l2) p) R m' /\
                   len (sort (l1 ++ [|x|])) = \[i]+1
            #**/ /**.
Derive insert SuchThat (fun_correct! insert) As insert_ok.
.**/ { /**.
  assert (len (sort l1 ++ [|x|]) = \[i]+1) by (rewrite List.len_app; simpl; ZnWords).
  assert (len l2 = \[n]-\[i]-1).
  {
    unfold with_mem, array in H0.
    step.
    step.
    rewrite List.len_app in H3.
    ZnWords.
  }
  assert ((sort l1 ++ [|x|])[:\[i] + 1] = (sort l1 ++ [|x|])).
  { rewrite List.upto_pastend. reflexivity. ZnWords. }

  .**/ real_insert(p, i); /**.
  instantiate (1 := x) in H5.
  instantiate (1 := l1) in H5.
.**/ } /**.
congruence.
Qed.

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
  assert (0 <= \[i] <= \[n]) by ZnWords.
  assert (len arr = \[n]-\[i]) as lenArrR by hwlia.
  assert (len (sort nil) = \[i]) as lenArrL by
      (bottom_up_simpl_in_goal; rewrite sort_nil; auto).
  replace arr with ((sort nil) ++ arr) in H1 by
    (rewrite sort_nil;
    rewrite List.app_nil_l;
    auto).

  (* assign some names so we can generalize *)
  set (arrL := nil) in * |-;
  set (arrR := arr) in * |-;
  assert (arr = arrL ++ arrR) as HarrSplit by (subst arrL arrR; auto).

  (* generalize *)
  loop invariant above arrL;
  clearbody i arrL arrR.

  .**/ while (i < n) /* decreases (n ^- i) */ { /**.

    (* claim: if we're in the loop, the array is not empty,
       so we can pull an element *)
    destruct arrR as [ | x arrR' ].
    { simpl in *; exfalso; ZnWords. }

    (* structure it so we can call insert *)
    rewrite List.assoc_app_cons in *.

    .**/ insert(p,n,i); /**.
    { (* Note: not proven automatically because evars are not yet determined
         when this equality is encountered. *)
      assumption. }

    .**/ i = i+1; /**.
    assert (len arrR' = \[n]-\[i]). {
      purify_heapletwise_hyps.
      rewrite ? List.len_app in *.
      rewrite <- ? sort_preserves_length in *.
      rewrite ? List.len_app in *.
      rewrite <- ? sort_preserves_length in *.
      ZnWords.
    }

  (* at this point we can now close the loop *)
  (* because the lengths of left side and right side have been established *)
  .**/ } /**. end while.

(* at the end of the loop now. arrR should be empty. *)
  assert (len arrR = 0) by ZnWords.
  assert (arrR = nil) by (destruct arrR; try discriminate; auto).
  subst.

(* close the function *)
.**/ } /**.
Qed.

End LiveVerif. Comments .**/ //.
