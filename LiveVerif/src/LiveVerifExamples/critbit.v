(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.onesize_malloc.
Require Import coqutil.Datatypes.PropSet.

(* NOTE THAT THIS FILE STILL ALSO CONTAINS MANY THINGS RELATED TO BSTs *)
(* some parts of this file are based on tree_set.v (binary search trees) *)

Inductive tree_skeleton: Set :=
| Leaf
| Node(leftChild rightChild: tree_skeleton).

Definition tree_skeleton_lt(sk1 sk2: tree_skeleton): Prop :=
  match sk2 with
  | Node leftChild rightChild => sk1 = leftChild \/ sk1 = rightChild
  | Leaf => False
  end.

Lemma tree_skeleton_lt_wf: well_founded tree_skeleton_lt.
Proof.
  unfold well_founded. intros sk2.
  induction sk2; eapply Acc_intro; intros sk1 Lt; unfold tree_skeleton_lt in Lt.
  - contradiction.
  - destruct Lt; subst; assumption.
Qed.


#[local] Hint Resolve tree_skeleton_lt_wf: wf_of_type.

Lemma tree_skeleton_lt_l: forall sk1 sk2,
    safe_implication True (tree_skeleton_lt sk1 (Node sk1 sk2)).
Proof. unfold safe_implication, tree_skeleton_lt. intros. auto. Qed.

Lemma tree_skeleton_lt_r: forall sk1 sk2,
    safe_implication True (tree_skeleton_lt sk2 (Node sk1 sk2)).
Proof. unfold safe_implication, tree_skeleton_lt. intros. auto. Qed.

#[local] Hint Resolve tree_skeleton_lt_l tree_skeleton_lt_r : safe_implication.

Load LiveVerif.

Context {consts: malloc_constants}.

Context {word_map: map.map word word}.
Context {word_map_ok: map.ok word_map}.

Definition prefix_bits (n: Z) (w: word) := word.and (word.not (/[-1] ^<< /[n])) w.

Record prefix: Type := {
    length: Z;
    bits: word
  }.

Definition is_prefix (p1 p2: prefix) :=
  p1.(length) <= p2.(length) /\ prefix_bits p1.(length) p1.(bits) = prefix_bits p1.(length) p2.(bits).

Definition canonic_bits (p: prefix) := prefix_bits p.(length) p.(bits).

Definition is_canonic (p: prefix) := canonic_bits p = p.(bits).

Definition bit_at (n: Z) := /[1] ^<< /[n].

Definition append_0 (p: prefix) :=
  {| length := p.(length) + 1;
     bits := canonic_bits p |}.

Definition append_1 (p: prefix) :=
  {| length := p.(length) + 1;
     bits := word.or (canonic_bits p) (bit_at p.(length)) |}.

Definition full_prefix (k: word) := {| length := 32; bits := k |}.

Fixpoint cbt' (sk: tree_skeleton) (p: prefix) (c: word_map) (a: word): mem -> Prop :=
  match sk with
    | Leaf => ex1 (fun k: word => ex1 (fun v: word =>
        <{ * emp (a <> /[0])
           * emp (c = map.singleton k v)
           * emp (p = full_prefix k)
           * <{ + uint 32 (-1)
                + uintptr k
                + uintptr v }> a }>))
  | Node skL skR => ex1 (fun aL: word => ex1 (fun pL: prefix => ex1 (fun cL: word_map =>
     ex1 (fun ix: Z => ex1 (fun aR: word => ex1 (fun pR: prefix => ex1 (fun cR: word_map
          =>
          <{ * emp (a <> /[0])
             * freeable 12 a
             * <{ + uint 32 p.(length)
                  + uintptr aL
                  + uintptr aR }> a
             * cbt' skL pL cL aL
             * cbt' skR pR cR aR
             * emp (0 <= p.(length) <= 31)
             * emp (is_canonic p)
             * emp (is_prefix (append_0 p) pL)
             * emp (is_prefix (append_1 p) pR)
             * emp (map.split c cL cR) }>)))))))
  end.

Definition nncbt (c: word_map) (a: word): mem -> Prop :=
  ex1 (fun sk: tree_skeleton => ex1 (fun p: prefix => cbt' sk p c a)).

(* in full generality, a CBT can be represented as a pointer which is either
   - NULL for an empty CBT, or
   - pointing to the CBT root node *)
Definition cbt (c: word_map) (a: word): mem -> Prop :=
  or1 (nncbt c a) (emp (c = map.empty /\ a = /[0])).

#[export] Instance spec_of_cbt_init: fnspec :=                              .**/

uintptr_t cbt_init( ) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := R m;
  ensures t' m' res := t' = t /\
                       <{ * cbt map.empty res
                          * R }> m' #**/                                   /**.
Derive cbt_init SuchThat (fun_correct! cbt_init) As cbt_init_ok.                .**/
{                                                                          /**. .**/
  return NULL;                                                             /**. .**/
}                                                                          /**.
unfold cbt. exists (map.empty). exists m. step. apply map.split_empty_l.
step. step. right. unfold emp. tauto. tauto.
Qed.


#[local] Hint Extern 1 (cannot_purify (cbt' _ _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (cbt _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (nncbt _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (freeable _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (or1 _ _))
      => constructor : suppressed_warnings.

#[local] Hint Unfold cbt : heapletwise_always_unfold.

#[export] Instance spec_of_dummy: fnspec := .**/
uintptr_t dummy( ) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := True;
                  ensures t' m' res := True #**/ /**. About spec_of_dummy.

Check .**/ void dummy( ) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := True;
                  ensures t' m' := True #**/ /**.

Check spec_of_dummy : Semantics.env -> Prop.
Print spec_of_dummy.

#[export] Instance spec_of_cbt_best_leaf: fnspec :=                             .**/

uintptr_t cbt_best_leaf(uintptr_t tp, uintptr_t k) /**#
  ghost_args := (c: word_map) (R: mem -> Prop);
  requires t m := <{ * nncbt c tp
                     * R }> m;
  ensures t' m' res := t' = t /\ ex1 (fun k' => ex1 (fun v' =>
                  let leaf := cbt' Leaf (full_prefix k') (map.singleton k' v') res in
                        <{ * leaf
                           * wand leaf (nncbt c tp)
                           * emp (k <> k' <-> map.get c k = None)}> )) m' #**/     /**.
Derive cbt_best_leaf SuchThat (fun_correct! cbt_best_leaf) As cbt_best_leaf_ok.  .**/
{                                                                            /**. .**/
  uintptr_t p = tp;                                                            /**.
  loop invariant above Def0. .**/
  while (load32(p) != 0) /* decreases (1) */ {                        /**.
  (* the termination measure should be the tree skeleton. How do we get
     the skeleton out of p? *)
  (* -> ?apply the while rule manually? *)
Abort.

#[export] Instance spec_of_cbt_lookup: fnspec :=                                .**/
(* parameter "d" for "default" *)
uintptr_t cbt_lookup(uintptr_t tp, uintptr_t k, uintptr_t d) /**#
  ghost_args := (c: word_map) (R: mem -> Prop);
  requires t m := <{ * cbt c tp
                     * R }> m;
  ensures t' m' res := t' = t
           /\ <{ * emp (match map.get c k with | Some v => v | None => d end = res)
                 * cbt c tp
                 * R }> m'         #**/                                     /**.
Derive cbt_lookup SuchThat (fun_correct! cbt_lookup) As cbt_lookup_ok.           .**/
{                                                                           /**. .**/
  if (tp == NULL) /* split */ {                                             /**. .**/
    return d;                                                               /**. .**/
  }                                                                         /*?.
  step. step. step. step. step.  destruct H0. destruct H0. destruct H0.
  destruct x; simpl in H0. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. subst c. rewrite map.get_empty. step.
  subst tp. steps.                                                               .**/
  else {                                                                    /**.
  Abort.

#[export] Instance spec_of_cbt_insert: fnspec :=                                  .**/

uintptr_t cbt_insert(uintptr_t tp, uintptr_t k, uintptr_t v) /**#
  ghost_args := (c c': word_map) (R: mem -> Prop);
  requires t m := <{ * cbt c tp
                     * R }> m;
  ensures t' m' res := t' = t
           /\ <{ * emp (map.put c k v = c') (* should this really be equality? *)
                 * cbt c' res
                 * R }> m'        #**/                                      /**.
Derive cbt_insert SuchThat (fun_correct! cbt_insert) As cbt_insert_ok.
(* TODO: implement & prove *)
Abort.

End LiveVerif. Comments .**/ //.
