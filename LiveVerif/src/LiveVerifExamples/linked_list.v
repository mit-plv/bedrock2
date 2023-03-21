Require Import LiveVerif.LiveVerifLib.
Require Import coqutil.Tactics.syntactic_unify.
Require Import Lia.

Load LiveVerif.

(* TODO support functions that don't access any memory *)
Definition dummy: mem -> Prop := emp True.

Record node := {
  data: word;
  next: word;
}.
Definition node_t(r: node): word -> mem -> Prop := .**/
typedef struct __attribute__ ((__packed__)) {
  uintptr_t data;
  uintptr_t next;
} node_t;
/**.

#[export] Instance spec_of_malloc: fnspec :=                         .**/
uintptr_t malloc(uintptr_t size)                                     /**#
  ghost_args := (R: mem -> Prop);
  requires t m := sep dummy R m;
  ensures t' m' retPtr := t' = t /\ exists anyData,
       <{ * dummy
          * array uintptr \[size] anyData retPtr
          * R }> m'                                                   #**/ /**.
Parameter malloc : function_with_callees.
Parameter malloc_ok : program_logic_goal_for "malloc" malloc.


#[export] Instance spec_of_malloc_node: fnspec :=                    .**/
uintptr_t malloc_node(uintptr_t anything)                                 /**#
  ghost_args := (R: mem -> Prop);
  requires t m := sep dummy R m;
  (* ensures t' m' retPtr := t' = t /\
                          <{ * ex1 (fun x => node x retPtr)
                             * R }> m                               #**/ /**. *)
  ensures t' m' retPtr := t' = t /\ exists x,
                          <{ * dummy
                             * node_t x retPtr
                             * R }> m'                               #**/ /**.
Derive malloc_node SuchThat (fun_correct! malloc_node) As malloc_node_ok. .**/
{ /**. .**/
  uintptr_t r = malloc(2);   /**.
  assert (len anyData = 2) as Hlen by hwlia.

  destruct anyData; [discriminate Hlen | idtac].
  destruct anyData; [discriminate Hlen | idtac].
  destruct anyData; [idtac | simpl in Hlen; lia].

  .**/ return r; /**.
.**/ } /**.

  unfold node_t.
  unfold sepapps.
  simpl.
  unfold sepapp.
  (* TODO: automated memory cast *)
  instantiate (1 := {| data := r0; next := r1 |}).
  unfold array.
  simpl.
  eapply iff1ToEq. cancel.
  unfold seps. unfold iff1. unfold emp. intuition.
Qed.


Fixpoint sll (L : list word) (p : word): mem -> Prop :=
  match L with
  | nil => emp (p = /[0])
  | x::L' => ex1 (fun (q:word) =>
      <{ * uintptr x p
         * uintptr q (p ^+ /[4])
         * sll L' q }>)
  end.

Lemma purify_sll:
  forall L p,
    purify (sll L p) (True).
Proof.
  unfold purify. auto.
Qed.
Hint Resolve purify_sll : purify.

#[export] Instance spec_of_sll_prepend: fnspec := .**/

uintptr_t sll_prepend(uintptr_t p, uintptr_t val) /**#
  ghost_args := (L : list word) (R: mem -> Prop);
  requires t m := <{ * dummy
                     * sll L p
                     * R }> m;
  ensures t' m' res := t' = t /\
       <{ * dummy
          * sll (val::L) res
          * R }> m' #**/ /**.
Derive sll_prepend SuchThat (fun_correct! sll_prepend) As sll_prepend_ok. .**/
{ /**.
  (* TODO: a lot of dummys *)
  (* TODO: should support empty arguments *)
  .**/ uintptr_t r = malloc_node(-123); /**.
  (* set r.data = val *)
  .**/ store(r, val); /**.
  .**/ store(r+4, p); /**.
  .**/ return r; /**.
  (* TODO: all of this should probably be automated *)
  replace ((m4 \*/ (m2 \*/ m3)) \*/ m) with (m \*/ m2 \*/ m3 \*/ m4) in D by admit.
  assert (exists (mm2:mem), m \*/ m2 = mm2) as Hex by admit.
  destruct Hex as [mm2 Hex]. rewrite Hex in D. clear Hex.
  assert (mm2 |= sll (val :: L) r) by admit.
.**/ } /**.
Abort.

End LiveVerif. Comments .**/ //.
