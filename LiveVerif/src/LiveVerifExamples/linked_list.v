Require Import LiveVerif.LiveVerifLib.
Require Import coqutil.Tactics.syntactic_unify.
Require Import Lia.

Load LiveVerif.

(* TODO support functions that don't access any memory *)
Definition dummy: mem -> Prop := emp True.

Record node_t := {
  data: word;
  next: word;
}.
Instance node: RepPredicate node_t := ltac:(create_predicate).

#[export] Instance spec_of_malloc: fnspec :=                         .**/
uintptr_t malloc(uintptr_t size)                                     /**#
  ghost_args := (R: mem -> Prop);
  requires t m := sep dummy R m;
  ensures t' m' retPtr := t' = t /\ exists anyData,
       <{ * array uintptr \[size] anyData retPtr
          * R }> m'                                                   #**/ /**.
Parameter malloc : function_with_callees.
Parameter malloc_ok : program_logic_goal_for "malloc" malloc.


#[export] Instance spec_of_malloc_node: fnspec :=                    .**/
uintptr_t malloc_node(uintptr_t x, uintptr_t y)                                 /**#
  ghost_args := (R: mem -> Prop);
  requires t m := sep dummy R m;
  (* ensures t' m' retPtr := t' = t /\
                          <{ * ex1 (fun x => node x retPtr)
                             * R }> m                               #**/ /**. *)
  ensures t' m' retPtr := t' = t /\ exists x,
                          <{ * node x retPtr
                             * R }> m'                               #**/ /**.
Derive malloc_node SuchThat (fun_correct! malloc_node) As malloc_node_ok. .**/
{ /**. .**/
  uintptr_t r = malloc(2);   /**.

  unfold array in *.
  unfold with_mem in *.  (* TODO: can't this be automatically done in step? *)
  step.
  step.
  bottom_up_simpl_in_hyps.
  match goal with
  | H: len ?l = ?n |- _ =>
      let H' := fresh "Hlen" in
      rename H into H'
  end.
  destruct anyData; [discriminate Hlen | idtac].
  destruct anyData; [discriminate Hlen | idtac].
  destruct anyData; [idtac | simpl in Hlen; lia].
  simpl in H4.
  unfold with_mem in *.
  step.
  step.
  change (m2 |= R) in H2.
  .**/ return r; /**.

  unfold node.
  unfold sepapps.
  simpl.
  unfold sepapp.
 .**/
} /**.
  instantiate (1 := {| data := _; next := _ |}).
  all: reflexivity.
Qed.

(*
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
  requires t m := <{ * sll L p
                     * R }> m;
  ensures t' m' res := t' = t /\
       <{ * sll (val::L) res
          * R }> m' #**/ /**.
Derive sll_prepend SuchThat (fun_correct! sll_prepend) As sll_prepend_ok. .**/
{ /**. .**/
  uintptr_t r = 0; /**. .**/
  if (p == 0) { /**. .**/
    r = malloc_node();           /**. .**/
  } else { /**. .**/
    r = 0; /**. .**/
  } /**. .**/
  return r; /**. .**/
} /**.
Qed. *)

End LiveVerif. Comments .**/ //.
