(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib. Load LiveVerif.

(* BEGIN EXAMPLE 1 *)

#[export] Instance spec_of_f_if_postcondition: fnspec :=                        .**/
void f_if_postcondition (uintptr_t p) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * uintptr /[42] p
                     * R }> m;
  ensures t' m' := t' = t
            /\ <{ * (if \[p] <? 12345 then uintptr /[42] p else uintptr /[42] p)
                  * R }> m' #**/                                            /**.
Derive f_if_postcondition SuchThat (fun_correct! f_if_postcondition)
  As f_if_postcondition_ok.                                                .**/
{                                                                          /**. .**/
}                                                                          /**.
  destruct (\[p] <? 12345); steps.
Qed.

#[export] Instance spec_of_caller1: fnspec :=                                   .**/
void caller1 (uintptr_t p) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * uintptr /[42] p
                     * R }> m;
  ensures t' m' := t' = t /\ <{ * uintptr /[42] p
                                * R }> m' #**/                             /**.
Derive caller1 SuchThat (fun_correct! caller1) As caller1_ok.                   .**/
{                                                                          /**. .**/
  uintptr_t local_before = load(p);                                        /**. .**/
  f_if_postcondition(p);                                                   /**.
  (* Old heaplets still in the context:

    H0 : m0 |= uintptr /[42] p

    ...
  *) .**/
  uintptr_t local_after = load(p);                                         /*?.
  (* ... so infinite loop when processing `steps` now. *)
  step. step. step. step. step. step. step. step. step. step. step. step.
Abort.

(* END EXAMPLE 1 *)
(* BEGIN EXAMPLE 2 *)

Definition two_ints v addr := <{ + uintptr v + uintptr v }> addr.

Lemma purify_two_ints: forall v addr, purify (two_ints v addr) True.
Proof.
  unfold purify. tauto.
Qed.

Hint Resolve purify_two_ints : purify.

#[export] Instance spec_of_packer: fnspec :=                   .**/
void packer (uintptr_t p) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * uintptr /[42] p * uintptr /[42] (p ^+ /[4])
                     * R }> m;
  ensures t' m' := t' = t
            /\ <{ * two_ints /[42] p
                  * R }> m' #**/                                            /**.
Derive packer SuchThat (fun_correct! packer)
  As packer_ok.                                                .**/
{                                                                          /**. .**/
}                                                                          /*?.
  unfold two_ints. steps.
Qed.

Opaque two_ints.

#[export] Instance spec_of_caller2: fnspec :=                                            .**/
void caller2 (uintptr_t p) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * uintptr /[42] p
                     * uintptr /[42] (p ^+ /[4])
                     * R }> m;
  ensures t' m' := t' = t /\ <{ * uintptr /[42] p
                                * uintptr /[42] (p ^+ /[4])
                                * R }> m' #**/                             /**.
Derive caller2 SuchThat (fun_correct! caller2) As caller2_ok.                   .**/
{                                                                          /**. .**/
  uintptr_t local_before = load(p);                                        /**. .**/
  packer(p);                                                               /**.
  (* Old heaplets still in the context:

    H0 : m0 |= uintptr /[42] p
    H2 : m2 |= uintptr /[42] (p ^+ /[4])

    ...
  *) .**/
  uintptr_t local_after = load(p);                                         /*?.
  (* ... so infinite loop when processing `steps` now. *)
  step. step. step. step. step. step. step. step. step. step. step. step.
Abort.

(* END EXAMPLE 2 *)

End LiveVerif. Comments .**/ //.
