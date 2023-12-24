(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

#[export] Instance spec_of_pass_two: fnspec :=                                  .**/

void pass_two(uintptr_t src) /**#
  ghost_args := (R: mem -> Prop) (w1 w2: word);
  requires t m := <{ * <{ + uintptr w1 + uintptr w2 }> src
                     * R }> m;
  ensures t' m' := t' = t /\ <{ * <{ + uintptr w1 + uintptr w2 }> src
                                * R }> m'    #**/                          /**.
Derive pass_two SuchThat (fun_correct! pass_two) As pass_two_ok.                .**/
{                                                                          /**. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_copy_two: fnspec :=                                  .**/

void copy_two(uintptr_t dst, uintptr_t src) /**#
  ghost_args := (R: mem -> Prop) (w1 w2: word);
  requires t m := <{ * <{ + uintptr w1 + uintptr w2 }> src
                     * (EX u1 u2, <{ + uintptr u1 + uintptr u2 }> dst)
                     * R }> m;
  ensures t' m' := t' = t /\
                  <{ * <{ + uintptr w1 + uintptr w2 }> src
                     * <{ + uintptr w1 + uintptr w2 }> dst
                     * R }> m' #**/                                        /**.
Derive copy_two SuchThat (fun_correct! copy_two) As copy_two_ok.                .**/
{                                                                          /**. .**/
  store(dst, load(src));                                                   /**. .**/
  store(dst + 4, load(src + 4));                                           /**. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_main: fnspec :=                                      .**/

void main( ) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * <{ + uintptr /[3] + uintptr /[7] }> /[40000]
                     * <{ + uintptr /[103] + uintptr /[107] }> /[50000]
                     * R }>m;
  ensures t' m' := True #**/                                               /**.
Derive main SuchThat (fun_correct! main) As main_ok.                            .**/
{                                                                          /**. .**/
  (* the point of this file is HERE:
     after processing the function call below, I would expect (and wish) to
     have 3 heaplets: one with sepapps with values 3 and 7 at addr 40000
                      one with sepapps with values 3 and 7 at addr 50000
                      one with R
     instead, I get those 3 but also two more of the form `<{ + hole 4 + hole 4 }>`
     and 4 `merge_step` hypotheses

     replacing `copy_two(50000, 40000);` with `pass_two(40000);` leads to a
     very similar effect

     motivation: I want(ed) to do have such a copy function (possibly combined with
     allocation of a new node) for the sepapps in my CBT nodes *)

  copy_two(50000, 40000);                                                  /**.
(*

processing the `Admitted.` below causes

Error:
Backtrace:

Backtrace:

Anomaly "in Lemmas.save_lemma_admitted: more than one statement."
Please report at http://coq.inria.fr/bugs/.

(vvvvvvv that one; using `Abort.` instead works)

Admitted.

*)
Abort.


End LiveVerif. Comments .**/ //.
