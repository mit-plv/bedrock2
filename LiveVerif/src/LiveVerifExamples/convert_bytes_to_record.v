(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

(* TODO can/should we use Z for n? But then, how to carry 0<=n hypothesis around? *)
Record bar_t{n: N} := {
  barA: uint_t 16;
  barB: uint_t 16;
  barC: word;
  barPayload: array_t (uint_t 32) (Z.of_N n);
}.
Arguments bar_t: clear implicits.

Instance bar(n: N): RepPredicate (bar_t n) := ltac:(create_predicate).

Record foo_t := {
  foobar_n: uint_t 32;
  foobar: bar_t (Z.to_N foobar_n);
}.

Instance foo: RepPredicate foo_t := ltac:(create_predicate).

#[export] Instance spec_of_swap_barAB: fnspec :=                                .**/

void swap_barAB(uintptr_t p) /**#
  ghost_args := n b (R: mem -> Prop);
  requires t m := <{ * bar n b p
                     * R }> m;
  ensures t' m' := t' = t /\
       <{ * bar n b{{ barA := barB b; barB := barA b }} p
          * R }> m' #**/                                                   /**.
Derive swap_barAB SuchThat (fun_correct! swap_barAB) As swap_barAB_ok.          .**/
{                                                                          /**. .**/
  uintptr_t tmp = load16(p+2);                                             /**.

Ltac run_steps_hook ::= idtac.

 .**/
  store16(p+2, load16(p));                                                 /**.

(* TODO: add markers that trigger simpl_hook once before solving preconditions,
   and once after the call (around the wp_cmd) *)
step. step. step. step. step. step. step. step. step. step. step. step.
(* here: precondition solving of store, first run simpl_hook *)
(* bottom_up_simpl_in_goal. already done in step *)
step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
(* here: step runs simpl_hook *)
step. step. step. step. step.

Ltac run_steps_hook ::= run_steps.                                              .**/
  store16(p, tmp);                                                         /**. .**/
}                                                                          /**.
reflexivity.
Qed.

#[export] Instance spec_of_init_foo: fnspec :=                                  .**/

void init_foo(uintptr_t p, uintptr_t barPayloadLen) /**#
  ghost_args := bs (R: mem -> Prop);
  requires t m := <{ * array (uint 8) (12 + 4 * \[barPayloadLen]) bs p
                     * R }> m;
  ensures t' m' := t' = t /\ exists f, f.(foobar_n) = \[barPayloadLen] /\
       <{ * foo f p
          * R }> m' #**/                                                   /**.
Derive init_foo SuchThat (fun_correct! init_foo) As init_foo_ok.                .**/
{                                                                          /**. .**/
  store32(p, barPayloadLen);                                               /**.

(* TODO first implement modifying a byte array with stores/loads/calls *)

(*
ltac1:(
lazymatch goal with
| |- foobar_n ?e = _ =>
    let t := type of e in
    lazymatch open_constr:(ltac:(econstructor) : t) with
    | ?c => instantiate (1 := c)
    end
end
*)
Abort.

End LiveVerif. Comments .**/ //.
