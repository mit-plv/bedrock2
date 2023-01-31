(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

Record bar_t(n: Z) := {
  barA: uint_t 16;
  barB: uint_t 16;
  barC: word;
  barPayload: array_t (uint_t 32) n;
}.

Instance bar(n: uint_t 32): RepPredicate (bar_t n) := ltac:(create_predicate).

Record foo_t := {
  foobar_n: uint_t 32;
  foobar: bar_t foobar_n;
}.

Instance foo: RepPredicate foo_t := ltac:(create_predicate).

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
