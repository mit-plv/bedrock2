(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

Record bar_t := {
  barA: Z;
  barB: Z;
  barC: word;
  barPayload: list Z
}.
Arguments bar_t: clear implicits.

Definition bar(n: N)(b: bar_t): word -> mem -> Prop := record!
  (cons (mk_record_field_description barA (uint 16))
  (cons (mk_record_field_description barB (uint 16))
  (cons (mk_record_field_description barC uintptr)
  (cons (mk_record_field_description barPayload (array (uint 32) (Z.of_N n))) nil)))).

Record foo_t := {
  foobar_n: Z;
  foobar: bar_t;
}.

Definition foo(f: foo_t): word -> mem -> Prop := record!
  (cons (mk_record_field_description foobar_n (uint 32))
  (cons (mk_record_field_description foobar (bar (Z.to_N (foobar_n f)))) nil)).

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
  uintptr_t tmp = load16(p+2);                                             /**. .**/
  store16(p+2, load16(p));                                                 /**. .**/
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
