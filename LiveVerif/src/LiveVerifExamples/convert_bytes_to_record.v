(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

Record bar := {
  barA: Z;
  barB: Z;
  barC: word;
  barPayload: list Z
}.

Definition bar_t(n: N)(b: bar): word -> mem -> Prop := .**/
typedef struct __attribute__ ((__packed__)) {
  uint16_t barA;
  uint16_t barB;
  uintptr_t barC;
  uint32_t barPayload[/**# Z.of_N n #**/];
} bar_t;
/**.

Record foo := {
  foobar_n: Z;
  foobar: bar;
}.

(* Note: parameterized usage of bar_t is not valid C syntax, and variable-size
   bar_t can't be used inside another struct. *)
Definition foo_t(f: foo): word -> mem -> Prop := .**/
typedef struct __attribute__ ((__packed__)) {
  uint32_t foobar_n;
  NOT_C!(bar_t (Z.to_N (foobar_n f))) foobar;
} foo_t;
/**.

#[export] Instance spec_of_swap_barAB: fnspec :=                                .**/

void swap_barAB(uintptr_t p) /**#
  ghost_args := n b (R: mem -> Prop);
  requires t m := <{ * bar_t n b p
                     * R }> m;
  ensures t' m' := t' = t /\
       <{ * bar_t n b{{ barA := barB b; barB := barA b }} p
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
       <{ * foo_t f p
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
