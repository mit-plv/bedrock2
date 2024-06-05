(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

Record baz := {
  bazA: Z;
  bazB: Z;
  bazC: word;
}.

Definition baz_t(b: baz): word -> mem -> Prop := .**/
typedef struct __attribute__ ((__packed__)) {
  uint16_t bazA;
  uint16_t bazB;
  uintptr_t bazC;
} baz_t;
/**.

Record bar := {
  barA: Z;
  barB: Z;
  barC: word;
  barPayload: list Z
}.

Definition bar_t(n: Z)(b: bar): word -> mem -> Prop := .**/
typedef struct __attribute__ ((__packed__)) {
  uint16_t barA;
  uint16_t barB;
  uintptr_t barC;
  uint32_t barPayload[/**# n #**/];
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
  NOT_C!(bar_t (foobar_n f)) foobar;
} foo_t;
/**.

Local Hint Extern 1 (cannot_purify (bar_t _ _ _))
      => constructor : suppressed_warnings.

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
subst tmp. bottom_up_simpl_in_goal. reflexivity.
Qed.


#[export] Instance spec_of_init_baz: fnspec :=                                  .**/

void init_baz(uintptr_t p, uintptr_t bazPayloadLen) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * array (uint 8) 8 ? p
                     * R }> m;
  ensures t' m' := t' = t /\
       <{ * baz_t ? p
          * R }> m' #**/                                                   /**.
Derive init_baz SuchThat (fun_correct! init_baz) As init_baz_ok.                .**/
{                                                                          /**. .**/
}                                                                          /**.
Qed.


#[export] Instance spec_of_init_sepapps: fnspec :=                              .**/

void init_sepapps(uintptr_t p, uintptr_t sepappsPayloadLen) /**#
  ghost_args := bs (R: mem -> Prop);
  requires t m := <{ * array (uint 8) 8 bs p
                     * R }> m;
  ensures t' m' := t' = t /\ exists v1 v2 v3,
       <{ * <{ + uint 16 v1
               + uint 16 v2
               + uintptr v3 }> p
          * R }> m' #**/                                                   /**.
Derive init_sepapps SuchThat (fun_correct! init_sepapps) As init_sepapps_ok.    .**/
{                                                                          /**. .**/
}                                                                          /*?.
  step. step. step.
  (* stop before the existentials get turned into evars! *)
  unfold sepapps. simpl. unfold sepapp.
  enough (<{ * uint 16 ? p
             * uint 16 ? (p ^+ /[2])
             * uintptr ? (p ^+ /[2] ^+ /[2])
             * R }> m).
  { unfold anyval in *. steps. }
  steps.
Qed.


#[export] Instance spec_of_init_bar: fnspec :=                                  .**/

void init_bar(uintptr_t p, uintptr_t barPayloadLen) /**#
  ghost_args := bs (R: mem -> Prop);
  requires t m := <{ * array (uint 8) (8 + 4 * \[barPayloadLen]) bs p
                     * R }> m;
  ensures t' m' := t' = t /\
       <{ * bar_t \[barPayloadLen] ? p
          * R }> m' #**/                                                   /**.
Derive init_bar SuchThat (fun_correct! init_bar) As init_bar_ok.                .**/
{                                                                          /**. .**/
}                                                                          /**.
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
