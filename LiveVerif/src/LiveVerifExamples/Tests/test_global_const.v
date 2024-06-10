(* -*- eval: (load-file "../../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Class my_consts: Set := {
  foo_const: Z;
}.

Definition other_const: Z := 42.

Load LiveVerif.

Context (section_var_const: Z).
Context (consts: my_consts).

#[export] Instance spec_of_test_global_const: fnspec :=                         .**/

uintptr_t test_global_const(uintptr_t px, uintptr_t py) /**#
  ghost_args := (R: mem -> Prop) x y;
  requires t m := <{ * uint 32 x px
                     * uint 32 y py
                     * R }> m;
  ensures t' m' retv := t' = t /\
            <{ * uint 32 x px
               * uint 32 y py
               * R }> m' #**/                                              /**.
Derive test_global_const SuchThat (fun_correct! test_global_const)
  As test_global_const_ok.                                                      .**/
{                                                                          /**. .**/
  uintptr_t a = 2 + other_const;                                           /**. .**/
  a = a + foo_const + section_var_const;                                   /**.

  Set Printing Implicit.

  assert_fails ( .**/  a = x;  /** ).
  (* cannot instantiate "?c" because "x" is not in its scope *)

  .**/ return a; /**.

  .**/ } /**.
Qed.

End LiveVerif.

(*
Open Scope string_scope.
Print test_global_const.
*)

Comments .**/ //.
