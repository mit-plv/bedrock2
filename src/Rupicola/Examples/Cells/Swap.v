Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Cells.Cells.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

Definition swap_gallina_spec (c1 c2: cell) :=
  let/d v1 := get c1 in
  let/d v2 := get c2 in
  let/d c1 := put v2 c1 in
  let/d c2 := put v1 c2 in
  (c1, c2).

Derive swap_body SuchThat
       (let swap := ("swap", (["a"; "b"], [], swap_body)) in
        program_logic_goal_for swap
        (forall functions,
         forall a_ptr a b_ptr b tr R mem,
           sep (TwoCells a_ptr b_ptr (a,b) []) R mem ->
           WeakestPrecondition.call
             (swap :: functions)
             "swap"
             tr mem [a_ptr;b_ptr]
             (postcondition_func_norets
                (TwoCells a_ptr b_ptr (swap_gallina_spec a b))
                R tr)))
  As swap_body_correct.
Proof.
  compile.
Qed.
End with_parameters.
