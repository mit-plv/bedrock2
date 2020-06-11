Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Cells.Cells.

Section with_semantics.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Definition incr_gallina_spec (c: cell) :=
    let/d v := get c in
    let/d one := word.of_Z 1 in
    let/d v := word.add v one in
    let/d c := put v c in
    c.

  Derive body SuchThat
         (let swap := ("swap", (["c"], [], body)) in
          program_logic_goal_for swap
          (forall functions,
           forall c_ptr c tr R mem,
             seps [cell_value c_ptr c; R] mem ->
             WeakestPrecondition.call
               (swap :: functions)
               "swap"
               tr mem [c_ptr]
               (postcondition_for (cell_value c_ptr (incr_gallina_spec c)) R tr (fun r => r = nil))))
    As body_correct.
  Proof.
    compile.
  Qed.

End with_semantics.
