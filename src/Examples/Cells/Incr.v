Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Cells.Cells.
Local Infix "~>" := cell_value.

Section with_semantics.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Definition incr_gallina_spec (c: cell) :=
    let/d v := get c in
    let/d one := word.of_Z 1 in
    let/d v := word.add v one in
    let/d c := put v c in
    c.

  Instance spec_of_incr : spec_of "incr" :=
    (forall! (c_ptr : address) (c :cell),
        (sep (c_ptr ~> c))
          ===>
          "incr" @ [c_ptr]
          ===>
          (OneCell c_ptr (incr_gallina_spec c))).

  Derive body SuchThat
         (let incr := ("incr", (["c_ptr"], [], body)) in
          program_logic_goal_for
            incr
            (ltac:(let x := program_logic_goal_for_function
                              incr (@nil string) in
                   exact x)))
         As body_correct.
  Proof.
    cbv [spec_of_incr].
    compile.
  Qed.

End with_semantics.
