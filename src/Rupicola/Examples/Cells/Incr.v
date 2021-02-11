Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Cells.Cells.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Definition incr_gallina_spec (c: cell) :=
    let/n v := get c in
    let/n one := word.of_Z 1 in
    let/n v := word.add v one in
    let/n c := put v c in
    c.

  Instance spec_of_incr : spec_of "incr" :=
    (forall! (c_ptr : address) (c :cell),
        (sep (cell_value c_ptr c))
          ===>
          "incr" @ [c_ptr]
          ===>
          (OneCell c_ptr (incr_gallina_spec c))).

  Derive body SuchThat
         (let incr := ("incr", (["c"], [], body)) in
          program_logic_goal_for
            incr
            (ltac:(let x := program_logic_goal_for_function
                             incr (@nil string) in
                   exact x)))
         As body_correct.
  Proof.
    compile.
  Qed.
End with_parameters.

(* Require Import bedrock2.NotationsCustomEntry. *)
(* Require Import bedrock2.NotationsInConstr. *)
(* Arguments body /. *)
(* Eval simpl in body. *)
