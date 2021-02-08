Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Cells.Cells.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Definition swap_gallina_spec (c1 c2: cell) :=
    let/n v1 := get c1 in
    let/n v2 := get c2 in
    let/n c1 := put v2 c1 in
    let/n c2 := put v1 c2 in
    (c1, c2).

  Derive swap_body SuchThat
         (let swap := ("swap", (["c1"; "c2"], [], swap_body)) in
          program_logic_goal_for swap
          (forall functions,
           forall c1_ptr c1 c2_ptr c2 tr R mem,
             sep (TwoCells c1_ptr c2_ptr (c1, c2) []) R mem ->
             WeakestPrecondition.call
               (swap :: functions)
               "swap"
               tr mem [c1_ptr; c2_ptr]
               (postcondition_func_norets
                  (TwoCells c1_ptr c2_ptr (swap_gallina_spec c1 c2))
                  R tr)))
    As swap_body_correct.
  Proof.
    compile.
  Qed.
End with_parameters.

(* Require Import bedrock2.NotationsCustomEntry. *)
(* Require Import bedrock2.NotationsInConstr. *)
(* Arguments swap_body /. *)
(* Eval simpl in swap_body. *)
