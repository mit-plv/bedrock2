Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Cells.Cells.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Definition swap_gallina (c1 c2: cell) :=
    let/n v1 := get c1 in
    let/n v2 := get c2 in
    let/n c1 := put v2 c1 in
    let/n c2 := put v1 c2 in
    (c1, c2).

  Instance spec_of_swap : spec_of "swap" :=
    fnspec! "swap" c1_ptr c2_ptr / c1 c2 R,
    { requires fns tr mem :=
        (cell_value c1_ptr c1 ⋆ cell_value c2_ptr c2 ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        let p := (swap_gallina c1 c2) in
        (cell_value c1_ptr (fst p) ⋆ cell_value c2_ptr (snd p) ⋆ R) mem' }.

  Derive swap_body SuchThat
         (defn! "swap"("c1", "c2") { swap_body },
          implements swap_gallina)
    As swap_body_correct.
  Proof.
    compile.
  Qed.
End with_parameters.

(* Require Import bedrock2.NotationsCustomEntry. *)
(* Require Import bedrock2.NotationsInConstr. *)
(* Arguments swap_body /. *)
(* Eval simpl in swap_body. *)
