Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Cells.Cells.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Definition incr_gallina (c: cell) :=
    let/n v := get c in
    let/n one := word.of_Z 1 in
    let/n v := word.add v one in
    let/n c := put v c in
    c.

  Instance spec_of_incr : spec_of "incr" :=
    fnspec! "incr" (c_ptr : address) / (c : cell) R,
    { requires fns tr mem :=
        (cell_value c_ptr c ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\ (cell_value c_ptr (incr_gallina c) ⋆ R) mem' }.

  Derive incr_body SuchThat
         (defn! "incr"("c") { incr_body },
          implements incr_gallina)
         As incr_body_correct.
  Proof.
    compile.
  Qed.
End with_parameters.

(* Require Import bedrock2.NotationsCustomEntry. *)
(* Require Import bedrock2.NotationsInConstr. *)
(* Arguments body /. *)
(* Eval simpl in body. *)
