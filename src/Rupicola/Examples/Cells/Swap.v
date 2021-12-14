Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Cells.Cells.

Section with_parameters.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Definition swap_gallina (c1 c2: cell) :=
    let/n v1 := get c1 in
    let/n v2 := get c2 in
    let/n c1 := put v2 in
    let/n c2 := put v1 in
    (c1, c2).

  Instance spec_of_swap : spec_of "swap" :=
    fnspec! "swap" c1_ptr c2_ptr / c1 c2 R,
    { requires tr mem :=
        (cell_value c1_ptr c1 ⋆ cell_value c2_ptr c2 ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        let p := (swap_gallina c1 c2) in
        (cell_value c1_ptr (fst p) ⋆ cell_value c2_ptr (snd p) ⋆ R) mem' }.

  Derive swap_br2fn SuchThat
         (defn! "swap"("c1", "c2") { swap_br2fn },
          implements swap_gallina)
    As swap_br2fn_ok.
  Proof.
    compile.
  Qed.
End with_parameters.

From bedrock2 Require Import BasicC64Semantics NotationsCustomEntry.
Compute swap_br2fn. (* (word := word) *)
