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

  Definition incr_gallina (c: cell) :=
    let/n v := get c in
    let/n one := word.of_Z 1 in
    let/n v := word.add v one in
    let/n c := put v in
    c.

  Instance spec_of_incr : spec_of "incr" :=
    fnspec! "incr" (c_ptr : word) / (c : cell) R,
    { requires tr mem :=
        (cell_value c_ptr c ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\ (cell_value c_ptr (incr_gallina c) ⋆ R) mem' }.

  Derive incr_br2fn SuchThat
         (defn! "incr"("c") { incr_br2fn },
          implements incr_gallina)
         As incr_br2fn_ok.
  Proof.
    compile.
  Qed.
End with_parameters.

From bedrock2 Require Import BasicC64Semantics NotationsCustomEntry.
Compute incr_br2fn (word := word).
