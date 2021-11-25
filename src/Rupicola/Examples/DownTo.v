Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Lib.ControlFlow.DownTo.

Section Gallina.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.

  Definition popcount (w: word) :=
    (* This code is here to demonstrate Rupicola features, not for speed (!) *)
    let/n ones := 0 in
    let/n (w, ones) := downto \< w, ones \> 64 (fun w_ones _ =>
      let '\< w, ones \> := w_ones in
      let/n ones := if word.eqb (word.and w (word.of_Z 1))
                               (word.of_Z 1)
                   then ones + 1 else ones in
      let/n w := word.sru w (word.of_Z 1) in
      \< w, ones \>) in
    ones.
End Gallina.

Section Compilation.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Instance spec_of_popcount : spec_of "popcount" :=
    fnspec! "popcount" (w: word) / (R: mem -> Prop) ~> c,
    { requires tr mem :=
        R mem;
      ensures tr' mem' :=
        tr' = tr /\ R mem' /\ c = word.of_Z (popcount w) }.

  Import DownToCompiler.

  Lemma fits64 : Z.of_nat 64 < 2 ^ width.
  Proof. destruct width_cases; subst; reflexivity. Qed.

  Hint Resolve fits64 : compiler_side_conditions.

  Derive popcount_br2fn SuchThat
         (defn! "popcount"("w") ~> "ones" { popcount_br2fn },
          implements (popcount (word := word)))
         As popcount_correct.
  Proof.
    compile.
  Qed.
End Compilation.
