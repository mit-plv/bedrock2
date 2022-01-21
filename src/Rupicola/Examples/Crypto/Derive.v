Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Crypto.Low.
Require Import bedrock2.BasicC32Semantics.

Section Bedrock2.
  
  Instance spec_of_quarter : spec_of "quarter" :=
    fnspec! "quarter" (a b c d : word) ~> (a' b' c' d' : word),
    { requires tr mem := True;
      ensures tr' mem' :=
        tr = tr' /\
        mem = mem' /\
        let '\<w, x, y, z\> := quarter a b c d in
        (a' = w /\ b' = x /\ c' = y /\ d' = z)}.

  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context {mem: map.map word Byte.byte} {locals: map.map String.string word}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env: map.map string (list string * list string * cmd)}.

  Derive quarter_body SuchThat
         (defn! "quarter" ("a", "b", "c", "d") ~> "a", "b", "c", "d" { quarter_body },
          implements (quarter) using [])
         As quarter_body_correct.
  Proof.
    compile.
  Qed.

End Bedrock2.
