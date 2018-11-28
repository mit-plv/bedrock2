Require Import Coq.NArith.BinNatDef.
Require Import bedrock2.BasicC64Syntax bedrock2.Semantics.
Require bedrock2.String bedrock2.Map.SortedList bedrock2.Map.SortedListString.
Require Import bedrock2.Word. Require bedrock2.Word.Naive.
Import ZArith.

Instance parameters : parameters :=
  let word := Word.Naive.word 64 (proj2 (Zlt_is_lt_bool 0 64) eq_refl) in
  let byte := Word.Naive.word 8 (proj2 (Zlt_is_lt_bool 0 8) eq_refl) in
  {|
  syntax := StringNamesSyntax.make BasicC64Syntax.StringNames_params;
  Semantics.word := word;
  word_zero := word.of_Z 0;
  word_succ := word.add (word.of_Z 1);
  word_test w := if word.eqb (word.of_Z 0) w then false else true;
  word_of_Z w := Some (word.of_Z w);
  interp_binop bop :=
    match bop with
    | bopname.add => word.add
    | bopname.sub => word.sub
    | bopname.mul => word.mul
    | bopname.and => word.and
    | bopname.or  => word.or
    | bopname.xor => word.xor
    | bopname.sru => word.sru
    | bopname.slu => word.slu
    | bopname.srs => word.srs
    | bopname.ltu => fun a b => if word.ltu a b then word.of_Z 1 else word.of_Z 0
    | bopname.lts => fun a b => if word.lts a b then word.of_Z 1 else word.of_Z 0
    | bopname.eq => fun a b => if word.eqb a b then word.of_Z 1 else word.of_Z 0
    end;
  (* TODO: bedrock2.Byte, bedrock2.Word8 *)
  byte := byte;
  mem := SortedList.map (SortedList.parameters.Build_parameters word byte word.eqb word.ltu);
  combine _ b w := word.or (word.slu w (word.of_Z 8)) (word.of_Z (word.unsigned b));
  split _ w := (word.of_Z (word.unsigned w), word.slu w (word.of_Z 8));
  locals := SortedListString.map _;
  funname_eqb := String.eqb;
|}.
Existing Instance Word.Naive.ok.