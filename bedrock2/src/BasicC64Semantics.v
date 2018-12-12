Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.BasicC64Syntax bedrock2.Semantics.
Require bedrock2.String bedrock2.Map.SortedList bedrock2.Map.SortedListString.
Require Import coqutil.Word.Interface.
Require coqutil.Word.Naive.

Definition TODO{T: Type}: T. Admitted.

Instance parameters : parameters :=
  let word := Word.Naive.word 64 (proj2 (Zlt_is_lt_bool 0 64) eq_refl) in
  let byte := Word.Naive.word 8 (proj2 (Zlt_is_lt_bool 0 8) eq_refl) in
  {|
  syntax := StringNamesSyntax.make BasicC64Syntax.StringNames_params;
  Semantics.word := word;
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
  Semantics.byte := byte;
  mem := SortedList.map (SortedList.parameters.Build_parameters word byte word.eqb word.ltu);
  locals := SortedListString.map _;
  env := TODO;
  funname_eqb := String.eqb;
  ext_spec := TODO;
|}.
Existing Instance Word.Naive.ok.
