Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import coqutil.Map.SortedList.
Require coqutil.Map.SortedListString.
Require Import bedrock2.ZNamesSyntax.
Require Import coqutil.Word.Naive riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import coqutil.Map.Empty_set_keyed_map.
Require Import coqutil.Map.Z_keyed_SortedListMap.


Instance Basic32Syntax: bedrock2.Syntax.parameters := {|
  Syntax.varname := Z;
  Syntax.funname := String.string;
  Syntax.actname := String.string;
|}.

Instance Basic32Semantics: bedrock2.Semantics.parameters := {|
  Semantics.syntax := Basic32Syntax;
  Semantics.width := 32;
  Semantics.word := word32;
  Semantics.byte := word8;
  Semantics.locals := _;
  Semantics.funname_env := coqutil.Map.SortedListString.map;
  Semantics.funname_eqb := String.eqb;
  Semantics.mem := Mem;
  Semantics.ext_spec _ _ _ _ _ := False;
|}.
