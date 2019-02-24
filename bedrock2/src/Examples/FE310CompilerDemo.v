Require Import Coq.ZArith.BinInt.
Require Import bedrock2.Syntax.

(* Require Import riscv.MMIOTrace. *)
(* -*- coq-prog-args: ("-Q" "/home/fiat/plv/bedrock2/deps/riscv-coq/src" "riscv"); -*- *)
Monomorphic Inductive MMIOAction : Set :=
  MMInput : MMIOAction | MMOutput : MMIOAction.


Local Instance syntax_parameters : Syntax.parameters := {|
  varname := Z;
  funname := Empty_set;
  actname := MMIOAction;
|}.

From coqutil.Map Require SortedListWord Z_keyed_SortedListMap Empty_set_keyed_map.
From coqutil Require Word.Interface Word.Naive.
Require Import bedrock2.Semantics.

Local Instance parameters : parameters :=
  let word := Word.Naive.word 32 eq_refl in
  let byte := Word.Naive.word 8 eq_refl in
  {|
  syntax := syntax_parameters;
  mem := SortedListWord.map _ _;
  locals := Z_keyed_SortedListMap.Zkeyed_map _;
  funname_env := Empty_set_keyed_map.map;
  funname_eqb := fun _ _ => true;
  ext_spec t m a args post := False; (* TODO *)
|}.