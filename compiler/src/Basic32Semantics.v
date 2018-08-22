Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.Map.UnorderedList.
Require Import compiler.NamesInstance.
Require Import compiler.Op.
Require Import riscv.MachineWidth32.
Require bbv.Word.

Instance Basic32Semantics: Semantics_parameters := {|
  syntax := compiler.NamesInstance.Names;
  word := Word.word 32;
  interp_binop bop := eval_binop bop;

  (* unused: *)
  word_zero := Word.wzero 32;
  word_succ := Word.wplus (Word.wone 32);
  word_test w := if Word.weq (Word.wzero 32) w then false else true;
  word_of_Z w := Some (Word.ZToWord 32 w);
  byte := Word.word 8;
  combine _ b w := Word.wor (Word.wlshift' w 8) (Word.zext b (32-8));
  split _ w := (Word.split1 8 (32-8) w, Word.zext (Word.split2 8 (32-8) w) 8);
  mem := UnorderedList.map {| UnorderedList.key_eqb a b := if Word.weq a b then true else false |};
  locals := UnorderedList.map {| UnorderedList.key_eqb := Z.eqb |};
  funname_eqb := Z.eqb;
|}.
