Require Import bedrock2.BasicC64Syntax bedrock2.Semantics.
Require bedrock2.String.
Require bbv.Word.

Instance parameters : parameters := {|
  syntax := StringNames.Syntax.make BasicC64Syntax.parameters;
  word := Word.word 64;
  word_zero := Word.wzero 64;
  word_succ := Word.wplus (Word.wone 64);
  word_test w := if Word.weq (Word.wzero 64) w then false else true;
  word_of_Z w := Some (Word.ZToWord 64 w);
  interp_binop := _;
  byte := Word.word 8;
  combine _ b w := Word.wor (Word.wlshift' w 8) (Word.zext b (64-8));
  split _ w := (Word.split1 8 (64-8) w, Word.zext (Word.split2 8 (64-8) w) 8);
  mem := _;
  locals := _;
  funname_eqb := String.eqb;
|}.
Admitted.