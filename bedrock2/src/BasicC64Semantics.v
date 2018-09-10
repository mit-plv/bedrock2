Require Import Coq.NArith.BinNatDef.
Require Import bedrock2.BasicC64Syntax bedrock2.Semantics.
Require bedrock2.String bedrock2.Map.UnorderedList.
Require bbv.Word.

Local Definition shiftWidth s := Word.wordToNat (Word.wand s (Word.NToWord 64 63)).
Instance parameters : parameters := {|
  syntax := StringNamesSyntax.make BasicC64Syntax.params;
  word := Word.word 64;
  word_zero := Word.wzero 64;
  word_succ := Word.wplus (Word.wone 64);
  word_test w := if Word.weq (Word.wzero 64) w then false else true;
  word_of_Z w := Some (Word.ZToWord 64 w);
  interp_binop bop :=
    match bop with
    | bopname.add => @Word.wplus _
    | bopname.sub => @Word.wminus _
    | bopname.mul => @Word.wmult _
    | bopname.and => @Word.wand _
    | bopname.or => @Word.wor _
    | bopname.xor => @Word.wxor _
    | bopname.sru => fun w s => Word.wrshift' w (shiftWidth s)
    | bopname.slu => fun w s => Word.wlshift' w (shiftWidth s)
    | bopname.srs => fun w s => Word.wrshifta' w (shiftWidth s)
    | bopname.ltu => fun a b => if Word.wltb a b then Word.wone 64 else Word.wzero 64
    | bopname.lts => fun a b => if Word.wsltb a b then Word.wone 64 else Word.wzero 64
    | bopname.eq => fun a b => if Word.weq a b then Word.wone 64 else Word.wzero 64
    end;
  (* TODO: bedrock2.Byte, bedrock2.Word8 *)
  byte := Word.word 8;
  combine _ b w := Word.wor (Word.wlshift' w 8) (Word.zext b (64-8));
  split _ w := (Word.split1 8 (64-8) w, Word.zext (Word.split2 8 (64-8) w) 8);
  (* TODO: faster maps *)
  mem := UnorderedList.map {| UnorderedList.key_eqb a b := if Word.weq a b then true else false |};
  locals := UnorderedList.map {| UnorderedList.key_eqb := String.eqb |};
  globname_eqb := String.eqb;
|}.
