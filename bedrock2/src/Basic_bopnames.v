Require Import Coq.ZArith.BinInt.
Require Import coqutil.Word.Interface.
Require bedrock2.Syntax.
Require bedrock2.BasicALU.

Module Import bopname.
  Inductive bopname := add | sub | mul | and | or | xor | sru | slu | srs | lts | ltu | eq.
End bopname.
Notation bopname := bopname.bopname.

Local Set Primitive Projections.
Class parameters := {
  varname: Type;
  funcname: Type;
  actname: Type;
}.

Instance make (p: parameters) : Syntax.parameters := {|
  Syntax.varname := @varname p;
  Syntax.funname := @funcname p;
  Syntax.actname := @actname p;
  Syntax.bopname := bopname;
|}.

Instance BasicALU{p: parameters}: BasicALU.operations :=
  BasicALU.Build_operations _ add sub mul and or xor sru slu srs lts ltu eq.

Section WithWord.
  Context {width : Z} {word : word width}.
  Definition interp_binop (bop : bopname) : word -> word -> word :=
    match bop with
    | bopname.add => word.add
    | bopname.sub => word.sub
    | bopname.mul => word.mul
    | bopname.and => word.and
    | bopname.or => word.or
    | bopname.xor => word.xor
    | bopname.sru => word.sru
    | bopname.slu => word.slu
    | bopname.srs => word.srs
    | bopname.lts => fun a b =>
      if word.lts a b then word.of_Z 1 else word.of_Z 0
    | bopname.ltu => fun a b =>
      if word.ltu a b then word.of_Z 1 else word.of_Z 0
    | bopname.eq => fun a b =>
      if word.eqb a b then word.of_Z 1 else word.of_Z 0
    end.
End WithWord.
