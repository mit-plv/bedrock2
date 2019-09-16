Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.

Open Scope Z_scope.

Section Change.

  Context {syntax : Syntax.parameters}
          {varname_eqb : Syntax.varname -> Syntax.varname -> bool}
          {funname_eqb : Syntax.funname -> Syntax.funname -> bool}
          {actname_eqb : Syntax.actname -> Syntax.actname -> bool}
          {width : BinNums.Z}
          (wordA : word width)
          (wordB : word width)
          (byteA : word 8)
          (byteB : word 8)
          (memA : map.map wordA byteA)
          (memB : map.map wordB byteB)
          (localsA: map.map Syntax.varname wordA)
          (localsB: map.map Syntax.varname wordB)
          {funname_env : forall T : Type, map.map Syntax.funname T}.

  Let traceA := list (memA * Syntax.actname * list wordA * (memA * list wordA)).
  Let traceB := list (memB * Syntax.actname * list wordB * (memB * list wordB)).

  Let ExtSpecA := traceA -> memA -> Syntax.actname -> list wordA ->
                  (memA -> list wordA -> Prop) -> Prop.
  Let ExtSpecB := traceB -> memB -> Syntax.actname -> list wordB ->
                  (memB -> list wordB -> Prop) -> Prop.

  Context {ext_specA : ExtSpecA}
          {ext_specB : ExtSpecB}.

  Instance p1: parameters := {
    Semantics.syntax := syntax;
    Semantics.varname_eqb := varname_eqb;
    Semantics.funname_eqb := funname_eqb;
    Semantics.actname_eqb := actname_eqb;
    Semantics.width := width;
    Semantics.word := wordA;
    Semantics.byte := byteA;
    Semantics.mem := memA;
    Semantics.locals := localsA;
    Semantics.funname_env := funname_env;
    Semantics.ext_spec := ext_specA;
  }.

  Instance p2: parameters := {
    Semantics.syntax := syntax;
    Semantics.varname_eqb := varname_eqb;
    Semantics.funname_eqb := funname_eqb;
    Semantics.actname_eqb := actname_eqb;
    Semantics.width := width;
    Semantics.word := wordB;
    Semantics.byte := byteB;
    Semantics.mem := memB;
    Semantics.locals := localsB;
    Semantics.funname_env := funname_env;
    Semantics.ext_spec := ext_specB;
  }.

  (* will need too many conversion functions/relations, don't do this, but generalize
     program logic proofs to abstract word instance
  Lemma change_params: exec
  *)
End Change.
