Require Import PyLevelLang.Language.
Require bedrock2.Syntax.
Require Import coqutil.Datatypes.Result.
Import ResultMonadNotations.

Definition compile_atom {t : type} (a : atom t) : result Syntax.expr :=
  match a with
  | AInt n => Success (Syntax.expr.literal n)
  | ABool b => Success (Syntax.expr.literal (Z.b2z b))
  | AString _ | ANil _ | AEmpty => error:("unimplemented")
  end.

Definition compile_unop {t1 t2 : type} (o : unop t1 t2) :
  result (Syntax.expr -> Syntax.expr) :=
  match o with
  | ONeg =>
      Success (Syntax.expr.op Syntax.bopname.sub (Syntax.expr.literal 0))
  | ONot =>
      Success (Syntax.expr.op Syntax.bopname.sub (Syntax.expr.literal 0))
  | OLength _
  | OLengthString
  | OFst _ _ _
  | OSnd _ _ _ =>
      error:("unimplemented")
  end.

Definition compile_binop {t1 t2 t3 : type} (o : binop t1 t2 t3) :
  result (Syntax.expr -> Syntax.expr -> Syntax.expr) :=
  match o with
  | OPlus =>
      Success (Syntax.expr.op Syntax.bopname.add)
  | OMinus =>
      Success (Syntax.expr.op Syntax.bopname.sub)
  | OTimes =>
      Success (Syntax.expr.op Syntax.bopname.mul)
  | ODiv =>
      Success (Syntax.expr.op Syntax.bopname.divu)
      (* FIXME *)
  | OMod =>
      Success (Syntax.expr.op Syntax.bopname.remu)
      (* FIXME *)
  | OAnd =>
      Success (Syntax.expr.op Syntax.bopname.and)
  | OOr =>
      Success (Syntax.expr.op Syntax.bopname.or)
  | OConcat _
  | OConcatString =>
      error:("unimplemented")
  | OLess =>
      Success (Syntax.expr.op Syntax.bopname.ltu)
      (* FIXME *)
  | OEq _ H =>
      Success (Syntax.expr.op Syntax.bopname.eq)
  | ORepeat _
  | OPair _ _ _
  | OCons _
  | ORange =>
      error:("unimplemented")
  end.

Fixpoint compile_expr {t : type} (e : expr t) : result Syntax.expr :=
  match e with
  | EAtom a => compile_atom a
  | EUnop o e1 =>
      f <- compile_unop o;;
      e1' <- compile_expr e1;;
      Success (f e1')
  | EBinop o e1 e2 =>
      f <- compile_binop o;;
      e1' <- compile_expr e1;;
      e2' <- compile_expr e2;;
      Success (f e1' e2')
  | _ => error:("unimplemented")
  end.

Compute (compile_expr (EAtom (AInt 4))).
Compute (compile_expr (EAtom (ABool true))).
Compute (compile_expr (EAtom (ABool false))).
Compute (compile_expr (EBinop OOr (EAtom (ABool true)) (EAtom (ABool false)))).
Compute (compile_expr (EBinop OPlus (EAtom (AInt 1)) (EAtom (AInt 1)))).
