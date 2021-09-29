(* constraints on FlatImp ASTs, referenced by several phases *)
Require Import compiler.FlatImp.
Require Import compiler.Registers.
Require Import Coq.ZArith.ZArith.

Fixpoint uses_standard_arg_regs(s: stmt Z): Prop :=
  match s with
  | SLoad _ _ _ _
  | SStore _ _ _ _
  | SInlinetable _ _ _ _
  | SLit _ _
  | SSkip
  | SOp _ _ _ _
  | SSet _ _
    => True
  | SStackalloc _ _ body
    => uses_standard_arg_regs body
  | SLoop s1 _ s2
  | SSeq s1 s2
  | SIf _ s1 s2
    => uses_standard_arg_regs s1 /\ uses_standard_arg_regs s2
  | SCall binds _ args
  | SInteract binds _ args
    => binds = List.firstn (List.length binds) (reg_class.all reg_class.arg) /\
       args = List.firstn (List.length args) (reg_class.all reg_class.arg)
  end.
