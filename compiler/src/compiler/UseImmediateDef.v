Require Import compiler.util.Common.
Require Import compiler.FlatImp.
From Coq Require Import List. Import ListNotations.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.fwd.
Require Import String.
Open Scope Z_scope.

Local Notation var := String.string (only parsing).

Section WithArgs.
  Context (is5BitImmediate : Z -> bool).
  Context (is12BitImmediate: Z -> bool).

  Context {env: map.map String.string (list var * list var * stmt var)}.

  Fixpoint useImmediate(s: stmt string) : stmt string :=
    match s with
    | SIf c s1 s2 => SIf c (useImmediate s1) (useImmediate s2)
    | SLoop s1 c s2 => SLoop (useImmediate s1) c (useImmediate s2)
    | SStackalloc v1 sz1 s => SStackalloc v1 sz1 (useImmediate s)
    | SSeq s1 s2 =>
        let default := SSeq (useImmediate s1) (useImmediate s2) in
        match s1, s2 with
        | SLit v1 l1, SOp v2 op v2a (Var v2b) =>
            match op with
            | Syntax.bopname.add
            | Syntax.bopname.and
            | Syntax.bopname.or
            | Syntax.bopname.xor => if (is12BitImmediate l1) then
                                      if eqb v1 v2b then
                                        SSeq s1 (SOp v2 op v2a (Const l1))
                                      else if eqb v1 v2a then
                                             SSeq s1 (SOp v2 op v2b (Const l1))
                                           else default
                                    else default
            | Syntax.bopname.ltu
            | Syntax.bopname.lts => if (is12BitImmediate l1) then
                                      if eqb v1 v2b then
                                        SSeq s1 (SOp v2 op v2a (Const l1))
                                      else default
                                    else default
            | Syntax.bopname.srs
            | Syntax.bopname.sru
            | Syntax.bopname.slu => if (is5BitImmediate l1) then
                                      if eqb v1 v2b then
                                        SSeq s1 (SOp v2 op v2a (Const l1))
                                      else default
                                    else default
            | Syntax.bopname.sub => if (is12BitImmediate (-l1)) then
                                      if eqb v1 v2b then
                                        SSeq s1 (SOp v2 Syntax.bopname.add v2a (Const (-l1)))
                                      else default
                                    else default
            | _ => default
            end
        | _, _ => default
        end
    | _ => s
    end.

  Definition useimmediate_function: (list string * list string * stmt string) -> result (list string * list string * stmt string) :=
    fun '(argnames, retnames, body) =>
      let body' := useImmediate body in
      Success (argnames, retnames, body').

  Definition useimmediate_functions : env -> result env :=
    map.try_map_values useimmediate_function.
End WithArgs.
