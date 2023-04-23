Require Import compiler.util.Common.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.fwd.
Require Import String.
Open Scope Z_scope.
Require Import coqutil.Map.MapEauto.
Require Import coqutil.Datatypes.ListSet.
Local Notation var := String.string (only parsing).

Section WithArgs.

  Context {env: map.map String.string (list var * list var * stmt var)}.

  Local Notation bcond  := (@FlatImp.bcond var).

  Definition accessed_vars_bcond(c: bcond): list var :=
    match c with
    | CondBinary _ x y => list_union String.eqb [x] [y]
    | CondNez x => [x]
    end.

  Fixpoint live(s: stmt var)(used_after: list var): list var :=
    match s with
    | SSet x y
    | SLoad _ x y _
    | SInlinetable _ x _ y =>
        list_union String.eqb [y] (list_diff String.eqb used_after [x])
    | SStore _ a x _ => list_union String.eqb [a; x] used_after
    | SStackalloc x _ body => list_diff String.eqb (live body used_after) [x]
    | SLit x _ => list_diff String.eqb used_after [x]
    | SOp x _ y z => let var_z := match z with
                                | Var vz => [vz]
                                | Const _ => []
                                end in
                     list_union String.eqb ([y] ++ var_z) (list_diff String.eqb used_after [x])
    | SIf c s1 s2 => list_union String.eqb
                       (list_union String.eqb (live s1 used_after) (live s2 used_after))
                       (accessed_vars_bcond c)
    | SSeq s1 s2 => live s1 (live s2 used_after)
    | SLoop s1 c s2 =>
        live s1 (list_union String.eqb (accessed_vars_bcond c) (list_union String.eqb used_after (live s2 [])))
    | SSkip => used_after
    | SCall binds _ args
    | SInteract binds _ args => list_union String.eqb args (list_diff String.eqb used_after binds)
    end.

  Fixpoint deadAssignment(used_after: list var)(s: stmt var) : stmt var :=
    let deadAssignment' := deadAssignment used_after in
    match s with
    | SIf c s1 s2 => SIf c (deadAssignment' s1) (deadAssignment' s2)
    | SLoop s1 c s2 =>
        let used_after_s1 := (list_union String.eqb (accessed_vars_bcond c) (list_union String.eqb used_after (live s2 []))) in
        let used_after_s2 := (live s1 used_after_s1) in
        SLoop (deadAssignment used_after_s1 s1) c (deadAssignment used_after_s2 s2)
    | SStackalloc v1 sz1 s => SStackalloc v1 sz1 (deadAssignment' s)
    | SSeq s1 s2 =>
        let s2' := deadAssignment' s2 in
        let s1_used_after := live s2' used_after in
        SSeq (deadAssignment s1_used_after s1) (s2')
    | SLit x _ =>
        if existsb (String.eqb x) used_after
        then s else SSkip
    | SOp x _ _ _ =>
        if existsb (String.eqb x) used_after
        then s else SSkip
    | SSet x _ =>
        if existsb (String.eqb x) used_after
        then s else SSkip
    | _ => s
    end.

  Definition deadassignment_function: (list string * list string * stmt string) -> result (list string * list string * stmt string) :=
    fun '(argnames, retnames, body) =>
      let body' := deadAssignment retnames body in
      Success (argnames, retnames, body').

  Definition deadassignment_functions : env -> result env :=
    map.try_map_values deadassignment_function.


End WithArgs.
