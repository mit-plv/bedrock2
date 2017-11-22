Require Import lib.LibTactics.
Require Import compiler.Common.
Require Import compiler.FlatImp.
Require Import compiler.StateCalculus.
Require Import compiler.zcast.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import compiler.Op.
Require Import compiler.Riscv.

Section FlatToRiscv.

  Context {w: nat}. (* bit width *)
  Context {var: Set}. (* var in the source language is the same as Register in the target language *)
  Context {R0: var}. (* register #0 is the read-only constant 0 *)
  Context {eq_var_dec: DecidableEq var}.
  Context {state: Type}.
  Context {stateMap: Map state var (word w)}.
  
  Definition compile_op(rd: var)(op: binop)(rs1 rs2: var): list (@Instruction var) :=
    match op with
    | OPlus => [Add rd rs1 rs2]
    | OMinus => [Sub rd rs1 rs2]
    | OTimes => [Mul rd rs1 rs2]
    | OEq => [Add rd R0 R0; Bne rs1 rs2 $4; Addi rd R0 $1] (* TODO super inefficient *)
    | OLt => [Add rd R0 R0; Bge rs1 rs2 $4; Addi rd R0 $1] (* TODO super inefficient *)
    | OAnd => [And rd rs1 rs2]
    end.

  (* using the same names (var) in source and target language *)
  Fixpoint compile_stmt(s: @stmt w var): list (@Instruction var) :=
    match s with
    | SLit x v => [Addi x R0 (zcast 12 v)] (* only works if literal is < 2^12 *)
    | SOp x op y z => compile_op x op y z
    | SSet x y => [Add x y R0]
    | SIf cond bThen bElse =>
        let bThen' := compile_stmt bThen in
        let bElse' := compile_stmt bElse in
        (* only works if branch lengths are < 2^12 *)
        [Beq cond R0 $(S (length bThen'))] ++ bThen' ++ [Jal R0 $(length bElse')] ++ bElse'
    | SLoop body1 cond body2 =>
        let body1' := compile_stmt body1 in
        let body2' := compile_stmt body2 in
        (* only works if branch lengths are < 2^12 *)
        body1' ++
        [Beq cond R0 $(S (length body2'))] ++
        body2' ++
        [Jal R0 (wneg $(S (length body1' + length body2')))]
    | SSeq s1 s2 => compile_stmt s1 ++ compile_stmt s2
    | SSkip => nil
    end.

End FlatToRiscv.
