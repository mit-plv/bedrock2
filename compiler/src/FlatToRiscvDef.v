Require Import bedrock2.Macros.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import compiler.Op.
Require Import riscv.Program.
Require Import riscv.Decode.
Require Import riscv.PseudoInstructions.
Require Import riscv.InstructionCoercions.
Require Import Coq.micromega.Lia.
Require Import riscv.Utility.


Local Open Scope ilist_scope.
Local Open Scope Z_scope.

Set Implicit Arguments.

Module Import FlatToRiscvDef.
  Class parameters := {
    actname: Set;
    LwXLEN: Register -> Register -> Z -> Instruction;
    SwXLEN: Register -> Register -> Z -> Instruction;
    compile_ext_call: list Register -> actname -> list Register -> list Instruction;
  }.
End FlatToRiscvDef.


Section FlatToRiscv1.
  Context {p: unique! FlatToRiscvDef.parameters}.

  Instance bopname_params: Basic_bopnames.parameters := {|
    Basic_bopnames.varname := Register;
    Basic_bopnames.funcname := Empty_set;
    Basic_bopnames.actname := actname;
  |}.

  Definition compile_op(rd: Register)(op: bopname)(rs1 rs2: Register): list Instruction :=
    match op with
    | bopname.add => [[Add rd rs1 rs2]]
    | bopname.sub => [[Sub rd rs1 rs2]]
    | bopname.mul => [[Mul rd rs1 rs2]]
    | bopname.and => [[And rd rs1 rs2]]
    | bopname.or  => [[Or  rd rs1 rs2]]
    | bopname.xor => [[Xor rd rs1 rs2]]
    | bopname.sru => [[Srl rd rs1 rs2]]
    | bopname.slu => [[Sll rd rs1 rs2]]
    | bopname.srs => [[Sra rd rs1 rs2]]
    | bopname.lts => [[Slt rd rs1 rs2]]
    | bopname.ltu => [[Sltu rd rs1 rs2]]
    | bopname.eq  => [[Sub rd rs1 rs2; Seqz rd rd]]
    end.

  Fixpoint compile_lit_rec(byteIndex: nat)(rd rs: Register)(v: Z): list Instruction :=
    let byte := bitSlice v ((Z.of_nat byteIndex) * 8) ((Z.of_nat byteIndex + 1) * 8) in
    [[ Addi rd rs byte ]] ++
    match byteIndex with
    | S b => [[ Slli rd rd 8]] ++ (compile_lit_rec b rd rd v)
    | O => [[]]
    end.

  Fixpoint compile_lit_rec'(byteIndex: nat)(rd rs: Register)(v: Z): list Instruction :=
    let d := (2 ^ ((Z.of_nat byteIndex) * 8))%Z in
    let hi := (v / d)%Z in
    let v' := (v - hi * d)%Z in
    [[ Addi rd rs hi ]] ++
    match byteIndex with
    | S b => [[ Slli rd rd 8]] ++ (compile_lit_rec b rd rd v')
    | O => [[]]
    end.

  (*
  Variable rd: Register.
  Eval cbv -[Register0] in (compile_lit_rec 7 rd Register0 10000).
  *)

  Definition compile_lit(rd: Register)(v: Z): list Instruction :=
    compile_lit_rec 7 rd Register0 v.

  Fixpoint compile_stmt(s: stmt): list (Instruction) :=
    match s with
    | SLoad x y => [[LwXLEN x y 0]]
    | SStore x y => [[SwXLEN x y 0]]
    | SLit x v => compile_lit x v
    | SOp x op y z => compile_op x op y z
    | SSet x y => [[Add x Register0 y]]
    | SIf cond bThen bElse =>
        let bThen' := compile_stmt bThen in
        let bElse' := compile_stmt bElse in
        (* only works if branch lengths are < 2^12 *)
        [[Beq cond Register0 ((Zlength bThen' + 2) * 4)]] ++
        bThen' ++
        [[Jal Register0 ((Zlength bElse' + 1) * 4)]] ++
        bElse'
    | SLoop body1 cond body2 =>
        let body1' := compile_stmt body1 in
        let body2' := compile_stmt body2 in
        (* only works if branch lengths are < 2^12 *)
        body1' ++
        [[Beq cond Register0 ((Zlength body2' + 2) * 4)]] ++
        body2' ++
        [[Jal Register0 (- (Zlength body1' + 1 + Zlength body2') * 4)]]
    | SSeq s1 s2 => compile_stmt s1 ++ compile_stmt s2
    | SSkip => nil
    | SCall resvars action argvars => nil (* unsupported *)
    | SInteract resvars action argvars => compile_ext_call resvars action argvars
    end.

End FlatToRiscv1.
