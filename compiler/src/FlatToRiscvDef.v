Require Import coqutil.Macros.unique.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Program.
Require Import riscv.Decode.
Require Import riscv.PseudoInstructions.
Require Import riscv.InstructionCoercions.
Require Import Coq.micromega.Lia.
Require Import riscv.AxiomaticRiscv.
Require Import riscv.Utility.
Require Import riscv.util.ListLib.
Require Import bedrock2.Syntax.

Local Open Scope ilist_scope.
Local Open Scope Z_scope.

Set Implicit Arguments.

Module Import FlatToRiscvDef.
  Class parameters := {
    actname: Type;
    compile_ext_call: list Register -> actname -> list Register -> list Instruction;
    max_ext_call_code_size: actname -> Z;
    compile_ext_call_length: forall binds f args,
        Zlength (compile_ext_call binds f args) <= max_ext_call_code_size f;
  }.
End FlatToRiscvDef.

Section FlatToRiscv1.
  Context {p: unique! FlatToRiscvDef.parameters}.

  Instance bopname_params: Syntax.parameters := {|
    Syntax.varname := Register;
    Syntax.funname := Empty_set;
    Syntax.actname := actname;
  |}.

  (* Part 1: Definitions needed to state when compilation outputs valid code *)

  Definition stmt_size_body(rec: stmt -> Z)(s: stmt): Z :=
    match s with
    | SLoad sz x a => 1
    | SStore sz a v => 1
    | SLit x v => 8
    | SOp x op y z => 2
    | SSet x y => 1
    | SIf cond bThen bElse => 1 + (rec bThen) + (rec bElse)
    | SLoop body1 cond body2 => 1 + (rec body1) + (rec body2)
    | SSeq s1 s2 => 1 + (rec s1) + (rec s2)
    | SSkip => 1
    | SCall binds f args => 1 + (Zlength binds + Zlength args)
    | SInteract binds f args => 1 + (Zlength binds + Zlength args) + max_ext_call_code_size f
    end.

  Fixpoint stmt_size(s: stmt): Z := stmt_size_body stmt_size s.
  (* TODO: in coq 8.9 it will be possible to state this lemma automatically: https://github.com/coq/coq/blob/91e8dfcd7192065f21273d02374dce299241616f/CHANGES#L16 *)
  Lemma stmt_size_unfold : forall s, stmt_size s = stmt_size_body stmt_size s. destruct s; reflexivity. Qed.

  Arguments Z.add _ _ : simpl never.

  Lemma max_ext_call_code_size_nonneg: forall a, 0 <= max_ext_call_code_size a.
  Proof.
    intros.
    pose proof (compile_ext_call_length [] a []) as P.
    pose proof (Zlength_nonneg (compile_ext_call [] a [])).
    lia.
  Qed.

  Lemma stmt_size_pos: forall s, stmt_size s > 0.
  Proof.
    induction s; simpl; try omega;
    pose proof (Zlength_nonneg binds);
    pose proof (Zlength_nonneg args);
    pose proof max_ext_call_code_size_nonneg;
    simpl in *.
    - destruct f.
    - specialize (H1 a). omega.
  Qed.

  (* TODO is 2^9 really the best we can get? *)
  Definition stmt_not_too_big(s: stmt): Prop := stmt_size s < 2 ^ 9.

  Definition valid_registers_bcond (cond: bcond) : Prop :=
    match cond with
    | CondBinary _ x y => valid_register x /\ valid_register y
    | CondNez x => valid_register x
    end.

  Fixpoint valid_registers(s: stmt): Prop :=
    match s with
    | SLoad _ x a => valid_register x /\ valid_register a
    | SStore _ a x => valid_register a /\ valid_register x
    | SLit x _ => valid_register x
    | SOp x _ y z => valid_register x /\ valid_register y /\ valid_register z
    | SSet x y => valid_register x /\ valid_register y
    | SIf c s1 s2 => valid_registers_bcond c /\ valid_registers s1 /\ valid_registers s2
    | SLoop s1 c s2 => valid_registers_bcond c /\ valid_registers s1 /\ valid_registers s2
    | SSeq s1 s2 => valid_registers s1 /\ valid_registers s2
    | SSkip => True
    | SCall binds _ args => Forall valid_register binds /\ Forall valid_register args (* untested *)
    | SInteract binds _ args => Forall valid_register binds /\ Forall valid_register args (* untested *)
    end.


  (* Part 2: compilation *)

  Definition is32bit(iset: InstructionSet): bool :=
    match iset with
    | RV32I | RV32IM | RV32IA | RV32IMA => true
    | RV64I | RV64IM | RV64IA | RV64IMA => false
    end.

  (* load & store depend on the bitwidth: on 32-bit machines, Lw just loads 4 bytes,
     while on 64-bit machines, it loads 4 bytes and sign-extends them.
     If we want a command which always loads 4 bytes without sign-extending them,
     we need to make a case distinction on the bitwidth and choose Lw on 32-bit,
     but Lwu on 64-bit.
     We can't just always choose Lwu, because Lwu is not available on 32-bit machines. *)

  Definition compile_load(iset: InstructionSet)(sz: access_size):
    Register -> Register -> Z -> Instruction :=
    match sz with
    | access_size.one => Lbu
    | access_size.two => Lhu
    | access_size.four => if is32bit iset then Lw else Lwu
    | access_size.word => if is32bit iset then Lw else Ld
    end.

  Definition compile_store(iset: InstructionSet)(sz: access_size):
    Register -> Register -> Z -> Instruction :=
    match sz with
    | access_size.one => Sb
    | access_size.two => Sh
    | access_size.four => Sw
    | access_size.word => if is32bit iset then Sw else Sd
    end.

  Definition compile_op(rd: Register)(op: Syntax.bopname)(rs1 rs2: Register): list Instruction :=
    match op with
    | Syntax.bopname.add => [[Add rd rs1 rs2]]
    | Syntax.bopname.sub => [[Sub rd rs1 rs2]]
    | Syntax.bopname.mul => [[Mul rd rs1 rs2]]
    | Syntax.bopname.and => [[And rd rs1 rs2]]
    | Syntax.bopname.or  => [[Or  rd rs1 rs2]]
    | Syntax.bopname.xor => [[Xor rd rs1 rs2]]
    | Syntax.bopname.sru => [[Srl rd rs1 rs2]]
    | Syntax.bopname.slu => [[Sll rd rs1 rs2]]
    | Syntax.bopname.srs => [[Sra rd rs1 rs2]]
    | Syntax.bopname.lts => [[Slt rd rs1 rs2]]
    | Syntax.bopname.ltu => [[Sltu rd rs1 rs2]]
    | Syntax.bopname.eq  => [[Sub rd rs1 rs2; Seqz rd rd]]
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

  (* Inverts the branch condition. *)
  Definition compile_bcond_by_inverting
             (cond: bcond) (amt: Z) : Instruction:=
    match cond with
    | CondBinary op x y =>
        match op with
        | BEq  => Bne x y amt
        | BNe  => Beq x y amt
        | BLt  => Bge x y amt
        | BGe  => Blt x y amt
        | BLtu => Bgeu x y amt
        | BGeu => Bltu x y amt
        end
    | CondNez x =>
        Beq x Register0 amt
    end.

  Context (iset: InstructionSet).

  Fixpoint compile_stmt(s: stmt): list Instruction :=
    match s with
    | SLoad  sz x y => [[compile_load  iset sz x y 0]]
    | SStore sz x y => [[compile_store iset sz x y 0]]
    | SLit x v => compile_lit x v
    | SOp x op y z => compile_op x op y z
    | SSet x y => [[Add x Register0 y]]
    | SIf cond bThen bElse =>
        let bThen' := compile_stmt bThen in
        let bElse' := compile_stmt bElse in
        (* only works if branch lengths are < 2^12 *)
        [[compile_bcond_by_inverting cond ((Zlength bThen' + 2) * 4)]] ++
        bThen' ++
        [[Jal Register0 ((Zlength bElse' + 1) * 4)]] ++
        bElse'
    | SLoop body1 cond body2 =>
        let body1' := compile_stmt body1 in
        let body2' := compile_stmt body2 in
        (* only works if branch lengths are < 2^12 *)
        body1' ++
        [[compile_bcond_by_inverting cond ((Zlength body2' + 2) * 4)]] ++
        body2' ++
        [[Jal Register0 (- (Zlength body1' + 1 + Zlength body2') * 4)]]
    | SSeq s1 s2 => compile_stmt s1 ++ compile_stmt s2
    | SSkip => nil
    | SCall resvars action argvars => nil (* unsupported *)
    | SInteract resvars action argvars => compile_ext_call resvars action argvars
    end.

End FlatToRiscv1.
