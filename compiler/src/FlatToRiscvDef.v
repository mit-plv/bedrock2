Require Import coqutil.Macros.unique.
Require Import coqutil.Decidable.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Utility.InstructionCoercions.
Require Import Coq.micromega.Lia.
Require Import riscv.Spec.Primitives.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.ListLib.
Require Import riscv.Utility.Encode.
Require Import bedrock2.Syntax.

Local Open Scope ilist_scope.
Local Open Scope Z_scope.

Set Implicit Arguments.

Definition valid_instructions(iset: InstructionSet)(prog: list Instruction): Prop :=
  forall instr, In instr prog -> verify instr iset.

Module Import FlatToRiscvDef.
  Class parameters := {
    (* the words implementations are not needed, but we need width,
       and EmitsValid needs width_cases *)
    W :> Utility.Words;
    actname: Type;
    compile_ext_call: list Register -> actname -> list Register -> list Instruction;
    max_ext_call_code_size: actname -> Z;
    compile_ext_call_length: forall binds f args,
        Zlength (compile_ext_call binds f args) <= max_ext_call_code_size f;
    (* TODO requiring corrrectness for all isets is too strong, and this hyp should probably
       be elsewhere *)
    compile_ext_call_emits_valid: forall iset binds a args,
      Forall valid_register binds ->
      Forall valid_register args ->
      valid_instructions iset (compile_ext_call binds a args)
  }.

  Instance mk_Syntax_params(p: parameters): Syntax.parameters := {|
    Syntax.varname := Register;
    Syntax.funname := Empty_set;
    Syntax.actname := actname;
  |}.

  Local Set Refine Instance Mode.

  Instance mk_FlatImpSize_params(p: parameters): FlatImpSize.parameters := {|
    FlatImpSize.max_ext_call_code_size := max_ext_call_code_size;
  |}.
  Proof.
    abstract (
        intros a;
        pose proof (compile_ext_call_length [] a []);
        pose proof (Zlength_nonneg (compile_ext_call [] a []));
        lia).
  Defined.

End FlatToRiscvDef.

Section FlatToRiscv1.
  Context {p: unique! FlatToRiscvDef.parameters}.

  (* Part 1: Definitions needed to state when compilation outputs valid code *)

  (* If stmt_size is < 2^10, it is compiled to < 2^10 instructions, which is
     < 2^12 bytes, and the branch instructions have 12 bits to encode the
     relative jump length. One of them is used for the sign, and the other
     11 encode the jump length as a multiple of 2, so jump lengths have to
     be < 2^12 bytes, i.e. < 2^10 instructions, so this bound is tight,
     unless we start using multi-instruction jumps. *)
  Definition stmt_not_too_big(s: stmt): Prop := stmt_size s < 2 ^ 10.

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

  (* load & store depend on the bitwidth: on 32-bit machines, Lw just loads 4 bytes,
     while on 64-bit machines, it loads 4 bytes and sign-extends them.
     If we want a command which always loads 4 bytes without sign-extending them,
     we need to make a case distinction on the bitwidth and choose Lw on 32-bit,
     but Lwu on 64-bit.
     We can't just always choose Lwu, because Lwu is not available on 32-bit machines. *)

  Definition compile_load(sz: access_size):
    Register -> Register -> Z -> Instruction :=
    match sz with
    | access_size.one => Lbu
    | access_size.two => Lhu
    | access_size.four => if width =? 32 then Lw else Lwu
    | access_size.word => if width =? 32 then Lw else Ld
    end.

  Definition compile_store(sz: access_size):
    Register -> Register -> Z -> Instruction :=
    match sz with
    | access_size.one => Sb
    | access_size.two => Sh
    | access_size.four => Sw
    | access_size.word => if width =? 32 then Sw else Sd
    end.

  Definition compile_op(rd: Register)(op: Syntax.bopname)(rs1 rs2: Register): list Instruction :=
    match op with
    | Syntax.bopname.add => [[Add rd rs1 rs2]]
    | Syntax.bopname.sub => [[Sub rd rs1 rs2]]
    | Syntax.bopname.mul => [[Mul rd rs1 rs2]]
    | Syntax.bopname.mulhuu => [[Mulhu rd rs1 rs2]]
    | Syntax.bopname.divu => [[Divu rd rs1 rs2]]
    | Syntax.bopname.remu => [[Remu rd rs1 rs2]]
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

  Definition compile_lit_12bit(rd: Register)(v: Z): list Instruction :=
    [[ Addi rd Register0 v ]].

  (* On a 64bit machine, loading a constant -2^31 <= v < 2^31 is not always possible with
     a Lui followed by an Addi:
     If the constant is of the form 0x7ffffXXX, and XXX has its highest bit set, we would
     have to put 0x80000--- into the Lui, but then that value will be sign-extended.

     Or spelled differently:
     If we consider all possible combinations of a Lui followed by an Addi, we get 2^32
     different values, but some of them are not in the range -2^31 <= v < 2^31.
     On the other hand, this property holds for combining Lui followed by a Xori.

     Or yet differently:
     Lui 0x80000--- ; Addi 0xXXX
     where XXX has the highest bit set,
     loads a value < 2^31, so some Lui+Addi pairs do not load a value in the range
     -2^31 <= v < 2^31, so some Lui+Addi pairs are "wasted" and we won't find a
     Lui+Addi pairs for all desired values in the range -2^31 <= v < 2^31
 *)

  Definition swrap(width: Z)(z: Z): Z := (z + 2^(width-1)) mod 2^width - 2^(width-1).

  Definition swrap_bitwise(width n: Z): Z :=
    if Z.testbit n (width - 1)
    then (Z.lor (Z.land n (Z.ones width)) (Z.shiftl (-1) width))
    else (Z.land n (Z.ones width)).

  Definition compile_lit_32bit(rd: Register)(v: Z): list Instruction :=
    let lo := swrap_bitwise 12 v in
    let hi := Z.lxor v lo in
    [[ Lui rd hi ; Xori rd rd lo ]].

  Definition compile_lit_64bit(rd: Register)(v: Z): list Instruction :=
    let v0 := bitSlice v  0 11 in
    let v1 := bitSlice v 11 22 in
    let v2 := bitSlice v 22 32 in
    let hi := bitSlice v 32 64 in
    compile_lit_32bit rd (signExtend 32 hi) ++
    [[ Slli rd rd 10 ;
       Addi rd rd v2 ;
       Slli rd rd 11 ;
       Addi rd rd v1 ;
       Slli rd rd 11 ;
       Addi rd rd v0 ]].

  Definition compile_lit_large(rd: Register)(v: Z): list Instruction :=
    if width =? 32 then compile_lit_32bit rd (swrap_bitwise 32 v) else
    compile_lit_64bit rd (v mod 2 ^ 64).

  Definition compile_lit_new(rd: Register)(v: Z): list Instruction :=
    if dec (-2^11 <= v < 2^11) then compile_lit_12bit rd v else
    compile_lit_large rd v.

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

  Fixpoint compile_stmt(s: stmt): list Instruction :=
    match s with
    | SLoad  sz x y => [[compile_load  sz x y 0]]
    | SStore sz x y => [[compile_store sz x y 0]]
    | SLit x v => compile_lit_new x v
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
