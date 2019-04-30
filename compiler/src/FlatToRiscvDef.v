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
Require Import coqutil.Z.Lia.
Require Import riscv.Spec.Primitives.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.ListLib.
Require Import compiler.util.ListLib.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.RegisterNames.
Require Import bedrock2.Syntax.
Require Import coqutil.Map.Interface.

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
    compile_ext_call: list Register -> String.string -> list Register -> list Instruction;
    compile_ext_call_length: forall binds f args,
        Zlength (compile_ext_call binds f args) <= 7;
    (* TODO requiring corrrectness for all isets is too strong, and this hyp should probably
       be elsewhere *)
    compile_ext_call_emits_valid: forall iset binds a args,
      Forall valid_register binds ->
      Forall valid_register args ->
      valid_instructions iset (compile_ext_call binds a args)
  }.

  Instance mk_Syntax_params(p: parameters): Syntax.parameters := {|
    Syntax.varname := Register;
    Syntax.funname := String.string;
    Syntax.actname := String.string;
  |}.

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
    [[ Addi rd Register0 (signExtend 12 v) ]].

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

  Definition compile_lit_32bit(rd: Register)(v: Z): list Instruction :=
    let lo := signExtend 12 v in
    let hi := Z.lxor (signExtend 32 v) lo in
    [[ Lui rd hi ; Xori rd rd lo ]].

  Definition compile_lit_64bit(rd: Register)(v: Z): list Instruction :=
    let v0 := bitSlice v  0 11 in
    let v1 := bitSlice v 11 22 in
    let v2 := bitSlice v 22 32 in
    let hi := bitSlice v 32 64 in
    compile_lit_32bit rd (signExtend 32 hi) ++
    [[ Slli rd rd 10 ;
       Xori rd rd v2 ;
       Slli rd rd 11 ;
       Xori rd rd v1 ;
       Slli rd rd 11 ;
       Xori rd rd v0 ]].

  Definition compile_lit(rd: Register)(v: Z): list Instruction :=
    if dec (-2^11 <= v < 2^11) then compile_lit_12bit rd v else
    if dec (width = 32 \/ - 2 ^ 31 <= v < 2 ^ 31) then compile_lit_32bit rd v else
    compile_lit_64bit rd v.

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

  Definition bytes_per_word: Z := Z.of_nat (@Memory.bytes_per width access_size.word).

  Fixpoint save_regs(regs: list Register)(offset: Z): list Instruction :=
    match regs with
    | nil => nil
    | r :: regs => compile_store access_size.word sp r offset
                   :: (save_regs regs (offset + bytes_per_word))
    end.

  Fixpoint load_regs(regs: list Register)(offset: Z): list Instruction :=
    match regs with
    | nil => nil
    | r :: regs => compile_load access_size.word r sp offset
                   :: (load_regs regs (offset + bytes_per_word))
    end.

  (* All positions are relative to the beginning of the progam, so we get completely
     position independent code. *)

  Context {fun_pos_env: map.map funname Z}.
  Context {env: map.map funname (list varname * list varname * stmt)}.

  Section WithEnv.
    Variable e: fun_pos_env.

    Definition compile_stmt_new: Z -> stmt -> list Instruction :=
      fix compile_stmt(mypos: Z)(s: stmt) :=
      match s with
      | SLoad  sz x y => [[compile_load  sz x y 0]]
      | SStore sz x y => [[compile_store sz x y 0]]
      | SLit x v => compile_lit x v
      | SOp x op y z => compile_op x op y z
      | SSet x y => [[Add x Register0 y]]
      | SIf cond bThen bElse =>
          let bThen' := compile_stmt (mypos + 4) bThen in
          let bElse' := compile_stmt (mypos + 4 + 4 * Z.of_nat (length bThen') + 4) bElse in
          (* only works if branch lengths are < 2^12 *)
          [[compile_bcond_by_inverting cond ((Z.of_nat (length bThen') + 2) * 4)]] ++
          bThen' ++
          [[Jal Register0 ((Z.of_nat (length bElse') + 1) * 4)]] ++
          bElse'
      | SLoop body1 cond body2 =>
          let body1' := compile_stmt mypos body1 in
          let body2' := compile_stmt (mypos + Z.of_nat (length body1') + 4) body2 in
          (* only works if branch lengths are < 2^12 *)
          body1' ++
          [[compile_bcond_by_inverting cond ((Z.of_nat (length body2') + 2) * 4)]] ++
          body2' ++
          [[Jal Register0 (- Z.of_nat (length body1' + 1 + length body2') * 4)]]
      | SSeq s1 s2 =>
          let s1' := compile_stmt mypos s1 in
          let s2' := compile_stmt (mypos + 4 * Z.of_nat (length s1')) s2 in
          s1' ++ s2'
      | SSkip => nil
      | SCall resvars f argvars =>
        let fpos := match map.get e f with
                    | Some pos => pos
                    (* don't fail so that we can measure the size of the resulting code *)
                    | None => 42
                    end in
        save_regs argvars (- bytes_per_word * Z.of_nat (length argvars)) ++
        [[ Jal ra (fpos - (mypos + 4 * Z.of_nat (length argvars))) ]] ++
        load_regs resvars (- bytes_per_word * Z.of_nat (length argvars + length resvars))
      | SInteract resvars action argvars => compile_ext_call resvars action argvars
      end.

    (*
     Stack layout:

     high addresses              ...
                      old sp --> mod_var_0 of previous function call arg0
                                 argn
                                 ...
                                 arg0
                                 retn
                                 ...
                                 ret0
                                 ra
                                 mod_var_n
                                 ...
                      new sp --> mod_var_0
     low addresses               ...

     Expected stack layout at beginning of function call: like above, but only filled up to arg0.
     Stack grows towards low addresses.
    *)
    Definition compile_function(mypos: Z):
      (list varname * list varname * stmt) -> list Instruction :=
      fun '(argvars, resvars, body) =>
        let mod_vars := modVars_as_list body in
        let framelength := Z.of_nat (length argvars + length resvars + 1 + length mod_vars) in
        let framesize := bytes_per_word * framelength in
        [[ Addi sp sp (-framesize) ]] ++
        [[ compile_store access_size.word sp ra
                         (bytes_per_word * (Z.of_nat (length mod_vars))) ]] ++
        save_regs mod_vars 0 ++
        load_regs argvars (bytes_per_word * (Z.of_nat (length mod_vars + 1 + length resvars))) ++
        compile_stmt_new (mypos + 4 * (2 + Z.of_nat (length mod_vars + length argvars))) body ++
        save_regs resvars (bytes_per_word * (Z.of_nat (length mod_vars + 1))) ++
        load_regs mod_vars 0 ++
        [[ compile_load access_size.word ra sp
                        (bytes_per_word * (Z.of_nat (length mod_vars))) ]] ++
        [[ Addi sp sp framesize ]] ++
        [[ Jalr zero ra 0 ]].

    Section WithImplEnv.
      Variable (e_impl: env).

      Fixpoint compile_funs(pos: Z)(funnames: list funname): list Instruction :=
        match funnames with
        | nil => nil
        | fname :: rest =>
          match map.get e_impl fname with
          | Some F => let insts := compile_function pos F in
                      let size := 4 * Z.of_nat (length (insts)) in
                      insts ++ compile_funs (pos + size) rest
          | None => nil
          end
        end.
    End WithImplEnv.
  End WithEnv.

  Section WithImplEnv.
    Variable (e_impl: env).

    (* compiles all functions just to obtain their code size *)
    Fixpoint build_fun_pos_env(pos: Z)(funnames: list funname): fun_pos_env :=
      match funnames with
      | nil => map.empty
      | fname :: rest =>
        match map.get e_impl fname with
        | Some F => let size := 4 * Z.of_nat (length (compile_function map.empty 42 F)) in
                    map.put (build_fun_pos_env (pos + size) rest) fname pos
        | None => map.empty
        end
      end.

    Definition compile_functions(funnames: list funname): list Instruction :=
      let e_pos := build_fun_pos_env 0 funnames in
      compile_funs e_pos e_impl 0 funnames.

    (* The main function is always some initialization code followed by an infinite loop.
       If no loop is desired, pass SSkip as loop_body, and this will guarantee that after
       the init code (i.e. your full program) has run to completion, no further output
       nor other undesired behavior is produced *)
    Definition compile_main(e_pos: fun_pos_env)(mypos: Z)(init_code loop_body: stmt)
      : list Instruction :=
      let insts1 := compile_stmt_new e_pos mypos init_code in
      let insts2 := compile_stmt_new e_pos (mypos + 4 * Z.of_nat (length insts1)) loop_body in
      insts1 ++ insts2 ++ [[Jal Register0 (- 4 * Z.of_nat (length insts2))]].

    Definition compile_prog(init loop_body: stmt)(funs: list funname): list Instruction :=
      let size1 := 4 * Z.of_nat (length (compile_main map.empty 42 init loop_body)) in
      let e_pos := build_fun_pos_env size1 funs in
      let insts1 := compile_main e_pos 0 init loop_body in
      let insts2 := compile_funs e_pos e_impl size1 funs in
      insts1 ++ insts2.

  End WithImplEnv.


  (* original compile_stmt: *)
  Fixpoint compile_stmt(s: stmt): list Instruction :=
    match s with
    | SLoad  sz x y => [[compile_load  sz x y 0]]
    | SStore sz x y => [[compile_store sz x y 0]]
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
