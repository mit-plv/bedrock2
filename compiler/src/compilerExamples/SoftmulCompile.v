Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Word.Bitwidth32.
From bedrock2 Require Import Semantics BasicC32Semantics WeakestPrecondition ProgramLogic.
From coqutil Require Import Word.Properties Word.Interface Tactics.letexists.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Utility.FreeMonad.
Require Import riscv.Utility.RegisterNames.
Require riscv.Spec.PseudoInstructions.
Require riscv.Utility.InstructionCoercions.
Require Import riscv.Spec.Decode.
Require riscv.Spec.Execute.
Require Import riscv.Spec.Machine.
Require Import riscv.Platform.Memory.
Require Import riscv.Spec.CSRFile.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.RecordSetters.
Require Import coqutil.Decidable.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.SeparationLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.ZnWords.
Require Import riscv.Utility.Encode.
Require Import riscv.Proofs.EncodeBound.
Require Import riscv.Platform.MinimalCSRs.
Require Import riscv.Platform.MaterializeRiscvProgram.
Require Import compiler.regs_initialized.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.SepAutoArray bedrock2.SepAuto.

Definition binary_mul :=
  ("binary_mul", (["x";"e"], (["ret"]:list String.string), bedrock_func_body:(
  ret = $0;
  while (e) {
    if (e & $1) { ret = ret + x };
    e = e >> $1;
    x = x + x
  }
))).

#[export] Instance spec_of_binary_mul : spec_of "binary_mul" := fun functions =>
  forall x e t m,
    WeakestPrecondition.call functions
      "binary_mul" t m [x; e]
      (fun t' m' rets => t=t'/\ m=m' /\ rets = [word.mul x e]).

Require Import bedrock2.AbsintWordToZ coqutil.Z.Lia.

Ltac t :=
  repeat match goal with x := _ |- _ => subst x end;
  repeat match goal with |- context [word.unsigned ?e] => progress (idtac; let H := rbounded (word.unsigned e) in idtac) end;
  repeat match goal with G: context [word.unsigned ?e] |- _ => progress (idtac; let H := rbounded (word.unsigned e) in idtac) end;
  repeat match goal with |- context [word.unsigned ?e] => progress (idtac; let H := unsigned.zify_expr e in try rewrite H) end;
  repeat match goal with G: context [word.unsigned ?e] |- _ => progress (idtac; let H := unsigned.zify_expr e in try rewrite H in G) end;
  repeat match goal with H: absint_eq ?x ?x |- _ => clear H end;
  cbv [absint_eq] in *.

Lemma binary_mul_ok : program_logic_goal_for_function! binary_mul.
Proof.
  repeat straightline.

  refine ((Loops.tailrec
    (* types of ghost variables*) HList.polymorphic_list.nil
    (* program variables *) (["e";"ret";"x"] : list String.string))
    (fun v t m e ret x => PrimitivePair.pair.mk (v = word.unsigned e) (* precondition *)
    (fun   T M E RET X => T = t /\ M = m /\ (* postcondition *)
      word.unsigned RET = (word.unsigned ret + word.unsigned x * word.unsigned e) mod 2^32))
    (fun n m => 0 <= n < m) (* well_founded relation *)
    _ _ _ _ _);
    (* TODO wrap this into a tactic with the previous refine *)
    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.

  { repeat straightline. }
  { exact (Z.lt_wf _). }
  { repeat straightline. } (* init precondition *)
  { (* loop test *)
    repeat straightline; try show_program.
    { (* loop body *)
      letexists; split; [repeat straightline|]. (* if condition evaluation *)
      split. (* if cases, path-blasting *)
      {
        repeat (straightline || (split; trivial; [])). all:t.
        { (* measure decreases *)
          set (word.unsigned x0) in *. (* WHY does blia need this? *)
          Z.div_mod_to_equations; blia. }
        { (* invariant preserved *)
          rewrite H3; clear H3.
          change (1+1) with 2 in *.
          assert (word.unsigned x0 mod 2 = 1) as Hbit by ZnWords.
          epose proof (Z.div_mod _ 2 ltac:(discriminate)) as Heq; rewrite Hbit in Heq.
          rewrite Heq at 2; clear Hbit Heq.
          change (2 ^ 1) with 2. ZnWords. } }
      {
        repeat (straightline || (split; trivial; [])).
        all: t.
        { ZnWords. }
        { (* invariant preserved *)
          rewrite H3; clear H3.
          change (1+1) with 2 in *.
          rename H0 into Hbit.
          epose proof (Z.div_mod _ 2 ltac:(discriminate)) as Heq; rewrite Hbit in Heq.
          rewrite Heq at 2; clear Hbit Heq.
          change (2 ^ 1) with 2. ZnWords. } } }
    { (* postcondition *) ssplit; auto. ZnWords. } }

  repeat straightline.
  ssplit; auto. f_equal. ZnWords.
Qed.

Open Scope bool_scope.

(* like (decode RV32I), but additionally also accepts the Mul instruction
   (but no other instructions from the M extension) *)
Definition mdecode(inst: Z): Instruction :=
  let opcode := bitSlice inst 0 7 in
  let rd := bitSlice inst 7 12 in
  let funct3 := bitSlice inst 12 15 in
  let rs1 := bitSlice inst 15 20 in
  let rs2 := bitSlice inst 20 25 in
  let funct7 := bitSlice inst 25 32 in
  if (opcode =? opcode_OP) && (funct3 =? funct3_MUL) && (funct7 =? funct7_MUL)
  then MInstruction (Mul rd rs1 rs2)
  else decode RV32I inst.

Definition idecode: Z -> Instruction := decode RV32I.

Section Riscv.
  Context {word: Word.Interface.word 32}.
  Context {word_ok: word.ok word}.
  Context {Mem: map.map word byte}.
  Context {Mem_ok: map.ok Mem}.
  Context {registers: map.map Z word}.
  Context {registers_ok: map.ok registers}.

  Add Ring wring : (word.ring_theory (word := word))
      ((*This preprocessing is too expensive to be always run, especially if
         we do many ring_simplify in a sequence, in which case it's sufficient
         to run it once before the ring_simplify sequence.
         preprocess [autorewrite with rew_word_morphism],*)
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  (* RISC-V Monad *)
  Local Notation M := (free riscv_primitive primitive_result).

  Local Hint Mode map.map - - : typeclass_instances.

  Definition run1(decoder: Z -> Instruction): M unit :=
    pc <- getPC;
    inst <- Machine.loadWord Fetch pc;
    Execute.execute (decoder (LittleEndian.combine 4 inst));;
    endCycleNormal.

  Definition instr(decoder: Z -> Instruction)(inst: Instruction)(addr: word): Mem -> Prop :=
    ex1 (fun z => sep (addr |-> truncated_scalar access_size.four z)
                      (emp (decoder z = inst /\ 0 <= z < 2 ^ 32))).

  Declare Scope array_abbrevs_scope.
  Open Scope array_abbrevs_scope.
  Notation "'program' d" := (array (instr d) 4) (at level 10): array_abbrevs_scope.

  (* both the finish-postcondition and the abort-postcondition are set to `post`
     to make sure `post` holds in all cases: *)
  Definition mcomp_sat(m: M unit)(initial: State)(post: State -> Prop): Prop :=
    free.interpret run_primitive m initial (fun tt => post) post.

  Import RegisterNames PseudoInstructions.
  Import InstructionCoercions. Open Scope ilist_scope.
  Import Decode.

  (* a3 := a1 * a2
     without using mul, but with a naive loop:
     a3 := 0;
     while (0 != a1) {
       a3 := a3 + a2;
       a1 := a1 - 1;
     } *)
  Definition softmul_insts := [[
    Addi a3 zero 0;
    Beq zero a1 16;
    Add a3 a3 a2;
    Addi a1 a1 (-1);
    J (-12)
  ]].

  (* TODO implement in bedrock2 and compile to riscv, and also need to prove that
     programs running on the RISC-V machine used by the compiler (without CSRs)
     also run correctly on a RISC-V machine with CSRs and a different state type. *)
  Definition mul_insts := [[
    Addi t1 a1 0;
    Srli t1 t1 5           ; (* t1 := t1 >> 5                                             *)
    Andi s3 t1 (31*4)      ; (* s3 := i[7:12]<<2   // (rd of the MUL)*4                   *)
    Srli t1 t1 8           ; (* t1 := t1 >> 8                                             *)
    Andi s1 t1 (31*4)      ; (* s1 := i[15:20]<<2  // (rs1 of the MUL)*4                  *)
    Srli t1 t1 5           ; (* t1 := t1 >> 5                                             *)
    Andi s2 t1 (31*4)      ; (* s2 := i[20:25]<<2  // (rs2 of the MUL)*4                  *)
    Add s1 s1 sp           ; (* s1 := s1 + stack_start                                    *)
    Add s2 s2 sp           ; (* s2 := s2 + stack_start                                    *)
    Add s3 s3 sp           ; (* s3 := s3 + stack_start                                    *)
    Lw a1 s1 0             ; (* a1 := stack[s1]                                           *)
    Lw a2 s2 0               (* a2 := stack[s2]                                           *)
  ]] ++ softmul_insts ++ [[  (* a3 := softmul(a1,a2)                                      *)
    Sw s3 a3 0;              (* stack[s3] := a3                                           *)
    Jalr zero ra 0           (* return;                                                   *)
  ]].

  (* update if index is nonzero *)
  Definition updNz{A: Type}(l: list A)(i: Z)(v: A): list A :=
    if Z.eqb i 0 then l else List.upd l (Z.to_nat i) v.

  (* TODO will need some stack space *)
  Lemma mul_correct: forall initial a_regs regvals invalidIInst R (post: State -> Prop)
                            ret_addr sp_val rd rs1 rs2,
      initial.(nextPc) = word.add initial.(pc) (word.of_Z 4) ->
      map.get initial.(regs) RegisterNames.a0 = Some (word.of_Z invalidIInst) ->
      map.get initial.(regs) RegisterNames.a1 = Some a_regs ->
      map.get initial.(regs) RegisterNames.ra = Some ret_addr ->
      map.get initial.(regs) RegisterNames.sp = Some sp_val ->
      mdecode invalidIInst = MInstruction (Mul rd rs1 rs2) ->
      seps [a_regs |-> word_array regvals; initial.(pc) |-> program idecode mul_insts; R]
           initial.(mem) /\
      (forall newMem newRegs,
        seps [a_regs |-> word_array (updNz regvals rd (word.mul
                   (List.nth (Z.to_nat rs1) regvals default)
                   (List.nth (Z.to_nat rs2) regvals default)));
               initial.(pc) |-> program idecode mul_insts; R] newMem ->
        map.get newRegs RegisterNames.sp = Some sp_val ->
        post { initial with pc := ret_addr;
                            nextPc := word.add ret_addr (word.of_Z 4);
                            mem := newMem;
                            regs := newRegs (* <- regs arbitrarily changed except sp *)
                            (* log and csrs remain the same *) }) ->
      runsTo (mcomp_sat (run1 idecode)) initial post.
  Admitted.

  (* Needed if the handler wants to handle the case where the instruction is not
     a multiplication: *)
  Lemma mul_correct_2: forall initial a_regs regvals invalidIInst R (post: State -> Prop),
      initial.(nextPc) = word.add initial.(pc) (word.of_Z 4) ->
      map.get initial.(regs) RegisterNames.a0 = Some invalidIInst ->
      map.get initial.(regs) RegisterNames.a1 = Some a_regs ->
      seps [a_regs |-> word_array regvals; initial.(pc) |-> program idecode mul_insts; R]
           initial.(mem) /\
      (forall final,
        ((* case 1: It was not the Mul instruction *)
         (map.get final.(regs) RegisterNames.a0 = Some (word.of_Z 0) /\
          (forall rd rs1 rs2, decode RV32IM (word.unsigned invalidIInst) <>
                                MInstruction (Mul rd rs1 rs2)) /\
          seps [a_regs |-> word_array regvals;
                initial.(pc) |-> program idecode mul_insts; R] final.(mem))
         \/ (* case 2: It was the Mul instruction *)
         (exists ans rd rs1 rs2 v1 v2,
          map.get final.(regs) RegisterNames.a0 = Some ans /\
          word.unsigned ans <> 0 /\
          decode RV32IM (word.unsigned invalidIInst) = MInstruction (Mul rd rs1 rs2) /\
          nth_error regvals (Z.to_nat rs1) = Some v1 /\
          nth_error regvals (Z.to_nat rs2) = Some v2 /\
          seps [a_regs |-> word_array (updNz regvals rd (word.mul v1 v2));
               initial.(pc) |-> program idecode mul_insts; R] final.(mem))) ->
        (* In common: *)
        final.(pc) = word.add initial.(pc) (word.mul (word.of_Z 4)
                           (word.of_Z (Z.of_nat (List.length mul_insts)))) ->
        final.(nextPc) = word.add final.(pc) (word.of_Z 4) ->
        post final) ->
      runsTo (mcomp_sat (run1 idecode)) initial post.
  Admitted.
End Riscv.
