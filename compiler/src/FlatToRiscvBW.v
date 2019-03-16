Require Import lib.LibTacticsMin.
Require Import riscv.Utility.Monads. Require Import riscv.Utility.MonadNotations.
Require Import coqutil.Macros.unique.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Spec.Execute.
Require Import riscv.Platform.Run.
Require Import riscv.Platform.Memory.
Require Import riscv.Utility.PowerFunc.
Require Import riscv.Utility.ListLib.
Require Import coqutil.Decidable.
Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Spec.Primitives.
Require Import Coq.micromega.Lia.
Require Import riscv.Utility.div_mod_to_quot_rem.
Require Import compiler.util.Misc.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.ZBitOps.
Require Import compiler.util.Common.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.Rem4.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.EmitsValid.
Require Import compiler.SeparationLogic.
Require Import bedrock2.Scalars.
Require Import compiler.Simp.
Require Import compiler.SimplWordExpr.

Local Open Scope ilist_scope.
Local Open Scope Z_scope.


Module Import FlatToRiscvBW.
  Export FlatToRiscvDef.FlatToRiscvDef.

  Class parameters(width: Z)(width_cases: width = 32 \/ width = 64) := {
    byte :> word.word 8;
    byte_ok :> word.ok byte;
    word :> word.word width;
    word_ok :> word.ok word;

    W :> Utility.Words := {|
      Utility.byte := byte;
      Utility.byte_ok := byte_ok;
      Utility.width := width;
      Utility.width_cases := width_cases;
      Utility.word := word;
      Utility.word_ok := word_ok;
    |};

    actname : Type;
    compile_ext_call : list Register -> actname -> list Register -> list Instruction;
    max_ext_call_code_size : actname -> Z;
    compile_ext_call_length : forall (binds : list Register) (f : actname) (args : list Register),
                              Zlength (compile_ext_call binds f args) <= max_ext_call_code_size f;
    compile_ext_call_emits_valid : forall (iset : InstructionSet) (binds : list Register)
                                     (a : actname) (args : list Register),
                                   Forall valid_register binds ->
                                   Forall valid_register args ->
                                   valid_instructions iset (compile_ext_call binds a args);

    locals :> map.map Register word;
    locals_ok :> map.ok locals;
    mem :> map.map word byte;
    mem_ok :> map.ok mem;

    M: Type -> Type;
    MM :> Monad M;

    RVM :> RiscvProgram M word;
    PRParams :> PrimitivesParams M (RiscvMachine Register actname);
    PR :> Primitives PRParams;
  }.

  Instance def_params{width: Z}{width_cases: width = 32 \/ width = 64}
        (p: parameters width width_cases): FlatToRiscvDef.parameters := {
    FlatToRiscvDef.FlatToRiscvDef.actname := actname;
    FlatToRiscvDef.FlatToRiscvDef.compile_ext_call := compile_ext_call;
    FlatToRiscvDef.FlatToRiscvDef.max_ext_call_code_size := max_ext_call_code_size;
    FlatToRiscvDef.FlatToRiscvDef.compile_ext_call_length := compile_ext_call_length;
    FlatToRiscvDef.FlatToRiscvDef.compile_ext_call_emits_valid := compile_ext_call_emits_valid;
  }.

  Class proofs{width: Z}{width_cases: width = 32 \/ width = 64}
        (p: parameters width width_cases) := {
    go_load: forall sz x a (addr v: word) initialL post f,
      valid_register x ->
      valid_register a ->
      map.get initialL.(getRegs) a = Some addr ->
      Memory.load sz (getMem initialL) addr = Some v ->
      mcomp_sat (f tt)
                (withRegs (map.put initialL.(getRegs) x v) initialL) post ->
      mcomp_sat (Bind (execute (compile_load sz x a 0)) f) initialL post;

   go_store: forall sz x a (addr v: word) initialL m' post f,
      valid_register x ->
      valid_register a ->
      map.get initialL.(getRegs) x = Some v ->
      map.get initialL.(getRegs) a = Some addr ->
      Memory.store sz (getMem initialL) addr v = Some m' ->
      mcomp_sat (f tt) (withMem m' initialL) post ->
      mcomp_sat (Bind (execute (compile_store sz a x 0)) f) initialL post;
  }.

End FlatToRiscvBW.


Section Proofs32.
  Context (p: FlatToRiscvBW.parameters 32 (or_introl eq_refl)).

  Arguments LittleEndian.combine: simpl never.

  Instance Proofs32: proofs p.
  Proof.
    constructor.
    - intros. unfold compile_load.
      destruct sz;
        unfold execute, ExecuteI.execute, ExecuteI64.execute, translate, DefaultRiscvState,
        Memory.load, Memory.load_Z in *;
        simp; simulate; simpl; simpl_word_exprs word_ok;
          try eassumption.
    - intros. unfold compile_store.
      destruct sz;
        unfold execute, ExecuteI.execute, ExecuteI64.execute, translate, DefaultRiscvState,
        Memory.store, Memory.store_Z in *;
        simp; simulate; simpl; simpl_word_exprs word_ok; eassumption.
  Qed.

End Proofs32.


Section Proofs64.
  Context (p: FlatToRiscvBW.parameters 64 (or_intror eq_refl)).

  Arguments LittleEndian.combine: simpl never.

  Instance Proofs64: proofs p.
  Proof.
    constructor.
    - intros. unfold compile_load.
      destruct sz;
        unfold execute, ExecuteI.execute, ExecuteI64.execute, translate, DefaultRiscvState,
        Memory.load, Memory.load_Z in *;
        simp; simulate; simpl; simpl_word_exprs word_ok;
          eassumption.
    - intros. unfold compile_store.
      destruct sz;
        unfold execute, ExecuteI.execute, ExecuteI64.execute, translate, DefaultRiscvState,
        Memory.store, Memory.store_Z in *;
        simp; simulate; simpl; simpl_word_exprs word_ok; eassumption.
  Qed.

End Proofs64.

Lemma ProofsBWHelper:
  forall (is32Bit: bool),
    let width: Z := if is32Bit then 32 else 64 in
    let width_cases: width = 32 \/ width = 64 :=
        if is32Bit as b return ((if b then 32 else 64) = 32 \/ (if b then 32 else 64) = 64)
        then or_introl eq_refl
        else or_intror eq_refl in
    forall (p: FlatToRiscvBW.parameters width width_cases), proofs p.
Proof.
  intro is32Bit. case is32Bit; simpl.
  - exact Proofs32.
  - exact Proofs64.
Qed.

Instance ProofsBW:
  forall (width: Z) (width_cases: width = 32 \/ width = 64)
         (p: FlatToRiscvBW.parameters width width_cases), proofs p.
Proof.
  intros width width_cases. destruct width_cases as [C | C].
  - pose proof (ProofsBWHelper true) as P. simpl in P. rewrite C. exact P.
  - pose proof (ProofsBWHelper false) as P. simpl in P. rewrite C. exact P.
Qed.
