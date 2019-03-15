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

Set Implicit Arguments.

Axiom TODO: False.

Module Import FlatToRiscv32.
  Export FlatToRiscvDef.FlatToRiscvDef.

  Class parameters := {
    def_params :> FlatToRiscvDef.parameters;

    byte :> word.word 8;
    byte_ok :> word.ok byte;
    word :> word.word 32;
    word_ok :> word.ok word;

    locals :> map.map Register word;
    locals_ok :> map.ok locals;
    mem :> map.map word byte;
    mem_ok :> map.ok mem;

    M: Type -> Type;
    MM :> Monad M;

    W :> Utility.Words := {|
      Utility.byte := byte;
      Utility.byte_ok := byte_ok;
      Utility.width := 32;
      Utility.width_cases := or_introl eq_refl;
      Utility.word := word;
      Utility.word_ok := word_ok;
    |};

    RVM :> RiscvProgram M word;
    PRParams :> PrimitivesParams M (RiscvMachine Register actname);
    PR :> Primitives PRParams;
  }.
End FlatToRiscv32.


Section Proofs.
  Context {p: unique! FlatToRiscv32.parameters}.

  Arguments LittleEndian.combine: simpl never.

  Lemma go_load: forall sz x a (addr v: word) initialL post f,
      valid_register x ->
      valid_register a ->
      map.get initialL.(getRegs) a = Some addr ->
      Memory.load sz (getMem initialL) addr = Some v ->
      mcomp_sat (f tt)
                (withRegs (map.put initialL.(getRegs) x v) initialL) post ->
      mcomp_sat (Bind (execute (compile_load RV32IM sz x a 0)) f) initialL post.
  Proof.
    intros. unfold compile_load.
    destruct sz;
    unfold execute, ExecuteI.execute, ExecuteI64.execute, translate, DefaultRiscvState,
           Memory.load, Memory.load_Z in *;
    simp; simulate; simpl; simpl_word_exprs word_ok;
    eassumption.
  Qed.

  Lemma go_store: forall sz x a (addr v: word) initialL m' post f,
      valid_register x ->
      valid_register a ->
      map.get initialL.(getRegs) x = Some v ->
      map.get initialL.(getRegs) a = Some addr ->
      Memory.store sz (getMem initialL) addr v = Some m' ->
      mcomp_sat (f tt) (withMem m' initialL) post ->
      mcomp_sat (Bind (execute (compile_store RV32IM sz a x 0)) f) initialL post.
  Proof.
    intros. unfold compile_store.
    destruct sz;
    unfold execute, ExecuteI.execute, ExecuteI64.execute, translate, DefaultRiscvState,
           Memory.store, Memory.store_Z in *;
    simp; simulate; simpl; simpl_word_exprs word_ok; eassumption.
  Qed.

End Proofs.
