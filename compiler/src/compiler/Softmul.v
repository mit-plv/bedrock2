Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.FreeMonad.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Platform.Memory.
Require Import riscv.Spec.CSRFile.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.StringRecords.
Import RecordNotations. (* Warnings are spurious, COQBUG https://github.com/coq/coq/issues/13058 *)
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.SeparationLogic.
Require Import riscv.Platform.Run.
Require Import riscv.Platform.MinimalCSRs.
Require Import riscv.Examples.SoftmulInsts. (* <-- TODO this are hardcoded to 32bit *)
Require Import riscv.Platform.MaterializeRiscvProgram.

Section Riscv.
  Context {W: Words}.
  Context {mem: map.map word byte}.
  Context {registers: map.map Z word}.

  (* RISC-V Monad *)
  Local Notation M := (free riscv_primitive primitive_result).

  (*
  Definition mcomp_sat{A: Type}(m: M A)(initial: State)(post: A -> State -> Prop): Prop :=
      free.interpret run_primitive m initial post (fun _ => False).
   *)
  Definition mcomp_sat(m: M unit)(initial: State)(post: State -> Prop): Prop :=
    free.interpret run_primitive m initial (fun tt => post) (fun _ => False).

  Definition RVI : InstructionSet := if Z.eqb Utility.width 32 then RV32I  else RV64I.
  Definition RVIM: InstructionSet := if Z.eqb Utility.width 32 then RV32IM else RV64IM.

  Definition related(r1 r2: State): Prop :=
    r1#"regs" = r2#"regs" /\
    r1#"pc" = r2#"pc" /\
    r1#"nextPc" = r2#"nextPc" /\
    r1#"log" = r2#"log" /\
    exists mtvec_base mscratch stacktrash,
      map.get r2#"csrs" CSRField.MTVecBase = Some mtvec_base /\
      map.get r2#"csrs" CSRField.MScratch = Some mscratch /\
      List.length stacktrash = 32%nat /\
      (eq r1#"mem" * word_array (word.of_Z mscratch) stacktrash *
       program (word.of_Z (mtvec_base * 4)) handler_insts)%sep r2#"mem".

  Lemma softmul_correct: forall initialH initialL post,
      runsTo (mcomp_sat (run1 RVIM)) initialH post ->
      related initialH initialL ->
      runsTo (mcomp_sat (run1 RVI)) initialL (fun finalL =>
        exists finalH, related finalH finalL /\ post finalH).
  Proof.
    intros *. intros R. revert initialL. induction R; intros. {
      apply runsToDone. eauto.
    }
    unfold mcomp_sat in H.
    cbn [run1 Monads.Bind free.Monad_free] in H.

  Abort.

End Riscv.
