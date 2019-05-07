Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Kami.Lib.Word.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Encode.
Require Import coqutil.Word.LittleEndian.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import processor.KamiWord.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.Machine.
Require riscv.Platform.Memory.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Proofs.EncodeBound.
Require Import riscv.Proofs.DecodeEncode.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.Monads. Import MonadNotations.
Require Import riscv.Utility.runsToNonDet.
Require Import coqutil.Datatypes.PropSet.
Require Import riscv.Utility.MMIOTrace.
Require Import riscv.Platform.RiscvMachine.

Require Import Kami.Syntax Kami.Semantics Kami.Tactics.
Require Import Kami.Ex.MemTypes Kami.Ex.SC Kami.Ex.SCMMInl.
Require Import Kami.Ex.IsaRv32.
Require Import processor.KamiProc.

Require Import processor.KamiRiscv.

Require Import compiler.EventLoop.
Require Import compiler.ForeverSafe.

Local Open Scope Z_scope.

Section Test.

  (* TODO not sure if we want to use ` or rather a parameter record *)
  Context {M: Type -> Type}.
  Instance W: Utility.Words := @KamiWord.WordsKami width width_cases.

  Context {Registers: map.map Register word}
          {mem: map.map word byte}
          {mm: Monad M}
          {rvm: RiscvProgram M word}.

  Local Definition KamiMachine := KamiProc.hst.

  Definition instrMemSizeLg: Z := 10.

  Definition kamiStep := kamiStep instrMemSizeLg.

  Definition pad: nat := 20.
  Lemma Hpad: (2 + (Z.to_nat instrMemSizeLg) + pad = nwidth)%nat. Proof. reflexivity. Qed.

  Variable dataMemSize: nat.

  Definition states_related := states_related instrMemSizeLg pad Hpad dataMemSize.

  Lemma kamiMultiStep_sound: forall (m1 m2: KamiMachine) (m1': RiscvMachine) (t: list Event)
                               (inv: RiscvMachine -> Prop),
      star kamiStep m1 m2 t ->
      states_related (m1, nil) m1' ->
(*      (forall n, GoFlatToRiscv.mcomp_sat (runN iset n) m1' inv) ->
RiscvMachine vs MetricRiscvMachine
*)
      exists m2', states_related (m2, t) m2' /\ inv m2'.
  Proof.



  Abort.

End Test.
