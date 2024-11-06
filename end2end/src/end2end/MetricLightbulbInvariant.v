Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import coqutil.Word.LittleEndian.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Datatypes.PropSet.
Require Import compiler.RunInstruction.
Require Import compiler.RiscvEventLoop.
Require Import compiler.ForeverSafe.
Require Import compiler.GoFlatToRiscv.
Require Import coqutil.Tactics.Simp.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import compiler.Pipeline.
Require Import compilerExamples.MMIO.
Require Import compiler.FlatToRiscvDef.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import compiler.SeparationLogic.
Require Import compiler.ToplevelLoop.
Require Import compiler.CompilerInvariant.
Require Import compiler.ExprImpEventLoopSpec.
Require Import Coq.Classes.Morphisms.
Require Import coqutil.Macros.WithBaseName.
Require Import bedrock2Examples.metric_lightbulb.
Require Import bedrock2Examples.lightbulb_spec.
From coqutil Require Import SortedListWord.
From bedrock2 Require Import Syntax NotationsCustomEntry. Import Syntax.Coercions.
From compiler Require Import Symbols.
Local Open Scope Z_scope.

From coqutil Require Import Word.Naive.
Require Import coqutil.Word.Bitwidth32.
#[local] Existing Instance Naive.word.
#[local] Existing Instance Naive.word32_ok.
#[local] Existing Instance SortedListString.map.
#[local] Existing Instance SortedListString.ok.
#[local] Existing Instance SortedListWord.ok.
#[local] Existing Instance SortedListWord.map.
#[local] Instance : FlatToRiscvCommon.bitwidth_iset 32 Decode.RV32IM := eq_refl.

Definition ml : MemoryLayout (width:=32) := {|
  code_start    := word.of_Z 0;
  code_pastend  := word.of_Z (2 ^ 12);
  heap_start    := word.of_Z (2 ^ 12);
  heap_pastend  := word.of_Z (2 ^ 12 + 2 ^ 11);
  stack_start   := word.of_Z (2 ^ 12 + 2 ^ 11);
  stack_pastend := word.of_Z (2 ^ 13);
|}.
Definition buffer_addr: Z := word.unsigned ml.(heap_start).

Lemma ml_ok : MemoryLayout.MemoryLayoutOk ml. Proof. split; cbv; trivial; inversion 1. Qed.

Definition init := func! { lightbulb_init() } .
Definition loop := func! { unpack! _err = lightbulb_loop() } .
Definition funcs := &[,init; loop] ++ map.tuples function_impls.

Derive lightbulb_compiler_result SuchThat
  (ToplevelLoop.compile_prog (string_keyed_map:=@SortedListString.map) MMIO.compile_ext_call ml funcs
  = Success lightbulb_compiler_result)
  As lightbulb_compiler_result_ok.
Proof.
  match goal with x := _ |- _ => cbv delta [x]; clear x end.
  vm_compute.
  match goal with |- @Success ?A ?x = Success ?e => is_evar e;
    exact (@eq_refl (result A) (@Success A x)) end.
Qed. Optimize Heap.

Definition lightbulb_stack_size := snd lightbulb_compiler_result.
Definition lightbulb_finfo := snd (fst lightbulb_compiler_result).
Definition lightbulb_insns := fst (fst lightbulb_compiler_result).
Definition lightbulb_bytes := Pipeline.instrencode lightbulb_insns.
Definition lightbulb_symbols : list byte := Symbols.symbols lightbulb_finfo.

Lemma compiler_emitted_valid_instructions :
  bverify.bvalidInstructions Decode.RV32IM lightbulb_insns = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Require Import compiler.CompilerInvariant.
Require Import compiler.NaiveRiscvWordProperties.
Import TracePredicate TracePredicateNotations metric_SPI lightbulb_spec.

Definition goodObservables iol (mc : MetricLogging.MetricLog) :=
  exists ioh, metric_SPI.mmio_trace_abstraction_relation ioh iol /\
                               goodHlTrace _ ioh.

Definition lightbulb_spec : ProgramSpec := {|
  datamem_start := MemoryLayout.heap_start ml;
  datamem_pastend := MemoryLayout.heap_pastend ml;
  ExprImpEventLoopSpec.goodObservables := goodObservables;
  isReady t m := exists buf R,
    (Separation.sep (Array.array Scalars.scalar8 (word.of_Z 1) (word.of_Z buffer_addr) buf) R) m /\
    Z.of_nat (Datatypes.length buf) = 1520;
|}.

Import ToplevelLoop GoFlatToRiscv regs_initialized LowerPipeline.
Require Import bedrock2.WordNotations. Local Open Scope word_scope.
Import bedrock2.Map.Separation. Local Open Scope sep_scope.
Require Import bedrock2.ReversedListNotations.
Local Notation run_one_riscv_instr := (mcomp_sat (run1 Decode.RV32IM)).
Local Notation RiscvMachine := MetricRiscvMachine.
Local Notation run1 := (mcomp_sat (run1 Decode.RV32IM)).
Implicit Types mach : RiscvMachine.
Local Coercion word.unsigned : word.rep >-> Z.

Definition initial_conditions mach :=
  code_start ml = mach.(getPc) /\
  [] = mach.(getLog) /\
  mach.(getNextPc) = word.add mach.(getPc) (word.of_Z 4) /\
  regs_initialized (getRegs mach) /\
  (forall a : word32, code_start ml <= a < code_pastend ml -> In a (getXAddrs mach)) /\
  valid_machine mach /\
  (imem (code_start ml) (code_pastend ml) lightbulb_insns ⋆
   mem_available (heap_start ml) (heap_pastend ml) ⋆
   mem_available (stack_start ml) (stack_pastend ml)) (getMem mach).

Lemma initial_conditions_sufficient mach :
  initial_conditions mach ->
  CompilerInvariant.initial_conditions compile_ext_call ml lightbulb_spec mach.
Proof.
  intros (? & ? & ? & ? & ? & ? & ?).
  econstructor.
  eexists lightbulb_insns.
  eexists lightbulb_finfo.
  eexists lightbulb_stack_size.
  rewrite lightbulb_compiler_result_ok; ssplit; trivial using compiler_emitted_valid_instructions; try congruence.
  2,3:vm_compute; inversion 1.
  1: econstructor (* ProgramSatisfiesSpec *).
  1: vm_compute; reflexivity.
  1: instantiate (1:=snd init).
  3: instantiate (1:=snd loop).
  1,3: exact eq_refl.
  1,2: cbv [hl_inv init loop]; cbn [fst snd]; intros; eapply MetricWeakestPreconditionProperties.sound_cmd.
  all : repeat MetricProgramLogic.straightline.

  (*
MetricWeakestPrecondition.cmd (map.of_list funcs)
  (snd init) [] m0 map.empty mc0
  (fun (t : trace) (m : SortedListWord.map word32 Init.Byte.byte)
     (_ : SortedListString.map word32) (mc : MetricLogging.MetricLog) =>
   isReady lightbulb_spec t m /\ goodObservables lightbulb_spec t mc)

========================= (2 / 2)

MetricWeakestPrecondition.cmd (map.of_list funcs)
  (snd loop) t m l mc
  (fun (t0 : trace) (m0 : SortedListWord.map word32 Init.Byte.byte)
     (_ : SortedListString.map word32) (mc0 : MetricLogging.MetricLog) =>
   isReady lightbulb_spec t0 m0 /\
   goodObservables lightbulb_spec t0 (eventLoopJumpMetrics mc0))
   *)
Admitted.

Import OmniSmallstepCombinators.

Theorem lightbulb_correct : forall mach : MetricRiscvMachine, initial_conditions mach ->
  always run1 (eventually run1 (fun mach' => goodObservables mach'.(getLog) (MetricsToRiscv.raiseMetrics mach'.(getMetrics)))) mach.
Proof.
  intros ? H%initial_conditions_sufficient; revert H.
  unshelve rapply @always_eventually_observables; trivial using ml_ok, @Naive.word32_ok.
  { eapply (naive_word_riscv_ok 5%nat). }
  { eapply @compile_ext_call_correct; try exact _. }
Qed.

Print Assumptions lightbulb_correct.
