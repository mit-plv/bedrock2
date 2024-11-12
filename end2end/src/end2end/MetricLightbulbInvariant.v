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
Definition loop := func! { unpack! _err = lightbulb_loop($buffer_addr) } .
Definition funcs := &[,init; loop] ++ metric_lightbulb.funcs.
Import metric_LAN9250 metric_SPI.
Local Ltac specapply s := eapply s; [reflexivity|..].
Lemma link_lightbulb_loop : spec_of_lightbulb_loop (map.of_list funcs).
Proof.
  specapply lightbulb_loop_ok;
  (specapply recvEthernet_ok || specapply lightbulb_handle_ok);
      specapply lan9250_readword_ok; specapply spi_xchg_ok;
      (specapply spi_write_ok || specapply spi_read_ok).
Qed.
Lemma link_lightbulb_init : spec_of_lightbulb_init (map.of_list funcs).
Proof.
  specapply lightbulb_init_ok; specapply lan9250_init_ok;
  try (specapply lan9250_wait_for_boot_ok || specapply lan9250_mac_write_ok);
  (specapply lan9250_readword_ok || specapply lan9250_writeword_ok);
      specapply spi_xchg_ok;
      (specapply spi_write_ok || specapply spi_read_ok).
Qed.

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
Import bedrock2.MetricLogging bedrock2.MetricCosts MetricProgramLogic.Coercions.

Definition lightbulb_loop_cost io_wait : MetricLog :=
  ((60+7*1520)*mc_spi_xchg_const + lightbulb_handle_cost + io_wait*mc_spi_mul).

Definition goodHlTrace n : list _ -> Prop :=
  BootSeq _ +++
  multiple (EX b, Recv _ b +++ LightbulbCmd _ b|||RecvInvalid _|||PollNone _) n.

Definition goodObservables iol (mc : MetricLogging.MetricLog) :=
  exists n ioh, metric_SPI.mmio_trace_abstraction_relation ioh iol /\
  goodHlTrace n ioh /\ (mc <= n*lightbulb_loop_cost (length ioh))%metricsH.

Definition lightbulb_spec : ProgramSpec := {|
  datamem_start := MemoryLayout.heap_start ml;
  datamem_pastend := MemoryLayout.heap_pastend ml;
  ExprImpEventLoopSpec.goodObservables := goodObservables;
  isReady t m := exists buf R,
    (Separation.sep (Array.array Scalars.scalar8 (word.of_Z 1) (word.of_Z buffer_addr) buf) R) m /\
    Z.of_nat (Datatypes.length buf) = 1520;
|}.

Import ToplevelLoop GoFlatToRiscv regs_initialized LowerPipeline.
Import bedrock2.Map.Separation. Local Open Scope sep_scope.
Require Import bedrock2.ReversedListNotations.
Local Notation run_one_riscv_instr := (mcomp_sat (run1 Decode.RV32IM)).
Local Notation RiscvMachine := MetricRiscvMachine.
Local Notation run1 := (mcomp_sat (run1 Decode.RV32IM)).
Implicit Types mach : RiscvMachine.

Definition initial_conditions mach :=
  code_start ml = mach.(getPc) /\
  [] = mach.(getLog) /\
  EmptyMetricLog = mach.(getMetrics) /\
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
  { eapply MetricSemantics.weaken_call; [eapply link_lightbulb_init|cbv beta]. admit. }
  { cbv [isReady lightbulb_spec ExprImpEventLoopSpec.goodObservables goodObservables] in *.
    destruct H6 as (?&?&?&?).
    eapply MetricSemantics.weaken_call; [eapply link_lightbulb_loop|cbv beta]; eauto.
    intros.
    Simp.simp.
    repeat MetricProgramLogic.straightline.
    split; eauto.
    unfold existsl, Recv, LightbulbCmd in *.
    destruct H10p1p1p1; Simp.simp; (eexists (S n), _; Tactics.ssplit;
      [eapply Forall2_app; eauto|..]).
    all: try (progress unfold goodHlTrace;
    (*
    { unfold "+++" in H7p2|-*. left. left. Simp.simp.
      unfold Recv. eexists _, _, _; Tactics.ssplit; eauto. }
    destruct H7; Simp.simp.
    { left. right. left. left. eauto. }
    destruct H7; Simp.simp.
    { right. unfold PollNone. eauto. }
    destruct H7; Simp.simp.
    { left. right. left. right. eauto. }
    left. right. right. eauto. }
     *) admit).
    { rewrite Nat2Z.inj_succ, <-Z.add_1_l.
  Local Ltac metrics' :=
    repeat match goal with | H := _ : MetricLog |- _ => subst H end;
    cost_unfold;
    repeat match goal with
    | H: context [?x] |- _ => is_const x; let t := type of x in constr_eq t constr:(MetricLog);
      progress cbv beta delta [x] in *
    | |- context [?x] => is_const x; let t := type of x in constr_eq t constr:(MetricLog);
      progress cbv beta delta [x] in *
    end;
    cbn -[Z.add Z.mul Z.of_nat] in *;
    rewrite ?List.length_app, ?List.length_cons, ?List.length_nil, ?List.length_firstn, ?LittleEndianList.length_le_split in *;
    flatten_MetricLog; repeat unfold_MetricLog; repeat simpl_MetricLog; try blia.
    metrics'.

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
