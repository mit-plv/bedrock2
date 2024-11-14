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
Require Import Coq.Classes.Morphisms.
Require Import coqutil.Macros.WithBaseName.
Require Import bedrock2Examples.metric_lightbulb.
Require Import bedrock2Examples.lightbulb_spec.
From Coq Require Import Derive.
From riscv Require Import bverify.
From coqutil Require Import SortedListWord.
From bedrock2 Require Import Syntax NotationsCustomEntry. Import Syntax.Coercions.
From compiler Require Import Symbols.
Local Open Scope Z_scope.

From coqutil Require Import Word.Naive.
Require Import coqutil.Word.Bitwidth32.
Require Import compiler.NaiveRiscvWordProperties.
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

Definition loop := func! { unpack! _err = lightbulb_loop($buffer_addr) } .
Definition funcs := &[,loop] ++ metric_lightbulb.funcs.
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

Derive out SuchThat (compile_prog compile_ext_call "lightbulb_init" "loop" ml funcs = Success (fst (fst out), snd (fst out), snd out)) As out_ok.
Proof.
  erewrite <-!surjective_pairing.
  match goal with x := _ |- _ => cbv delta [x]; clear x end.
  vm_compute.
  match goal with |- @Success ?A ?x = Success ?e =>
    exact (@eq_refl (result A) (@Success A x)) end.
Qed. Optimize Heap.

Import TracePredicate TracePredicateNotations metric_SPI lightbulb_spec.
Import bedrock2.MetricLogging bedrock2.MetricCosts MetricProgramLogic.Coercions.

Definition loop_progress t t' dmc :=
  exists dt, t' = dt ++ t /\
  exists ioh, metric_SPI.mmio_trace_abstraction_relation ioh dt /\
  let dmc := metricsSub (MetricsToRiscv.raiseMetrics dmc) (cost_call PreSpill (cost_lit (prefix "reg_") ""%string loop_overhead)) in
  (* spec_of_lightbulb_loop postcondition without return value: *)
  (exists packet cmd, (lan9250_recv _ packet +++ gpio_set _ 23 cmd) ioh /\ lightbulb_packet_rep _ cmd packet /\
  ((dmc <= (60+7*length packet)*mc_spi_xchg_const + lightbulb_handle_cost + (length ioh)*mc_spi_mul))%metricsH
  ) \/
  (exists packet, (lan9250_recv _ packet) ioh /\ not (exists cmd, lightbulb_packet_rep _ cmd packet) /\
  ((dmc  <= (60+7*length packet)*mc_spi_xchg_const + lightbulb_handle_cost + (length ioh)*mc_spi_mul))%metricsH
  ) \/
  (lan9250_recv_no_packet _ ioh /\
  ((dmc  <= (60                )*mc_spi_xchg_const + lightbulb_handle_cost + (length ioh)*mc_spi_mul))%metricsH) \/
  (lan9250_recv_packet_too_long _ ioh) \/
  ((TracePredicate.any +++ (spi_timeout _)) ioh).

(* We want to prove a theorem that's purely about RISC-V execution, so we want
   to express everything in terms of RISC-V metrics (metricL notation scope),
   but that doesn't have all the operators yet *)
Notation RiscvMetrics := Platform.MetricLogging.MetricLog.

Definition metricAdd(metric: RiscvMetrics -> Z) finalM initialM: Z :=
  Z.sub (metric finalM) (metric initialM).
Definition metricsAdd := Platform.MetricLogging.metricsOp metricAdd.
Infix "+" := metricsAdd : MetricL_scope.

Definition metricsMul (n : Z) (m : RiscvMetrics) :=
  riscv.Platform.MetricLogging.mkMetricLog
    (n * riscv.Platform.MetricLogging.instructions m)
    (n * riscv.Platform.MetricLogging.stores m)
    (n * riscv.Platform.MetricLogging.loads m)
    (n * riscv.Platform.MetricLogging.jumps m).
Infix "*" := metricsMul : MetricL_scope.

Definition mc_spi_write_const :=
  riscv.Platform.MetricLogging.mkMetricLog 348 227 381 204.
Definition mc_spi_read_const :=
  riscv.Platform.MetricLogging.mkMetricLog 199 116 217 103.
Definition mc_spi_xchg_const :=
  (mc_spi_write_const + mc_spi_read_const +
     riscv.Platform.MetricLogging.mkMetricLog 410 402 414 401)%metricsL.
Definition mc_spi_mul := riscv.Platform.MetricLogging.mkMetricLog 157 109 169 102.
Definition lightbulb_handle_cost :=
  riscv.Platform.MetricLogging.mkMetricLog 552 274 639 203.

(*
  let dmc := metricsSub (MetricsToRiscv.raiseMetrics dmc) (cost_call PreSpill (cost_lit (prefix "reg_") ""%string loop_overhead)) in
 *)

(* TODO fix implicit-ness status at definition site *)
Arguments OP {word}.
Arguments lan9250_recv {word}.
Arguments lightbulb_packet_rep {word}.
Arguments gpio_set {word}.
Arguments lan9250_recv_packet_too_long {word}.
Arguments spi_timeout {word}.
Arguments lan9250_recv_no_packet {word}.

(*------desired code width for papers: max 88 columns---------------------------------*)

Section WithMetricsScope. Open Scope metricsL.

Definition handle_request_spec(t t': trace)(mc mc': RiscvMetrics) :=
  exists dt, t' = dt ++ t /\
  exists ioh, metric_SPI.mmio_trace_abstraction_relation ioh dt /\ (
    (* Case 1: Received packet with valid command: *)
    (exists packet cmd,
        (lan9250_recv packet +++ gpio_set 23 cmd) ioh /\
        lightbulb_packet_rep cmd packet /\
        ((mc-mc' <= (60+7*length packet)*mc_spi_xchg_const +
                    lightbulb_handle_cost + (length ioh)*mc_spi_mul))) \/
    (* Case 2: Received invalid packet: *)
    (exists packet,
        (lan9250_recv packet) ioh /\
        not (exists cmd, lightbulb_packet_rep cmd packet) /\
        ((mc-mc' <= (60+7*length packet)*mc_spi_xchg_const +
                    lightbulb_handle_cost + (length ioh)*mc_spi_mul))) \/
    (* Case 3: Polled, but no new packet was available: *)
    (lan9250_recv_no_packet ioh /\
        ((mc-mc' <= (60                )*mc_spi_xchg_const +
                    lightbulb_handle_cost + (length ioh)*mc_spi_mul))) \/
    (* Case 4: Received too long packet *)
    (lan9250_recv_packet_too_long ioh) \/
    (* Case 5: SPI protocol timeout *)
    ((TracePredicate.any +++ spi_timeout) ioh)).

End WithMetricsScope.

Compute
let length_packet := 1520%nat in
bedrock2.MetricLogging.metricsAdd (cost_call PreSpill (cost_lit (prefix "reg_") ""%string loop_overhead)) (((60+7*length_packet)*bedrock2Examples.metric_SPI.mc_spi_xchg_const + bedrock2Examples.metric_lightbulb.lightbulb_handle_cost + 0*bedrock2Examples.metric_SPI.mc_spi_mul)).

(*
= {|
         instructions := 10240858;
         stores := 7972170;
         loads := 10829445;
         jumps := 7576200
       |}
     : MetricLog

     (* 10M instructions, less than 0.85ss at 12MHz or less 32ms at 320MHz (plus I/O wait) *)
 *)

Local Notation run1 := (ToplevelLoop.run1 (iset:=Decode.RV32I)).

Lemma mem_available_to_seplog: forall m0,
    LowerPipeline.mem_available (heap_start ml) (heap_pastend ml) m0 ->
    exists buf R,
      (array ptsto (word.of_Z 1) (word.of_Z buffer_addr) buf * R)%sep m0 /\
      Datatypes.length buf = 1520 :> Z.
Proof.
  intros. unfold LowerPipeline.mem_available, ex1 in *.
  destruct H as (buf & mp & mq & Sp & P & Q).
  unfold emp in P. destruct P as (E & P). subst mp.
  eapply map.split_empty_l in Sp. subst mq.
  change (Z.of_nat (Datatypes.length buf) = 2048) in P.
  unfold LowerPipeline.ptsto_bytes, buffer_addr in *.
  (* Set Printing Coercions. *) rewrite word.of_Z_unsigned.
  rewrite <- (List.firstn_skipn 1520 buf) in Q.
  eapply array_append in Q.
  do 2 eexists. split. 1: exact Q.
  rewrite List.firstn_length. Lia.lia.
Qed.

Module riscv.
  (* just implicit arguments, as inferred by Coq in previous version
     that used Ltac... :P *)
  Definition run1 :=
    (@ToplevelLoop.run1 (2 ^ Nat.log2 32) BW32 (Naive.word (2 ^ Nat.log2 32))
       (@map (2 ^ Nat.log2 32) (Naive.word (2 ^ Nat.log2 32)) word32_ok Init.Byte.byte)
       (Z_keyed_SortedListMap.Zkeyed_map (Naive.word (2 ^ Nat.log2 32)))
       (FreeMonad.free.free
          (@MetricMaterializeRiscvProgram.action 32 BW32 (Naive.word (2 ^ Nat.log2 32)))
          (@MetricMaterializeRiscvProgram.result 32 BW32 (Naive.word (2 ^ Nat.log2 32))))
       (@FreeMonad.free.Monad_free
          (@MetricMaterializeRiscvProgram.action 32 BW32 (Naive.word (2 ^ Nat.log2 32)))
          (@MetricMaterializeRiscvProgram.result 32 BW32 (Naive.word (2 ^ Nat.log2 32))))
       (@MetricMaterializeRiscvProgram.MetricMaterialize 32 BW32
          (Naive.word (2 ^ Nat.log2 32)))
       (@MetricMinimalMMIO.MetricMinimalMMIOPrimitivesParams 32 BW32
          (Naive.word (2 ^ Nat.log2 32))
          (@map (2 ^ Nat.log2 32) (Naive.word (2 ^ Nat.log2 32)) word32_ok
             Init.Byte.byte)
          (Z_keyed_SortedListMap.Zkeyed_map (Naive.word (2 ^ Nat.log2 32)))
          (@FE310ExtSpec.FE310_mmio 32 BW32 (Naive.word (2 ^ Nat.log2 32))
             (@map (2 ^ Nat.log2 32) (Naive.word (2 ^ Nat.log2 32)) word32_ok
                Init.Byte.byte))) RV32IM).
End riscv.

Import coqutil.Semantics.OmniSmallstepCombinators.

Lemma eventually_weaken_step {State} f g P (s : State) :
  eventually f P s ->  (forall t Q, f t Q -> g t Q) -> eventually g P s.
Proof. induction 1; [econstructor 1 | econstructor 2]; eauto. Qed.

Lemma always_weaken_step {State} f g P (s : State) :
  always f P s ->  (forall t Q, f t Q -> g t Q) ->  always g P s.
Proof. intros [] ?; eapply mk_always; intuition eauto. Qed.

Lemma successively_weaken {State} step Q R (s : State) :
  successively step Q s -> (forall x y, Q x y -> R x y) -> successively step R s.
Proof.
  intros; eapply always_weaken_step; eauto; cbv beta; intros.
  eapply eventually_weaken; eauto; cbv beta.
  intuition eauto.
Qed.

Lemma successively_weaken_step {State} f g R (s : State) :
  successively f R s -> (forall t Q, f t Q -> g t Q) ->
  successively g R s.
Proof. intros; eapply always_weaken_step; eauto; cbv beta; eauto using eventually_weaken_step. Qed.

Axiom TODO: False.

Lemma metric_lightbulb_correct: forall (initial : MetricRiscvMachine) R,
    valid_machine initial ->
    getLog initial = [] ->
    regs_initialized.regs_initialized (getRegs initial) ->
    getNextPc initial = word.add (getPc initial) (word.of_Z 4) ->
    getPc initial = code_start ml ->
    (program RV32IM (code_start ml) (fst (fst out)) * R *
       LowerPipeline.mem_available (heap_start ml) (heap_pastend ml) *
       LowerPipeline.mem_available (stack_start ml) (stack_pastend ml))%sep
      (getMem initial) ->
    subset (footpr (program RV32IM (code_start ml) (fst (fst out))))
      (of_list (getXAddrs initial)) ->
    eventually riscv.run1
      (successively riscv.run1
         (fun s s' : MetricRiscvMachine =>
            handle_request_spec (getLog s) (getLog s')
              (getMetrics s) (getMetrics s'))) initial.
Proof.

intros.

eapply eventually_weaken.
1: refine (
let bedrock2_invariant t m := exists buf R,
  (Separation.sep (Array.array Scalars.scalar8 (word.of_Z 1) (word.of_Z buffer_addr) buf) R) m /\
  Z.of_nat (Datatypes.length buf) = 1520 in

successively_execute_bedrock2_loop
(word_riscv_ok:=naive_word_riscv_ok (Nat.log2 32))
compile_ext_call
ltac:(eapply @compile_ext_call_correct; try exact _)
ltac:(trivial)
"lightbulb_init"
"loop"
ml
funcs
ml_ok
loop_progress
bedrock2_invariant
_
(snd lightbulb_init)
_
_
(snd loop)
_
_
_
_
_
_
_
ltac:(unfold initial_conditions; Tactics.ssplit)
).

1:vm_compute; reflexivity.
1:vm_compute; reflexivity.
all : cycle 1.
1:vm_compute; reflexivity.
all : cycle 1.
1:eassumption.
1:eassumption.
1:eassumption.
1:eassumption.
1:eassumption.
all : cycle 1.
all : cycle 1.
all : cycle 1.
all : cycle 1.
1:exact out_ok.
all : cycle -1.
all : cycle -1.
all : cycle -1.
all : cycle -1.
1:eassumption.
1:eassumption.
1:apply Z.lt_le_incl; vm_compute; reflexivity.
1:apply Z.lt_le_incl; vm_compute; reflexivity.
{
  unfold loop_progress, handle_request_spec.
  intros.
  eapply successively_weaken; eauto; cbv beta.
  repeat (intuition Simp.simp); eauto 9; [| |].
  all : eexists; split; eauto.
  all : eexists; split; eauto.
  1: left; exists packet, cmd; intuition eauto.
  2: right; left; exists packet; intuition eauto.
  3: right; right; left; intuition eauto.
all :
    (* metrics accounting *)
    repeat (
    repeat match goal with | H := _ : MetricLog |- _ => subst H end;
    repeat match goal with | H := _ : RiscvMetrics |- _ => subst H end;
    repeat match goal with
    | H: context [?x] |- _ => is_const x; let t := type of x in constr_eq t constr:(MetricLog);
      progress cbv beta delta [x] in *
    | |- context [?x] => is_const x; let t := type of x in constr_eq t constr:(MetricLog);
      progress cbv beta delta [x] in *
    | H: context [?x] |- _ => is_const x; let t := type of x in constr_eq t constr:(RiscvMetrics);
      progress cbv beta delta [x] in *
    | |- context [?x] => is_const x; let t := type of x in constr_eq t constr:(RiscvMetrics);
      progress cbv beta delta [x] in *
    end;
    cbn [Platform.MetricLogging.instructions Platform.MetricLogging.stores Platform.MetricLogging.loads Platform.MetricLogging.jumps] in *;
    cbv [metricsAdd metricsMul] in *;
    cbv [metricAdd] in *;
          cbv [MetricsToRiscv.raiseMetrics MetricsToRiscv.lowerMetrics] in *;
          cbv [Spilling.cost_spill_spec cost_call cost_lit loop_overhead ] in *;
          change (isRegStr "") with false in *;
          change (prefix ?x ?y) with false in *;
           MetricLogging.unfold_MetricLog;  MetricLogging.simpl_MetricLog;
                         unfold_MetricLog;                simpl_MetricLog);
          intuition try blia.
    1,2,3,4,5,6,7,8,9,10,11,12 : case TODO.
}
{
  intros.
  edestruct link_lightbulb_init as (?&?&?&D&?&E&X).
  vm_compute in D; inversion D; subst; clear D.
  apply map.of_list_zip_nil_values in E; case E as []; subst.
  eapply MetricSemantics.exec.weaken; [exact X|].
  cbv beta; intros * ?; intros (?&?&?&?&?&?&?&?&?); subst.
  cbv [bedrock2_invariant].
  eapply mem_available_to_seplog. assumption. }
{ cbv [bedrock2_invariant handle_request_spec].
  intros; eapply MetricWeakestPreconditionProperties.sound_cmd.
  repeat MetricProgramLogic.straightline.
  { eapply MetricSemantics.weaken_call; [eapply link_lightbulb_loop|cbv beta]; try eassumption.
    intros * (?&?&?&?&?&?&?&?).
    repeat MetricProgramLogic.straightline; exists []; split; [exact eq_refl|].
    split. { eexists _, _; split; eassumption. }
    eexists; split; [exact eq_refl|].
    eexists; split; [eassumption|].
    intuition (Simp.simp; eauto).
    1: left; exists packet, cmd; intuition eauto.
    2: right; left; exists packet; intuition eauto.
all :
    repeat (
    repeat match goal with | H := _ : MetricLog |- _ => subst H end;
    repeat match goal with
    | H: context [?x] |- _ => is_const x; let t := type of x in constr_eq t constr:(MetricLog);
      progress cbv beta delta [x] in *
    | |- context [?x] => is_const x; let t := type of x in constr_eq t constr:(MetricLog);
      progress cbv beta delta [x] in *
    end;
    cbn [Platform.MetricLogging.instructions Platform.MetricLogging.stores Platform.MetricLogging.loads Platform.MetricLogging.jumps] in *;
          cbv [MetricsToRiscv.raiseMetrics MetricsToRiscv.lowerMetrics] in *;
          cbv [Spilling.cost_spill_spec cost_call cost_lit loop_overhead ] in *;
          change (isRegStr "") with false in *;
          change (prefix ?x ?y) with false in *;
           MetricLogging.unfold_MetricLog;  MetricLogging.simpl_MetricLog;
                         unfold_MetricLog;                simpl_MetricLog);
          intuition try blia. } }
Qed.

Import OmniSmallstepCombinators.
Check metric_lightbulb_correct.

(*
metric_lightbulb_correct
     : forall (initial : MetricRiscvMachine)
         (R : map (Naive.word (2 ^ Nat.log2 32)) Init.Byte.byte -> Prop),
       valid_machine initial ->
       getLog initial = [] ->
       regs_initialized.regs_initialized (getRegs initial) ->
       getNextPc initial = word.add (getPc initial) (word.of_Z 4) ->
       getPc initial = code_start ml ->
       (program RV32IM (code_start ml) (fst (fst out)) * R *
        LowerPipeline.mem_available (heap_start ml) (heap_pastend ml) *
        LowerPipeline.mem_available (stack_start ml) (stack_pastend ml))%sep
         (getMem initial) ->
       subset (footpr (program RV32IM (code_start ml) (fst (fst out))))
         (of_list (getXAddrs initial)) ->
       eventually riscv.run1
         (successively riscv.run1
            (fun s s' : MetricRiscvMachine =>
             handle_request_spec (getLog s) (getLog s') (getMetrics s) (getMetrics s')))
         initial
 *)

Print Assumptions metric_lightbulb_correct.
(*
Axioms:
PropExtensionality.propositional_extensionality :
  forall P Q : Prop, P <-> Q -> P = Q
functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
TODO : False
used in metric_lightbulb_correct to prove
 successively riscv.run1
   (fun s s' : MetricRiscvMachine =>
    exists dt : list Semantics.LogItem,
      getLog s' = dt ++ getLog s /\
      (exists ioh : list OP,
         metric_SPI.mmio_trace_abstraction_relation ioh dt /\
         ((exists (packet : list Init.Byte.byte) (cmd : bool),
             (lan9250_recv packet +++ gpio_set 23 cmd) ioh /\
             lightbulb_packet_rep cmd packet /\
             (getMetrics s - getMetrics s' <=
              (60 + 7 * Datatypes.length packet) * mc_spi_xchg_const +
              lightbulb_handle_cost + Datatypes.length ioh * mc_spi_mul)%metricsL) \/
          (exists packet : list Init.Byte.byte,
             lan9250_recv packet ioh /\
             ~ (exists cmd : bool, lightbulb_packet_rep cmd packet) /\
             (getMetrics s - getMetrics s' <=
              (60 + 7 * Datatypes.length packet) * mc_spi_xchg_const +
              lightbulb_handle_cost + Datatypes.length ioh * mc_spi_mul)%metricsL) \/
          lan9250_recv_no_packet ioh \/
          lan9250_recv_packet_too_long ioh \/ (any +++ spi_timeout) ioh))) final
*)
(*------desired code width for papers: max 85 columns------------------------------*)
(* OLD STUFF BELOW, may be useful for instantiating some assumptions




Definition bedrock2_invariant

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

*)
