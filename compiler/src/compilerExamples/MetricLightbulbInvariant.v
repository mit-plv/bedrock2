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
  Z.add (metric finalM) (metric initialM).
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

(* very silly duplication because riscv-coq and bedrock2 don't share any common metrics
   library *)
Ltac raise_metrics_const c :=
  lazymatch c with
  | mc_spi_write_const => bedrock2Examples.metric_SPI.mc_spi_write_const
  | mc_spi_read_const => bedrock2Examples.metric_SPI.mc_spi_read_const
  | mc_spi_xchg_const => bedrock2Examples.metric_SPI.mc_spi_xchg_const
  | mc_spi_mul => bedrock2Examples.metric_SPI.mc_spi_mul
  | lightbulb_handle_cost => bedrock2Examples.metric_lightbulb.lightbulb_handle_cost
  end.

Ltac raise_metrics_getter g :=
  lazymatch g with
  | riscv.Platform.MetricLogging.instructions => bedrock2.MetricLogging.instructions
  | riscv.Platform.MetricLogging.stores => bedrock2.MetricLogging.stores
  | riscv.Platform.MetricLogging.loads => bedrock2.MetricLogging.loads
  | riscv.Platform.MetricLogging.jumps => bedrock2.MetricLogging.jumps
  end.

Ltac raise_step :=
  match goal with
  | |- context[?g ?c] =>
      let g' := raise_metrics_getter g in
      let c' := raise_metrics_const c in
      change (g c) with (g' c')
  end.

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

Definition loop_compilation_overhead :=
  MetricsToRiscv.lowerMetrics
    (cost_call PreSpill (cost_lit (prefix "reg_") ""%string loop_overhead)).

Definition loop_cost(packet_length trace_length: Z): RiscvMetrics :=
  (60 + 7 * packet_length) * mc_spi_xchg_const +
  lightbulb_handle_cost + trace_length * mc_spi_mul +
  loop_compilation_overhead.

(*------desired code width for papers: max 88 columns---------------------------------*)

Section WithMetricsScope. Open Scope metricsL.

Definition handle_request_spec(t t': trace)(mc mc': RiscvMetrics) :=
  exists dt, t' = dt ++ t /\
  exists ioh, metric_SPI.mmio_trace_abstraction_relation ioh dt /\ (
    (* Case 1: Received packet with valid command: *)
    (exists packet cmd,
        (lan9250_recv packet +++ gpio_set 23 cmd) ioh /\
        lightbulb_packet_rep cmd packet /\
        (mc' - mc <= loop_cost (length packet) (length ioh))) \/
    (* Case 2: Received invalid packet: *)
    (exists packet,
        (lan9250_recv packet) ioh /\
        not (exists cmd, lightbulb_packet_rep cmd packet) /\
        (mc' - mc <= loop_cost (length packet) (length ioh))) \/
    (* Case 3: Polled, but no new packet was available: *)
    (lan9250_recv_no_packet ioh /\
        (mc' - mc <= loop_cost 0 (length ioh))) \/
    (* Case 4: Received too long packet *)
    (lan9250_recv_packet_too_long ioh) \/
    (* Case 5: SPI protocol timeout *)
    ((TracePredicate.any +++ spi_timeout) ioh)).

End WithMetricsScope.

Compute (loop_cost 1520 0).
(*
     = {|
         Platform.MetricLogging.instructions := 10240858;
         Platform.MetricLogging.stores := 7972170;
         Platform.MetricLogging.loads := 10829445;
         Platform.MetricLogging.jumps := 7576200
       |}
     : RiscvMetrics

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

Require Import coqutil.Tactics.fwd.

Theorem metric_lightbulb_correct: forall (initial : MetricRiscvMachine) R,
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
  lazymatch goal with
  | H: successively _ _ _ |- _ => rename H into HS
  end.
  eapply successively_weaken; [exact HS | clear HS].
  cbv beta.
  clear.
  intros s s' H.
  fwd.
  eexists. split. 1: eauto.
  eexists. split. 1: eauto.

Ltac t :=
cbn [Platform.MetricLogging.instructions Platform.MetricLogging.stores Platform.MetricLogging.loads Platform.MetricLogging.jumps] in *;
    cbv [metricsAdd metricsMul] in *;
    cbv [metricAdd] in *;
          cbv [MetricsToRiscv.raiseMetrics MetricsToRiscv.lowerMetrics] in *;
          cbv [Spilling.cost_spill_spec cost_call cost_lit loop_overhead ] in *;
          change (isRegStr "") with false in *;
          change (prefix ?x ?y) with false in *;
           MetricLogging.unfold_MetricLog;  MetricLogging.simpl_MetricLog;
                         unfold_MetricLog;                simpl_MetricLog.

  unfold loop_cost, loop_compilation_overhead.
  destruct Hp1p1 as [Case1 | [Case2 | [Case3 | [Case4 | Case5] ] ] ]; fwd.
  - left. do 2 eexists. do 2 (split; eauto).
    clear -Case1p2. forget (getMetrics s') as mc'. forget (getMetrics s) as mc.
    destruct mc'. destruct mc. t.
    riscv.Platform.MetricLogging.simpl_MetricLog.
    repeat raise_step.
    Lia.lia.
  - right. left. eexists. do 2 (split; eauto).
    clear -Case2p2. forget (getMetrics s') as mc'. forget (getMetrics s) as mc.
    destruct mc'. destruct mc. t.
    riscv.Platform.MetricLogging.simpl_MetricLog.
    repeat raise_step.
    Lia.lia.
  - right. right. left. split; eauto.
    clear -Case3p1. forget (getMetrics s') as mc'. forget (getMetrics s) as mc.
    destruct mc'. destruct mc. t.
    riscv.Platform.MetricLogging.simpl_MetricLog.
    repeat raise_step.
    Lia.lia.
  - right. right. right. left. assumption.
  - do 4 right. assumption.
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
*)
