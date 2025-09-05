Require Import Coq.Lists.List.
Import ListNotations.
Require bedrock2Examples.Demos.
Require Import coqutil.Decidable.
Require Import bedrock2.NotationsCustomEntry coqutil.Macros.WithBaseName.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Pipeline.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import riscv.Utility.Monads.
Require Import compiler.util.Common.
Require Import coqutil.Decidable.
Require        riscv.Utility.InstructionNotations.
Require Import riscv.Platform.MinimalLogging.
Require Import bedrock2.MetricLogging.
Require Import riscv.Platform.MetricMinimal.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
Require Import coqutil.Map.SortedList.
Require Import coqutil.Tactics.fwd.
Require Import compiler.MemoryLayout.
Require Import compiler.StringNameGen.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Spec.LeakageOfInstr.
Require Import riscv.Spec.Decode.
Require compiler.NaiveRiscvWordProperties.
Require Import bedrock2.MetricLeakageSemantics.
Require Import compiler.MMIO.
Require Import bedrock2.FE310CSemantics.
Require Import coqutil.Map.SortedListZ.
Require Import compiler.util.Common.
Require Import bedrock2Examples.one_printer.

Open Scope Z_scope. Open Scope string_scope. Open Scope ilist_scope.

Notation RiscvMachine := MetricRiscvMachine.

Local Existing Instance coqutil.Map.SortedListString.map.
Local Existing Instance coqutil.Map.SortedListString.ok.
Local Instance mem32 : map.map Words32Naive.word Init.Byte.byte := SortedListWord.map Words32Naive.word byte.
Local Instance mem32_ok : map.ok mem32 := SortedListWord.ok _ _.
Local Instance localsL32 : map.map Z Words32Naive.word := SortedListZ.map Words32Naive.word.
Local Instance localsL32_ok : map.ok localsL32 := SortedListZ.ok _.
Local Instance localsH32: map.map string Words32Naive.word := SortedListString.map Words32Naive.word.
Local Instance localsH32_ok : map.ok localsH32 := SortedListString.ok _.
Local Instance RV32I_bitwidth: FlatToRiscvCommon.bitwidth_iset 32 RV32I := eq_refl.

Lemma word_ok : RiscvWordProperties.word.riscv_ok Words32Naive.word.
Proof.
  cbv [Words32Naive.word]. replace 32 with (2 ^ BinInt.Z.of_nat 5) by reflexivity.
  apply NaiveRiscvWordProperties.naive_word_riscv_ok.
Qed.

Lemma word_ok' : word.ok Words32Naive.word.
Proof. exact Naive.word32_ok. Qed.

Definition fs_one_printer := &[,one_printer_fun].
Definition instrs_one_printer :=
  match (compile compile_ext_call fs_one_printer) with
  | Success (instrs, _, _) => instrs
  | _ => nil
  end.
Definition finfo_one_printer :=
  match (compile compile_ext_call fs_one_printer) with
  | Success (_, finfo, _) => finfo
  | _ => nil
  end.
Definition req_stack_size_one_printer :=
  match (compile compile_ext_call fs_one_printer) with
  | Success (_, _, req_stack_size) => req_stack_size
  | _ => 0
  end.
Definition fname_one_printer := "one_printer_fun".
Definition f_rel_pos_one_printer := 0.

Theorem one_printer_prints_ones :
  forall p_funcs stack_hi ret_addr,
  forall m stack_lo
    Rdata Rexec (initial : RiscvMachine),
    req_stack_size_one_printer <= word.unsigned (word.sub stack_hi stack_lo) / SeparationLogic.bytes_per_word ->
    word.unsigned (word.sub stack_hi stack_lo) mod SeparationLogic.bytes_per_word = 0 ->
    getPc initial = word.add p_funcs (word.of_Z f_rel_pos_one_printer) ->
    initial.(getTrace) = Some [] ->
    map.get (getRegs initial) RegisterNames.ra = Some ret_addr ->
    word.unsigned ret_addr mod 4 = 0 ->
    LowerPipeline.arg_regs_contain (getRegs initial) [] ->
    LowerPipeline.machine_ok p_funcs stack_lo stack_hi instrs_one_printer m Rdata Rexec initial ->
    FlatToRiscvCommon.runsTo initial
      (fun s' =>
         exists garbage_length : nat,
         forall num_ones : nat,
           FlatToRiscvCommon.runsTo s'
             (fun s'' =>
                exists garbage,
                  Datatypes.length garbage = garbage_length /\
                    getLog s'' = (repeat one num_ones ++ garbage)%list)).
Proof.
  assert (spec := @eventual_one_printer_eventually_prints_ones _ Words32Naive.word mem32 (SortedListString.map (@Naive.rep 32)) _ _).
  intros.
  edestruct (@compiler_correct_nonterm _ _ Words32Naive.word mem32 _ leakage_ext_spec _ _ _ leakage_ext_spec_ok _ _ _ _ _ word_ok _ _ RV32I _ compile_ext_call leak_ext_call compile_ext_call_correct ltac:(reflexivity) fs_one_printer instrs_one_printer finfo_one_printer req_stack_size_one_printer fname_one_printer p_funcs stack_hi ret_addr eq_refl eq_refl) as [pick_sp H'].
  specialize spec with (1 := (SortedListString.ok _)).
  specialize H' with (argvals := nil). edestruct H' as [f_rel_pos H'']; clear H'.
  { do 4 eexists. split; [reflexivity|]. split; [reflexivity|].
    eapply exec.weaken; [solve[eauto]|]. simpl. intros.
    1: eauto.
    { simpl. fwd. split; [reflexivity|]. instantiate (1 := fun _ _ _ => _). exact H7p1. } }
  fwd. vm_compute in H''p0. inversion H''p0. subst. clear H''p0.
  specialize (H''p1 initial _ Rdata Rexec ltac:(eassumption) ltac:(eassumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(reflexivity) ltac:(eassumption) ltac:(reflexivity) ltac:(eassumption)).
  apply SmallStep.push_in_exists.
  eapply runsToNonDet.runsTo_weaken. 1: eassumption.
  simpl. intros final [n Hn]. exists n. eapply runsToNonDet.runsTo_weaken. 1: eassumption.
  simpl. intros final0 Hn' n'. specialize (Hn' n'). eapply runsToNonDet.runsTo_weaken.
  1: eassumption. simpl. intros. fwd. eauto using EmptyMetricLog.
  Unshelve. 1: exact nil. 1: exact EmptyMetricLog.
Qed.
(*Print Assumptions one_printer_prints_ones.*)
(*
Axioms:
PropExtensionality.propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
FlatImp.exec.choice : forall x y : Type, ChoiceFacts.FunctionalChoice_on x y
 *)
