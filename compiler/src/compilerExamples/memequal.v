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
Require Import bedrock2Examples.memequal.
Require Import compiler.MMIO.
Require Import bedrock2.FE310CSemantics.
Require Import coqutil.Map.SortedListZ.
Require Import compiler.util.Common.

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

Definition fs_memequal := &[,memequal].
Definition instrs_memequal :=
  match (compile compile_ext_call fs_memequal) with
  | Success (instrs, _, _) => instrs
  | _ => nil
  end.
Definition finfo_memequal :=
  match (compile compile_ext_call fs_memequal) with
  | Success (_, finfo, _) => finfo
  | _ => nil
  end.
Definition req_stack_size_memequal :=
  match (compile compile_ext_call fs_memequal) with
  | Success (_, _, req_stack_size) => req_stack_size
  | _ => 0
  end.
Definition fname_memequal := "memequal".
Definition f_rel_pos_memequal := 0.
Definition post : list LogItem -> mem32 -> list Words32Naive.word -> Prop := fun _ _ _ => True.

Lemma memequal_ct :
  forall x y n p_funcs stack_hi ret_addr,
  exists finalTrace : list LeakageEvent,
  forall Rx Ry xs ys m stack_lo
    Rdata Rexec (initial : RiscvMachine),
    Separation.sep (Array.array Separation.ptsto (word.of_Z 1) x xs) Rx m /\
      Separation.sep (Array.array Separation.ptsto (word.of_Z 1) y ys) Ry m /\
      Z.of_nat (Datatypes.length xs) = word.unsigned n /\
      Z.of_nat (Datatypes.length ys) = word.unsigned n /\
      req_stack_size_memequal <= word.unsigned (word.sub stack_hi stack_lo) / SeparationLogic.bytes_per_word ->
    word.unsigned (word.sub stack_hi stack_lo) mod SeparationLogic.bytes_per_word = 0 ->
    getPc initial = word.add p_funcs (word.of_Z f_rel_pos_memequal) ->
    initial.(getTrace) = Some [] ->
    map.get (getRegs initial) RegisterNames.ra = Some ret_addr ->
    word.unsigned ret_addr mod 4 = 0 ->
    LowerPipeline.arg_regs_contain (getRegs initial) [x; y; n] ->
    LowerPipeline.machine_ok p_funcs stack_lo stack_hi instrs_memequal m Rdata Rexec initial ->
    FlatToRiscvCommon.runsTo initial
      (fun final : RiscvMachine =>
         (exists mH' (retvals : list Words32Naive.word),
             LowerPipeline.arg_regs_contain (getRegs final) retvals /\
               post (getLog final) mH' retvals /\
               map.only_differ (getRegs initial) reg_class.caller_saved (getRegs final) /\
               getPc final = ret_addr /\
               final.(getTrace) = Some finalTrace /\
               LowerPipeline.machine_ok p_funcs stack_lo stack_hi instrs_memequal mH' 
                 Rdata Rexec final)).
Proof.
  assert (spec := @memequal_ok _ _ Words32Naive.word mem32 (SortedListString.map (@Naive.rep 32)) leakage_ext_spec).
  intros.
  edestruct (@compiler_correct_wp _ _ Words32Naive.word mem32 _ leakage_ext_spec _ _ _ leakage_ext_spec_ok _ _ _ _ _ word_ok _ _ RV32I _ compile_ext_call leak_ext_call compile_ext_call_correct ltac:(reflexivity) fs_memequal instrs_memequal finfo_memequal req_stack_size_memequal fname_memequal p_funcs stack_hi ret_addr f_rel_pos_memequal) as [f_ [pick_sp_ H] ].
  { simpl. reflexivity. }
  { vm_compute. reflexivity. }
  specialize (spec pick_sp_ word_ok' _ ltac:(apply SortedListString.ok) leakage_ext_spec_ok).
  cbv [LeakageProgramLogic.program_logic_goal_for] in spec.
  specialize (spec (map.of_list fs_memequal) eq_refl).
  cbv [spec_of_memequal] in spec. destruct spec as [f spec].
  eexists. intros.
  cbv [FlatToRiscvCommon.runsTo].
  eapply runsToNonDet.runsTo_weaken.
  1: eapply H with (post := (fun k_ t_ m_ r_ mc => k_ = _ /\
                                                  post t_ m_ r_)).
  { simpl. repeat constructor. tauto. }
  2: { eapply map.get_of_list_In_NoDup.
       { vm_compute. repeat constructor; eauto. }
       { vm_compute. left. reflexivity. } }
  all: try eassumption.   
  2: { fwd. assumption. }

  { subst. cbv [fname_memequal]. move spec at bottom.
    specialize (spec x y n xs ys Rx Ry [] (initial.(getLog)) m ltac:(intuition eauto)).
    eapply MetricLeakageSemantics.weaken_call.
    { eapply MetricLeakageSemantics.to_leakage_call. exact spec. }
    cbv beta. intros. fwd. split; [|reflexivity]. reflexivity. }
  { reflexivity. }
  { reflexivity. }
  cbv beta. intros. fwd. do 2 eexists. intuition eauto.
  Unshelve. exact EmptyMetricLog.
Qed.
(* Print Assumptions memequal_ct. *)
(*
  Axioms:
  PropExtensionality.propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
  FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g
 *)
