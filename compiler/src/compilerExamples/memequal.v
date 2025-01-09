Require Import Coq.Lists.List.
Import ListNotations.
Require bedrock2Examples.Demos.
Require Import coqutil.Decidable.
Require Import bedrock2.NotationsCustomEntry coqutil.Macros.WithBaseName.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Pipeline.
Require Import riscv.Spec.LeakageOfInstr.
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
Require Import compiler.MemoryLayout.
Require Import compiler.StringNameGen.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Platform.MetricRiscvMachine.
Require bedrock2.Hexdump.
(*Require Import bedrock2Examples.swap.
Require Import bedrock2Examples.stackalloc.*)
Require Import compilerExamples.SpillingTests.

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
Require Import compiler.MemoryLayout.
Require Import compiler.StringNameGen.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Platform.MetricRiscvMachine.
Require bedrock2.Hexdump.
(*Require Import bedrock2Examples.swap.
Require Import bedrock2Examples.stackalloc.*)
Require Import compilerExamples.SpillingTests.
Require compiler.NaiveRiscvWordProperties.

Require Import compiler.util.Common.


Open Scope Z_scope.
Open Scope string_scope.
Open Scope ilist_scope.

Definition var: Set := Z.
Definition Reg: Set := Z.


Local Existing Instance DefaultRiscvState.

Local Instance funpos_env: map.map string Z := SortedListString.map _.

Notation RiscvMachine := MetricRiscvMachine.

Local Existing Instance coqutil.Map.SortedListString.map.
Local Existing Instance coqutil.Map.SortedListString.ok.

Print compiler_correct_wp.
Print ExtSpec.
Section WithParameters.
  (*Context {mem : map.map Words32Naive.word byte}.
  Context {mem_ok : map.ok mem}.*)

  Search (map.map _ _).
  
  Print funpos_env.
  Definition mem32 := SortedListWord.map Words32Naive.word byte.
  Existing Instance mem32.
  Search SortedListWord.map.
  Definition mem32_ok : map.ok mem32 := SortedListWord.ok _ _.
  Existing Instance mem32_ok.
  Require Import coqutil.Map.SortedListZ.

  Definition localsL32 := SortedListZ.map Words32Naive.word.
  Existing Instance localsL32.
  Definition localsL32_ok : map.ok localsL32 := SortedListZ.ok _.
  Existing Instance localsL32_ok.

  Definition localsH32 := SortedListString.map Words32Naive.word.
  Existing Instance localsH32.
  Definition localsH32_ok : map.ok localsH32 := SortedListString.ok _.
  Existing Instance localsH32_ok.
  
  (*Context {localsL : map.map Z Words32Naive.word}.
  Context {localsL_ok : map.ok localsL}.
  Context {localsH : map.map string Words32Naive.word}.
  Context {localsH_ok : map.ok localsH}.
  Context {envL : map.map string (list Z * list Z * FlatImp.stmt Z)}.
  Context {envH : map.map string (list string * list string * cmd)}.
  Context {envH_ok : map.ok envH}.*)
  (*Context {M : Type -> Type} {MM : Monad M}.*)
  (*Context {RVM: RiscvProgramWithLeakage}.
Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
Context {PR: MetricPrimitives PRParams}.*)

  Require Import compiler.MMIO.
  Import bedrock2.FE310CSemantics.

  Print compile_ext_call.
  Local Instance RV32I_bitwidth: FlatToRiscvCommon.bitwidth_iset 32 RV32I.
  Proof. reflexivity. Qed.

  Check (@FlatToRiscvCommon.compiles_FlatToRiscv_correctly RV32I _ _ _ _ _ compile_ext_call
           leak_ext_call _ _ _ _ _ _ _ _ compile_ext_call).
  Check @compiler_correct_wp.
  (*Check (@PrimitivesParams _ _ _ _ _ M MetricRiscvMachine).
Check (@compiler_correct_wp _ _ Words32Naive.word mem _ ext_spec _ _ _ _ ext_spec_ok _ _ _ _ _).*)
  Check NaiveRiscvWordProperties.naive_word_riscv_ok.
  Lemma word_ok : RiscvWordProperties.word.riscv_ok Words32Naive.word.
  Proof.
    cbv [Words32Naive.word]. replace 32 with (2 ^ BinInt.Z.of_nat 5) by reflexivity.
    apply NaiveRiscvWordProperties.naive_word_riscv_ok.
  Qed.

  Lemma word_ok' : word.ok Words32Naive.word.
  Proof.
    Search (word.ok _). cbv [Words32Naive.word]. exact Naive.word32_ok. Qed.

  Check compile_ext_call_correct.

  (*Lemma compile_ext_call_works :
  (forall (resvars : list Z) (extcall : string) (argvars : list Z),
        @FlatToRiscvCommon.compiles_FlatToRiscv_correctly RV32I 32 Bitwidth32.BW32
          Words32Naive.word localsL (SortedListString.map Z) (@compile_ext_call SortedListString.map) (@leak_ext_call Words32Naive.word SortedListString.map) mem
          (SortedListString.map (list Z * list Z * FlatImp.stmt Z)) M MM RVM PRParams ext_spec
          leak_ext RV32I_bitwidth compile_ext_call (@FlatImp.SInteract Z resvars extcall argvars)).
Proof.
  intros. Search compile_ext_call. cbv [FlatToRiscvCommon.compiles_FlatToRiscv_correctly]. intros.
  apply compile_ext_call_correct. exfalso. clear -H.
  inversion H. subst. cbv [ext_spec] in *. assumption.
Qed.*)

  Lemma compile_ext_call_length :
    (forall (stackoffset : Z) (posmap1 posmap2 : SortedListString.map Z) 
       (c : FlatImp.stmt Z) (pos1 pos2 : Z),
        @Datatypes.length Instruction (compile_ext_call posmap1 pos1 stackoffset c) =
          @Datatypes.length Instruction (compile_ext_call posmap2 pos2 stackoffset c)).
  Proof.
    intros. cbv [compile_ext_call]. reflexivity. Qed.

  Require Import bedrock2Examples.memequal.

  Definition fs_memequal := &[,memequal].
  Definition instrs_memequal :=
    match (compile compile_ext_call fs_memequal) with
    | Success (instrs, _, _) => instrs
    | _ => nil
    end.
  Compute instrs_memequal.
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
  
  Print spec_of_memequal.
  Check compiler_correct_wp.

  Print spec_of_memequal.
  Require Import coqutil.Tactics.fwd.

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
    edestruct (@compiler_correct_wp _ _ Words32Naive.word mem32 _ leakage_ext_spec _ _ _ leakage_ext_spec_ok _ _ _ _ _ word_ok _ _ RV32I _ compile_ext_call leak_ext_call compile_ext_call_correct compile_ext_call_length fs_memequal instrs_memequal finfo_memequal req_stack_size_memequal fname_memequal p_funcs stack_hi ret_addr f_rel_pos_memequal) as [f_ [pick_sp_ H] ].
    { simpl. reflexivity. }
    { vm_compute. reflexivity. } Search SortedListString.map.
    specialize (spec pick_sp_ word_ok' _ ltac:(apply SortedListString.ok) leakage_ext_spec_ok).
    cbv [LeakageProgramLogic.program_logic_goal_for] in spec.
    specialize (spec (map.of_list fs_memequal) eq_refl).
    cbv [spec_of_memequal] in spec. destruct spec as [f spec].
    eexists. (*exists (rev (f_ (rev (f a_addr b_addr)))).*) intros.
    cbv [FlatToRiscvCommon.runsTo].
    eapply runsToNonDet.runsTo_weaken.
    1: eapply H with (post := (fun k_ t_ m_ r_ mc => k_ = _ /\
                                                    post t_ m_ r_)).
    { exact EmptyMetricLog. }
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
  Print Assumptions memequal_ct.
(*
  Axioms:
  PropExtensionality.propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
  FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g
 *)
End WithParameters.
