Require Import Coq.Lists.List.
Import ListNotations.
Require bedrock2.Examples.Demos.
Require Import coqutil.Decidable.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Pipeline.
Require Import compiler.Basic32Semantics.
Require Import riscv.Utility.Monads.
Require Import compiler.util.Common.
Require Import coqutil.Decidable.
Require        riscv.Utility.InstructionNotations.
Require Import riscv.Platform.MinimalLogging.
Require Import bedrock2.MetricLogging.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Platform.MetricMinimal.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
Require Import coqutil.Map.SortedList.
Require Import compiler.ZNameGen.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import bedrock2.Byte.
Require bedrock2.Hexdump.
Require Import compiler.RegAllocAnnotatedNotations.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.Simp.

Section FibCompiled.

  Definition fib_ExprImp(n: Z): cmd := Eval cbv in
        snd (snd (Demos.fibonacci n)).

  Instance flatToRiscvDef_params: FlatToRiscvDef.FlatToRiscvDef.parameters := {
    FlatToRiscvDef.FlatToRiscvDef.actname := Empty_set;
    FlatToRiscvDef.FlatToRiscvDef.compile_ext_call _ := Empty_set_rect _;
    FlatToRiscvDef.FlatToRiscvDef.compile_ext_call_length _ := Empty_set_rect _;
    FlatToRiscvDef.FlatToRiscvDef.compile_ext_call_emits_valid _ _ := Empty_set_rect _;
  }.

  Notation RiscvMachine := (MetricRiscvMachine Register Empty_set).

  Existing Instance coqutil.Map.SortedListString.map.
  Existing Instance coqutil.Map.SortedListString.ok.

  Instance pipeline_params: Pipeline.parameters := {
    Pipeline.ext_spec _ _ := Empty_set_rect _;
    Pipeline.ext_guarantee _ := True;
    Pipeline.M := OState RiscvMachine;
    Pipeline.PRParams := MetricMinimalMetricPrimitivesParams;
  }.
  
  Axiom TODO: forall {T: Type}, T.

  Instance pipeline_assumptions: @Pipeline.assumptions pipeline_params := {
    Pipeline.actname_eq_dec := _;
    Pipeline.varname_eq_dec := _ ;
    Pipeline.mem_ok := _ ;
    Pipeline.locals_ok := _ ;
    Pipeline.funname_env_ok := _ ;
    Pipeline.PR := MetricMinimalSatisfiesMetricPrimitives;
    Pipeline.FlatToRiscv_hyps := TODO ;
    Pipeline.ext_spec_ok := TODO;
  }.

  (* just to make sure all typeclass instances are available: *)
  Definition mcomp_sat:
    Pipeline.M unit -> RiscvMachine -> (RiscvMachine -> Prop) -> Prop :=
    @GoFlatToRiscv.mcomp_sat _ _ _ _ _ MetricMinimalMetricPrimitivesParams.

  Definition zeroedRiscvMachine: RiscvMachine := {|
    getMetrics := EmptyMetricLog;
    getMachine := {|
      getRegs := map.empty;
      getPc := word.of_Z 0;
      getNextPc := word.of_Z 4;
      getMem := map.empty;
      getLog := nil;
    |};
  |}.

  Definition insts(n: Z) := ExprImp2Riscv (fib_ExprImp n).

  Definition imem(n: Z) := List.map encode (insts n).

  Definition programmedMachine (n : Z) : RiscvMachine :=
    putProgram (imem n) (getPc zeroedRiscvMachine) zeroedRiscvMachine.

  Definition run1 : Pipeline.M unit := @run1 _ _ _ _ Pipeline.RVM _ iset.

  Fixpoint fib (n: nat): Z :=
    match n with
    | O => 0
    | S x =>
      match x with
      | O => 1
      | S y => (fib x + fib y)
      end
    end.

  Definition regb : Register := 2.

  Existing Instance Demos.Fibonacci.ZNames.Inst.
                                  
  Axiom fib_program_logic: forall n t m l mc,
     n < BinInt.Z.pow_pos 2 32 ->
     Semantics.exec map.empty (fib_ExprImp n) t m l mc (
                      fun t' m ' l' mc' =>
                        bedrock2.MetricLogging.instructions mc' <= bedrock2.MetricLogging.instructions mc + 34 * n + 39 /\
                        exists (result: Utility.word),
                          word.unsigned result = (fib (Z.to_nat n)) /\
                          map.get l' regb = Some result).

  Lemma fib_demo: forall n,
    0 <= n <= 60 ->
    runsToNonDet.runsTo (mcomp_sat run1)
                        (programmedMachine n)
                        (fun (finalL: RiscvMachine) =>
                           exists (result: Utility.word),
                             map.get finalL.(getRegs) regb = Some result /\
                             word.unsigned result = (fib (Z.to_nat n)) /\
                             finalL.(getMetrics).(instructions) <= 34 * n + 39).
  Proof.
    intros.
    eapply runsToNonDet.runsTo_weaken.
    - eapply Pipeline.exprImp2Riscv_correct with (sH := fib_ExprImp n) 
        (mcH := bedrock2.MetricLogging.EmptyMetricLog).
      + simpl. blia.
      + cbv. repeat constructor.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + cbv [programmedMachine zeroedRiscvMachine getMem putProgram zeroedRiscvMachine
                               getMem withPc withNextPc withMem].
        unfold Separation.sep. do 2 eexists; split; [ | split; [|reflexivity] ].
        1: apply map.split_empty_r; reflexivity.
        apply store_program_empty.
        cbv [fib_ExprImp ExprImp2Riscv FlatToRiscvDef.compile_stmt ExprImp2FlatImp flattenStmt flattenExpr].
        simpl. cbn.
        unfold FlatToRiscvDef.compile_lit, FlatToRiscvDef.compile_lit_12bit, FlatToRiscvDef.compile_lit_32bit,
        FlatToRiscvDef.compile_lit_64bit.
        match goal with
        | |- context[dec(?P)] => destruct (dec(P)); try (exfalso; blia)
        end.
        simpl. blia.
      + cbv [Pipeline.ext_guarantee pipeline_params]. exact I.
      + eapply ExprImp.weaken_exec; [eapply fib_program_logic|].
        * match goal with
          | |- _ < ?x => let r := eval cbv in x in change x with r
          end.
          blia.
        * intros.
          match goal with
          | H: _ ?t ?m ?l ?mc |- _ ?t ?m ?l ?mc => apply H
          end.
    - intros.
      repeat match goal with
               | H: (fun _ => _) _ |- _ => destruct H
               | H: exists _, _ |- _ => destruct H
               | H: _ /\ _ |- _ => destruct H
               end.
        eexists.
        repeat split.
       + match goal with
        | H: map.extends ?m1 _ |- map.get ?m1 _ = Some _ => unfold map.extends in H; apply H
        end.
        eassumption.
      + eassumption.
      + repeat unfold_MetricLog. repeat simpl_MetricLog. simpl in *.
        repeat rewrite Z.sub_0_r in *.
        repeat rewrite Z.add_0_l in *.
        repeat match goal with
               | H: _ /\ _ |- _ => destruct H
               end.
        eapply Z.le_trans; [eassumption|assumption].
  Qed.

End FibCompiled.