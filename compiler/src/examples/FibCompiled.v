Require bedrock2.Examples.Demos.
Require Import coqutil.Decidable.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Pipeline.
Require Import compiler.Basic32Semantics.
Require Import bedrock2.MetricLogging.
Require Import riscv.Platform.MinimalLogging.
Require Import riscv.Platform.MetricMinimal.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
Require Import coqutil.Map.SortedList.
Require Import compiler.ZNameGen.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import compiler.GoFlatToRiscv.

Section FibCompiled.

  Definition fib_ExprImp(n: Z): cmd := Eval cbv in
    snd (snd (Demos.fibonacci n)).


  Instance flatToRiscvDef_params: FlatToRiscvDef.FlatToRiscvDef.parameters.
  Proof.
    refine ({|
               FlatToRiscvDef.FlatToRiscvDef.compile_ext_call _ _ _ := nil;
             |}).
    all: intros; simpl.
    - cbv. discriminate.
    - unfold FlatToRiscvDef.valid_instructions. intros. destruct H1.
  Defined.

  Notation RiscvMachine := MetricRiscvMachine.

  Existing Instance coqutil.Map.SortedListString.map.
  Existing Instance coqutil.Map.SortedListString.ok.

  Instance pipeline_params: Pipeline.parameters := {
    Pipeline.FlatToRiscvDef_params := flatToRiscvDef_params;
    Pipeline.ext_spec _ _  _ _ _ := False;
    Pipeline.ext_guarantee _ := True;
    Pipeline.M := OState RiscvMachine;
    Pipeline.PRParams := MetricMinimalMetricPrimitivesParams;
  }.

  Set Refine Instance Mode.

  Instance pipeline_assumptions: @Pipeline.assumptions pipeline_params := {
    Pipeline.varname_eq_dec := _ ;
    Pipeline.mem_ok := _ ;
    Pipeline.locals_ok := _ ;
    Pipeline.funname_env_ok := _ ;
    Pipeline.PR := MetricMinimalSatisfiesMetricPrimitives;
  }.
  Proof.
    - constructor; try typeclasses eauto.
      + admit. (* This is doable.. *)
      + simpl. apply MetricMinimalSatisfiesMetricPrimitives.
      + constructor.
      + intros. inversion H6. destruct H17.
    - constructor; destruct 1.
  Admitted.

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

  Existing Instance Demos.Fibonacci.ZNames.Inst.

  Local Notation instructionsH := (bedrock2.MetricLogging.instructions).
  
  Fixpoint get_next_bb exprimp :=
    match exprimp with
    | cmd.seq _ x => get_next_bb x
    | _ => exprimp
    end.

  Definition get_while_body exprimp :=
    match exprimp with
    | cmd.while _ x => x
    | _ => exprimp
    end.

  Definition fib_while n := get_next_bb (fib_ExprImp n).

  Definition fib_while_body n := get_while_body (fib_while n).

  Ltac destruct_hyp :=
    repeat match goal with
           | H : _ /\ _ |- _ => destruct H
           end.

  Ltac eval_fib_var_names :=
    cbv [Demos.Fibonacci.a
           Demos.Fibonacci.b
           Demos.Fibonacci.c
           Demos.Fibonacci.i
           Demos.Fibonacci.ZNames.Inst] in *.

  Ltac known_var :=
    match goal with
    | H: map.get ?l ?a = Some ?v |- context[map.get ?l ?a] => rewrite H
    end.

  Ltac fib_step_precondition :=
    match goal with
    | |- map.get (map.put _ _ _) _ = Some _ =>
      rewrite map.get_put_diff; [assumption|discriminate] || apply map.get_put_same
    | |- _ => assumption || simpl; Lia.blia
    end.

  Ltac eval_var_solve :=
    unfold eval_expr;
    eval_fib_var_names;
    repeat known_var;
    reflexivity.

  Ltac exec_set_solve :=
    intros; destruct_hyp;
    eapply @exec.set;
    [
      eval_var_solve |
      repeat split; fib_step_precondition
    ].

  Lemma fib_bounding_metrics_body: forall t m (l : locals) mc a b i n,
      map.get l Demos.Fibonacci.a = Some a ->
      map.get l Demos.Fibonacci.b = Some b ->
      map.get l Demos.Fibonacci.i = Some i ->
      exec map.empty (fib_while_body n) t m l mc (fun t' m' l' mc' =>
                                                    map.get l' Demos.Fibonacci.a = Some b /\
                                                    map.get l' Demos.Fibonacci.b = Some (word.add a b) /\
                                                    map.get l' Demos.Fibonacci.i = Some (word.add i (word.of_Z 1)) /\
                                                    instructionsH mc' - instructionsH mc = 21).
  Proof.
    intros.
    cbv [fib_ExprImp get_next_bb get_while_body fib_while fib_while_body].
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
                                     t' = t /\
                                     map.get l' Demos.Fibonacci.a = Some a /\
                                     map.get l' Demos.Fibonacci.b = Some b /\
                                     map.get l' Demos.Fibonacci.c = Some (word.add a b) /\
                                     map.get l' Demos.Fibonacci.i = Some i /\
                                     instructionsH mc' = instructionsH mc + 5));
      [exec_set_solve|].
    intros.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
                                     t' = t /\
                                     map.get l' Demos.Fibonacci.a = Some b /\
                                     map.get l' Demos.Fibonacci.b = Some b /\
                                     map.get l' Demos.Fibonacci.c = Some (word.add a b) /\
                                     map.get l' Demos.Fibonacci.i = Some i /\
                                     instructionsH mc' = instructionsH mc + 7));
      [exec_set_solve|].
    intros.
        eapply @exec.seq with (mid := (fun t' m' l' mc' =>
                                         t' = t /\
                                         map.get l' Demos.Fibonacci.a = Some b /\
                                         map.get l' Demos.Fibonacci.b = Some (word.add a b) /\
                                         map.get l' Demos.Fibonacci.c = Some (word.add a b) /\
                                         map.get l' Demos.Fibonacci.i = Some i /\
                                         instructionsH mc' = instructionsH mc + 9));
       exec_set_solve.
  Qed.

  Lemma fib_bounding_metrics_while: forall (n : nat) (iter : nat) t m (l : locals) mc a b,
      (Z.of_nat n) < 2 ^ 32 ->
      (iter <= n)%nat ->
      map.get l Demos.Fibonacci.a = Some a ->
      map.get l Demos.Fibonacci.b = Some b ->
      map.get l Demos.Fibonacci.i = Some (word.of_Z ((Z.of_nat n) - (Z.of_nat iter)) : word) ->
      exec map.empty (fib_while (Z.of_nat n)) t m l mc (fun t' m' l' mc' =>
                                                          instructionsH mc' <= instructionsH mc + (Z.of_nat iter) * 34 + 12).
  Proof.
    induction iter.
    - intros.
      eapply @exec.while_false.
      + eval_var_solve.
      + simpl. destruct_one_match.
        * rewrite Z.sub_0_r in *. rewrite Z.ltb_irrefl in *. discriminate.
        * reflexivity.
      + simpl. Lia.blia.
    - intros.
      eapply @exec.while_true.
      + eval_var_solve.
      + simpl. destruct_one_match.
        * simpl. rewrite Zdiv.Zmod_1_l; [discriminate | cbv; reflexivity].
        * repeat match goal with
                 | H: context[_ mod _] |- _ => rewrite Z.mod_small in H; [|blia]
                 end.
          assert (Z.of_nat n - Z.of_nat (S iter) < Z.of_nat n) by Lia.blia.
          rewrite <- Z.ltb_lt in *.
          match goal with
          | H1: _ = false, H2: _ = true |- _ => rewrite H1 in H2; discriminate
          end.
      + eapply fib_bounding_metrics_body with (n := Z.of_nat n); eauto.
      + intros.
        eval_fib_var_names.
        destruct_hyp.
        eapply weaken_exec in IHiter.
        * eapply IHiter.
        * assumption.
        * Lia.blia.
        * eassumption.
        * eassumption.
        * match goal with
          | H: ?x = _ |- ?x = _ => rewrite H
          end.
          f_equal.
          apply word.unsigned_inj.
          rewrite word.unsigned_add. rewrite !word.unsigned_of_Z.
          f_equal. unfold word.wrap. change (1 mod 2 ^ Semantics.width) with 1. simpl.
          rewrite Z.mod_small; blia.
        * intros. simpl in *. Lia.blia.
  Qed.

  Lemma fib_bounding_metrics: forall (n: nat) t m (l : locals) mc,
      (Z.of_nat n) < BinInt.Z.pow_pos 2 32 ->
      exec map.empty (fib_ExprImp (Z.of_nat n)) t m l mc (fun t' m ' l' mc' =>
        instructionsH mc' <= instructionsH mc + (Z.of_nat n) * 34 + 39).
  Proof.
    intros.
    unfold fib_ExprImp.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
                                     t' = t /\
                                     map.get l' Demos.Fibonacci.a = Some (word.of_Z 0) /\
                                     instructionsH mc' = instructionsH mc + 9));
      [exec_set_solve|].
    intros. destruct_hyp.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
                                     t' = t /\
                                     map.get l' Demos.Fibonacci.a = Some (word.of_Z 0) /\
                                     map.get l' Demos.Fibonacci.b = Some (word.of_Z 1) /\
                                     instructionsH mc' = instructionsH mc + 18));
      [exec_set_solve|].
    intros. destruct_hyp.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
                                     t' = t /\
                                     map.get l' Demos.Fibonacci.a = Some (word.of_Z 0) /\
                                     map.get l' Demos.Fibonacci.b = Some (word.of_Z 1) /\
                                     map.get l' Demos.Fibonacci.i = Some (word.of_Z 0) /\
                                     instructionsH mc' = instructionsH mc + 27));
      [exec_set_solve|].
    intros.
    destruct_hyp.
    pose proof fib_bounding_metrics_while as HWhile.
    specialize HWhile with (iter := n) (n := n).
    replace (Z.of_nat n - Z.of_nat n) with 0 in HWhile by Lia.blia.
    specialize HWhile with (1 := H) (3 := H8) (4 := H9) (5 := H10).
    specialize (HWhile t'1 m'1 mc'1).
    eapply weaken_exec in HWhile.
    - apply HWhile.
     - apply le_n.
    - intros. simpl. Lia.blia.
  Qed.
                                  
  Axiom fib_program_correct: forall n t m l mc,
      0 <= n <= 60 ->
      Semantics.exec map.empty (fib_ExprImp n) t m l mc (
                       fun t' m ' l' mc' =>
                         exists (result: Utility.word),
                           word.unsigned result = (fib (Z.to_nat n)) /\
                           map.get l' Demos.Fibonacci.b = Some result).
    

  Lemma fib_program_correct_bounded: forall n t m l mc,
      0 <= n <= 60 ->
      Semantics.exec map.empty (fib_ExprImp n) t m l mc (
                       fun t' m ' l' mc' =>
                         instructionsH mc' <= instructionsH mc + n * 34 + 39 /\
                         exists (result: Utility.word),
                           word.unsigned result = (fib (Z.to_nat n)) /\
                           map.get l' Demos.Fibonacci.b = Some result).
  Proof.
    intros.
    eapply intersect_exec.
    + pose proof fib_bounding_metrics as Hbound.
      specialize Hbound with (n := Z.to_nat n).
      rewrite Z2Nat.id in Hbound; [|blia].
      eapply Hbound. cbn. blia.
    + eapply fib_program_correct. blia.
  Qed.

  Definition mcomp_sat := GoFlatToRiscv.mcomp_sat.

  Lemma fib_compiled: forall n,
    0 <= n <= 60 ->
    runsToNonDet.runsTo (mcomp_sat run1)
                        (programmedMachine n)
                        (fun (finalL: RiscvMachine) =>
                           exists (result: Utility.word),
                             map.get finalL.(getRegs) Demos.Fibonacci.b = Some result /\
                             word.unsigned result = (fib (Z.to_nat n)) /\
                             finalL.(getMetrics).(instructions) <= n * 34 + 39).
  Proof.
    intros.
    eapply runsToNonDet.runsTo_weaken.
    - pose proof Pipeline.exprImp2Riscv_correct as Hp.
      specialize Hp with (sH := fib_ExprImp n)
                         (mcH := bedrock2.MetricLogging.EmptyMetricLog).
      eapply Hp.
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
      + eapply ExprImp.weaken_exec; [eapply fib_program_correct_bounded; cbn; blia|].
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
        eapply Z.le_trans.
        * eassumption.
        * assumption.
  Qed.

  Print Assumptions fib_compiled.

End FibCompiled.