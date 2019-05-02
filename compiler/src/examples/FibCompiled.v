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
      + admit. (* logs when the machine has no MMIO should always be the same..? *)
      + admit.
    - admit.
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
                                     instructionsH mc' = instructionsH mc + 5)).
    - eapply @exec.set.
      + unfold eval_expr. eval_fib_var_names.
        rewrite H. rewrite H0. eauto.
      + repeat split.
        * rewrite map.get_put_diff; [assumption | discriminate].
        * rewrite map.get_put_diff; [assumption | discriminate].
        * apply map.get_put_same.
        * rewrite map.get_put_diff; [assumption | discriminate].
        * simpl. Lia.lia.
    - intros.
      eapply @exec.seq with (mid := (fun t' m' l' mc' =>
                                       t' = t /\
                                       map.get l' Demos.Fibonacci.a = Some b /\
                                       map.get l' Demos.Fibonacci.b = Some b /\
                                       map.get l' Demos.Fibonacci.c = Some (word.add a b) /\
                                       map.get l' Demos.Fibonacci.i = Some i /\
                                       instructionsH mc' = instructionsH mc + 7)).
      + destruct_hyp.
        eapply @exec.set.
        * unfold eval_expr. eval_fib_var_names.
          rewrite H4. eauto.
        * repeat split.
          -- assumption.
          -- apply map.get_put_same.
          -- rewrite map.get_put_diff; [assumption | discriminate].
          -- rewrite map.get_put_diff; [assumption | discriminate].
          -- rewrite map.get_put_diff; [assumption | discriminate].
          -- simpl. Lia.lia.
      + intros.
        eapply @exec.seq with (mid := (fun t' m' l' mc' =>
                                         t' = t /\
                                         map.get l' Demos.Fibonacci.a = Some b /\
                                         map.get l' Demos.Fibonacci.b = Some (word.add a b) /\
                                         map.get l' Demos.Fibonacci.c = Some (word.add a b) /\
                                         map.get l' Demos.Fibonacci.i = Some i /\
                                         instructionsH mc' = instructionsH mc + 9)).
        * destruct_hyp.
          eapply @exec.set.
          -- unfold eval_expr. eval_fib_var_names.
             rewrite H6. eauto.
          -- repeat split.
             ++ assumption.
             ++ rewrite map.get_put_diff; [assumption | discriminate].
             ++ apply map.get_put_same.
             ++ rewrite map.get_put_diff; [assumption | discriminate].
             ++ rewrite map.get_put_diff; [assumption | discriminate].
             ++ simpl. Lia.lia.
        * intros.
          destruct_hyp.
          eapply @exec.set.
          -- unfold eval_expr. eval_fib_var_names.
             rewrite H8. eauto.
          -- repeat split.
             ++ rewrite map.get_put_diff; [assumption | discriminate].
             ++ rewrite map.get_put_diff; [assumption | discriminate].
             ++ apply map.get_put_same.
             ++ simpl. Lia.lia.
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
      + unfold eval_expr. eval_fib_var_names.
        rewrite H3. eauto.
      + simpl. destruct_one_match.
        * rewrite Z.sub_0_r in E. pose proof Z.ltb_irrefl.
          specialize (H4 (Z.of_nat n mod 2 ^ 32)). rewrite H4 in E. discriminate.
        * auto.
      + simpl. Lia.lia.
    - intros.
      eapply @exec.while_true.
      + unfold eval_expr. eval_fib_var_names.
        rewrite H3. eauto.
      + simpl. destruct_one_match.
        * simpl. rewrite Zdiv.Zmod_1_l.
          { discriminate. }
          { cbv. reflexivity. }
        * rewrite Z.mod_small in E; [| blia ].
          rewrite Z.mod_small in E; [| blia ].
          assert (Z.of_nat n - Z.of_nat (S iter) < Z.of_nat n) by Lia.lia.
          apply Z.ltb_lt in H4.
          rewrite H4 in E. discriminate.
      + eapply fib_bounding_metrics_body with (n := Z.of_nat n); eauto.
      + intros. destruct H4. destruct H5. destruct H6.
        eval_fib_var_names.
        assert (iter <= n)%nat by Lia.lia.
        assert (map.get l' 4 = Some (word.of_Z (Z.of_nat n - Z.of_nat iter))). {
          rewrite H6. f_equal.
          apply word.unsigned_inj.
          rewrite word.unsigned_add. rewrite !word.unsigned_of_Z.
          f_equal. unfold word.wrap. change (1 mod 2 ^ Semantics.width) with 1. simpl.
          rewrite Z.mod_small; blia.
        }
        specialize IHiter with (1 := H) (2 := H8) (3 := H4) (4 := H5) (5 := H9).
        simpl in H7.
        unfold_MetricLog. simpl in IHiter.
        eapply weaken_exec in IHiter.
        * eapply IHiter.
        * intros. simpl in *. Lia.lia.
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
                                     instructionsH mc' = instructionsH mc + 9)).
    - eapply @exec.set.
      + unfold eval_expr. eauto.
      + repeat split.
        * apply map.get_put_same.
        * simpl. Lia.lia.
    - intros.
      destruct H0. destruct H1.
      eapply @exec.seq with (mid := (fun t' m' l' mc' =>
                                       t' = t /\
                                       map.get l' Demos.Fibonacci.a = Some (word.of_Z 0) /\
                                       map.get l' Demos.Fibonacci.b = Some (word.of_Z 1) /\
                                       instructionsH mc' = instructionsH mc + 18)).
      + eapply @exec.set.
        * unfold eval_expr. eauto.
        * repeat split.
          -- assumption.
          -- rewrite map.get_put_diff; [assumption | discriminate].
          -- apply map.get_put_same.
          -- simpl. Lia.lia.
      + intros.
        destruct H3. destruct H4. destruct H5.
        eapply @exec.seq with (mid := (fun t' m' l' mc' =>
                                         t' = t /\
                                         map.get l' Demos.Fibonacci.a = Some (word.of_Z 0) /\
                                         map.get l' Demos.Fibonacci.b = Some (word.of_Z 1) /\
                                         map.get l' Demos.Fibonacci.i = Some (word.of_Z 0) /\
                                         instructionsH mc' = instructionsH mc + 27)).
        * eapply @exec.set.
          -- unfold eval_expr. eauto.
          -- repeat split.
             ++ assumption.
             ++ rewrite map.get_put_diff; [assumption | discriminate].
             ++ rewrite map.get_put_diff; [assumption | discriminate].
             ++ apply map.get_put_same.
             ++ simpl. Lia.lia.
        * intros.
          destruct H7. destruct H8. destruct H9. destruct H10.
          assert (n <= n)%nat by auto.
          pose proof fib_bounding_metrics_while as HWhile.
          specialize HWhile with (iter := n) (n := n).
          replace (Z.of_nat n - Z.of_nat n) with 0 in HWhile by Lia.lia.
          specialize HWhile with (1 := H) (2 := H12) (3 := H8) (4 := H9) (5 := H10).
          specialize (HWhile t'1 m'1 mc'1).
          eapply weaken_exec in HWhile.
          -- apply HWhile.
          -- intros. simpl. Lia.lia.
  Qed.
                                  
  Axiom fib_program_correct: forall n t m l mc,
      0<= n < BinInt.Z.pow_pos 2 32 ->
      Semantics.exec map.empty (fib_ExprImp n) t m l mc (
                       fun t' m ' l' mc' =>
                         exists (result: Utility.word),
                           word.unsigned result = (fib (Z.to_nat n)) /\
                           map.get l' Demos.Fibonacci.b = Some result).
    

  Lemma fib_program_correct_bounded: forall n t m l mc,
      0 <= n < BinInt.Z.pow_pos 2 32 ->
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
      eapply Hbound. blia.
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
    unfold mcomp_sat, run1.
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