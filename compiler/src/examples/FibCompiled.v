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
Require Import bedrock2.Examples.Demos.

Section FibCompiled.

  Definition n_addr: Z := 4096.

  Definition fib_ExprImp: cmd := Eval cbv in
    snd (snd (Demos.fibonacciServer n_addr)).


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

  Fixpoint fib (n: nat): Z :=
    match n with
    | O => 0
    | S x =>
      match x with
      | O => 1
      | S y => (fib x + fib y)
      end
    end.

  Existing Instance Fibonacci.ZNames.Inst.

  Local Notation instructionsH := (bedrock2.MetricLogging.instructions).
  
  Fixpoint get_next_bb exprimp :=
    match exprimp with
    | cmd.seq _ x => get_next_bb x
    | _ => exprimp
    end.

  Definition fib_if := Eval cbv in get_next_bb fib_ExprImp.

  Definition fib_while := Eval cbv in
        match fib_if with
        | cmd.cond _ w _ => w
        | _ => fib_if
        end.

  Definition fib_while_body := Eval cbv in
        match fib_while with
        | cmd.while _ b => b
        | _ => fib_while
        end.

  Ltac destruct_hyp :=
    repeat match goal with
           | H : _ /\ _ |- _ => destruct H
           end.

  Ltac eval_fib_var_names :=
    cbv [FibonacciServer.a
           FibonacciServer.b
           Demos.FibonacciServer.c
           Demos.FibonacciServer.i
           Demos.FibonacciServer.n
           Demos.FibonacciServer.ZNames.Inst] in *.

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
      map.get l FibonacciServer.a = Some a ->
      map.get l FibonacciServer.b = Some b ->
      map.get l FibonacciServer.i = Some i ->
      map.get l FibonacciServer.n = Some n ->
      exec map.empty fib_while_body t m l mc (fun t' m' l' mc' =>
                                                map.get l' FibonacciServer.a = Some b /\
                                                map.get l' FibonacciServer.b = Some (word.add a b) /\
                                                map.get l' FibonacciServer.i = Some (word.add i (word.of_Z 1)) /\
                                                map.get l' FibonacciServer.n = Some n /\
                                                instructionsH mc' - instructionsH mc = 21).
  Proof.
    intros.
    cbv [fib_while_body].
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
                                     t' = t /\
                                     map.get l' FibonacciServer.a = Some a /\
                                     map.get l' FibonacciServer.b = Some b /\
                                     map.get l' FibonacciServer.c = Some (word.add a b) /\
                                     map.get l' FibonacciServer.i = Some i /\
                                     map.get l' FibonacciServer.n = Some n /\
                                     instructionsH mc' = instructionsH mc + 5));
      [exec_set_solve|].
    intros.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
                                     t' = t /\
                                     map.get l' FibonacciServer.a = Some b /\
                                     map.get l' FibonacciServer.b = Some b /\
                                     map.get l' FibonacciServer.c = Some (word.add a b) /\
                                     map.get l' FibonacciServer.i = Some i /\
                                     map.get l' FibonacciServer.n = Some n /\
                                     instructionsH mc' = instructionsH mc + 7));
      [exec_set_solve|].
    intros.
        eapply @exec.seq with (mid := (fun t' m' l' mc' =>
                                         t' = t /\
                                         map.get l' FibonacciServer.a = Some b /\
                                         map.get l' FibonacciServer.b = Some (word.add a b) /\
                                         map.get l' FibonacciServer.c = Some (word.add a b) /\
                                         map.get l' FibonacciServer.i = Some i /\
                                         map.get l' FibonacciServer.n = Some n /\

                                         instructionsH mc' = instructionsH mc + 9));
       exec_set_solve.
  Qed.

  Lemma fib_bounding_metrics_while: forall (iter : nat) n t m (l : locals) mc a b,
      Z.of_nat n < 2 ^ 32 ->
      (iter <= n)%nat ->
      map.get l FibonacciServer.a = Some a ->
      map.get l FibonacciServer.b = Some b ->
      map.get l FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) ->
      map.get l FibonacciServer.i = Some (word.of_Z ((Z.of_nat n) - (Z.of_nat iter)) : word) ->
      exec map.empty fib_while t m l mc (fun t' m' l' mc' =>
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
      + eapply fib_bounding_metrics_body; eauto.
      + intros.
        eval_fib_var_names.
        destruct_hyp.
        eapply weaken_exec in IHiter.
        * eapply IHiter.
        * eassumption.
        * Lia.blia.
        * eassumption.
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
                                                                    
  Lemma fib_bounding_metrics: forall (n: nat) t (m: mem) (l : locals) mc,
      load access_size.four m (word.of_Z n_addr) = Some (word.of_Z (Z.of_nat n)) ->
      Z.of_nat n < 2 ^ 32 ->
      exec map.empty fib_ExprImp t m l mc (fun t' m ' l' mc' =>
        instructionsH mc' <= instructionsH mc + (Z.of_nat n) * 34 + 62).
  Proof.
    intros *. intro Hload. intros.
    cbv [n_addr] in *.
    unfold fib_ExprImp.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
                                     t' = t /\
                                     map.get l' FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) /\
                                     instructionsH mc' = instructionsH mc + 10));
      [eapply @exec.set; [simpl in *; rewrite Hload; f_equal | repeat split; fib_step_precondition] |].
    intros. destruct_hyp.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
                                     t' = t /\
                                     map.get l' FibonacciServer.a = Some (word.of_Z 0) /\
                                     map.get l' FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) /\
                                     instructionsH mc' = instructionsH mc + 19));
      [exec_set_solve|].
    intros. destruct_hyp.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
                                     t' = t /\
                                     map.get l' FibonacciServer.a = Some (word.of_Z 0) /\
                                     map.get l' FibonacciServer.b = Some (word.of_Z 1) /\
                                     map.get l' FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) /\
                                                                          
                                     instructionsH mc' = instructionsH mc + 28));
      [exec_set_solve|].
    intros. destruct_hyp.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
                                     t' = t /\
                                     map.get l' FibonacciServer.a = Some (word.of_Z 0) /\
                                     map.get l' FibonacciServer.b = Some (word.of_Z 1) /\
                                     map.get l' FibonacciServer.i = Some (word.of_Z 0) /\
                                     map.get l' FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) /\
                                     instructionsH mc' = instructionsH mc + 37));
      [exec_set_solve|].
    intros.
    destruct_hyp.
    
    pose proof Nat2Z.is_nonneg as Hpos.
    specialize Hpos with (n := n).

    destruct (Z.of_nat n <? 48) eqn:Hcond.
    + rewrite Z.ltb_lt in *.
      eapply @exec.if_true.
      * eval_var_solve.
      * simpl.
        destruct_one_match; [discriminate|].
        rewrite Z.ltb_ge in *.
        repeat rewrite Z.mod_small in * by blia.
        exfalso. blia.
      * eapply weaken_exec.
        -- eapply fib_bounding_metrics_while with (iter := n); try eassumption.
           ++ blia.
           ++ rewrite Z.sub_diag. assumption.
        -- intros. unfold_MetricLog. simpl in *. blia.
    + rewrite Z.ltb_ge in *.
      eapply @exec.if_false.
      * eval_var_solve.
      * simpl.
        destruct_one_match; [|reflexivity].
        rewrite Z.ltb_lt in *.
        repeat rewrite Z.mod_small in * by blia.
        exfalso. blia.
      * exec_set_solve.
  Qed.
                                  
  Axiom fib_program_correct: forall n t m l mc,
      0 <= n <= 60 ->
      Semantics.exec map.empty (fib_ExprImp n) t m l mc (
                       fun t' m ' l' mc' =>
                         exists (result: Utility.word),
                           word.unsigned result = (fib (Z.to_nat n)) /\
                           map.get l' FibonacciServer.b = Some result).
    

  Lemma fib_program_correct_bounded: forall n t m l mc,
      0 <= n <= 60 ->
      Semantics.exec map.empty (fib_ExprImp n) t m l mc (
                       fun t' m ' l' mc' =>
                         instructionsH mc' <= instructionsH mc + n * 34 + 39 /\
                         exists (result: Utility.word),
                           word.unsigned result = (fib (Z.to_nat n)) /\
                           map.get l' FibonacciServer.b = Some result).
  Proof.
    intros.
    eapply intersect_exec.
    + pose proof fib_bounding_metrics as Hbound.
      specialize Hbound with (n := Z.to_nat n).
      rewrite Z2Nat.id in Hbound; [|blia].
      eapply Hbound. cbn. blia.
    + eapply fib_program_correct. blia.
  Qed.

  Definition run1 : Pipeline.M unit := @run1 _ _ _ _ Pipeline.RVM _ iset.
  Definition mcomp_sat := GoFlatToRiscv.mcomp_sat.

  Lemma fib_compiled: forall n,
    0 <= n <= 60 ->
    runsToNonDet.runsTo (mcomp_sat run1)
                        (programmedMachine n)
                        (fun (finalL: RiscvMachine) =>
                           exists (result: Utility.word),
                             map.get finalL.(getRegs) FibonacciServer.b = Some result /\
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