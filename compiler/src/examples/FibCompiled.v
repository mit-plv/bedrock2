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
Require Import compiler.FlatToRiscvCommon.
Require Import bedrock2.Examples.Demos.

Section FibCompiled.

  Definition n_load_addr: Z := 4096.
  Definition n_store_addr: Z := 5000.

  Definition fib_ExprImp: cmd := Eval cbv in
    snd (snd (Demos.fibonacciServer n_load_addr n_store_addr)).

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

  Eval cbv in fib_ExprImp.
  
  Fixpoint get_if s :=
    match s with
    | cmd.seq s1 s2 =>
      match s1 with
      | cmd.cond _ _ _ => s1
      | _ => get_if s2
      end
    | _ => s
    end.

  Definition fib_if := get_if fib_ExprImp.

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
      try (repeat split; fib_step_precondition)
    ].

  Ltac propogate_eq :=
    repeat match goal with
           | H0: ?x = ?y, H1: ?y = ?z |- _ => rewrite H1 in H0
           end; assumption.

  Lemma fib_correct_body: forall t m (l : locals) mc a b i n,
      (exists old, load access_size.four m (word.of_Z n_store_addr) = Some (word.of_Z old)) ->
      map.get l FibonacciServer.a = Some a ->
      map.get l FibonacciServer.b = Some b ->
      map.get l FibonacciServer.i = Some i ->
      map.get l FibonacciServer.n = Some n ->
      exec map.empty fib_while_body t m l mc (fun t' m' l' mc' =>
        t' = t /\
        (exists old, load access_size.four m' (word.of_Z n_store_addr) = Some (word.of_Z old)) /\
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
      (exists old, load access_size.four m' (word.of_Z n_store_addr) = Some (word.of_Z old)) /\
      map.get l' FibonacciServer.a = Some a /\
      map.get l' FibonacciServer.b = Some b /\
      map.get l' FibonacciServer.c = Some (word.add a b) /\
      map.get l' FibonacciServer.i = Some i /\
      map.get l' FibonacciServer.n = Some n /\
      instructionsH mc' = instructionsH mc + 5));
      [exec_set_solve|].
    intros.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
      (exists old, load access_size.four m' (word.of_Z n_store_addr) = Some (word.of_Z old)) /\
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
      (exists old, load access_size.four m' (word.of_Z n_store_addr) = Some (word.of_Z old)) /\
      t' = t /\
      map.get l' FibonacciServer.a = Some b /\
      map.get l' FibonacciServer.b = Some (word.add a b) /\
      map.get l' FibonacciServer.c = Some (word.add a b) /\
      map.get l' FibonacciServer.i = Some i /\
      map.get l' FibonacciServer.n = Some n /\
      instructionsH mc' = instructionsH mc + 9));
      exec_set_solve.
  Qed.

  Lemma fib_correct_while: forall n (iter : nat) t m (l : locals) mc i,
      Z.of_nat n < 2 ^ 32 ->
      (iter <= n)%nat ->
      (i = n - iter)%nat ->
      (exists old, load access_size.four m (word.of_Z n_store_addr) = Some (word.of_Z old)) ->
      map.get l FibonacciServer.a = Some (word.of_Z (fib i)) ->
      map.get l FibonacciServer.b = Some (word.of_Z (fib (S i))) ->
      map.get l FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) ->
      map.get l FibonacciServer.i = Some (word.of_Z (Z.of_nat i) : word) ->
      exec map.empty fib_while t m l mc (fun t' m' l' mc' =>
        (exists old, load access_size.four m' (word.of_Z n_store_addr) = Some (word.of_Z old)) /\
        t' = t /\
        instructionsH mc' <= instructionsH mc + (Z.of_nat iter) * 34 + 12 /\
        map.get l' FibonacciServer.b = Some (word.of_Z (fib (n + 1)))).
  Proof.
    induction iter.
    - intros.
      eapply @exec.while_false.
      + eval_var_solve.
      + simpl. destruct_one_match.
        * admit.
        * reflexivity.
      + repeat split.
        * assumption.
        * simpl. Lia.blia.
        * replace n with i by blia. rewrite H4. repeat f_equal. rewrite Nat.add_1_r. reflexivity.
    - intros.
      eapply @exec.while_true.
      + eval_var_solve.
      + simpl. destruct_one_match.
        * simpl. rewrite Zdiv.Zmod_1_l; [discriminate | cbv; reflexivity].
        * repeat match goal with
                 | H: context[_ mod _] |- _ => rewrite Z.mod_small in H; [|blia]
                 end.
          assert (i < n)%nat by blia.
          apply Z.ltb_ge in E. blia.
      + eapply fib_correct_body; eauto.
      + intros.
        eval_fib_var_names.
        destruct_hyp.
        eapply weaken_exec.
        * eapply IHiter; try (reflexivity || assumption).
          -- blia.
          -- rewrite H9. f_equal. f_equal. f_equal. blia.
          -- rewrite H10. f_equal. replace (S i) with (n - iter)%nat by blia. rewrite H1.
             assert (n - iter > 0)%nat by blia. admit.
          -- rewrite H11. f_equal. rewrite H1. admit.
        * cbv beta. intros. destruct_hyp.
          repeat split.
          -- assumption.
          -- propogate_eq.
          -- unfold_MetricLog. simpl in *. blia.
          -- assumption.
  Admitted.

  Lemma fib_if_true_correct: forall (n: nat) t m (l: locals) mc,
      (n < 48)%nat ->
      (exists old, load access_size.four m (word.of_Z n_store_addr) = Some (word.of_Z old)) ->
      map.get l FibonacciServer.a = Some (word.of_Z 0) ->
      map.get l FibonacciServer.b = Some (word.of_Z 1) ->
      map.get l FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) ->
      map.get l FibonacciServer.i = Some (word.of_Z 0)  ->
      exec map.empty fib_if t m l mc (fun t' m' l' mc' =>
        (exists old, load access_size.four m' (word.of_Z n_store_addr) = Some (word.of_Z old)) /\
        t' = t /\
        instructionsH mc' <= instructionsH mc + (Z.of_nat n) * 34 + 25 /\
        map.get l' FibonacciServer.b = Some (word.of_Z (fib (n + 1)))).
  Proof.
    intros.
    eapply @exec.if_true.
    - eval_var_solve.
    - simpl.
      destruct_one_match; [discriminate|].
      rewrite Z.ltb_ge in *.
      repeat rewrite Z.mod_small in * by blia.
      exfalso. blia.
    - eapply weaken_exec.
      + eapply fib_correct_while with (iter := n) (i := 0%nat); try eassumption.
        * blia.
        * apply le_n.
        * rewrite Nat.sub_diag. reflexivity. 
      + intros. cbv beta in *. destruct_hyp.
        repeat split; try assumption.
        unfold_MetricLog. simpl in *. blia.
  Qed.

  Lemma fib_if_false_correct: forall (n: nat) t m (l: locals) mc,
      Z.of_nat n < 2 ^ 32 ->
      (n >= 48)%nat ->
      (exists old, load access_size.four m (word.of_Z n_store_addr) = Some (word.of_Z old)) ->
      map.get l FibonacciServer.a = Some (word.of_Z 0) ->
      map.get l FibonacciServer.b = Some (word.of_Z 1) ->
      map.get l FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) ->
      map.get l FibonacciServer.i = Some (word.of_Z 0)  ->
      exec map.empty fib_if t m l mc (fun t' m' l' mc' =>
        (exists old, load access_size.four m' (word.of_Z n_store_addr) = Some (word.of_Z old)) /\
        t' = t /\
        instructionsH mc' <= instructionsH mc + (Z.of_nat n) * 34 + 25 /\
        map.get l' FibonacciServer.b = Some (word.of_Z (-1))).
  Proof.
    intros.
    eapply @exec.if_false.
    + eval_var_solve.
    + simpl.
      destruct_one_match; [|reflexivity].
      rewrite Z.ltb_lt in *.
      repeat rewrite Z.mod_small in * by blia.
      exfalso. blia.
    + exec_set_solve.
  Qed.
    
  Lemma fib_correct: forall (n: nat) t (m: mem) (l : locals) mc,
      load access_size.four m (word.of_Z n_load_addr) = Some (word.of_Z (Z.of_nat n)) ->
      (exists old, load access_size.four m (word.of_Z n_store_addr) = Some (word.of_Z old)) ->
      Z.of_nat n < 2 ^ 32 ->
      exec map.empty fib_ExprImp t m l mc (fun t' m' l' mc' =>
        instructionsH mc' <= instructionsH mc + (Z.of_nat n) * 34 + 62 /\
        ((n < 48)%nat /\ ptsto_word (word.of_Z n_load_addr) (word.of_Z (fib (n + 1))) m') \/
        ((n >= 48)%nat /\ ptsto_word (word.of_Z n_load_addr) (word.of_Z (-1)) m')).
  Proof.
    intros *. intro Hload. intro HStore. intros.
    cbv [n_load_addr] in *.
    unfold fib_ExprImp.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
      t' = t /\
      (exists old, load access_size.four m' (word.of_Z n_store_addr) = Some (word.of_Z old)) /\
      map.get l' FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) /\
      instructionsH mc' = instructionsH mc + 10));
      [eapply @exec.set; [simpl in *; rewrite Hload; f_equal | repeat split; fib_step_precondition] |].
    intros. destruct_hyp.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
      t' = t /\
      (exists old, load access_size.four m' (word.of_Z n_store_addr) = Some (word.of_Z old)) /\
      map.get l' FibonacciServer.a = Some (word.of_Z 0) /\
      map.get l' FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) /\
      instructionsH mc' = instructionsH mc + 19));
      [exec_set_solve|].
    intros. destruct_hyp.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
      t' = t /\
      (exists old, load access_size.four m' (word.of_Z n_store_addr) = Some (word.of_Z old)) /\
      map.get l' FibonacciServer.a = Some (word.of_Z 0) /\
      map.get l' FibonacciServer.b = Some (word.of_Z 1) /\
      map.get l' FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) /\
      instructionsH mc' = instructionsH mc + 28));
      [exec_set_solve|].
    intros. destruct_hyp.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
      t' = t /\
      (exists old, load access_size.four m' (word.of_Z n_store_addr) = Some (word.of_Z old)) /\
                                     map.get l' FibonacciServer.a = Some (word.of_Z 0) /\
                                     map.get l' FibonacciServer.b = Some (word.of_Z 1) /\
                                     map.get l' FibonacciServer.i = Some (word.of_Z 0) /\
                                     map.get l' FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) /\
                                     instructionsH mc' = instructionsH mc + 37));
      [exec_set_solve|].
    intros.
    destruct_hyp.
    (*
    pose proof Nat2Z.is_nonneg as Hpos.
    specialize Hpos with (n := n). *)

    destruct (n <? 48)%nat eqn:Hlt.
    - eapply @exec.seq with (mid := (fun t' m' l' mc' =>
        t' = t /\
        (exists old, load access_size.four m' (word.of_Z n_store_addr) = Some (word.of_Z old)) /\
        instructionsH mc' <= instructionsH mc + (Z.of_nat n) * 34 + 62 /\
        map.get l' FibonacciServer.b = Some (word.of_Z (fib (n + 1))))).
        * rewrite Nat.ltb_lt in *.
          eapply weaken_exec; [eapply fib_if_true_correct; eassumption|].
          cbv beta. intros. destruct_hyp.
          repeat split; try assumption.
          -- propogate_eq.
          -- blia.   
        * intros. destruct_hyp.
          eapply @exec.store.
          -- reflexivity.
          -- eval_var_solve.
          -- cbv [load load_Z] in HStore.
             cbv [store store_Z bedrock2.Memory.store_bytes].
             destruct_one_match; [reflexivity|].
             cbv [bedrock2.Memory.unchecked_store_bytes].
  Qed.
                                  
  Axiom fib_program_correct: forall n t m l mc,
      0 <= n <= 60 ->
      Semantics.exec map.empty fib_ExprImp t m l mc (
                       fun t' m ' l' mc' =>
                         exists (result: Utility.word),
                           word.unsigned result = (fib (Z.to_nat n)) /\
                           map.get l' FibonacciServer.b = Some result).
    

  Lemma fib_program_correct_bounded: forall n t m l mc,
      0 <= n <= 60 ->
      load access_size.four m (word.of_Z n_load_addr) = Some (word.of_Z n) ->
      Semantics.exec map.empty fib_ExprImp t m l mc (
                       fun t' m ' l' mc' =>
                         instructionsH mc' <= instructionsH mc + n * 34 + 62 /\
                         exists (result: Utility.word),
                           word.unsigned result = (fib (Z.to_nat n)) /\
                           map.get l' FibonacciServer.b = Some result).
  Proof.
    intros.
    eapply intersect_exec.
    + pose proof fib_bounding_metrics as Hbound.
      specialize Hbound with (n := Z.to_nat n).
      rewrite Z2Nat.id in Hbound; [|blia].
      eapply Hbound; [assumption|].
      cbn. blia.
    + eapply fib_program_correct. blia.
  Qed.

  Definition run1 : Pipeline.M unit := @run1 _ _ _ _ Pipeline.RVM _ iset.
  Definition mcomp_sat := GoFlatToRiscv.mcomp_sat.

  (* Forall initial metrics *)
  Lemma fib_compiled: forall n (initialMachine: RiscvMachine) (m: map.map word byte) initialMem,
      0 <= n <= 60 ->
      word.unsigned (getPc initialMachine) mod 4 = 0 ->
      getNextPc initialMachine = word.add (getPc initialMachine) (word.of_Z 4) ->
      load access_size.four initialMem (word.of_Z n_load_addr) = Some (word.of_Z n) ->
      getMetrics initialMachine = EmptyMetricLog ->
      Separation.sep (program (getPc initialMachine) (ExprImp2Riscv fib_ExprImp)) (eq initialMem) (getMem initialMachine) ->
      runsToNonDet.runsTo (mcomp_sat run1)
                          initialMachine
                          (fun (finalL: RiscvMachine) =>
                             exists (result: Utility.word),
                               map.get finalL.(getRegs) FibonacciServer.b = Some result /\
                               word.unsigned result = (fib (Z.to_nat n)) /\
                               finalL.(getMetrics).(instructions) <= n * 34 + 62).
  Proof.
    intros.
    eapply runsToNonDet.runsTo_weaken.
    - pose proof Pipeline.exprImp2Riscv_correct as Hp.
      specialize Hp with (sH := fib_ExprImp)
                         (mcH := bedrock2.MetricLogging.EmptyMetricLog).
      eapply Hp.
      + simpl. blia.
      + cbv. repeat constructor.
      + reflexivity.
      + assumption.
      + assumption.
      + reflexivity.
      + eassumption.
      + cbv [Pipeline.ext_guarantee pipeline_params]. exact I.
      + eapply ExprImp.weaken_exec.
        * eapply fib_program_correct_bounded with (n := n); assumption.
        * intros. eassumption.
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
        * match goal with
          | H: (getMetrics initialMachine) = ?m |- _ => rewrite H in *
          end.
          simpl in *. rewrite Z.sub_0_r in *. eassumption.
        * assumption.
  Qed.

  Print Assumptions fib_compiled.

End FibCompiled.