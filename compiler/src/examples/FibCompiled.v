Require Import compiler.Pipeline.
Require Import riscv.Platform.MetricLogging.
Require Import bedrock2.Examples.Demos.

Section FibCompiled.

  Context {p: Pipeline.parameters}.
  Context {h: Pipeline.assumptions}.

  Local Notation RiscvMachine := (MetricRiscvMachine Register Pipeline.actname).

  (* just to make sure all typeclass instances are available: *)
  Definition mcomp_sat:
    Pipeline.M unit -> RiscvMachine -> (RiscvMachine -> Prop) -> Prop :=
    GoFlatToRiscv.mcomp_sat.

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

  Definition programmedMachine (n : Z) : RiscvMachine := zeroedRiscvMachine (* putProgram (compile (fib_ExprImp n)) zeroedriscvmachine *).

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

  Eval vm_compute in (fib 35).

  Definition regb : Register := 2.

  Existing Instance Demos.Fibonacci.ZNames.Inst.

  Definition fib_ExprImp(n: Z): Syntax.cmd. Admitted.
                                  
  Axiom fib_program_logic: forall n t m l mc,
     (Z.of_nat n) < BinInt.Z.pow_pos 2 32 ->
     Semantics.exec map.empty (fib_ExprImp (Z.of_nat n)) t m l mc (
                      fun t' m ' l' mc' =>
                        bedrock2.MetricLogging.instructions mc' <= bedrock2.MetricLogging.instructions mc + (Z.of_nat n) * 34 + 39 /\
                        exists (result: Utility.word),
                          word.unsigned result = (fib n) /\
                          map.get l' regb = Some result).

  Lemma fib_demo: forall n,
    0 <= n <= 50 ->
    runsToNonDet.runsTo (mcomp_sat run1)
                        (programmedMachine n)
                        (fun (finalL: RiscvMachine) =>
                           exists (result: Utility.word),
                             map.get finalL.(getRegs) regb = Some result /\
                             word.unsigned result = (fib (Z.to_nat n)) /\
                             finalL.(getMetrics).(instructions) <= 34 * n + 39).
  Proof.
    pose proof Pipeline.exprImp2Riscv_correct.
    intros.
    eapply runsToNonDet.runsTo_weaken; [eapply H|].
    9 : {
      eapply ExprImp.weaken_exec; [eapply fib_program_logic with (n := (Z.to_nat n))|].
      + match goal with
        | |- _ < ?x => let r := eval cbv in x in change x with r
        end.
        rewrite Z2Nat.id by blia. blia.
      + intros.
        simpl in H1.
        + 
      eapply fib_program_logic.
      10 : {
      intros.
      
End FibCompiled.