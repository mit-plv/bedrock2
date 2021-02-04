Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import compiler.Simulation.
Require Import coqutil.Tactics.Simp.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Primitives.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.util.Common.
Require Import compiler.SeparationLogic.
Require Export coqutil.Word.SimplWordExpr.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.DivisibleBy4.
Require Import compiler.MetricsToRiscv.
Require Import compiler.FlatImp.
Require Import compiler.RunInstruction.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvFunctions.
Require Import bedrock2.MetricLogging.
Require Import riscv.Utility.InstructionCoercions.


Section Sim.
  Context {p: FlatToRiscvCommon.parameters}.

  Local Open Scope ilist_scope.

  Add Ring wring : (word.ring_theory (word := Utility.word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := Utility.word)),
       constants [word_cst]).

  Context (f_entry_rel_pos: Z)
          (f_entry_name: string)
          (p_call: word)
          (Rdata Rexec: mem -> Prop)
          (functions_start stack_start stack_pastend: word)
          (prog: env).

  Definition ghostConsts: GhostConsts := {|
    p_sp := stack_pastend;
    rem_stackwords := word.unsigned (word.sub stack_pastend stack_start) / bytes_per_word;
    rem_framewords := 0;
    p_insts := p_call;
    insts := [[Jal RegisterNames.ra (f_entry_rel_pos + word.signed (word.sub functions_start p_call))]];
    program_base := functions_start;
    e_pos := FlatToRiscvDef.build_fun_pos_env prog;
    e_impl := prog;
    dframe := Rdata;
    xframe := Rexec;
  |}.

  Definition related(done: bool):
    FlatImp.SimState Z -> MetricRiscvMachine -> Prop :=
    fun '(t, m, l, mc) st =>
        st.(getPc) = word.add p_call (word.of_Z (if done then 4 else 0)) /\
        goodMachine t m l ghostConsts st.

  Lemma flatToRiscvSim{hyps: @FlatToRiscvCommon.assumptions p}:
    (forall resvars extcall argvars,
        compiles_FlatToRiscv_correctly
          compile_ext_call (SInteract resvars extcall argvars)) ->
    let c := SSeq SSkip (SCall nil f_entry_name nil) in
    (word.unsigned p_call) mod 4 = 0 ->
    (word.unsigned functions_start) mod 4 = 0 ->
    map.get (build_fun_pos_env prog) f_entry_name = Some f_entry_rel_pos ->
    fits_stack ghostConsts.(rem_framewords) ghostConsts.(rem_stackwords) prog c ->
    good_e_impl prog ghostConsts.(e_pos) ->
    simulation (FlatImp.SimExec Z prog c) FlatToRiscvCommon.runsTo related.
  Proof.
    unfold simulation, FlatImp.SimExec, related, FlatImp.SimState.
    intros.
    destruct s1 as (((t & m) & l) & mc).
    destruct_RiscvMachine s2.
    simp.
    match goal with
    | A: _, H: mid _ _ _ _ |- _ => specialize A with (1 := H)
    end.
    simp.
    match goal with
    | A: map.get prog f_entry_name = Some ?r1, B: map.get prog f_entry_name = Some ?r2 |- _ =>
      pose proof (eq_trans (eq_sym A) B); clear B
    end.
    simp.
    eapply runsTo_weaken.
    - eapply compile_stmt_correct with (g := ghostConsts)
                                       (pos := - word.signed (word.sub functions_start p_call)); simpl.
      + assumption.
      + eapply exec.call; cycle -1; try eassumption.
        Fail eassumption. (* TODO why?? *)
        match goal with
        | H: _ |- _ => exact H
        end.
      + clear. intros k v ?. eassumption.
      + assumption.
      + eauto using fits_stack_call.
      + simpl. change (4 * BinIntDef.Z.of_nat 0) with 0. rewrite Z.add_0_r.
        rewrite_match. f_equal. f_equal. f_equal. ring.
      + unfold stmt_not_too_big. simpl. cbv. reflexivity.
      + simpl. auto using Forall_nil.
      + assert (word.ok word) by exact Utility.word_ok.
        solve_divisibleBy4.
      + assumption.
      + (* TODO why are these manual steps needed? *)
        rewrite word.ring_morph_opp.
        rewrite word.of_Z_signed.
        solve_word_eq Utility.word_ok.
      + (* TODO why are these manual steps needed? *)
        rewrite word.ring_morph_opp.
        rewrite word.of_Z_signed.
        solve_word_eq Utility.word_ok.
      + assumption.
    - simpl. intros. simp.
      eexists; split; [|eassumption].
      cbv beta iota.
      repeat match goal with
             | |- _ /\ _ => split
             | _ => eassumption
             | _ => reflexivity
             end.
      + (* TODO make word automation from bsearch work here *)
        match goal with
        | H: getPc _ = _ |- getPc _ = _ => rewrite H
        end.
        solve_word_eq Utility.word_ok. (* TODO make sure solve_word complains if no ring found *)
  Qed.

End Sim.
