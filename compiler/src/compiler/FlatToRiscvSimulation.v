Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import compiler.Simulation.
Require Import compiler.Simp.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Primitives.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.util.Common.
Require Import compiler.Simp.
Require Import compiler.SeparationLogic.
Require Import compiler.SimplWordExpr.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.DivisibleBy4.
Require Import compiler.EmitsValid.
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

  Add Ring wring : (word.ring_theory (word := Utility.word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := Utility.word)),
       constants [word_cst]).

  Context (f_entry_rel_pos: Z)
          (f_entry_name: string)
          (p_call: word)
          (Rdata Rexec: mem -> Prop)
          (code_start stack_start stack_pastend: word).

  Local Open Scope ilist_scope.

  Definition ghostConsts(prog: env): GhostConsts := {|
    p_sp := stack_pastend;
    num_stackwords := word.unsigned (word.sub stack_pastend stack_start) / bytes_per_word;
    p_insts := p_call;
    insts := [[Jal RegisterNames.ra (f_entry_rel_pos - word.unsigned (word.sub p_call code_start))]];
    program_base := code_start;
    e_pos := FlatToRiscvDef.function_positions prog;
    e_impl := prog;
    funnames := map.fold (fun acc fname fimpl => cons fname acc) nil prog;
    dframe := Rdata;
    xframe := Rexec;
  |}.

  Definition related(done: bool):
    FlatImp.SimState Z -> MetricRiscvMachine -> Prop :=
    fun '(e, c, t, m, l, mc) st =>
        c = SCall nil f_entry_name nil /\
        (word.unsigned p_call) mod 4 = 0 /\
        (word.unsigned code_start) mod 4 = 0 /\
        map.get (function_positions e) f_entry_name = Some f_entry_rel_pos /\
        fits_stack (ghostConsts e).(num_stackwords) e c /\
        good_e_impl e (ghostConsts e).(funnames) (ghostConsts e).(e_pos) /\
        regs_initialized st.(getRegs) /\
        st.(getPc) = word.add p_call (word.of_Z (if done then 4 else 0)) /\
        goodMachine t m l (ghostConsts e) st.

  Lemma flatToRiscvSim{hyps: @FlatToRiscvCommon.assumptions p}:
      simulation (FlatImp.SimExec Z) FlatToRiscvCommon.runsTo related.
  Proof.
    unfold simulation, FlatImp.SimExec, related, FlatImp.SimState.
    intros.
    destruct s1 as (((((e & c) & t) & m) & l) & mc).
    destruct_RiscvMachine s2.
    simp.
    match goal with
    | A: map.get e f_entry_name = Some ?r1, B: map.get e f_entry_name = Some ?r2 |- _ =>
      pose proof (eq_trans (eq_sym A) B); clear B
    end.
    simp.
    eapply runsTo_weaken.
    - eapply compile_stmt_correct with (g := ghostConsts e)
                                       (pos := word.unsigned (word.sub p_call code_start)); simpl.
      + eapply exec.call; cycle -1; try eassumption.
        Fail eassumption. (* TODO why?? *)
        match goal with
        | H: _ |- _ => exact H
        end.
      + reflexivity.
      + unfold good_reduced_e_impl.
        split. {
          clear. intros k v ?. eassumption.
        }
        assumption.
      + eauto using fits_stack_call.
      + simpl. change (4 * BinIntDef.Z.of_nat 0) with 0. rewrite Z.add_0_r.
        rewrite_match. reflexivity.
      + unfold stmt_not_too_big. simpl. cbv. reflexivity.
      + simpl. auto using Forall_nil.
      + solve_divisibleBy4.
      + assumption.
      + rewrite word.of_Z_unsigned. ring.
      + rewrite word.of_Z_unsigned. ring.
      + clear - hyps.
        eapply proj1 with (B := forall k, In k (map.fold
          (fun (acc : list string) (fname : string) (_ : list Z * list Z * stmt Z) => fname :: acc)
          [] e) -> map.get e k <> None).
        eapply map.fold_spec.
        * split; [constructor|]. intros. simpl in *. contradiction.
        (* TODO define map.keys, map.keys_NoDup *)
        * intros. simp. split.
          -- constructor. 2: assumption. intro C. specialize (H0r _ C). contradiction.
          -- intros. rewrite map.get_put_dec.
             destruct_one_match. 1: congruence.
             simpl in *. destruct H0. 1: congruence. eauto.
      + assumption.
    - simpl. intros. simp.
      eexists; split; [|eassumption].
      cbv beta iota.
      repeat match goal with
             | |- _ /\ _ => split
             | _ => eassumption
             | _ => reflexivity
             end.
      + unfold goodMachine in *. simp. eauto using fits_stack_call.
      + (* TODO remove regs_initialized from compile_stmt_correct_new because
           it's already in goodMachine *)
        unfold goodMachine in *. simp. assumption.
      + (* TODO make word automation from bsearch work here *)
        match goal with
        | H: getPc _ = _ |- getPc _ = _ => rewrite H
        end.
        solve_word_eq Utility.word_ok. (* TODO make sure solve_word complains if no ring found *)
  Qed.

End Sim.
