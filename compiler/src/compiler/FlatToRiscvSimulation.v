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
Require Import compiler.util.ListLib.
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


Section Sim.
  Context {p: FlatToRiscv.parameters}.

  Add Ring wring : (word.ring_theory (word := Utility.word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := Utility.word)),
       constants [word_cst]).

  (* The GhostConsts tell us how to look at the low-level state in order to
     establish the relationship to the high-level state.
     Before we can use "related", we will have to provide GhostConsts.
     In other relations, we might also need to provide more "how to look at"
     parameters which say things about the interpretation of the high-level
     and/or low-level state.
     Since we have to provide GhostConsts from outside, we can also make sure
     that they match with "how to look at" parameters from the other phases.
     The argument "pos" is the position of the code relative to program_base. *)
  Definition related(g: GhostConsts)(pos: Z): FlatImp.SimState -> MetricRiscvMachine -> Prop :=
    fun '(e, c, done, t, m, l) st =>
        e = g.(e_impl) /\
        fits_stack g.(num_stackwords) g.(e_impl) c /\
        (forall f argnames retnames body,
            map.get g.(e_impl) f = Some (argnames, retnames, body) ->
            Forall valid_register argnames /\
            Forall valid_register retnames /\
            valid_registers body /\
            stmt_not_too_big body /\
            In f g.(funnames) /\
            (exists pos : Z, map.get g.(e_pos) f = Some pos /\ pos mod 4 = 0)) /\
        stmt_not_too_big c /\
        valid_registers c /\
        compile_stmt_new g.(e_pos) pos c = g.(insts) /\
        pos mod 4 = 0 /\
        regs_initialized st.(getRegs) /\
        st.(getPc)  = word.add g.(program_base) (word.of_Z
           (pos + if done then 4 * Z.of_nat (length g.(insts)) else 0)) /\
        g.(p_insts) = word.add g.(program_base) (word.of_Z pos) /\
        goodMachine t m l g st.

  (* will probably have to be part of the invariant in compile_stmt_correct_new *)
  Axiom TODO_preserve_regs_initialized: forall regs1 regs2,
      regs_initialized regs1 -> regs_initialized regs2.

  Lemma flatToRiscvSim{hyps: @FlatToRiscv.assumptions p}: forall (g: GhostConsts) (pos: Z),
      NoDup g.(funnames) ->
      word.unsigned g.(program_base) mod 4 = 0 ->
      simulation FlatImp.SimExec FlatToRiscvCommon.runsTo (related g pos).
  Proof.
    unfold simulation, FlatImp.SimExec, related, FlatImp.SimState.
    intros.
    destruct s1 as (((((e & c) & done) & t) & m) & l).
    destruct_RiscvMachine s2.
    simp.
    eapply runsTo_weaken.
    - eapply compile_stmt_correct_new; simpl.
      + lazymatch goal with
        | H: forall (_: MetricLog), _ |- _ =>
          apply (H (mkMetricLog 0 0 0 0))
        end.
      + reflexivity.
      + unfold good_reduced_e_impl.
        split. {
          clear. intros k v ?. eassumption.
        }
        assumption.
      + eassumption.
      + eassumption.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
      + ring_simplify (pos + 0). reflexivity.
      + assumption.
      + assumption.
      + assumption.
    - simpl. intros. simp.
      eexists; split; [|eassumption].
      cbv beta iota.
      repeat match goal with
             | |- _ /\ _ => split
             | _ => eapply TODO_preserve_regs_initialized; (eassumption||reflexivity)
             | _ => eassumption
             | _ => reflexivity
             end.
      (* TODO make word automation from bsearch work here *)
      match goal with
      | H: getPc _ = _ |- getPc _ = _ => rewrite H
      end.
      solve_word_eq word_ok. (* TODO make sure solve_word complains if no ring found *)
  Qed.

End Sim.
