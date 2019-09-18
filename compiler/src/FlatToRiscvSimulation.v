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

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Definition State1: Type := FlatImp.env * FlatImp.stmt *
                             bool * Semantics.trace * Semantics.mem * FlatToRiscv.locals.

  Definition exec1: State1 -> (State1 -> Prop) -> Prop :=
    fun '(e, c, done, t, m, l) post =>
      done = false /\
      forall mc, FlatImp.exec e c t m l mc (fun t' m' l' mc' =>
                                              post (e, c, true, t', m', l')).

  Definition State2: Type := MetricRiscvMachine.

  Definition exec2: State2 -> (State2 -> Prop) -> Prop := FlatToRiscvCommon.runsTo.

  Definition goodMachine t m l g st := exists mc, goodMachine t m l mc g st.

  Definition related: State1 -> State2 -> Prop :=
    fun '(e, c, done, t, m, l) st =>
      exists (g: GhostConsts) (pos: Z),
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

  Lemma flatToRiscvSim{hyps: @FlatToRiscv.assumptions p}: simulation exec1 exec2 related.
  Proof.
    unfold simulation, exec1, exec2, related, State1, State2.
    intros.
    destruct s1 as (((((e & c) & done) & t) & m) & l).
    unfold goodMachine in *. (* TODO inline *)
    destruct_RiscvMachine s2.
    simp.
    eapply runsTo_weaken.
    - eapply compile_stmt_correct_new; simpl.
      + lazymatch goal with
        | H: forall (_: MetricLog), _ |- _ =>
          apply (H (mkMetricLog 0 0 0 0))
        end.
      + reflexivity.
      + unfold exists_good_reduced_e_impl. exists g.(e_impl).
        split. {
          clear. intros k v H. assumption.
        }
        split; assumption.
      + eassumption.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
      + ring_simplify (pos + 0). reflexivity.
      + assumption.
      + assumption.
    - simpl. intros. simp.
      eexists; split; [|eassumption].
      cbv beta iota.
      do 2 eexists.
      repeat match goal with
             | |- _ /\ _ => split
             | _ => eapply TODO_preserve_regs_initialized; (eassumption||reflexivity)
             | _ => eassumption
             | _ => reflexivity
             end.
      2: eexists; eassumption.
      (* TODO make word automation from bsearch work here *)
      match goal with
      | H: getPc _ = _ |- getPc _ = _ => rewrite H
      end.
      solve_word_eq word_ok. (* TODO make sure solve_word complains if no ring found *)
  Qed.

End Sim.
