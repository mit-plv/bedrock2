Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Utility.FreeMonad.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Platform.Memory.
Require Import riscv.Spec.CSRFile.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.StringRecords.
Import RecordNotations. (* Warnings are spurious, COQBUG https://github.com/coq/coq/issues/13058 *)
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.SeparationLogic.
Require Import compiler.Simp.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.Encode.
Require Import riscv.Platform.MinimalCSRs.
Require Import riscv.Examples.SoftmulInsts.
Require Import riscv.Platform.MaterializeRiscvProgram.

Section Riscv.
  Context {word: Word.Interface.word 32}.
  Context {word_ok: word.ok word}.
  Context {mem: map.map word byte}.
  Context {registers: map.map Z word}.

  (* RISC-V Monad *)
  Local Notation M := (free riscv_primitive primitive_result).

  Local Instance Words32: Utility.Words := {
    Utility.word := word;
    Utility.width_cases := or_introl eq_refl;
  }.

  (*
  Definition mcomp_sat{A: Type}(m: M A)(initial: State)(post: A -> State -> Prop): Prop :=
      free.interpret run_primitive m initial post (fun _ => False).
   *)
  Definition mcomp_sat(m: M unit)(initial: State)(post: State -> Prop): Prop :=
    free.interpret run_primitive m initial (fun tt => post) (fun _ => False).

  Lemma invert_fetch: forall initial post k,
      mcomp_sat (pc <- Machine.getPC; i <- Machine.loadWord Fetch pc; k i)
        initial post ->
      exists w, load_bytes 4 initial#"mem" initial#"pc" = Some w /\
                mcomp_sat (k w) initial post.
  Proof.
    intros. unfold mcomp_sat in *. cbn -[HList.tuple load_bytes] in H.
    unfold load in H.
    simp. eauto.
  Qed.

  Lemma build_fetch: forall (initial: State) post k w,
      load_bytes 4 initial#"mem" initial#"pc" = Some w ->
      mcomp_sat (k w) initial post ->
      mcomp_sat (pc <- Machine.getPC; i <- Machine.loadWord Fetch pc; k i) initial post.
  Proof.
    intros. unfold mcomp_sat in *. cbn -[HList.tuple load_bytes].
    unfold load. simpl in *. rewrite H. assumption.
  Qed.

  Lemma decode_verify_iset: forall iset i, verify_iset (decode iset i) iset.
  Proof.
  Admitted.

  Lemma decode_I_to_IM: forall i inst,
      decode RV32IM i = IInstruction inst ->
      decode RV32I  i = IInstruction inst.
  Proof.
  Admitted.

  Lemma decode_CSR_to_IM: forall i inst,
      decode RV32IM i = CSRInstruction inst ->
      decode RV32I  i = CSRInstruction inst.
  Proof.
  Admitted.

  Lemma decode_verify: forall iset i, verify (decode iset i) iset.
  Proof.
  Abort. (* maybe not needed *)

  Definition related(r1 r2: State): Prop :=
    r1#"regs" = r2#"regs" /\
    r1#"pc" = r2#"pc" /\
    r1#"nextPc" = r2#"nextPc" /\
    r1#"log" = r2#"log" /\
    exists mtvec_base mscratch stacktrash,
      map.get r2#"csrs" CSRField.MTVecBase = Some mtvec_base /\
      map.get r2#"csrs" CSRField.MScratch = Some mscratch /\
      List.length stacktrash = 32%nat /\
      (eq r1#"mem" * word_array (word.of_Z mscratch) stacktrash *
       program RV32I (word.of_Z (mtvec_base * 4)) handler_insts)%sep r2#"mem".

  Lemma softmul_correct: forall initialH initialL post,
      runsTo (mcomp_sat (run1 RV32IM)) initialH post ->
      related initialH initialL ->
      runsTo (mcomp_sat (run1 RV32I)) initialL (fun finalL =>
        exists finalH, related finalH finalL /\ post finalH).
  Proof.
    intros *. intros R. revert initialL. induction R; intros. {
      apply runsToDone. eauto.
    }
    unfold run1 in H |- *.
    unfold related in H2.
    eapply invert_fetch in H. simp.
    pose proof (decode_verify_iset RV32IM (LittleEndian.combine 4 w)) as V.
    rename initial into initialH.
    destruct (decode RV32IM (LittleEndian.combine 4 w)) as
        [inst|inst|inst|inst|inst|inst|inst|inst|inst|inst] eqn: E;
      cbn in V; try intuition congruence.
    - (* IInstruction *)
      eapply runsToStep with (midset0 := fun midL => exists midH, related midH midL /\ midset midH).
      + eapply build_fetch with (w := w). {
          admit. (* separation logic *)
        }
        apply decode_I_to_IM in E. rewrite E.
        (* lower Hr *)
        admit.
      + intros midL. intros. simp. eapply H1; eassumption.
    - (* MInstruction *)
      admit.
    - (* CSRInstruction *)
      eapply runsToStep with (midset0 := fun midL => exists midH, related midH midL /\ midset midH).
      + eapply build_fetch with (w := w). {
          admit. (* separation logic *)
        }
        apply decode_CSR_to_IM in E. rewrite E.
        (* lower Hr *)
        admit.
      + intros midL. intros. simp. eapply H1; eassumption.

  Abort.

End Riscv.
