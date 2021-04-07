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
Require Import coqutil.Decidable.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Datatypes.HList.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.SeparationLogic.
Require Import coqutil.Tactics.Simp.
Require Import bedrock2.Syntax.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.Encode.
Require Import riscv.Platform.MinimalCSRs.
Require Import riscv.Examples.SoftmulInsts.
Require Import riscv.Platform.MaterializeRiscvProgram.
Require Import compiler.UniqueSepLog.

Axiom TODO: False.

Section Riscv.
  Context {word: Word.Interface.word 32}.
  Context {word_ok: word.ok word}.
  Context {mem: map.map word byte}.
  Context {mem_ok: map.ok mem}.
  Context {registers: map.map Z word}.
  Context {registers_ok: map.ok registers}.

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

  Lemma weaken_mcomp_sat: forall m initial (post1 post2: State -> Prop),
      (forall s, post1 s -> post2 s) ->
      mcomp_sat m initial post1 ->
      mcomp_sat m initial post2.
  Proof.
    unfold mcomp_sat. intros.
    eapply free.interpret_weaken_post with (postA1 := fun _ => False); eauto; simpl;
      eauto using weaken_run_primitive.
  Qed.

  Lemma invert_fetch0: forall initial post k,
      mcomp_sat (pc <- Machine.getPC; i <- Machine.loadWord Fetch pc; k i)
        initial post ->
      exists w, load_bytes 4 initial#"mem" initial#"pc" = Some w /\
                mcomp_sat (k w) initial post.
  Proof.
    intros. unfold mcomp_sat in *. cbn -[HList.tuple load_bytes] in H.
    unfold load in H.
    simp. eauto.
  Qed.

  Lemma invert_fetch1: forall initial post k,
      mcomp_sat (pc <- Machine.getPC; i <- Machine.loadWord Fetch pc; k i) initial post ->
      exists (w: w32) R, R \*/ bytes (n:=4) initial#"pc" w = Some initial#"mem" /\
                  mcomp_sat (k w) initial post.
  Proof.
    intros. apply invert_fetch0 in H. simp.
  Admitted.

  Lemma invert_fetch: forall initial post iset,
      mcomp_sat (run1 iset) initial post ->
      exists R i, R \*/ instr initial#"pc" i = Some initial#"mem" /\
                  verify i iset /\
                  mcomp_sat (Execute.execute i;; endCycleNormal) initial post.
  Proof.
    intros. apply invert_fetch0 in H. simp.
  Admitted.

  Lemma build_fetch0: forall (initial: State) post k w,
      load_bytes 4 initial#"mem" initial#"pc" = Some w ->
      mcomp_sat (k w) initial post ->
      mcomp_sat (pc <- Machine.getPC; i <- Machine.loadWord Fetch pc; k i) initial post.
  Proof.
    intros. unfold mcomp_sat in *. cbn -[HList.tuple load_bytes].
    unfold load. simpl in *. rewrite H. assumption.
  Qed.

  Lemma build_fetch1: forall (initial: State) post k w R,
      mcomp_sat (k w) initial post ->
      R \*/ bytes (n:=4) initial#"pc" w = Some initial#"mem" ->
      mcomp_sat (pc <- Machine.getPC; i <- Machine.loadWord Fetch pc; k i) initial post.
  Proof.
    intros. eapply build_fetch0. 2: eassumption.
  Admitted.

  Definition store'(n: nat)(ctxid: SourceType)(a: word)(v: tuple byte n)(mach: State)(post: State -> Prop) :=
    exists (R: option mem) (v_old: tuple byte n),
      R \*/ bytes a v_old = Some mach#"mem" /\ post mach(#"mem" := mmap.force (R \*/ bytes a v)).

  Definition store_orig(n: nat)(ctxid: SourceType)(a: word) v (mach: State)(post: State -> Prop) :=
    match Memory.store_bytes n mach#"mem" a v with
    | Some m => post mach(#"mem" := m)
    | None => False
    end.

  Definition load'(n: nat)(ctxid: SourceType)(a: word)(mach: State)(post: tuple byte n -> State -> Prop): Prop :=
    exists (R: option mem) (v: tuple byte n), R \*/ bytes a v = Some mach#"mem" /\ post v mach.

  Definition load_orig(n: nat)(ctxid: SourceType)(a: word)(mach: State)(post: tuple byte n -> State -> Prop) :=
    match Memory.load_bytes n mach#"mem" a with
    | Some v => post v mach
    | None => False
    end.

  Lemma build_fetch: forall (initial: State) iset post (i: Instruction) (R: option mem),
      verify i iset ->
      R \*/ (instr initial#"pc" i) = Some initial#"mem" ->
      mcomp_sat (Execute.execute i;; endCycleNormal) initial post ->
      mcomp_sat (run1 iset) initial post.
  Proof.
    intros. unfold run1, mcomp_sat in *. cbn -[HList.tuple load_bytes].
    assert (load = load') as E by case TODO. rewrite E; clear E.
    unfold load'. do 2 eexists. split; try eassumption.
    replace (decode iset
             (LittleEndian.combine 4
                (LittleEndian.split (Memory.bytes_per access_size.four) (word.unsigned (word.of_Z (encode i))))))
      with i. 2: {
      case TODO. (* decode_encode and split_combine *)
    }
    eassumption.
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
    r1#"csrs" = map.empty /\
    exists mtvec_base mscratch stacktrash,
      map.get r2#"csrs" CSRField.MTVecBase = Some mtvec_base /\
      map.get r2#"csrs" CSRField.MScratch = Some mscratch /\
      List.length stacktrash = 32%nat /\
      Some r1#"mem" \*/ word_array (word.of_Z mscratch) stacktrash \*/
      program (word.of_Z (mtvec_base * 4)) handler_insts = Some r2#"mem".

  Ltac paramrecords :=
    change (@Utility.word Words32) with word in *;
    change (@SortedList.rep CSRFile_map_params) with (@map.rep CSRField.CSRField Z CSRFile) in *;
    change (@width Words32) with 32 in *.

  Lemma related_preserves_load_bytes: forall n sH sL a w,
      related sH sL ->
      load_bytes n sH#"mem" a = Some w ->
      load_bytes n sL#"mem" a = Some w.
  Proof.
  Admitted.

  Lemma load_preserves_related: forall n c a initialH initialL postH,
      related initialH initialL ->
      load n c a initialH postH ->
      load n c a initialL
           (fun res finalL => exists finalH, related finalH finalL /\ postH res finalH).
  Proof.
    unfold load.
    cbn. intros.
    destruct_one_match_hyp. 2: contradiction.
    erewrite related_preserves_load_bytes; eauto.
  Qed.

  Lemma store_preserves_related: forall n c a v initialH initialL postH,
      related initialH initialL ->
      store n c a v initialH postH ->
      store n c a v initialL
            (fun finalL => exists finalH, related finalH finalL /\ postH finalH).
  Proof.
    unfold store.
    cbn. intros.
    destruct_one_match_hyp. 2: contradiction.
    (* TODO separation logic/memory stuff *)
  Admitted.

  Lemma run_primitive_preserves_related: forall a initialH initialL postH,
      related initialH initialL ->
      run_primitive a initialH postH (fun _ => False) ->
      run_primitive a initialL
                    (fun res finalL => exists finalH, related finalH finalL /\ postH res finalH)
                    (fun _ => False).
  Proof.
    intros. pose proof H as R.
    unfold related in H|-*.
    simp.
    destruct a; cbn [run_primitive] in *.
    - exists initialH. intuition (congruence || eauto 10).
    - exists initialH(#"regs" := setReg initialH#"regs" z r). record.simp. intuition (congruence || eauto 10).
    - eapply load_preserves_related; eauto.
    - eapply load_preserves_related; eauto.
    - eapply load_preserves_related; eauto.
    - eapply load_preserves_related; eauto.
    - eapply store_preserves_related; eauto.
    - eapply store_preserves_related; eauto.
    - eapply store_preserves_related; eauto.
    - eapply store_preserves_related; eauto.
    - contradiction.
    - contradiction.
    - contradiction.
    - simp. rewrite Hp4 in E. rewrite map.get_empty in E. discriminate E.
    - simp. rewrite Hp4 in E. rewrite map.get_empty in E. discriminate E.
    - eauto 10.
    - simp. eauto 10.
    - simp. eauto 10.
    - exists initialH.
      intuition (congruence || eauto 10).
    - eexists. ssplit; cycle -1. 1: eassumption. all: record.simp; try congruence. eauto 10.
    - eexists. unfold updatePc in *. ssplit; cycle -1. 1: eassumption.
      all: record.simp; try congruence. eauto 10.
    - contradiction.
  Qed.

  (* If we're running the same primitives on two related states, they remain related.
     (Note: decoding using RV32I vs RV32IM does not result in the same primitives). *)
  Lemma mcomp_sat_preserves_related: forall m initialL initialH postH,
      related initialH initialL ->
      mcomp_sat m initialH postH ->
      mcomp_sat m initialL (fun finalL => exists finalH, related finalH finalL /\ postH finalH).
  Proof.
    induction m; intros. 2: {
      eapply weaken_mcomp_sat. 2: eassumption. eauto.
    }
    unfold mcomp_sat in *.
    cbn in *.
    eapply weaken_run_primitive with (postA1 := fun _ => False). 3: {
      eapply run_primitive_preserves_related; eassumption.
    }
    2: auto.
    cbn.
    intros. simp.
    eapply H. 1: eassumption.
    eassumption.
  Qed.

(*
  Lemma go_exception: forall iset initial post R,
      R \*/
      runsTo (mcomp_sat (run1 iset)) initial(#"pc" := ini post.
      runsTo (mcomp_sat (run1 iset)) initial post.
*)

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
    pose proof H2 as Rel.
    unfold related in H2.
    eapply invert_fetch in H. simp.
    rename initial into initialH.
    rewrite <- Hp0 in H2p5p3.
    pose proof (proj2 Hp1) as V.
    destruct i as [inst|inst|inst|inst|inst|inst|inst|inst|inst|inst] eqn: E;
      cbn in V; try (intuition congruence).
    - (* IInstruction *)
      subst.
      eapply runsToStep with (midset0 := fun midL => exists midH, related midH midL /\ midset midH).
      + eapply build_fetch with (i := (IInstruction inst)).
        { replace RV32I with RV32IM by case TODO. assumption. }
        {
          etransitivity. 2: exact H2p5p3.
          reify_goal.
          cancel_at 1%nat 1%nat. 1: congruence.
          cbn [mmap.dus].
          reflexivity.
        }
        eapply mcomp_sat_preserves_related; eassumption.
      + intros midL. intros. simp. eapply H1; eassumption.
    - (* MInstruction *)
      destruct inst.
      + (* Mul *)
        cbn in Hp2.

        case TODO.

      + (* Mulh *)
        case TODO.
      + (* Mulhsu *)
        case TODO.
      + (* Mulhu *)
        case TODO.
      + (* Div *)
        case TODO.
      + (* Divu *)
        case TODO.
      + (* Rem *)
        case TODO.
      + (* Remu *)
        case TODO.
      + (* InvalidM *)
        case TODO.
    - (* CSRInstruction *)
      subst.
      eapply runsToStep with (midset0 := fun midL => exists midH, related midH midL /\ midset midH).
      + eapply build_fetch with (i := (CSRInstruction inst)).
        { replace RV32I with RV32IM by case TODO. assumption. }
        {
          etransitivity. 2: exact H2p5p3.
          reify_goal.
          cancel_at 1%nat 1%nat. 1: congruence.
          cbn [mmap.dus].
          reflexivity.
        }
        eapply mcomp_sat_preserves_related; eassumption.
      + intros midL. intros. simp. eapply H1; eassumption.
  Qed.

End Riscv.
