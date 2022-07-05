Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.Utility.
Require Import coqutil.Word.LittleEndian.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.Machine.
Require riscv.Platform.Memory.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Proofs.EncodeBound.
Require Import riscv.Proofs.DecodeEncode.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.Monads. Import MonadNotations.
Require Import riscv.Utility.runsToNonDet.
Require Import coqutil.Datatypes.PropSet.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Spec.MetricPrimitives.
Require Import compiler.RunInstruction.
Require Import compiler.RiscvEventLoop.
Require Import compiler.ForeverSafe.
Require Import compiler.GoFlatToRiscv.
Require Import coqutil.Tactics.Simp.
Require Import processor.KamiWord.
Require Import processor.KamiRiscvStep.
Require Import processor.KamiRiscv.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import compiler.Pipeline.
Require Import compilerExamples.MMIO.
Require Import riscv.Platform.FE310ExtSpec.
Require Import compiler.FlatToRiscvDef.
Require Import coqutil.Tactics.rdelta.
Require Import end2end.KamiRiscvWordProperties.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import compiler.SeparationLogic.
Require Import compiler.ToplevelLoop.
Require Import compiler.CompilerInvariant.
Require Import compiler.ExprImpEventLoopSpec.

Local Open Scope Z_scope.

Require Import Coq.Classes.Morphisms.

#[global] Instance word_riscv_ok: @RiscvWordProperties.word.riscv_ok 32 KamiWord.wordW.
refine (@KamiRiscvWordProperties.kami_word_riscv_ok 5 _ _).
all: cbv; congruence.
Qed.

#[global] Existing Instance SortedListString.map.
#[global] Existing Instance SortedListString.ok.

(* TODO these definitions should be in KamiRiscv.v: *)

Definition get_kamiMemInit{memSizeLg: Z}
  (memInit: Syntax.Vec (Syntax.ConstT (Syntax.Bit MemTypes.BitsPerByte)) (Z.to_nat memSizeLg))
  (n: nat): Byte.byte :=
  byte.of_Z (Kami.Lib.Word.uwordToZ
               (Kami.Semantics.evalConstT (kamiMemInit _ memInit) (Kami.Lib.Word.natToWord _ n))).

Definition kami_mem_contains_bytes(bs: list Coq.Init.Byte.byte){memSizeLg}(from: KamiWord.word 32)
           (mem: Syntax.Vec (Syntax.ConstT (Syntax.Bit MemTypes.BitsPerByte)) (Z.to_nat memSizeLg)): Prop :=
  List.map (get_kamiMemInit mem) (seq 0 (List.length bs)) = bs.

Section Connect.

  Context (instrMemSizeLg memSizeLg stack_size_in_bytes: Z).

  Context {Registers: map.map Register (KamiWord.word 32)}
          {Registers_ok: map.ok Registers}
          {mem: map.map (KamiWord.word 32) byte}
          {mem_ok: map.ok mem}.

  Let instrMemSizeBytes: Z := 2 ^ (2 + instrMemSizeLg).

  Definition ml: MemoryLayout (width := 32) := {|
    code_start := word.of_Z 0;
    code_pastend := word.of_Z instrMemSizeBytes;
    heap_start := word.of_Z instrMemSizeBytes;
    heap_pastend := word.of_Z (2 ^ memSizeLg - stack_size_in_bytes);
    stack_start := word.of_Z (2 ^ memSizeLg - stack_size_in_bytes);
    stack_pastend := word.of_Z (2 ^ memSizeLg);
  |}.

  Context (memInit: Syntax.Vec (Syntax.ConstT (Syntax.Bit MemTypes.BitsPerByte))
                               (Z.to_nat memSizeLg)).

  Hypotheses (instrMemSizeLg_bounds: 3 <= instrMemSizeLg <= 30)
             (Hkmem: 2 + instrMemSizeLg < memSizeLg <= 16).

  Lemma memSizeLg_width_trivial: memSizeLg <= 32. Proof. blia. Qed.

  Definition p4mm: Kami.Syntax.Modules :=
    KamiRiscv.p4mm instrMemSizeLg memSizeLg (proj1 instrMemSizeLg_bounds)
                   (proj2 instrMemSizeLg_bounds)
                   memInit.

  Add Ring wring : (word.ring_theory (word := Consistency.word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := Consistency.word)),
       constants [word_cst]).

  Goal True.
  epose (_ : PrimitivesParams (FreeMonad.free MetricMinimalMMIO.action MetricMinimalMMIO.result)
                              MetricRiscvMachine).
  Abort.

  Existing Instance MetricMinimalMMIO.MetricMinimalMMIOSatisfiesPrimitives.

  Definition states_related :=
    states_related instrMemSizeLg memSizeLg (proj1 instrMemSizeLg_bounds) (proj2 instrMemSizeLg_bounds).

  Lemma split_ll_trace: forall {t2' t1' t},
      traces_related t (t2' ++ t1') ->
      exists t1 t2, t = t2 ++ t1 /\ traces_related t1 t1' /\ traces_related t2 t2'.
  Proof.
    induction t2'; intros.
    - exists t, nil. simpl in *. repeat constructor. assumption.
    - simpl in H. simp. specialize IHt2' with (1 := H4).
      destruct IHt2' as (t1 & t2 & E & R1 & R2). subst.
      exists t1. exists (e :: t2). simpl. repeat constructor; assumption.
  Qed.

  Lemma states_related_to_traces_related: forall m m' t,
      states_related (m, t) m' -> traces_related t m'.(getLog).
  Proof. intros. inversion H. simpl. assumption. Qed.

  (* for debugging f_equal *)
  Lemma cong_app: forall {A B: Type} (f f': A -> B) (a a': A),
      f = f' ->
      a = a' ->
      f a = f' a'.
  Proof. intros. congruence. Qed.

  Context (spec: ProgramSpec)
          (funimplsList: list (string * (list string * list string * cmd))).

  Hypothesis heap_start_agree: spec.(datamem_start) = ml.(heap_start).
  Hypothesis heap_pastend_agree: spec.(datamem_pastend) = ml.(heap_pastend).
  Hypothesis stack_size_div: stack_size_in_bytes mod bytes_per_word = 0.
  Hypothesis stack_size_bounds: 0 <= stack_size_in_bytes <= 2 ^ memSizeLg - instrMemSizeBytes.

  Lemma mlOk: MemoryLayoutOk ml.
  Proof.
    constructor;
      unfold ml, code_start, code_pastend, heap_start, heap_pastend, stack_start, stack_pastend.
    - reflexivity.
    - rewrite word.unsigned_of_Z.
      unfold word.wrap.
      etransitivity.
      1: exact (ToplevelLoop.mod_2width_mod_bytes_per_word (2 ^ memSizeLg - stack_size_in_bytes)).
      change bytes_per_word with 4.
      apply mod4_0.mod4_0_sub.
      + replace memSizeLg with (memSizeLg - 2 + 2) by blia.
        rewrite Z.pow_add_r by blia.
        apply mod4_0.mod4_mul4_r.
      + exact stack_size_div.
    - rewrite word.unsigned_of_Z.
      unfold word.wrap.
      etransitivity.
      1: exact (ToplevelLoop.mod_2width_mod_bytes_per_word (2 ^ memSizeLg)).
      replace memSizeLg with (memSizeLg - 2 + 2) by blia.
      rewrite Z.pow_add_r by blia.
      apply mod4_0.mod4_mul4_r.
    - rewrite word.unsigned_of_Z. change (word.wrap 0) with 0.
      eapply proj1. eapply word.unsigned_range.
    - reflexivity.
    - rewrite ?word.unsigned_of_Z. unfold word.wrap.
      pose proof (Z.pow_nonneg 2 (2 + instrMemSizeLg)).
      change width with 32 in *.
      assert (2 ^ memSizeLg < 2 ^ 32). {
        apply Z.pow_lt_mono_r; blia.
      }
      rewrite ?Z.mod_small; try split; try apply Z.pow_nonneg; try blia.
    - reflexivity.
    - rewrite ?word.unsigned_of_Z. unfold word.wrap.
      pose proof (Z.pow_nonneg 2 (2 + instrMemSizeLg)).
      change width with 32 in *.
      assert (2 ^ memSizeLg < 2 ^ 32). {
        apply Z.pow_lt_mono_r; blia.
      }
      rewrite ?Z.mod_small; try split; try apply Z.pow_nonneg; try blia.
  Qed.

  Hypothesis funimplsList_NoDup: NoDup (List.map fst funimplsList).

  (* goodTrace in terms of "exchange format" (list Event).
     Only holds at the beginning/end of each loop iteration,
     will be transformed into "exists suffix, ..." form later *)
  Definition goodTraceE(t: list Event): Prop :=
    exists bedrockTrace, traces_related t bedrockTrace /\ spec.(goodTrace) bedrockTrace.

  Definition bedrock2Inv := (fun t m l => forall mc, hl_inv spec t m l mc).

  Let funspecs := WeakestPrecondition.call funimplsList.

  Hypothesis goodTrace_implies_related_to_Events: forall (t: list LogItem),
      spec.(goodTrace) t -> exists t': list Event, traces_related t' t.

  Definition riscvMemInit_all_values: list byte :=
    List.map (get_kamiMemInit memInit) (seq 0 (Z.to_nat (2 ^ memSizeLg))).

  Definition riscvMemInit_values(from len: nat): list byte :=
    List.firstn len (List.skipn from riscvMemInit_all_values).

  Lemma riscvMemInit_to_seplog_aux: forall len from,
      Z.of_nat from + Z.of_nat len <= 2 ^ memSizeLg ->
      LowerPipeline.ptsto_bytes
        (word.of_Z (width := width) (Z.of_nat from))
        (map (get_kamiMemInit memInit) (seq from len))
        (map.of_list (map
          (fun i => (word.of_Z (BinIntDef.Z.of_nat i),
                     byte.of_Z (Word.uwordToZ (Semantics.evalConstT (kamiMemInit memSizeLg memInit)
                         (Word.natToWord (BinIntDef.Z.to_nat memSizeLg) i)))))
          (seq from len))).
  Proof.
    induction len; intros.
    - cbv. auto.
    - unfold LowerPipeline.ptsto_bytes, riscvMemInit_values in *.
      cbn [seq map array map.of_list].
      match goal with
      | |- context [map.put ?m ?k ?v] => pose proof map.put_putmany_commute k v m map.empty as P
      end.
      rewrite map.putmany_empty_r in P.
      rewrite P. clear P.
      eapply sep_comm.
      unfold sep.
      do 2 eexists.
      ssplit; cycle 1.
      + specialize (IHlen (S from)).
        replace (Z.of_nat (S from)) with (Z.of_nat from + 1) in IHlen by blia.
        rewrite word.ring_morph_add in IHlen.
        apply IHlen. blia.
      + unfold ptsto. reflexivity.
      + unfold map.split, map.disjoint. split; [reflexivity|].
        intros.
        rewrite map.get_put_dec in H1.
        destruct_one_match_hyp. 2: {
          rewrite map.get_empty in H1. discriminate.
        }
        subst.
        rewrite get_of_list_not_In in H0.
        * discriminate.
        * simpl. apply Word.weq.
        * exact mem_ok.
        * intro C.
          rewrite map_map in C.
          unfold fst in C.
          apply in_map_iff in C.
          destruct C as [ from' [E C] ].
          apply (f_equal word.unsigned) in E.
          do 2 rewrite word.unsigned_of_Z in E.
          unfold word.wrap in E.
          change width with 32 in *.
          rewrite (Z.mod_small (Z.of_nat from)) in E. 2: {
            split; [blia|].
            eapply Z.le_lt_trans with (m := 2 ^ memSizeLg). 1: blia.
            eapply Z.pow_lt_mono_r; blia.
          }
          apply in_seq in C.
          rewrite (Z.mod_small (Z.of_nat from')) in E. 2: {
            split; [blia|].
            eapply Z.le_lt_trans with (m := 2 ^ memSizeLg). 1: blia.
            eapply Z.pow_lt_mono_r; blia.
          }
          blia.
  Qed.

  Lemma riscvMemInit_to_seplog:
    (LowerPipeline.ptsto_bytes (word.of_Z 0) riscvMemInit_all_values)
    (riscvMemInit memSizeLg memInit).
  Proof.
    intros.
    unfold riscvMemInit_all_values, riscvMemInit.
    pose proof (riscvMemInit_to_seplog_aux (Z.to_nat (2 ^ memSizeLg)) 0) as P.
    change (Z.of_nat 0) with 0 in *.
    (* TODO could adapt riscvMemInit definition to make this not needed *)
    replace (2 ^ BinIntDef.Z.to_nat memSizeLg)%nat with (Z.to_nat (2 ^ memSizeLg)).
    1: eapply P.
    - rewrite Z2Nat.id. 1: blia.
      apply Z.pow_nonneg. blia.
    - rewrite N_Z_nat_conversions.Z2Nat.inj_pow; try blia. reflexivity.
  Qed.

  (* end to end, but still generic over the program *)
  Lemma end2end:
    (* Assumptions on the program logic level: *)
    forall init_code loop_body,
    map.get (map.of_list funimplsList) "init"%string = Some ([], [], init_code) ->
    (forall m, LowerPipeline.mem_available ml.(heap_start) ml.(heap_pastend) m ->
               WeakestPrecondition.cmd funspecs init_code [] m map.empty bedrock2Inv) ->
    map.get (map.of_list funimplsList) "loop"%string = Some ([], [], loop_body) ->
    (forall t m l, bedrock2Inv t m l ->
                   WeakestPrecondition.cmd funspecs loop_body t m l bedrock2Inv) ->
    (* Assumptions on the compiler level: *)
    forall (instrs: list Instruction) positions (required_stack_space: Z),
    compile_prog compile_ext_call ml (map.of_list funimplsList) = Success (instrs, positions, required_stack_space) ->
    required_stack_space <= word.unsigned (word.sub (stack_pastend ml) (stack_start ml)) / bytes_per_word ->
    word.unsigned (code_start ml) + Z.of_nat (Datatypes.length (instrencode instrs)) <=
      word.unsigned (code_pastend ml) ->
    Forall (fun i : Instruction => verify i iset) instrs ->
    ExprImp.valid_funs (map.of_list funimplsList) ->
    (* Assumptions on the Kami level: *)
    kami_mem_contains_bytes (instrencode instrs) ml.(code_start) memInit ->
    forall (t: Kami.Semantics.LabelSeqT) (mFinal: KamiImplMachine),
      (* IF the 4-stage pipelined processor steps to some final state mFinal, producing trace t,*)
      Kami.Semantics.Behavior p4mm mFinal t ->
      (* THEN the trace produced by the kami implementation can be mapped to an MMIO trace
         (this guarantees that the only external behavior of the kami implementation is MMIO)
         and moreover, this MMIO trace satisfies "not yet bad", as in, there exists at
         least one way to complete it to a good trace *)
      exists (t': list Event), KamiLabelSeqR t t' /\
                               exists (suffix: list Event), goodTraceE (suffix ++ t').
  Proof.
    intros *. intros GetInit Establish GetLoop Preserve. intros *. intros C RS L F V M. intros *. intros B.

    set (traceProp := fun (t: list Event) =>
                        exists (suffix: list Event), goodTraceE (suffix ++ t)).
    change (exists t' : list Event,
               KamiLabelSeqR t t' /\ traceProp t').

    (* stack of proofs, bottom-up: *)

    (* 1) Kami pipelined processor to riscv-coq *)
    pose proof @riscv_to_kamiImplProcessor as P1.
    specialize_first P1 traceProp.
    specialize_first P1 (ll_inv compile_ext_call ml spec).
    specialize_first P1 B.
    specialize_first P1 (proj1 Hkmem).
    specialize_first P1 memSizeLg_width_trivial.
    specialize_first P1 (proj2 Hkmem).
    (* destruct spec. TODO why "Error: sat is already used." ?? *)

    (* 2) riscv-coq to bedrock2 semantics *)
    pose proof compiler_invariant_proofs compile_ext_call compile_ext_call_correct as P2.
    specialize_first P2 spec.
    specialize_first P2 ml.
    specialize_first P2 mlOk.
    destruct P2 as [ P2establish [P2preserve P2use] ]. {
      intros. reflexivity.
    }
    eapply P1; clear P1.
    - assumption.
    - assumption.
    - (* establish *)
      intros.
      eapply P2establish.
      unfold initial_conditions.
      exists (map.of_list funimplsList), instrs, positions, required_stack_space.
      destr_RiscvMachine m0RV.
      subst.
      ssplit.
      + (* 3) bedrock2 semantics to bedrock2 program logic *)
        econstructor.
        * exact V.
        * exact GetInit.
        * intros.
          eapply ExprImp.weaken_exec.
          -- match goal with
             | H: LowerPipeline.mem_available ?from ?to _ |- _ =>
               rewrite heap_start_agree in H;
               rewrite heap_pastend_agree in H
             end.
             refine (WeakestPreconditionProperties.sound_cmd _ _ _ _ _ _ _ _ _); eauto.
          -- simpl. clear. intros. unfold bedrock2Inv in *. eauto.
        * exact GetLoop.
        * intros. unfold bedrock2Inv in *.
          eapply ExprImp.weaken_exec.
          -- refine (WeakestPreconditionProperties.sound_cmd _ _ _ _ _ _ _ _ _); eauto.
          -- simpl. clear. intros. eauto.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
      + pose proof word.eqb_spec.
        cbv [imem LowerPipeline.mem_available].
        unfold code_start, code_pastend, heap_start, heap_pastend, stack_start, stack_pastend, ml in *.
        assert (Bounds_instrs: 0 <= Z.of_nat (Datatypes.length (instrencode instrs))) by blia.
        assert (Bounds_unused_imem: Z.of_nat (Datatypes.length (instrencode instrs)) <= instrMemSizeBytes). {
          move L at bottom.
          rewrite ?word.unsigned_of_Z in L.
          change (word.wrap 0) with 0 in L.
          unfold word.wrap in L.
          rewrite (Z.mod_small instrMemSizeBytes) in L. 1: blia.
          split.
          - apply Z.pow_nonneg. blia.
          - change width with 32. apply Z.pow_lt_mono_r; blia.
        }
        assert (Bounds_heap: instrMemSizeBytes <= 2 ^ memSizeLg - stack_size_in_bytes) by blia.
        assert (Bounds_stack: 2 ^ memSizeLg - stack_size_in_bytes <= 2 ^ memSizeLg) by blia.
        assert (Bounds_unmapped: 2 ^ memSizeLg < 2 ^ width). {
          change width with 32.
          apply Z.pow_lt_mono_r; try blia.
        }
        assert (Datatypes.length riscvMemInit_all_values = Z.to_nat (2 ^ memSizeLg)). {
          unfold riscvMemInit_all_values.
          rewrite map_length. rewrite seq_length.
          blia.
        }
        clear P2establish P2preserve P2use.
        eapply Proper_iff1_iff1; [|reflexivity..|].
        { progress repeat rewrite ?sep_ex1_r, ?sep_ex1_l; reflexivity. }
        eexists ?[stack].
         eapply Proper_iff1_iff1; [|reflexivity..|].
        { progress repeat rewrite ?sep_ex1_r, ?sep_ex1_l; reflexivity. }
        eexists ?[heap].
        eapply Proper_iff1_iff1; [|reflexivity..|].
        { progress repeat rewrite ?sep_ex1_r, ?sep_ex1_l; reflexivity. }
        eexists ?[unused_imem].
        eapply Proper_iff1_iff1; [|reflexivity..|].
        { progress repeat rewrite ?sep_emp_2, ?sep_emp_l, ?sep_emp_r; reflexivity. }
        eapply sep_emp_l; split.
        2: eapply sep_assoc; eapply sep_emp_l; split.
        3: eapply Proper_iff1_iff1; [|reflexivity..|].
        3: { progress repeat rewrite ?sep_assoc, ?sep_emp_2, ?sep_emp_l, ?sep_emp_r; reflexivity. }
        3: eapply sep_emp_l; split.

        all : cycle 3.
        Unshelve. {
          pose proof riscvMemInit_to_seplog as P.
          unfold LowerPipeline.ptsto_bytes in *.
          remember riscvMemInit_all_values as l. symmetry in Heql. pose proof Heql as E.
          (* 1) chop off instructions *)
          rewrite <- (firstn_skipn (Datatypes.length (instrencode instrs)) l) in E. subst l.
          match type of E with
          | _ = _ ++ ?L => remember L as l
          end.
          (* 2) chop off unused instruction memory *)
          rewrite <- (firstn_skipn (Z.to_nat instrMemSizeBytes - Datatypes.length (instrencode instrs))
                                   l) in E. subst l.
          rewrite List.app_assoc in E.
          match type of E with
          | _ = _ ++ ?L => remember L as l
          end.
          (* 3 chop off heap *)
          rewrite <- (firstn_skipn (Z.to_nat (2 ^ memSizeLg - instrMemSizeBytes - stack_size_in_bytes))
                                   l) in E. subst l.
          rewrite List.app_assoc in E.
          rewrite E in P; clear E.
          use_sep_assumption.
          wseplog_pre.
          simpl_addrs.
          unfold code_start, code_pastend, heap_start, heap_pastend, stack_start, stack_pastend, ml.
          replace (firstn (Datatypes.length (instrencode instrs)) riscvMemInit_all_values)
            with (instrencode instrs). 2: {
            unfold riscvMemInit_all_values.
            rewrite List.firstn_map.
            rewrite List.firstn_seq.
            rewrite Nat.min_l by blia.
            symmetry.
            exact M.
          }
          cancel.
          cancel_seps_at_indices 0%nat 0%nat. {
            f_equal.
            ring.
          }
          cancel_seps_at_indices 0%nat 0%nat. {
            f_equal.
            rewrite firstn_length.
            rewrite skipn_length.
            let word_ok := constr:(_ : word.ok _) in simpl_word_exprs word_ok.
            f_equal.
            blia.
          }
          cancel_seps_at_indices 0%nat 0%nat. {
            f_equal.
            rewrite ?firstn_length.
            rewrite ?skipn_length.
            let word_ok := constr:(_ : word.ok _) in simpl_word_exprs word_ok.
            f_equal.
            blia.
          }
          cbn [seps]. reflexivity.
        }
        all: repeat rewrite ?word.unsigned_sub, ?word.unsigned_add,
                            ?firstn_length, ?skipn_length, ?word.unsigned_of_Z;
             unfold word.wrap;
             change width with 32 in *.
        all: try (
          Z.div_mod_to_equations;
          (* COQBUG (performance) https://github.com/coq/coq/issues/10743#issuecomment-530673037
             cond_hyp_factor: *)
          repeat match goal with
                 | H : ?x -> _, H' : ?x -> _ |- _  =>
                   pose proof (fun u : x => conj (H u) (H' u)); clear H H'
                 end;
          blia).
      + change (word.unsigned (code_start ml)) with 0.
        assert (Hend: code_pastend ml = word.of_Z instrMemSizeBytes) by reflexivity.
        setoid_rewrite Hend.
        rewrite word.unsigned_of_Z.
        cbv [word.wrap].
        rewrite Z.mod_small. 2: {
          split.
          - apply Z.pow_nonneg; blia.
          - apply Z.pow_lt_mono_r; blia.
        }
        assumption.
      + reflexivity.
      + reflexivity.
      + unfold regs_initialized.regs_initialized. intros.
        match goal with
        | |- exists _, ?x = Some _ => destr x; [eauto|exfalso]
        end.
        match goal with
        | H: forall _, _ -> _ <> None |- _ => eapply H; eauto
        end.
      + reflexivity.
      + simpl. split.
        * apply @riscv_init_memory_undef_on_MMIO with (instrMemSizeLg:= instrMemSizeLg).
          { apply instrMemSizeLg_bounds. }
          { apply Hkmem. }
          { cbv [KamiProc.width]; blia. }
          { apply Hkmem. }
          { assumption. }
        * assumption.
    - (* preserve *)
      intros.
      refine (P2preserve _ _). assumption.
    - (* use *)
      intros *. intro Inv.
      subst traceProp. simpl.
      specialize_first P2use Inv.
      destruct P2use as [suff Good].
      unfold goodTraceE.
      pose proof (goodTrace_implies_related_to_Events _ Good) as G.
      destruct G as [t' R].
      pose proof (split_ll_trace R). simp.
      eauto 10.
  Qed.

End Connect.
