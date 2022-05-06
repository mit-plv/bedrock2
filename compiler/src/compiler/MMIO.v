Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Macros.unique.
Require Import compiler.util.Common.
Require Import bedrock2.Semantics.
Require Import riscv.Utility.Monads.
Require Import compiler.FlatImp.
Require Import riscv.Spec.Decode.
Require Import coqutil.sanity.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Spec.Machine.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscvFunctions.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MinimalMMIO.
Require Import riscv.Platform.MetricMinimalMMIO.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.MetricPrimitives.
Require Import compiler.MetricsToRiscv.
Require Import compiler.FlatToRiscvDef.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.SeparationLogic.
Require Import coqutil.Datatypes.Option.
Require Import coqutil.Tactics.Simp.
Require Import compiler.util.Learning.
Require Export coqutil.Word.SimplWordExpr.
Require Import compiler.RiscvWordProperties.
Require Import riscv.Platform.FE310ExtSpec.
Require Import coqutil.Z.div_mod_to_equations.
Require Import coqutil.Datatypes.ListSet.
Require bedrock2.FE310CSemantics.
Import ListNotations.

Open Scope ilist_scope.

Definition compile_interact(results: list Z) a (args: list Z):
  list Instruction :=
  if String.eqb "MMIOWRITE" a then
    match results, args with
    | [], [addr; val] => [[ Sw addr val 0 ]]
    | _, _ => [[]] (* invalid, excluded by ext_spec *)
    end
  else
    match results, args with
    | [res], [addr] => [[ Lw res addr 0 ]]
    | _, _ => [[]] (* invalid, excluded by ext_spec *)
    end.

Lemma compile_interact_length: forall binds f args,
    Z.of_nat (List.length (compile_interact binds f args)) <= 1.
Proof.
  intros. unfold compile_interact.
  destruct (String.eqb _ _); destruct binds; try destruct binds;
  try destruct args; try destruct args; try destruct args;
  cbv; intros; discriminate.
Qed.

Lemma compile_interact_length': forall binds f args,
    Z.of_nat (List.length (compile_interact binds f args)) <= 7.
Proof. intros. rewrite compile_interact_length. blia. Qed.

Lemma compile_interact_emits_valid: forall iset binds a args,
    Forall valid_FlatImp_var binds ->
    Forall valid_FlatImp_var args ->
    valid_instructions iset (compile_interact binds a args).
Proof.
  intros.
  unfold compile_interact.
  destruct (String.eqb _ _); destruct args; try destruct args; try destruct args;
    destruct binds; try destruct binds;
    intros instr HIn; cbn -[String.eqb] in *; intuition idtac; try contradiction.
  - rewrite <- H1.
    simp_step.
    simp_step.
    (* try simp_step. (* TODO this should not fail fatally *) *)
    split; [|cbv;auto].
    unfold Encode.respects_bounds. simpl.
    unfold Encode.verify_S, valid_FlatImp_var, opcode_STORE, funct3_SW in *.
    repeat split; (blia || assumption).
  - rewrite <- H1.
    simp_step.
    simp_step.
    simp_step.
    simp_step.
    (* try simp_step. (* TODO this should not fail fatally *) *)
    split; [|cbv;auto].
    unfold Encode.respects_bounds. simpl.
    unfold Encode.verify_I, valid_FlatImp_var, opcode_LOAD, funct3_LW in *.
    repeat split; (blia || assumption).
Qed.

Global Instance RV32I_bitwidth: FlatToRiscvCommon.bitwidth_iset 32 RV32I.
Proof. reflexivity. Qed.

Local Arguments Z.mul: simpl never.
Local Arguments Z.add: simpl never.
Local Arguments Z.of_nat: simpl never.
Local Arguments Z.modulo : simpl never.
Local Arguments Z.pow: simpl never.
Local Arguments Z.sub: simpl never.
Local Arguments Registers.reg_class.all: simpl never.

Section MMIO1.
  Context {word: Word.Interface.word 32}.
  Context {word_ok: word.ok word}.
  Context {word_riscv_ok: word.riscv_ok word}.
  Context {mem: map.map word byte}.
  Context {mem_ok: map.ok mem}.
  Context {locals: map.map Z word}.
  Context {locals_ok: map.ok locals}.
  Context {funname_env: forall T, map.map String.string T}.
  Context {funname_env_ok: forall T, map.ok (funname_env T)}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Definition compile_ext_call(_: funname_env Z)(_ _: Z)(s: stmt Z) :=
      match s with
      | SInteract resvars action argvars => compile_interact resvars action argvars
      | _ => []
      end.

  Section CompilationTest.
    Definition magicMMIOAddrLit: Z := 0x10024000.
    Variable addr: Z.
    Variable i: Z.
    Variable s: Z.

    (*
    addr = magicMMIOAddr;
    loop {
      i = input addr;
      stay in loop only if i is non-zero;
      s = i _ i;
      output addr s;
    }
    *)
    Definition doubler: stmt Z :=
      (SSeq (SLit addr magicMMIOAddrLit)
            (SLoop (SLoad Syntax.access_size.four i addr 0)
                   (CondNez i)
                   (SSeq (SOp s Syntax.bopname.add i i)
                         (SStore Syntax.access_size.four addr s 0)))).

    Definition compiled: list Instruction :=
      Eval cbv in compile_stmt RV32I compile_ext_call map.empty 0 0 doubler.
    Goal True.
      let c := eval cbv in compiled in pose c.
    Abort.
  End CompilationTest.

  Lemma load4bytes_in_MMIO_is_None: forall (m: mem) (addr: word),
      map.undef_on m isMMIOAddr ->
      isMMIOAddr addr ->
      Memory.load_bytes 4 m addr = None.
  Proof.
    intros. unfold Memory.load_bytes, map.undef_on, map.agree_on, map.getmany_of_tuple in *.
    simpl.
    rewrite H by assumption.
    rewrite map.get_empty.
    reflexivity.
  Qed.

  Lemma loadWord_in_MMIO_is_None: forall (m: mem) (addr: word),
      map.undef_on m isMMIOAddr ->
      isMMIOAddr addr ->
      Memory.loadWord m addr = None.
  Proof.
    intros. unfold Memory.loadWord.
    apply load4bytes_in_MMIO_is_None; assumption.
  Qed.

  Lemma storeWord_in_MMIO_is_None: forall (m: mem) (addr: word) v,
      map.undef_on m isMMIOAddr ->
      isMMIOAddr addr ->
      Memory.storeWord m addr v = None.
  Proof.
    unfold Memory.storeWord. intros. unfold Memory.store_bytes.
    rewrite load4bytes_in_MMIO_is_None; auto.
  Qed.

  Ltac contrad := contradiction || discriminate || congruence.

  (* TODO: why are these here? *)
  Arguments LittleEndian.combine: simpl never. (* TODO can we put this next to its definition? *)
  Arguments mcomp_sat: simpl never.
  Arguments LittleEndian.split: simpl never.
  Local Arguments String.eqb: simpl never.

  Ltac fwd :=
    match goal with
    |- free.interp interp_action ?p ?s ?post =>
      let p' := eval hnf in p in
      change (free.interp interp_action p' s post);
      rewrite free.interp_act;
      cbn [interp_action MinimalMMIO.interpret_action snd fst];
        simpl_MetricRiscvMachine_get_set
    | |- load ?n ?ctx ?a ?s ?k =>
        let g' := eval cbv beta delta [load] in (load n ctx a s k) in
        change g';
        simpl_MetricRiscvMachine_get_set
    | _ => progress cbn [free.bind]
    | |- store ?n ?ctx ?a ?v ?s ?k =>
        let g' := eval cbv beta delta [store] in (store n ctx a v s k) in
        change g';
        simpl_MetricRiscvMachine_get_set
    | _ => progress cbn [free.bind]
    | _ => rewrite free.interp_ret
    end.

  Lemma disjoint_MMIO_goal: forall (x y: word),
      isMMIOAddr x ->
      ~ isMMIOAddr y ->
      word.unsigned x mod 4 = 0 ->
      word.add (word.add (word.add x (word.of_Z 1)) (word.of_Z 1)) (word.of_Z 1) <> y /\
      word.add (word.add x (word.of_Z 1)) (word.of_Z 1) <> y /\
      word.add x (word.of_Z 1) <> y /\
      x <> y.
  Proof.
    intros.
    unfold isMMIOAddr, FE310_mmio, isOTP,isPRCI, isGPIO0, isUART0, isSPI1 in *.
    simpl in *.
    ssplit.
    all: intro C.
    1: replace x with (word.sub y (word.of_Z 3)) in * by (subst y; solve_word_eq word_ok).
    2: replace x with (word.sub y (word.of_Z 2)) in * by (subst y; solve_word_eq word_ok).
    3: replace x with (word.sub y (word.of_Z 1)) in * by (subst y; solve_word_eq word_ok).
    4: replace x with y in * by assumption.
    all: clear C;
      rewrite ?word.unsigned_sub, ?word.unsigned_of_Z in H, H1;
      unfold word.wrap in *;
      pose proof (word.unsigned_range y);
      forget (word.unsigned y) as Y; clear x y;
      let r := eval cbv in (2 ^ 32) in change (2 ^ 32) with r in *;
      Z.div_mod_to_equations;
      (* COQBUG (performance) https://github.com/coq/coq/issues/10743,
         workaround by @thery *)
      repeat match goal with
             | [ H : ?x -> _, H' : ?x -> _ |- _ ] =>
               pose proof (fun u : x => conj (H u) (H' u)); clear H H'
             end.
    all: time blia.
  Time Qed.

  Lemma compile_ext_call_correct: forall resvars extcall argvars,
      FlatToRiscvCommon.compiles_FlatToRiscv_correctly compile_ext_call compile_ext_call
        (FlatImp.SInteract resvars extcall argvars).
  Proof.
    unfold FlatToRiscvCommon.compiles_FlatToRiscv_correctly. simpl. intros.
    destruct H5 as (? & ? & V_resvars & V_argvars).
    rename extcall into action.
    pose proof (compile_interact_emits_valid RV32I _ action _ V_resvars V_argvars).
    simp.
    destruct_RiscvMachine initialL.
    unfold FlatToRiscvCommon.goodMachine in *.
    match goal with
    | H: forall _ _, outcome _ _ -> _ |- _ => specialize H with (mReceive := map.empty)
    end.
    destruct (String.eqb "MMIOWRITE" action) eqn: E;
      cbn [getRegs getPc getNextPc getMem getLog getMachine getMetrics getXAddrs] in *.
    + (* MMOutput *)
      progress simpl in *|-.
      match goal with
      | H: FE310CSemantics.ext_spec _ _ _ _ _ |- _ => rename H into Ex
      end.
      unfold compile_interact in *.
      cbv [FE310CSemantics.ext_spec] in Ex.
      rewrite E in *.
      destruct Ex as (?&?&?&(?&?&?)&?). subst mGive argvals.
      repeat match goal with
             | H: _ /\ _ |- _ => destruct H
             | H: exists x, _ |- _ => let x' := fresh x in destruct H as [x' H]
             end.
      destruct argvars. {
        exfalso.
        match goal with
        | A: map.getmany_of_list _ ?L1 = Some ?L2 |- _ =>
          clear -A; cbn in *; congruence
        end.
      }
      destruct argvars. {
        exfalso.
        match goal with
        | A: map.getmany_of_list _ ?L1 = Some ?L2 |- _ =>
          clear -A; cbn in *; destruct_one_match_hyp; congruence
        end.
      }
      destruct argvars; cycle 1. {
        exfalso.
        match goal with
        | A: map.getmany_of_list _ ?L1 = Some ?L2 |- _ =>
          clear -A; cbn in *; simp; destruct_one_match_hyp; congruence
        end.
      }
      cbn in *|-.
      match goal with
      | H: map.split _ _ map.empty |- _ => rewrite map.split_empty_r in H; subst
      end.
      match goal with
      | HO: outcome _ _, H: _ |- _ => specialize (H _ HO); rename H into HP
      end.
      destruct g. FlatToRiscvCommon.simpl_g_get.
      simp.
      subst.
      cbn in *.
      simp.
      eapply runsToNonDet.runsToStep_cps.
      match goal with
      | H: iff1 allx _ |- _ => apply iff1ToEq in H; subst allx
      end.

      split; simpl_MetricRiscvMachine_get_set. {
        intros _.
        eapply ptsto_instr_subset_to_isXAddr4.
        eapply shrink_footpr_subset. 1: eassumption.
        cbn in *. wwcancel.
      }

      erewrite ptsto_bytes.load_bytes_of_sep; cycle 1.
      { cbv [program ptsto_instr Scalars.truncated_scalar Scalars.littleendian] in *.
        cbn [array bytes_per] in *.
        simpl_MetricRiscvMachine_get_set.
        wcancel_assumption. }
      change (@Bind _ _) with (@free.bind MetricMinimalMMIO.action result) in *.
      unfold free.bind at 1.

      rewrite <-LittleEndian.split_eq, LittleEndian.combine_split.
      rewrite Z.mod_small by eapply EncodeBound.encode_range.
      rewrite DecodeEncode.decode_encode; cycle 1. {
        unfold valid_instructions in *. cbn in *. eauto.
      }
      repeat fwd.

      unfold getReg.
      destr ((0 <? z1) && (z1 <? 32))%bool; cbv [valid_FlatImp_var] in *; [|exfalso; blia].
      destr ((0 <? z2) && (z2 <? 32))%bool; cbv [valid_FlatImp_var] in *; [|exfalso; blia].
      replace (map.get initialL_regs z1) with (Some x) by (symmetry; unfold map.extends in *; eauto).
      replace (map.get initialL_regs z2) with (Some x0) by (symmetry; unfold map.extends in *; eauto).

      cbv [Utility.add Utility.ZToReg MachineWidth_XLEN]; rewrite add_0_r.
      unshelve erewrite (_ : _ = None); [eapply storeWord_in_MMIO_is_None; eauto|].

      cbv [MinimalMMIO.nonmem_store FE310_mmio].
      split; [trivial|].
      split; [red; auto|].

      repeat fwd.

      eapply runsToNonDet.runsToDone.
      simpl_MetricRiscvMachine_get_set.
      simpl_word_exprs word_ok.
      unfold mmioStoreEvent, signedByteTupleToReg in *.
      unfold regToInt32.
      rewrite LittleEndian.combine_split.
      rewrite sextend_width_nop by reflexivity.
      rewrite Z.mod_small by apply word.unsigned_range.
      rewrite word.of_Z_unsigned.
      apply eqb_eq in E. subst action.
      cbn -[invalidateWrittenXAddrs] in *.
      specialize (HPp1 mKeep). rewrite map.split_empty_r in HPp1. specialize (HPp1 eq_refl).
      do 4 eexists.
      split; eauto.
      split; eauto.
      split; [unfold map.only_differ; eauto|].
      split. {
        unfold id. MetricsToRiscv.solve_MetricLog.
      }
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split; eauto.
      split. {
        lazymatch goal with
        | H: map.undef_on initialL_mem ?A |- _ =>
          rename H into U; change (map.undef_on initialL_mem isMMIOAddr) in U; move U at bottom
        end.
        lazymatch goal with
        | H: disjoint (of_list initialL_xaddrs) ?A |- _ =>
          rename H into D; change (disjoint (of_list initialL_xaddrs) isMMIOAddr) in D;
            move D at bottom
        end.
        lazymatch goal with
        | H: FE310CSemantics.isMMIOAddr x |- _ =>
          rename H into M0; change (isMMIOAddr x) in M0; move M0 at bottom
        end.
        lazymatch goal with
        | H: word.unsigned x mod 4 = 0 |- _ => rename H into D4; move D4 at bottom
        end.
        assert (forall {T: Type} (a b c: set T), subset a b -> subset b c -> subset a c)
          as subset_trans. {
          clear. unfold subset, PropSet.elem_of. intros. firstorder idtac.
        }
        eapply subset_trans. 1: eassumption.
        clear -D4 M0 D word_ok.
        unfold invalidateWrittenXAddrs.
        change removeXAddr with (@List.removeb word word.eqb).
        rewrite ?ListSet.of_list_removeb.
        unfold map.undef_on, map.agree_on, disjoint in *.
        unfold subset, diff, singleton_set, of_list, PropSet.elem_of in *.
        intros y HIn.
        specialize (D y). destruct D; [contradiction|].
        rewrite ?and_assoc.
        split; [exact HIn|clear HIn].
        eapply disjoint_MMIO_goal; assumption.
      }
      ssplit; eauto.
      unfold invalidateWrittenXAddrs.
      change removeXAddr with (@List.removeb word word.eqb).
      rewrite ?ListSet.of_list_removeb.
      repeat apply disjoint_diff_l.
      assumption.

    + (* MMInput *)
      simpl in *|-.
      match goal with
      | H: FE310CSemantics.ext_spec _ _ _ _ _ |- _ => rename H into Ex
      end.
      unfold compile_interact in *.
      cbv [FE310CSemantics.ext_spec] in Ex.
      simpl in *|-.

      rewrite E in *.
      destruct ("MMIOREAD" =? action)%string eqn:EE in Ex; try contradiction.
      destruct Ex as (?&?&(?&?&?)&?). subst mGive argvals.
      repeat match goal with
             | l: list _ |- _ => destruct l;
                                   try (exfalso; (contrad || (cheap_saturate; contrad))); []
             end.
      destruct argvars; cycle 1. {
        exfalso.
        match goal with
        | A: map.getmany_of_list _ ?L1 = Some ?L2 |- _ =>
          clear -A; cbn in *; simp; destruct_one_match_hyp; congruence
        end.
      }
      cbn in *|-.
      match goal with
      | H: map.split _ _ map.empty |- _ => rewrite map.split_empty_r in H; subst
      end.
      destruct g. FlatToRiscvCommon.simpl_g_get.
      simp.
      subst.
      cbn in *.
      eapply runsToNonDet.runsToStep_cps.
      match goal with
      | H: iff1 allx _ |- _ => apply iff1ToEq in H; subst allx
      end.

      split; simpl_MetricRiscvMachine_get_set. {
        intros _.
        eapply ptsto_instr_subset_to_isXAddr4.
        eapply shrink_footpr_subset. 1: eassumption.
        unfold program.
        cbn in *. wwcancel.
      }
      erewrite ptsto_bytes.load_bytes_of_sep; cycle 1.
      { cbv [program ptsto_instr Scalars.truncated_scalar Scalars.littleendian] in *.
        cbn [array bytes_per] in *.
        simpl_MetricRiscvMachine_get_set.
        wcancel_assumption. }

      change (@Bind _ _) with (@free.bind MetricMinimalMMIO.action result) in *.
      unfold free.bind at 1.

      rewrite <-LittleEndian.split_eq, LittleEndian.combine_split.
      rewrite Z.mod_small by (eapply EncodeBound.encode_range).
      rewrite DecodeEncode.decode_encode; cycle 1. {
        unfold valid_instructions in *. cbn in *. eauto.
      }

      repeat fwd.

      unfold getReg.
      destr ((0 <? z1) && (z1 <? 32))%bool; cbv [valid_FlatImp_var] in *; [|exfalso; blia].
      replace (map.get initialL_regs z1) with (Some x) by (symmetry; unfold map.extends in *; eauto).

      split; try discriminate.
      cbv [Utility.add Utility.ZToReg MachineWidth_XLEN]; rewrite add_0_r.
      unshelve erewrite (_ : _ = None); [eapply loadWord_in_MMIO_is_None|]; eauto.

      cbv [MinimalMMIO.nonmem_load FE310_mmio].
      split; [trivial|].
      split; [red; auto|].
      split; [ cbv [MMIOReadOK];
               exists (LittleEndian.split 4 0); trivial |].
      intros.

      repeat fwd.

      eapply runsToNonDet.runsToDone.
      simpl_MetricRiscvMachine_get_set.
      simpl_word_exprs word_ok.

      unfold mmioLoadEvent, signedByteTupleToReg.
      match goal with
      | A: forall _, outcome _ _ -> _, OC: forall _, outcome _ _ |- _ =>
         epose proof (A (cons _ nil) (OC _)) as P; clear A
      end.
      cbn in P.
      simp.
      apply eqb_eq in EE. subst action.
      cbn in *.
      specialize (Pp1 mKeep). rewrite map.split_empty_r in Pp1. specialize (Pp1 eq_refl).
      unfold setReg.
      destr ((0 <? z1) && (z1 <? 32))%bool; [|exfalso;blia].
      do 4 eexists.
      split; eauto.
      split; eauto.
      split. {
        unfold map.only_differ. intros. unfold union, of_list, elem_of, singleton_set. simpl.
        rewrite map.get_put_dec.
        destruct_one_match; auto.
      }
      split. {
        unfold id. MetricsToRiscv.solve_MetricLog.
      }
      split. {
        eapply map.put_extends. eassumption.
      }
      split. {
        unfold map.forall_keys in *.
        intros.
        lazymatch goal with
        | H : context [map.get _ ?x] |- _ <= ?x < _ =>
          rewrite map.get_put_dec in H
        end.
        destruct_one_match_hyp. 1: blia. eauto.
      }
      split. {
        rewrite map.get_put_diff; eauto. unfold RegisterNames.sp. blia.
      }
      split. {
        eapply @regs_initialized.preserve_regs_initialized_after_put.
        2: eassumption.
        typeclasses eauto.
      }
      eauto 10.
  Time Qed. (* takes ~30s *)

End MMIO1.
