Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Macros.unique.
Require Import compiler.util.Common.
Require Import bedrock2.Semantics.
Require Import riscv.Utility.Monads.
Require Import coqutil.Map.SortedList.
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
Require Import compiler.Rem4.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.SeparationLogic.
Require Import coqutil.Datatypes.Option.
Require Import coqutil.Z.HexNotation.
Require Import compiler.Simp.
Require Import compiler.util.Learning.
Require Import compiler.SimplWordExpr.
Require Import riscv.Platform.FE310ExtSpec.
Require bedrock2Examples.FE310CompilerDemo.
Import ListNotations.


Open Scope ilist_scope.

Definition varname: Type := Z.
Definition funname: Type := string.

Definition compile_ext_call(results: list varname) a (args: list varname):
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

Lemma compile_ext_call_length: forall binds f args,
    Z.of_nat (List.length (compile_ext_call binds f args)) <= 1.
Proof.
  intros. unfold compile_ext_call.
  destruct (String.eqb _ _); destruct binds; try destruct binds;
  try destruct args; try destruct args; try destruct args;
  cbv; intros; discriminate.
Qed.

Lemma compile_ext_call_length': forall binds f args,
    Z.of_nat (List.length (compile_ext_call binds f args)) <= 7.
Proof. intros. rewrite compile_ext_call_length. blia. Qed.

Lemma compile_ext_call_emits_valid: forall iset binds a args,
    Forall valid_register binds ->
    Forall valid_register args ->
    valid_instructions iset (compile_ext_call binds a args).
Proof.
  intros.
  unfold compile_ext_call.
  destruct (String.eqb _ _); destruct args; try destruct args; try destruct args;
    destruct binds; try destruct binds;
    intros instr HIn; cbn -[String.eqb] in *; intuition idtac; try contradiction.
  - rewrite <- H1.
    simp_step.
    simp_step.
    (* try simp_step. (* TODO this should not fail fatally *) *)
    split; [|cbv;auto].
    unfold Encode.respects_bounds. simpl.
    unfold Encode.verify_S, valid_register, opcode_STORE, funct3_SW in *.
    repeat split; (blia || assumption).
  - rewrite <- H1.
    simp_step.
    simp_step.
    simp_step.
    simp_step.
    (* try simp_step. (* TODO this should not fail fatally *) *)
    split; [|cbv;auto].
    unfold Encode.respects_bounds. simpl.
    unfold Encode.verify_I, valid_register, opcode_LOAD, funct3_LW in *.
    repeat split; (blia || assumption).
Qed.

Instance mmio_syntax_params: Syntax.parameters := {|
  Syntax.varname := varname;
  Syntax.funname := funname;
  Syntax.actname := String.string;
|}.

Module Import MMIO.
  Class parameters := {
    byte :> Word.Interface.word 8;
    byte_ok :> word.ok byte;
    word :> Word.Interface.word 32;
    word_ok :> word.ok word;
    mem :> map.map word byte;
    mem_ok :> map.ok mem;
    locals :> map.map varname word;
    locals_ok :> map.ok locals;
    funname_env: forall T, map.map funname T;
    funname_env_ok :> forall T, map.ok (funname_env T);
  }.
End MMIO.

Section MMIO1.
  Context {p: unique! MMIO.parameters}.

  Local Instance Words32: Utility.Words := {
    Utility.byte := byte;
    Utility.word := word;
    Utility.width_cases := or_introl eq_refl;
  }.

  Local Notation bedrock2_trace := (list (mem * String.string * list word * (mem * list word))).
  Definition bedrock2_interact (t : bedrock2_trace) (mGive : mem) a (args: list word) (post:mem -> list word -> Prop) :=
    mGive = map.empty /\
    if String.eqb "MMIOWRITE" a
    then
      exists addr val,
        args = [addr; val] /\ isMMIOAddr addr /\ word.unsigned addr mod 4 = 0 /\
        post map.empty nil
    else if String.eqb "MMIOREAD" a
    then
      exists addr,
        args = [addr] /\ isMMIOAddr addr /\ word.unsigned addr mod 4 = 0 /\
        forall val, post map.empty [val]
    else False.

  Instance mmio_semantics_params: Semantics.parameters := {|
    Semantics.syntax := mmio_syntax_params;
    Semantics.varname_eqb := Z.eqb;
    Semantics.funname_eqb := String.eqb;
    Semantics.actname_eqb := String.eqb;
    Semantics.width := 32;
    Semantics.ext_spec := bedrock2_interact;
    Semantics.funname_env := funname_env;
  |}.

  Instance compilation_params: FlatToRiscvDef.parameters := {|
    FlatToRiscvDef.compile_ext_call := compile_ext_call;
    FlatToRiscvDef.compile_ext_call_length := compile_ext_call_length';
    FlatToRiscvDef.compile_ext_call_emits_valid := compile_ext_call_emits_valid;
  |}.

  Instance FlatToRiscv_params: FlatToRiscvCommon.FlatToRiscv.parameters := {
    FlatToRiscv.def_params := compilation_params;
    FlatToRiscv.locals := locals;
    FlatToRiscv.mem := (@mem p);
    FlatToRiscv.funname_env := funname_env;
    FlatToRiscv.MM := free.Monad_free;
    FlatToRiscv.RVM := MetricMinimalMMIO.IsRiscvMachine;
    FlatToRiscv.PRParams := MetricMinimalMMIOPrimitivesParams;
    FlatToRiscv.ext_spec := ext_spec;
  }.

  Section CompilationTest.
    Definition magicMMIOAddrLit: Z := Ox"10024000".
    Variable addr: varname.
    Variable i: varname.
    Variable s: varname.

    (*
    addr = magicMMIOAddr;
    loop {
      i = input addr;
      stay in loop only if i is non-zero;
      s = i * i;
      output addr s;
    }
    *)
    Definition squarer: stmt :=
      (SSeq (SLit addr magicMMIOAddrLit)
            (SLoop (SLoad Syntax.access_size.four i addr)
                   (CondNez i)
                   (SSeq (SOp s Syntax.bopname.mul i i)
                         (SStore Syntax.access_size.four addr s)))).

    Definition compiled: list Instruction := Eval cbv in compile_stmt squarer.
    Goal True.
      let c := eval cbv in compiled in pose c.
    Abort.
  End CompilationTest.

  (* TODO: move *)
  Local Existing Instance MetricMinimalMMIO.IsRiscvMachine.

  Lemma load4bytes_in_MMIO_is_None: forall (m: mem) (addr: word),
      map.undef_on m isMMIOAddr ->
      isMMIOAddr addr ->
      Memory.load_bytes 4 m addr = None.
  Admitted.

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

  Instance assume_riscv_word_properties: RiscvWordProperties.word.riscv_ok word. Admitted.

  Ltac contrad := contradiction || discriminate || congruence.

  (* TODO: why are these here? *)
  Arguments LittleEndian.combine: simpl never. (* TODO can we put this next to its definition? *)
  Arguments mcomp_sat: simpl never.
  Arguments LittleEndian.split: simpl never.
  Local Arguments String.eqb: simpl never.
  (* give it priority over FlatToRiscvCommon.FlatToRiscv.PRParams to make eapply work better *)
  Existing Instance MetricMinimalMMIOPrimitivesParams.
  Existing Instance MetricMinimalMMIOSatisfiesPrimitives.
  Local Existing Instance MetricMinimalMMIOSatisfiesPrimitives.

  Ltac fwd :=
    match goal with
    |- free.interp interp_action ?p ?s ?post =>
      let p' := eval hnf in p in
      change (free.interp interp_action p' s post);
      rewrite free.interp_act;
      cbn [interp_action MinimalMMIO.interp_action snd fst];
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

  Axiom XAddrs_admitted : False.
  Instance FlatToRiscv_hyps: FlatToRiscvCommon.FlatToRiscv.assumptions.
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
    - eapply MetricMinimalMMIOSatisfiesPrimitives; cbn; intuition eauto.
    - (* compile_ext_call_correct *)
      intros *. intros ? ? V_argvars V_resvars. intros.
      pose proof (compile_ext_call_emits_valid EmitsValid.iset _ action _ V_resvars V_argvars).
      destruct_RiscvMachine initialL.
      unfold FlatToRiscvDef.compile_ext_call, FlatToRiscvCommon.FlatToRiscv.def_params,
             FlatToRiscv_params, compilation_params, compile_ext_call in *.
      destruct (String.eqb _ action) eqn: E;
        cbn [getRegs getPc getNextPc getMem getLog getMachine getMetrics] in *.
      + (* MMOutput *)
        simpl in *|-.
        simp.
        cbv [ext_spec FlatToRiscvCommon.FlatToRiscv.Semantics_params FlatToRiscvCommon.FlatToRiscv.ext_spec bedrock2_interact] in H16.
        simpl in *|-.

        destruct H16 as [? H16]; subst mGive.
        repeat match goal with
               | l: list _ |- _ => destruct l;
                                     try (exfalso; (contrad || (cheap_saturate; contrad))); []
               end.
        simp.
        destruct argvars. {
          exfalso. rename H10 into A. clear -A. cbn in *.
          destruct_one_match_hyp; congruence.
        }
        destruct argvars; cycle 1. {
          exfalso. rename H10 into A. clear -A. cbn in *. simp.
          destruct_one_match_hyp; congruence.
        }
        cbn in *|-.
        destruct resvars; cycle 1. {
          match goal with
          | HO: outcome _ _, H: _ |- _ => specialize (H _ _ HO); move H at bottom
          end.
          simp.
          cbn in *. discriminate.
        }
        simp.
        subst insts.

        eapply runsToNonDet.runsToStep_cps.
        cbv [mcomp_sat Primitives.mcomp_sat MetricMinimalMMIOPrimitivesParams].

        repeat fwd.

        split. 1:case XAddrs_admitted.
        erewrite ptsto_bytes.load_bytes_of_sep; cycle 1.
        { cbv [program ptsto_instr Scalars.truncated_scalar Scalars.littleendian] in *.
          cbn [array bytes_per] in *.
          ecancel_assumption. }

        repeat fwd.

        rewrite LittleEndian.combine_split.
        rewrite Z.mod_small by (eapply EncodeBound.encode_range).
        rewrite DecodeEncode.decode_encode by (eapply H5; left; trivial).

        repeat fwd.

        destruct (Z.eq_dec r Register0); cbv [Register0 valid_register] in *; try ((* WHY *) exfalso; Lia.lia).

        unshelve erewrite (_ : _ = @Some word _); [ | eassumption | ].

        repeat fwd.

        cbv [Register0 valid_register] in *.
        destruct (Z.eq_dec r0 0); try ((* WHY *) exfalso; Lia.lia).

        unshelve erewrite (_ : _ = @Some word _); [ | eassumption | ].
        destruct (Z.eq_dec r 0); try Lia.lia.

        repeat fwd.

        cbv [Utility.add Utility.ZToReg MachineWidth_XLEN]; rewrite add_0_r.

        unshelve erewrite (_ : _ = None); [eapply storeWord_in_MMIO_is_None; eauto|].

        cbv [MinimalMMIO.nonmem_store FE310_mmio].
        split; [trivial|].
        split; [red; auto|].

        repeat fwd.

        eapply runsToNonDet.runsToDone.
        simpl_MetricRiscvMachine_get_set.

        match goal with
        | Hoc: outcome _ _, H: _ |- _ => specialize H with (1 := Hoc)
        end.
        eexists. simp. simpl_word_exprs word_ok.
        do 2 match goal with
        | H: map.split _ _ map.empty |- _ => apply map.split_empty_r in H; subst
        end.
        unfold mmioStoreEvent, signedByteTupleToReg in *.
        setoid_rewrite LittleEndian.combine_split.
        rewrite sextend_width_nop by reflexivity.
        rewrite Z.mod_small by apply word.unsigned_range.
        rewrite word.of_Z_unsigned.
        apply eqb_eq in E0. subst action.
        cbn in *. replace l' with initialL_regs in * by congruence.
        split; eauto.
        split; eauto.
        split; eauto.
        split; eauto.
        split; eauto.
        cbv [id]; repeat split; MetricsToRiscv.solve_MetricLog.

      + (* MMInput *)
        simpl in *|-.
        simp.
        cbv [ext_spec FlatToRiscvCommon.FlatToRiscv.Semantics_params FlatToRiscvCommon.FlatToRiscv.ext_spec bedrock2_interact] in H16.
        simpl in *|-.

        destruct H16 as [? H16]; subst mGive.
        repeat match goal with
               | l: list _ |- _ => destruct l;
                                     try (exfalso; (contrad || (cheap_saturate; contrad))); []
               end.
        simp.
        destruct argvars; cycle 1. {
          exfalso. rename H10 into A. clear -A. cbn in *. simp.
          destruct_one_match_hyp; congruence.
        }
        cbn in *|-.
        destruct resvars. {
          match goal with
          | HO: forall _, outcome _ _, H: _ |- _ =>
          specialize (H _ _ (HO (word.of_Z 0))); move H at bottom
          end.
          simp.
          cbn in *. discriminate.
        }
        simp.
        destruct resvars; cycle 1. {
          match goal with
          | HO: forall _, outcome _ _, H: _ |- _ =>
          specialize (H _ _ (HO (word.of_Z 0))); move H at bottom
          end.
          simp.
          cbn in *. discriminate.
        }
        simp.
        subst insts.
        eapply runsToNonDet.runsToStep_cps.
        cbv [mcomp_sat Primitives.mcomp_sat MetricMinimalMMIOPrimitivesParams].

        repeat fwd.

        split. 1:case XAddrs_admitted.
        erewrite ptsto_bytes.load_bytes_of_sep; cycle 1.
        { cbv [program ptsto_instr Scalars.truncated_scalar Scalars.littleendian] in *.
          cbn [array bytes_per] in *.
          ecancel_assumption. }

        repeat fwd.

        rewrite LittleEndian.combine_split.
        rewrite Z.mod_small by (eapply EncodeBound.encode_range).
        rewrite DecodeEncode.decode_encode by (eapply H5; left; trivial).

        repeat fwd.

        cbv [Register0 valid_register] in *.
        destruct (Z.eq_dec r 0); try ((* WHY *) exfalso; Lia.lia).

        unshelve erewrite (_ : _ = @Some word _); [ | eassumption | ].

        repeat fwd.

        split; try discriminate.
        cbv [Utility.add Utility.ZToReg MachineWidth_XLEN]; rewrite add_0_r.
        unshelve erewrite (_ : _ = None); [eapply loadWord_in_MMIO_is_None|]; eauto.

        cbv [MinimalMMIO.nonmem_load FE310_mmio].
        split; [trivial|].
        split; [red; auto|].
        intros.

        repeat fwd.

        cbv [Register0 valid_register] in *.
        destruct (Z.eq_dec r0 0); try ((* WHY *) exfalso; Lia.lia).

        repeat fwd.

        eapply runsToNonDet.runsToDone.
        simpl_MetricRiscvMachine_get_set.

        eexists.
        match goal with
        | H: forall val, outcome _ [val], G: _ |- context [map.put _ _ ?resval] =>
        specialize (H resval);
        specialize G with (1 := H)
        end.
        simp.
        do 2 match goal with
             | H: map.split _ _ map.empty |- _ => apply map.split_empty_r in H; subst
             end.
        unfold mmioLoadEvent, signedByteTupleToReg.
        apply eqb_eq in E1. subst action.
        cbn in *. simp.
        split; eauto.
        split. { simpl_word_exprs word_ok; trivial. }
        split. { simpl_word_exprs word_ok; trivial. }
        split; eauto.
        repeat split; eauto; cbv [id]; try solve [MetricsToRiscv.solve_MetricLog].
  Qed.

End MMIO1.

Existing Instance Words32.
Existing Instance mmio_semantics_params.
Existing Instance compilation_params.
Existing Instance FlatToRiscv_params.
Existing Instance assume_riscv_word_properties.
Existing Instance FlatToRiscv_hyps.
