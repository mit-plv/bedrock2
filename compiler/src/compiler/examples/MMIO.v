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
Require Import compiler.FlatToRiscvMetric.
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
Require bedrock2.Examples.FE310CompilerDemo.
Import ListNotations.


Open Scope ilist_scope.

Definition varname: Type := Z.
Definition funname: Type := string.

Definition compile_ext_call(results: list varname)(a: MMIOAction)(args: list varname):
  list Instruction :=
  if isMMOutput a then
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
  destruct (isMMOutput f); destruct binds; try destruct binds;
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
  destruct (isMMOutput a); destruct args; try destruct args; try destruct args;
    destruct binds; try destruct binds;
    intros instr HIn; simpl in *; intuition idtac; try contradiction.
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
  Syntax.actname := MMIOAction;
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

  (* Using the memory layout of FE310-G000 *)
  Definition isOTP  (addr: word): Prop := Ox"00020000" <= word.unsigned addr < Ox"00022000".
  Definition isPRCI (addr: word): Prop := Ox"10008000" <= word.unsigned addr < Ox"10010000".
  Definition isGPIO0(addr: word): Prop := Ox"10012000" <= word.unsigned addr < Ox"10013000".
  Definition isUART0(addr: word): Prop := Ox"10013000" <= word.unsigned addr < Ox"10014000".
  Definition isMMIOAddr(addr: word): Prop :=
    word.unsigned addr mod 4 = 0 /\ (isOTP addr \/ isPRCI addr \/ isGPIO0 addr \/ isUART0 addr).

  Local Instance Words32: Utility.Words := {
    Utility.byte := byte;
    Utility.word := word;
    Utility.width_cases := or_introl eq_refl;
  }.

  Local Instance processor_mmio : ExtSpec := {|
    mmio_load n ctxid a m t post := isMMIOAddr a /\ forall v, post m v;
    mmio_store n ctxid a v m t post := isMMIOAddr a /\ post m;
  |}.

  Local Notation bedrock2_trace := (list (mem * MMIOAction * list word * (mem * list word))).
  Definition bedrock2_interact (t : bedrock2_trace) (mGive : mem) (a : MMIOAction) (args: list word) (post:mem -> list word -> Prop) :=
    mGive = map.empty /\
    if isMMOutput a
    then exists addr val, args = [addr; val] /\ isMMIOAddr addr /\ post map.empty nil
    else if isMMInput a
    then exists addr, args = [addr] /\ isMMIOAddr addr /\ forall val, post map.empty [val]
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
    FlatToRiscv.ext_guarantee mach := map.undef_on mach.(getMem) isMMIOAddr;
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

  Definition ext_guarantee mach :=
    forall addr, isMMIOAddr addr -> Memory.load_bytes 4 (getMem mach) addr = None.

  Lemma execute_mmio_load
    addr_reg (Haddr_reg : valid_register addr_reg)
    res_reg (Hres_reg : valid_register res_reg)
    (mach : MetricRiscvMachine) (Hguarantee : ext_guarantee mach)
    addr (Haddr : map.get mach.(getRegs) addr_reg = Some addr)
    (HisMMIO : isMMIOAddr addr)
    instr (Hcompile :compile_ext_call [res_reg] MMInput [addr_reg] = [instr])
    : interp (Execute.execute instr) mach (fun _ m => exists v,
      m = 
      withRegs (map.put mach.(getRegs) res_reg (word.of_Z (LittleEndian.combine 4 v))) (
      withLogItem (mmioLoadEvent addr v)
      (updateMetrics (addMetricLoads 1) (mach)))).
  Proof.
    inversion Hcompile; clear dependent instr.
    cbn.

    destruct (Z.eq_dec addr_reg Register0).
    { subst addr_reg. inversion Haddr_reg. cbv [Register0] in *; Omega.omega. }
    split; trivial.

    change (@map.get Register (@word p) (@locals p) (@getRegs Words32 (@locals p) (@mem p) mach) addr_reg) with (@map.get Register (@Utility.word Words32) (@locals p) (@getRegs Words32 (@locals p) (@mem p) mach) addr_reg).
    rewrite Haddr.
    rewrite add_0_r.

    cbv [load].
    split; [inversion 1|].

    change (@Memory.load_bytes (@Utility.byte Words32) (@Utility.width Words32) (@Utility.word Words32) (@mem p) 4 (@getMem Words32 (@locals p) (@mem p) mach) addr)
    with (@Memory.load_bytes (@Utility.byte Words32) (@Utility.width Words32) (@Utility.word Words32) (@mem p) 4 (@getMem Words32 (@locals p) (@mem p) mach) addr).
    rewrite (Hguarantee addr HisMMIO).

    cbv [mmio_load processor_mmio id].
    destruct (Z.eq_dec res_reg Register0); try (subst; cbv [valid_register Register0] in * ; exfalso; clear -Hres_reg; Omega.omega).

    split; trivial.
    intros.
    split; trivial.
    eexists.

    rewrite sextend_width_nop by trivial.
    destruct mach as [ [] ?]; exact eq_refl.
  Qed.

  Lemma execute_mmio_store
    addr_reg (Haddr_reg : valid_register addr_reg)
    val_reg (Hval_reg : valid_register val_reg)
    instr (Hcompile :compile_ext_call [] MMOutput [addr_reg;val_reg] = [instr])
    (mach : MetricRiscvMachine) (Hguarantee : ext_guarantee mach)
    addr (Haddr : map.get mach.(getRegs) addr_reg = Some addr)
    val (Hval : map.get mach.(getRegs) val_reg = Some val)
    (HisMMIO : isMMIOAddr addr)
    : interp (Execute.execute instr) mach (fun _ m =>
      let vv := LittleEndian.split 4 (word.unsigned val) in
      m = withLogItem (mmioStoreEvent addr vv)
          (updateMetrics (addMetricStores 1) (withXAddrs (invalidateWrittenXAddrs 4 addr mach.(getXAddrs)) mach))).
  Proof.
    cbn in Hcompile.
    inversion Hcompile; clear dependent instr.
    cbn.

    destruct (Z.eq_dec val_reg Register0).
    { subst val_reg. inversion Hval_reg. cbv [Register0] in *; Omega.omega. }

    destruct (Z.eq_dec addr_reg Register0).
    { subst addr_reg. inversion Haddr_reg. cbv [Register0] in *; Omega.omega. }

    split; trivial.

    change (@map.get Register (@word p) (@locals p) (@getRegs Words32 (@locals p) (@mem p) mach) addr_reg) with (@map.get Register (@Utility.word Words32) (@locals p) (@getRegs Words32 (@locals p) (@mem p) mach) addr_reg).
    rewrite Haddr.
    rewrite add_0_r.

    cbv [store].
    split; trivial.

    change (@map.get Register (@word p) (@locals p) (@getRegs Words32 (@locals p) (@mem p) mach) val_reg) with (@map.get Register (@Utility.word Words32) (@locals p) (@getRegs Words32 (@locals p) (@mem p) mach) val_reg).
    rewrite Hval.

    cbv [Memory.store_bytes].

    set (mach1 := (RiscvMachine.withXAddrs (invalidateWrittenXAddrs 4 addr (getXAddrs mach)) mach)).
    change (@Memory.load_bytes (@Utility.byte Words32) (@Utility.width Words32) (@Utility.word Words32) (@mem p) 4 (@getMem Words32 (@locals p) (@mem p) mach1) addr)
    with (@Memory.load_bytes (@Utility.byte Words32) (@Utility.width Words32) (@Utility.word Words32) (@mem p) 4 (@getMem Words32 (@locals p) (@mem p) mach1) addr).
    rewrite (Hguarantee addr HisMMIO).

    cbv [mmio_store processor_mmio id].

    split; trivial.

    destruct mach as [ [] ?]; exact eq_refl.
  Qed.




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
  Arguments isMMOutput: simpl never.
  Arguments isMMInput: simpl never.
  (* give it priority over FlatToRiscvCommon.FlatToRiscv.PRParams to make eapply work better *)
  Existing Instance MetricMinimalMMIOPrimitivesParams.
  Existing Instance MetricMinimalMMIOSatisfiesPrimitives.

  Lemma go_storeWord_mmio: forall (initialL : MetricRiscvMachine) (addr : Utility.word)
        (v : Utility.w32) (post : MetricRiscvMachine -> Prop) f,
      Memory.store_bytes 4 initialL.(getMem) addr v = None ->
      mcomp_sat (f tt) (updateMetrics (addMetricStores 1)
                                      (withLogItem (mmioStoreEvent addr v) initialL)) post ->
      mcomp_sat (Bind (Machine.storeWord Execute addr v) f) initialL post.
  Proof.
  Admitted.

  Lemma go_loadWord_mmio: forall (initialL : MetricRiscvMachine) (addr : Utility.word)
                                 (post : MetricRiscvMachine -> Prop) f,
      Memory.load_bytes 4 initialL.(getMem) addr = None ->
      (forall  (v : Utility.w32),
          mcomp_sat (f v) (updateMetrics (addMetricLoads 1)
                                          (withLogItem (mmioLoadEvent addr v) initialL)) post) ->
      mcomp_sat (Bind (Machine.loadWord Execute addr) f) initialL post.
  Proof.
  Admitted.

  Instance FlatToRiscv_hyps: FlatToRiscvCommon.FlatToRiscv.assumptions.
  Proof.
    constructor.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
    - typeclasses eauto.
    - exact MetricMinimalMMIOSatisfiesPrimitives.
    - (* ext_guarantee preservable: *)
      simpl. unfold map.same_domain, map.sub_domain, map.undef_on, map.agree_on in *.
      intros. destruct H0 as [A B].
      specialize H with (1 := H2).
      rewrite map.get_empty in *.
      match goal with
      | |- ?X = None => destruct X eqn: E; [exfalso|reflexivity]
      end.
      edestruct B; [eassumption|]. rewrite H in H0. discriminate.
    - (* compile_ext_call_correct *)
      intros *. intros ? ? V_argvars V_resvars. intros.
      pose proof (compile_ext_call_emits_valid EmitsValid.iset _ action _ V_resvars V_argvars).
      destruct_RiscvMachine initialL.
      unfold FlatToRiscvDef.compile_ext_call, FlatToRiscvCommon.FlatToRiscv.def_params,
             FlatToRiscv_params, compilation_params, compile_ext_call in *.
      destruct (isMMOutput action) eqn: E;
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
        eapply runsToNonDet.runsToStep. {
          simulate_step.
          simulate_step.
          simulate_step.
          eapply go_storeWord_mmio. {
            simpl. apply storeWord_in_MMIO_is_None; simpl_word_exprs word_ok; assumption.
          }
          simpl_MetricRiscvMachine_get_set.
          refine (go_step _ _ _); [ sidecondition.. | idtac ].
          instantiate (1 := @eq MetricRiscvMachine _). reflexivity.
        }
        intros. subst. simpl. apply runsToNonDet.runsToDone. simpl.
        match goal with
        | Hoc: outcome _ _, H: _ |- _ => specialize H with (1 := Hoc)
        end.
        eexists. simp. simpl_word_exprs word_ok.
        repeat split; try eassumption.
        { do 2 match goal with
          | H: map.split _ _ map.empty |- _ => apply map.split_empty_r in H; subst
          end.
          unfold mmioStoreEvent, signedByteTupleToReg, MMOutput in *.
          rewrite LittleEndian.combine_split.
          rewrite sextend_width_nop by reflexivity.
          rewrite Z.mod_small by apply word.unsigned_range.
          rewrite word.of_Z_unsigned.
          unfold isMMOutput in E0. apply eqb_eq in E0. subst action. unfold MMOutput in *.
          cbn in *. replace l' with initialL_regs in * by congruence.
          eassumption. }
        all: solve [MetricsToRiscv.solve_MetricLog].

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
        eapply runsToNonDet.runsToStep; cycle 1.
        * intro mid.
          apply id.
        * simulate_step.
          cbn.
          simulate_step.
          eapply go_loadWord_mmio. {
            apply loadWord_in_MMIO_is_None; simpl_word_exprs word_ok; try assumption.
          }
          intros. subst.
          cbn.
          simulate_step.
          simulate_step.
          apply runsToNonDet.runsToDone.
          simpl. eexists.
          repeat split; try assumption.
          { match goal with
            | H: forall val, outcome _ [val], G: _ |- context [map.put _ _ ?resval] =>
              specialize (H resval);
              specialize G with (1 := H)
            end.
            simp.
            do 2 match goal with
                 | H: map.split _ _ map.empty |- _ => apply map.split_empty_r in H; subst
                 end.
            unfold mmioLoadEvent, signedByteTupleToReg, MMInput in *.
            unfold isMMInput in E1. apply eqb_eq in E1. subst action. unfold MMInput in *.
            cbn in *. simp.
            replace (word.add addr (word.of_Z 0)) with addr; [eassumption|].
            simpl_word_exprs word_ok.
            reflexivity. }
          all: try solve [MetricsToRiscv.solve_MetricLog].
          all : simpl_word_exprs word_ok; trivial.
  Qed.

End MMIO1.

Existing Instance Words32.
Existing Instance mmio_semantics_params.
Existing Instance processor_mmio.
Existing Instance compilation_params.
Existing Instance FlatToRiscv_params.
Existing Instance assume_riscv_word_properties.
Existing Instance FlatToRiscv_hyps.
