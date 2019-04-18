Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Macros.unique.
Require Import compiler.util.Common.
Require Import bedrock2.Semantics.
Require Import riscv.Utility.Monads.
Require Import coqutil.Map.SortedList.
Require Import compiler.FlatImp.
Require Import riscv.Utility.ListLib.
Require Import riscv.Spec.Decode.
Require Import coqutil.sanity.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Spec.Machine.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscv.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MinimalMMIO.
Require Import riscv.Platform.MetricMinimalMMIO.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.MetricPrimitives.
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
Definition funname: Type := Empty_set.

Instance actname_eq_dec: DecidableEq MMIOAction.
intros a b. destruct a; destruct b; (left + right); congruence.
Defined.

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
    Zlength (compile_ext_call binds f args) <= 1.
Proof.
  intros. unfold compile_ext_call.
  destruct f; destruct binds; try destruct binds;
  try destruct args; try destruct args; try destruct args;
  cbv; intros; discriminate.
Qed.

Lemma compile_ext_call_length': forall binds f args,
    Zlength (compile_ext_call binds f args) <= 7.
Proof. intros. rewrite compile_ext_call_length. blia. Qed.

Lemma compile_ext_call_emits_valid: forall iset binds a args,
    Forall valid_register binds ->
    Forall valid_register args ->
    valid_instructions iset (compile_ext_call binds a args).
Proof.
  intros.
  destruct a; destruct args; try destruct args; try destruct args;
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
  }.
End MMIO.

Section MMIO1.
  Context {p: unique! MMIO.parameters}.

  Instance Words32: Utility.Words := {
    Utility.byte := byte;
    Utility.word := word;
    Utility.width_cases := or_introl eq_refl;
  }.

  (* Using the memory layout of FE310-G000 *)
  Definition isOTP  (addr: word): Prop := Ox"00020000" <= word.unsigned addr < Ox"00022000".
  Definition isPRCI (addr: word): Prop := Ox"10008000" <= word.unsigned addr < Ox"10010000".
  Definition isGPIO0(addr: word): Prop := Ox"10012000" <= word.unsigned addr < Ox"10013000".
  Definition isUART0(addr: word): Prop := Ox"10013000" <= word.unsigned addr < Ox"10014000".
  Definition isMMIOAddr(addr: word): Prop :=
    word.unsigned addr mod 4 = 0 /\ (isOTP addr \/ isPRCI addr \/ isGPIO0 addr \/ isUART0 addr).

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

  Definition trace: Type := list (mem * MMIOAction * list word * (mem * list word)).

  Definition simple_ext_spec(t: trace)(mGive: mem)(action: MMIOAction)(argvals: list word)
             (post: mem -> list word -> Prop) :=
      match argvals with
      | addr :: _ =>
        isMMIOAddr addr /\
        mGive = map.empty /\
        if isMMOutput action then
          exists val, argvals = [addr; val] /\ post map.empty nil
        else
          argvals = [addr] /\ forall val, post map.empty [val]
      | nil => False
      end.

  Section Real.
    Import FE310CompilerDemo.
    Definition real_ext_spec(t: trace)(mGive: mem)(action: MMIOAction)(args: list word)
               (post: mem -> list word -> Prop) :=
      mGive = map.empty /\
      match action, List.map word.unsigned args with
      | MMInput, [addr] => (
        if addr =? hfrosccfg                                then True else
        if (  otp_base <=? addr) && (addr <?   otp_pastend) then True else
        if (gpio0_base <=? addr) && (addr <? gpio0_pastend) then True else
        if (uart0_base <=? addr) && (addr <? uart0_pastend) then True else
        False )
        /\ addr mod 4 = 0
        /\ forall v, post map.empty [v]
      | MMOutput, [addr; value] => (
        if addr =? hfrosccfg                                then True else
        if (gpio0_base <=? addr) && (addr <? gpio0_pastend) then True else
        if (uart0_base <=? addr) && (addr <? uart0_pastend) then True else
        False )
        /\ addr mod 4 = 0
        /\ post map.empty []
      | _, _ =>
        False
      end%list%bool.
  End Real.

  Lemma real_ext_spec_implies_simple_ext_spec: forall t m a args post,
      real_ext_spec t m a args post ->
      simple_ext_spec t m a args post.
  Proof.
    unfold real_ext_spec, simple_ext_spec.
    intros.
    simp.
    unfold
      FE310CompilerDemo.otp_base,
      FE310CompilerDemo.otp_pastend,
      FE310CompilerDemo.hfrosccfg,
      FE310CompilerDemo.gpio0_base,
      FE310CompilerDemo.gpio0_pastend,
      FE310CompilerDemo.uart0_base,
      FE310CompilerDemo.uart0_pastend,
      FE310CompilerDemo.uart0_rxdata,
      FE310CompilerDemo.uart0_txdata in *.
    repeat (destruct_one_match_hyp; simp; try contradiction);
      repeat ((destruct args; simpl in *; try discriminate); []);
      simp;
      repeat split;
      eauto;
      unfold isOTP, isPRCI, isGPIO0, isUART0;
      repeat match goal with
             | H: (_ =? _) = true |- _ => apply Z.eqb_eq in H; rewrite ?H
             | H: (_ =? _) = false |- _ => apply Z.eqb_neq in H
             | H: (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
             | H: (_ && _)%bool = false |- _ => apply Bool.andb_false_iff in H; destruct H
             | H: (_ <? _) = true |- _ => apply Z.ltb_lt in H
             | H: (_ <? _) = false |- _ => apply Z.ltb_ge in H
             | H: (_ <=? _) = true |- _ => apply Z.leb_le in H
             | H: (_ <=? _) = false |- _ => apply Z.leb_gt in H
             end;
      try solve [ hex_csts_to_dec; blia ].
  Qed.

  Instance mmio_semantics_params: Semantics.parameters := {|
    Semantics.syntax := mmio_syntax_params;
    Semantics.width := 32;
    Semantics.funname_eqb := Empty_set_rect _;
    Semantics.ext_spec := real_ext_spec;
  |}.

  Instance compilation_params: FlatToRiscvDef.parameters := {
    FlatToRiscvDef.actname := MMIOAction;
    FlatToRiscvDef.compile_ext_call := compile_ext_call;
    FlatToRiscvDef.compile_ext_call_length := compile_ext_call_length';
    FlatToRiscvDef.compile_ext_call_emits_valid := compile_ext_call_emits_valid;
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
    Print compiled.
  End CompilationTest.

  Arguments LittleEndian.combine: simpl never. (* TODO can we put this next to its definition? *)
  Arguments mcomp_sat: simpl never.

  Instance FlatToRiscv_params: FlatToRiscv.parameters := {
    FlatToRiscv.def_params := compilation_params;
    FlatToRiscv.locals := locals;
    FlatToRiscv.mem := (@mem p);
    FlatToRiscv.MM := OStateND_Monad _;
    FlatToRiscv.RVM := IsMetricRiscvMachineL;
    FlatToRiscv.PRParams := MetricMinimalMMIOPrimitivesParams;
    FlatToRiscv.ext_spec := ext_spec;
    FlatToRiscv.ext_guarantee mach := map.undef_on mach.(getMem) isMMIOAddr;
  }.

  Instance assume_riscv_word_properties: RiscvWordProperties.word.riscv_ok word. Admitted.

  Ltac contrad := contradiction || discriminate || congruence.

  Arguments LittleEndian.split: simpl never.

  Instance FlatToRiscv_hyps: FlatToRiscv.assumptions.
  Proof.
    constructor. all: try typeclasses eauto.
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
      destruct initialL as [ [initialRegs initialPc initialNpc initialMem initialLog] initialMetrics].
      destruct action; cbn [getRegs getPc getNextPc getMem getLog getMachine getMetrics] in *.
      + (* MMOutput *)
        simpl in *|-.
        simp.
        apply real_ext_spec_implies_simple_ext_spec in H16.
        unfold simple_ext_spec in *.
        simpl in *|-.
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
        simp.
        subst insts.
        eapply runsToNonDet.runsToStep; cycle 1.
        * intro mid.
          apply id.
        * simulate_step.
          simulate_step.
          simulate_step.
          simulate_step.
          simulate_step.
          simulate_step.
          simulate_step.
          unfold Utility.add, Utility.ZToReg, Utility.regToInt32, MachineWidth_XLEN.
          simpl_word_exprs word_ok.
          apply spec_Bind.
          refine (ex_intro _ (fun v m => m = {| getMachine := {| getLog := _ |} |}) _).
          split.
          { apply spec_storeWord. simpl. right. simpl. split; [|reflexivity].
            apply storeWord_in_MMIO_is_None; simpl_word_exprs word_ok; assumption. }
          { intros. subst. simulate. simpl. apply runsToNonDet.runsToDone. simpl.
            specialize H17 with (1 := H8).
            eexists. simp.
            repeat split; try eassumption.
            { apply map.split_empty_r in H2. subst.
              apply map.split_empty_r in H9. subst.
              unfold mmioStoreEvent, signedByteTupleToReg, MMOutput in *.
              rewrite LittleEndian.combine_split.
              rewrite sextend_width_nop by reflexivity.
              rewrite Z.mod_small by apply word.unsigned_range.
              rewrite word.of_Z_unsigned.
              eassumption. }
            all: solve [solve_MetricLog]. }

      + (* MMInput *)
        simpl in *|-.
        simp.
        apply real_ext_spec_implies_simple_ext_spec in H16.
        unfold simple_ext_spec in *.
        simpl in *|-.
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
        simp.
        subst insts.
        eapply runsToNonDet.runsToStep; cycle 1.
        * intro mid.
          apply id.
        * simulate_step.
          simulate_step.
          simulate_step.
          simulate_step.
          simulate_step.
          simulate_step.
          simpl_word_exprs word_ok.
          apply spec_Bind.
          refine (ex_intro _ (fun v m => m = {| getMachine := {| getLog := _ |} |}) _).
          split.
          { apply spec_loadWord. simpl. right. repeat split; try assumption.
            apply loadWord_in_MMIO_is_None; simpl_word_exprs word_ok; assumption. }
          { intros. subst. simulate. simpl. apply runsToNonDet.runsToDone.
            simpl. eexists.
            repeat split; try assumption.
            { match goal with
              | |- context [map.put _ _ ?resval] => specialize (H7 resval)
              end.
              specialize H17 with (1 := H7).
              simp.
              apply map.split_empty_r in H2. subst.
              apply map.split_empty_r in H9. subst.
              unfold mmioLoadEvent, signedByteTupleToReg, MMInput in *.
              replace (word.add r (word.of_Z 0)) with r; [eassumption|].
              simpl_word_exprs word_ok.
              reflexivity. }
            all: solve [solve_MetricLog]. }
  Qed.

End MMIO1.

Existing Instance Words32.
Existing Instance mmio_semantics_params.
Existing Instance compilation_params.
Existing Instance FlatToRiscv_params.
Existing Instance assume_riscv_word_properties.
Existing Instance FlatToRiscv_hyps.
