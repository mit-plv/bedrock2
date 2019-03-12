Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
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
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MinimalMMIO.
Require Import riscv.Spec.Primitives.
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
Require Import compiler.FlatToRiscv32.
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
    repeat split; (lia || assumption).
  - rewrite <- H1.
    simp_step.
    simp_step.
    simp_step.
    simp_step.
    (* try simp_step. (* TODO this should not fail fatally *) *)
    split; [|cbv;auto].
    unfold Encode.respects_bounds. simpl.
    unfold Encode.verify_I, valid_register, opcode_LOAD, funct3_LW in *.
    repeat split; (lia || assumption).
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
  Definition isGPIO0(addr: word): Prop := Ox"10012000" <= word.unsigned addr < Ox"10013000".
  Definition isQSPI1(addr: word): Prop := Ox"10024000" <= word.unsigned addr < Ox"10025000".
  Definition isMMIOAddr(addr: word): Prop :=
    word.unsigned addr mod 4 = 0 /\ (isGPIO0 addr \/ isQSPI1 addr).

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

  Definition simple_ext_spec(t: trace) m action (argvals: list word)
             (post: mem -> list word -> Prop) :=
      match argvals with
      | addr :: _ =>
        isMMIOAddr addr /\
        if isMMOutput action then
          exists val, argvals = [addr; val] /\ post m nil
        else
          argvals = [addr] /\ forall val, post m [val]
      | nil => False
      end.

  Section Real.
    Import FE310CompilerDemo.
    Definition real_ext_spec(t: trace) m (action: MMIOAction) args
               (post: mem -> list word -> Prop) :=
      match action, List.map word.unsigned args with
      | MMInput, [addr] => (
        if addr =? hfrosccfg                                then True else
        if (  otp_base <=? addr) && (addr <?   otp_pastend) then True else
        if (gpio0_base <=? addr) && (addr <? gpio0_pastend) then True else
        if (uart0_base <=? addr) && (addr <? uart0_pastend) then True else
        False )
        /\ addr mod 4 = 0
        /\ forall v, post m [v]
      | MMOutput, [addr; value] => (
        if addr =? hfrosccfg                                then True else
        if (gpio0_base <=? addr) && (addr <? gpio0_pastend) then True else
        if (uart0_base <=? addr) && (addr <? uart0_pastend) then True else
        False )
        /\ addr mod 4 = 0
        /\ post m []
      | _, _ =>
        False
      end%list%bool.
  End Real.

  Lemma real_ext_spec_implies_simple_ext_spec: forall t m a args post,
      real_ext_spec t m a args post ->
      simple_ext_spec t m a args post.
  Admitted.

  Instance mmio_semantics_params: Semantics.parameters := {|
    Semantics.syntax := mmio_syntax_params;
    Semantics.width := 32;
    Semantics.funname_eqb := Empty_set_rect _;
    Semantics.ext_spec := real_ext_spec;
  |}.

  Instance compilation_params: FlatToRiscvDef.parameters := {
    FlatToRiscvDef.actname := MMIOAction;
    FlatToRiscvDef.compile_ext_call := compile_ext_call;
    FlatToRiscvDef.max_ext_call_code_size _ := 1;
    FlatToRiscvDef.compile_ext_call_length := compile_ext_call_length;
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

    Definition compiled: list Instruction := Eval cbv in compile_stmt RV32IM squarer.
    Print compiled.
  End CompilationTest.

  Arguments LittleEndian.combine: simpl never. (* TODO can we put this next to its definition? *)
  Arguments mcomp_sat: simpl never.

  Instance FlatToRiscv_params: FlatToRiscv.parameters := {
    FlatToRiscv.def_params := compilation_params;
    FlatToRiscv.locals := locals;
    FlatToRiscv.mem := (@mem p);
    FlatToRiscv.MM := OStateND_Monad _;
    FlatToRiscv.RVM := IsRiscvMachineL;
    FlatToRiscv.PRParams := MinimalMMIOPrimitivesParams;
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
      destruct (map.get (getMem m2) k) eqn: E; [exfalso|reflexivity].
      edestruct B; [eassumption|]. congruence.
    - (* compile_ext_call_correct *)
      intros *. intros ? ? V_argvars V_resvars. intros.
      pose proof (compile_ext_call_emits_valid FlatToRiscv.iset _ action _ V_resvars V_argvars).
      destruct initialL as [initialRegs initialPc initialNpc initialMem initialLog].
      destruct action; cbv [getRegs getPc getNextPc getMem getLog] in *.
      + (* MMOutput *)
        simpl in *|-.
        simp.
        apply real_ext_spec_implies_simple_ext_spec in H14.
        unfold simple_ext_spec in *.
        simpl in *|-.
        repeat match goal with
               | l: list _ |- _ => destruct l;
                                     try (exfalso; (contrad || (cheap_saturate; contrad))); []
               end.
        simp.
        destruct argvars. {
          exfalso. rename H9 into A. clear -A. simpl in *.
          destruct_one_match_hyp; congruence.
        }
        destruct argvars; cycle 1. {
          exfalso. rename H9 into A. clear -A. simpl in *. simp.
          destruct_one_match_hyp; congruence.
        }
        simpl in *|-.
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
          simpl_word_exprs word_ok.
          apply spec_Bind.
          unfold Utility.regToInt32, MachineWidth_XLEN.
          refine (ex_intro _ (fun v m => m = _) _).
          split.
          { apply spec_storeWord. simpl. right. split; [|reflexivity]. repeat split.
            apply storeWord_in_MMIO_is_None; assumption. }
          { intros. subst. simulate. simpl. apply runsToNonDet.runsToDone.
            simpl.
            repeat split; try assumption.
              specialize (H15 initialMem []).
              destruct H15 as [ l' [A B] ].
              { Fail exact H8. (* TODO trace translation *) case TODO. }
              { inversion_option.
                subst l'.
                unfold mmioStoreEvent, signedByteTupleToReg, MMOutput in *.
                Fail exact B. (* TODO trace translation & other matching *) case TODO. } }

      + (* MMInput *)
        simpl in *|-.
        simp.
        apply real_ext_spec_implies_simple_ext_spec in H14.
        unfold simple_ext_spec in *.
        simpl in *|-.
        repeat match goal with
               | l: list _ |- _ => destruct l;
                                     try (exfalso; (contrad || (cheap_saturate; contrad))); []
               end.
        simp.
        destruct argvars; cycle 1. {
          exfalso. rename H9 into A. clear -A. simpl in *. simp.
          destruct_one_match_hyp; congruence.
        }
        simpl in *|-.
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
          refine (ex_intro _ (fun v m => m = _) _).
          split.
          { apply spec_loadWord. simpl. right. repeat split; try assumption.
            apply loadWord_in_MMIO_is_None; assumption. }
          { intros. subst. simulate. simpl. apply runsToNonDet.runsToDone.
            simpl.
            repeat split; try assumption.
              specialize (H15 initialMem [signedByteTupleToReg a]).
              destruct H15 as [ l' [A B] ].
              { specialize (H8 (signedByteTupleToReg a)).
                Fail exact H8. (* TODO trace translation *) case TODO. }
              { inversion_option.
                subst l'.
                unfold mmioLoadEvent, signedByteTupleToReg in *. simpl in *.
                Fail exact B. (* TODO trace translation *) case TODO. } }
    - (* go_load *)
      (* TODO make FlatToRiscv32.parameters and eapply go_load *)
      case TODO.
    - (* go_store *)
      case TODO.
  Qed.

End MMIO1.

Existing Instance Words32.
Existing Instance mmio_semantics_params.
Existing Instance compilation_params.
Existing Instance FlatToRiscv_params.
Existing Instance assume_riscv_word_properties.
Existing Instance FlatToRiscv_hyps.
