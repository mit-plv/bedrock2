Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Tactics.fwd.
Require Import compiler.util.Common.
Require Import bedrock2.Semantics.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.FreeMonad.
Require Import compiler.FlatImp.
Require Import riscv.Spec.Decode.
Require Import coqutil.sanity.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Spec.Machine.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvFunctions.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.MetricPrimitives.
Require Import compiler.MetricsToRiscv.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.SeparationLogic.
Require Import coqutil.Datatypes.Option.
Require Import compiler.RiscvWordProperties.
Require Import coqutil.Datatypes.ListSet.
Require Import compiler.memory_mapped_ext_calls_riscv.

Import ListNotations.

Local Open Scope bool_scope.
Local Open Scope string_scope.

Definition compile_load(action: string): Z -> Z -> Z -> Instruction :=
  if action =? "memory_mapped_extcall_read64" then Ld else
  if action =? "memory_mapped_extcall_read32" then Lw else
  if action =? "memory_mapped_extcall_read16" then Lh else Lb.

Definition compile_store(action: string): Z -> Z -> Z -> Instruction :=
  if action =? "memory_mapped_extcall_write64" then Sd else
  if action =? "memory_mapped_extcall_write32" then Sw else
  if action =? "memory_mapped_extcall_write16" then Sh else Sb.

Definition compile_interact(results: list Z)(a: string)(args: list Z): list Instruction :=
  match args with
  | [addr; val] => [compile_store a addr val 0]
  | [addr] => [compile_load a (List.hd 0 results) addr 0]
  | _ => [] (* invalid, excluded by ext_spec *)
  end.

Local Arguments Z.mul: simpl never.
Local Arguments Z.add: simpl never.
Local Arguments Z.of_nat: simpl never.
Local Arguments Z.modulo : simpl never.
Local Arguments Z.pow: simpl never.
Local Arguments Z.sub: simpl never.
Local Arguments Registers.reg_class.all: simpl never.

Section MMIO.
  Context {iset: InstructionSet}.
  Context {width: Z} {BW: Bitwidth width}.
  Context {bitwidth_iset : FlatToRiscvCommon.bitwidth_iset width iset}.
  Context {word: Word.Interface.word width}.
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

(*
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
*)

  Ltac contrad := contradiction || discriminate || congruence.

  (* TODO: why are these here? *)
  Arguments LittleEndian.combine: simpl never. (* TODO can we put this next to its definition? *)
  Arguments mcomp_sat: simpl never.
  Arguments LittleEndian.split: simpl never.
  Local Arguments String.eqb: simpl never.

  Ltac step :=
    match goal with
    |- free.interp interp_action ?p ?s ?post =>
      let p' := eval hnf in p in
      change (free.interp interp_action p' s post);
      rewrite free.interp_act;
      cbn [interp_action interpret_action snd fst];
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

  (* these are abstract and used both on the bedrock2 level and in riscv *)
  Context {ext_spec: ExtSpec} {ext_spec_ok: ext_spec.ok ext_spec}.

  Lemma compile_ext_call_correct: forall resvars extcall argvars,
      FlatToRiscvCommon.compiles_FlatToRiscv_correctly compile_ext_call compile_ext_call
        (FlatImp.SInteract resvars extcall argvars).
  Proof.
    unfold FlatToRiscvCommon.compiles_FlatToRiscv_correctly. simpl. intros.
    inversion H.
    subst resvars0 extcall argvars0 initialTrace initialMH initialRegsH
      initialMetricsH postH. clear H.
    destruct H5 as (? & ? & V_resvars & V_argvars).
    unfold goodMachine in *|-.
    fwd.
    apply one_step.
    lazymatch goal with
    | H: map.getmany_of_list _ argvars = Some argvals |- _ =>
        pose proof (map.getmany_of_list_length _ _ _ H) as Hl
    end.
    destruct g. FlatToRiscvCommon.simpl_g_get.
    match goal with
    | H: iff1 allx  _ |- _ => apply iff1ToEq in H; subst allx
    end.
    unfold compile_interact in *.
    destruct_RiscvMachine initialL. subst.
    (* need to make sure that all ext_specs can be compiled to loads or stores,
       i.e. need to restrict action names and arg/retval counts
    destruct HExt as [HExt | HExt]; fwd.
    - (* load *)
      destruct argvars as [ |addr_reg argvars]. 1: discriminate Hl.
      destruct argvars. 2: discriminate Hl. clear Hl.
      eapply go_fetch_inst; simpl_MetricRiscvMachine_get_set.
      { reflexivity. }
      { eapply rearrange_footpr_subset. 1: eassumption. wwcancel. }
      { wcancel_assumption. }
      { unfold not_InvalidInstruction, compile_load.
        repeat match goal with
               | |- _ => exact I
               | |- _ => progress cbn
               | |- context[String.eqb ?l ?r] => destruct (String.eqb l r)
               end. }
       TODO only allow valid n's in ext_spec *)
  Abort.

End MMIO.
