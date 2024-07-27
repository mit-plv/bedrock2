From Coq Require Import ZArith.
From Coq Require Import Lia.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.Domain.
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

(* Goal of this file: compile from this (bedrock2 ext calls): *)
Require Import bedrock2.memory_mapped_ext_spec.
(* to this (risc-v "ext calls" implemented by load and store instructions): *)
Require Import compiler.memory_mapped_ext_calls_riscv.

Import ListNotations.

Local Open Scope bool_scope.
Local Open Scope string_scope.

(* Note: RISC-V has are no unsigned XLEN-bit load operations because they are the
   same as signed, so we need an extra case distinction for 32-bit loads, and 64-bit load
   is Ld because Ldu doesn't exist *)
Definition compile_load{width: Z}{BW: Bitwidth width}
  (action: string): Z -> Z -> Z -> Instruction :=
  if action =? "memory_mapped_extcall_read64" then Ld else
  if action =? "memory_mapped_extcall_read32" then (if Z.eqb width 32 then Lw else Lwu) else
  if action =? "memory_mapped_extcall_read16" then Lhu else Lbu.

Definition compile_store(action: string): Z -> Z -> Z -> Instruction :=
  if action =? "memory_mapped_extcall_write64" then Sd else
  if action =? "memory_mapped_extcall_write32" then Sw else
  if action =? "memory_mapped_extcall_write16" then Sh else Sb.

Definition compile_interact{width: Z}{BW: Bitwidth width}
  (results: list Z)(a: string)(args: list Z): list Instruction :=
  match args with
  | [addr; val] => [compile_store a addr val 0]
  | [addr] => [compile_load a (List.hd RegisterNames.a0 results) addr 0]
  | _ => [] (* invalid, excluded by ext_spec *)
  end.

Local Arguments Z.mul: simpl never.
Local Arguments Z.add: simpl never.
Local Arguments Z.of_nat: simpl never.
Local Arguments Z.modulo : simpl never.
Local Arguments Z.pow: simpl never.
Local Arguments Z.sub: simpl never.
Local Arguments Registers.reg_class.all: simpl never.

Section GetSetRegValid.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {locals: map.map Z word}.

  Lemma getReg_valid: forall x (v: word) regs,
      valid_register x -> map.get regs x = Some v -> getReg regs x = v.
  Proof.
    unfold valid_register, getReg. intros. destruct_one_match.
    - rewrite H0. reflexivity.
    - exfalso. lia.
  Qed.

  Lemma setReg_valid:
    forall x (v: word) regs, valid_register x -> setReg x v regs = map.put regs x v.
  Proof.
    unfold valid_register, setReg. intros. destruct_one_match. 1: reflexivity. exfalso. lia.
  Qed.
End GetSetRegValid.

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

  Local Arguments mcomp_sat: simpl never.

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
  Context {mmio_ext_calls: MemoryMappedExtCalls}
          {mmio_ext_calls_ok: MemoryMappedExtCallsOk mmio_ext_calls}.

  Lemma go_ext_call_load: forall n action x a addr (initialL: MetricRiscvMachine) post f,
      action = "memory_mapped_extcall_read" ++ String.of_nat (n * 8) ->
      (n = 1%nat \/ n = 2%nat \/ n = 4%nat \/ n = 8%nat /\ width = 64) ->
      valid_register x ->
      valid_register a ->
      map.get initialL.(getRegs) a = Some addr ->
      Memory.load_bytes n initialL.(getMem) addr = None ->
      read_step n initialL.(getLog) addr (fun val mRcv =>
        forall m' : mem,
        map.split m' (getMem initialL) mRcv ->
        let v := word.of_Z (LittleEndian.combine n val) in
        mcomp_sat (f tt)
          (withRegs (map.put initialL.(getRegs) x v)
          (updateMetrics (addMetricLoads 1)
          (withLogItem ((map.empty, action, [addr]), (mRcv, [v]))
          (withMem m' initialL)))) post) ->
      mcomp_sat (Bind (Execute.execute (compile_load action x a 0)) f) initialL post.
  Proof.
    destruct width_cases as [W | W]; subst width;
    intros; subst action;
    unfold compile_load, Execute.execute;
    match goal with
    | H: _ |- _ => destruct H as [? | [? | [? | [? ?] ] ] ]; subst n
    end;
    try lazymatch goal with
        | H: 32 = 64 |- _ => discriminate H
        end;
    lazymatch goal with
    | |- context[match ?i with _ => _ end] =>
        let i' := eval hnf in i in change i with i'
    end;
    cbv iota;
    unfold ExecuteI.execute, ExecuteI64.execute;
    eapply go_associativity;
    (eapply go_getRegister; [ eassumption | eassumption | ]);
    eapply go_associativity;
    eapply go_associativity;
    unfold mcomp_sat, Primitives.mcomp_sat, primitivesParams, Bind, free.Monad_free in *;
    repeat step;
    (split; [ discriminate 1 | ]);
    unfold ZToReg, Utility.add, MachineWidth_XLEN;
    rewrite word.add_0_r;
    rewrite_match;
    unfold nonmem_load;
    (eapply weaken_read_step; [eassumption | cbv beta]);
    intros; repeat step;
    unfold uInt8ToReg, uInt16ToReg, int32ToReg, uInt32ToReg, int64ToReg, MachineWidth_XLEN;
    rewrite setReg_valid by assumption;
    rewrite ?sextend_width_nop by reflexivity;
    only_destruct_RiscvMachine initialL;
    cbn -[HList.tuple Memory.load_bytes] in *;
    try (eapply H; assumption).
  Qed.

  Lemma go_ext_call_store: forall n action a addr v val mGive mKeep
                                  (initialL: MetricRiscvMachine) post f,
      action = "memory_mapped_extcall_write" ++ String.of_nat (n * 8) ->
      (n = 1%nat \/ n = 2%nat \/ n = 4%nat \/ n = 8%nat /\ width = 64) ->
      valid_register a ->
      valid_register v ->
      map.get initialL.(getRegs) a = Some addr ->
      map.get initialL.(getRegs) v = Some val ->
      word.unsigned val < 2 ^ (Z.of_nat n * 8) ->
      Memory.load_bytes n initialL.(getMem) addr = None ->
      map.split initialL.(getMem) mKeep mGive ->
      write_step n initialL.(getLog) addr (LittleEndian.split n (word.unsigned val)) mGive ->
      mcomp_sat (f tt)
        (updateMetrics (addMetricStores 1)
        (withXAddrs (list_diff word.eqb initialL.(getXAddrs)
                        (list_union word.eqb (footprint_list addr n) (map.keys mGive)))
        (withLogItem ((mGive, action, [addr; val]),
                      (map.empty, nil))
        (withMem mKeep initialL)))) post ->
      mcomp_sat (Bind (Execute.execute (compile_store action a v 0)) f) initialL post.
  Proof.
    destruct width_cases as [W | W]; subst width;
    intros; subst action;
    unfold compile_store, Execute.execute;
    match goal with
    | H: _ |- _ => destruct H as [? | [? | [? | [? ?] ] ] ]; subst n
    end;
    try lazymatch goal with
        | H: 32 = 64 |- _ => discriminate H
        end;
    lazymatch goal with
    | |- context[match ?i with _ => _ end] =>
        let i' := eval hnf in i in change i with i'
    end;
    cbv iota;
    unfold ExecuteI.execute, ExecuteI64.execute;
    eapply go_associativity;
    (eapply go_getRegister; [ eassumption | eassumption | ]);
    eapply go_associativity;
    eapply go_associativity;
    unfold mcomp_sat, Primitives.mcomp_sat, primitivesParams, Bind, free.Monad_free in *;
    repeat step;
    unfold Memory.store_bytes;
    unfold ZToReg, Utility.add, MachineWidth_XLEN;
    rewrite word.add_0_r;
    rewrite_match;
    unfold nonmem_store;
    unfold regToInt8, regToInt16, regToInt32, regToInt64, MachineWidth_XLEN;
    eexists _, _;
    (split; [eassumption | ]);
    erewrite getReg_valid by eassumption;
    (split; [assumption | ]);
    rewrite LittleEndian.combine_split;
    only_destruct_RiscvMachine initialL;
    cbn -[HList.tuple Memory.load_bytes invalidateWrittenXAddrs] in *;
    rewrite Z.mod_small by (split; [eapply word.unsigned_range|assumption]);
    rewrite word.of_Z_unsigned;
    lazymatch goal with
    | H: free.interp interp_action _ _ _ |- free.interp interp_action _ _ _ => exact H
    end.
  Qed.

  Lemma disjoint_load_bytes_is_None: forall m (addr: word) n,
      (0 < n)%nat ->
      disjoint (map.domain m) (of_list (footprint_list addr n)) ->
      Memory.load_bytes n m addr = None.
  Proof.
    unfold disjoint, of_list, footprint_list, map.domain, PropSet.elem_of.
    intros.
    destruct n. 1: inversion H. cbn.
    destr (map.get m addr). 2: reflexivity. exfalso.
    specialize (H0 addr). destruct H0; apply H0; clear H0. 1: congruence.
    simpl. left. reflexivity.
  Qed.

  Lemma load_bytes_in_mmio_or_ext_mem_is_None: forall n mAll m mExt (addr : word),
      (0 < n)%nat ->
      subset (of_list (footprint_list addr n)) mmio_addrs \/
      subset (of_list (footprint_list addr n)) (map.domain mExt) ->
      map.split mAll m mExt ->
      disjoint (map.domain mAll) mmio_addrs ->
      Memory.load_bytes n m addr = None.
  Proof.
    intros.
    eapply disjoint_load_bytes_is_None. 1: assumption.
    lazymatch goal with
    | H: map.split _ m _ |- _ => destruct H as (? & D)
    end.
    subst.
    lazymatch goal with
    | H: disjoint (map.domain (map.putmany _ _)) mmio_addrs |- _ =>
        rewrite map.domain_putmany in H; rename H into D2
    end.
    apply disjoint_union_l_iff in D2. destruct D2 as (D2 & D3).
    destruct H0 as [A | A]; (eapply subset_disjoint_r; [exact A | ]).
    1: exact D2.
    eapply map.disjoint_to_domain_disjoint. assumption.
  Qed.

  Lemma subset_footpr_domain: forall (P R: mem -> Prop) m,
      sep P R m ->
      subset (footpr P) (map.domain m).
  Proof.
    clear -mem_ok word_ok.
    unfold sep, subset, footpr, footprint_underapprox, map.domain, elem_of.
    intros. destruct H as (mP & mR & Sp & HP & HR).
    specialize (H0 _ HP). destruct H0 as (v & G).
    eapply map.split_comm in Sp.
    apply proj1 in Sp. subst m. erewrite map.get_putmany_right by exact G.
    discriminate.
  Qed.

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
    destruct_RiscvMachine initialL. subst.
    lazymatch goal with
    | H: ext_spec _ _ _ _ _ |- _ => destruct H as (n & nValid & HExt)
    end.
    destruct HExt; fwd.
    - (* load *)
      destruct argvars as [ |addr_reg argvars]. 1: discriminate Hl.
      destruct argvars. 2: discriminate Hl. clear Hl.
      fwd.
      unfold compile_interact in *. cbn [List.length] in *.
      eapply go_fetch_inst; simpl_MetricRiscvMachine_get_set.
      { reflexivity. }
      { eapply rearrange_footpr_subset. 1: eassumption. wwcancel. }
      { wcancel_assumption. }
      { unfold not_InvalidInstruction, compile_load.
        repeat destruct nValid as [nValid|nValid]; [..|apply proj1 in nValid]; subst n.
        all: try exact I.
        destruct width_cases as [W | W]; rewrite W; exact I. }
      eapply go_ext_call_load.
      { reflexivity. }
      { assumption. }
      { clear -V_resvars.
        destruct resvars.
        - cbv. auto.
        - eapply Forall_inv in V_resvars. cbn.
          unfold valid_FlatImp_var, valid_register in *. lia. }
      { unfold valid_FlatImp_var, valid_register in *. lia. }
      { cbn. unfold map.extends in *. eauto. }
      { cbn. pose_specialized_as read_step_addrs_ok A.
        assert (0 < n)%nat by lia.
        eauto using load_bytes_in_mmio_or_ext_mem_is_None. }
      cbn -[String.append].
      eapply weaken_read_step.
      { (* Note: we need to foresee that we'll need this stronger postcondition of
           read_step later *)
        eapply read_step_returns_owned_mem; eassumption. }
      cbv beta. intros v mRcv HO mL' Hsp.
      destruct HO as (HO & mExt' & HsE).
      lazymatch goal with
      | H: forall _ _, outcome _ _ -> _ |- _ =>
          specialize H with (1 := HO); destruct H as (l' & Hp & HPost)
      end.
      fwd.
      lazymatch goal with
      | H: map.split _ mKeep map.empty |- _ => eapply map.split_empty_r in H; subst mKeep
      end.
      eassert (sep (eq m) _ initialL_mem) as HM by wcancel_assumption.
      pose proof HM as HM'.
      destruct HM' as (mm & mL & D & ? & HmL). subst mm.
      eapply grow_eq_sep in HM. 2: exact Hsp.
      unfold mcomp_sat, Primitives.mcomp_sat, primitivesParams, Bind, free.Monad_free.
      repeat step. unfold goodMachine. cbn -[String.append valid_machine].
      repeat match goal with
             | |- exists _, _  => eexists
             | |- _ /\ _ => split
             end.
      { eapply HPost.
        move D at bottom. move Hsp at bottom.
        unfold map.split in D, Hsp|-*. split. 1: reflexivity.
        apply proj2 in Hsp. destruct D as (? & D). subst initialL_mem.
        eapply map.disjoint_putmany_l in Hsp. apply (proj1 Hsp). }
      { reflexivity. }
      { eapply MapEauto.only_differ_union_l.
        eapply MapEauto.only_differ_put.
        cbn. left. reflexivity. }
      { MetricsToRiscv.solve_MetricLog. }
      { eapply map.put_extends. eassumption. }
      { eapply map.forall_keys_put; assumption. }
      { rewrite map.get_put_diff; eauto. unfold RegisterNames.sp.
        unfold valid_FlatImp_var in *. lia. }
      { eapply regs_initialized.preserve_regs_initialized_after_put. assumption. }
      { reflexivity. }
      { assumption. }
      { reflexivity. }
      { reflexivity. }
      { wcancel_assumption. }
      { reflexivity. }
      { cbn -[String.append].
        split.
        - destruct Hsp as (? & Hsp). subst mL'. rewrite map.domain_putmany.
          eapply subset_union_rl. assumption.
        - eexists. split.
          + eexists. split. 1: eassumption.
            eexists. split. 1: eapply map.split_empty_r; reflexivity.
            exact HsE.
          + repeat match goal with
                   | H: ?T |- _ => lazymatch T with
                                   | map.split _ _ _ => fail
                                   | map.ok _ => fail
                                   | word.ok _ => fail
                                   | disjoint _ _ => fail
                                   | _ => clear H
                                   end
                   end.
            unfold map.split in *.
            repeat match goal with
                   | H: _ /\ _ |- _ => destruct H
                   | |- _ => progress subst
                   | H: map.disjoint (map.putmany _ _) _ |- _ =>
                       eapply map.disjoint_putmany_l in H
                   | H: map.disjoint _ (map.putmany _ _) |- _ =>
                       eapply map.disjoint_putmany_r in H
                   end.
            eexists. ssplit. 1: reflexivity.
            * repeat lazymatch goal with
              | |- map.disjoint (map.putmany _ _) _ => eapply map.disjoint_putmany_l
              | |- map.disjoint _ (map.putmany _ _) => eapply map.disjoint_putmany_r
              | |- _ /\ _ => split
              end.
              all: (idtac + apply map.disjoint_comm); assumption.
            * rewrite ?map.domain_putmany in *.
              match goal with
              | H: disjoint ?s1 mmio_addrs |- disjoint ?s2 mmio_addrs =>
                  replace s2 with s1; [exact H| ]
              end.
              unfold union, elem_of. Import FunctionalExtensionality. extensionality x.
              apply PropExtensionality.propositional_extensionality.
              clear. intuition. }
    - (* store *)
      destruct argvars as [ |addr_reg argvars]. 1: discriminate Hl.
      destruct argvars. 1: discriminate Hl.
      destruct argvars. 2: discriminate Hl. clear Hl.
      fwd.
      unfold compile_interact in *. cbn [List.length] in *.
      eapply go_fetch_inst; simpl_MetricRiscvMachine_get_set.
      { reflexivity. }
      { eapply rearrange_footpr_subset. 1: eassumption. wwcancel. }
      { wcancel_assumption. }
      { unfold not_InvalidInstruction, compile_store.
        repeat destruct nValid as [nValid|nValid]; [..|apply proj1 in nValid]; subst n.
        all: exact I. }
      eassert (sep (eq m) _ initialL_mem) as HM by wcancel_assumption.
      eapply subst_split in HM. 2: eassumption.
      destruct HM as (mH & mL & D & HmH & HM).
      destruct HmH as (mKeep' & mGive' & HmH & ? & ?). subst mGive' mKeep'.
      pose proof (LittleEndian.combine_bound v) as B. rewrite Z.mul_comm in B.
      assert (2 ^ (Z.of_nat n * 8) <= 2 ^ width). {
        destruct width_cases as [W | W]; rewrite W;
          match goal with
          | H: _ |- _ => destruct H as [? | [? | [? | [? ?] ] ] ]; subst n
          end;
          cbv; congruence.
      }
      eapply go_ext_call_store with (mKeep := map.putmany mKeep mL) (mGive := mGive).
      { reflexivity. }
      { assumption. }
      { unfold valid_FlatImp_var, valid_register in *. lia. }
      { unfold valid_FlatImp_var, valid_register in *. lia. }
      { cbn. unfold map.extends in *. eauto. }
      { cbn. unfold map.extends in *. eauto. }
      { rewrite word.unsigned_of_Z_nowrap; lia. }
      { cbn. pose_specialized_as write_step_addrs_ok A.
        assert (0 < n)%nat by lia.
        eauto using load_bytes_in_mmio_or_ext_mem_is_None. }
      { cbn. clear HM.
        unfold map.split in D, HmH|-*.
        destruct D as (? & D1). destruct HmH as (? & D2). subst initialL_mem mH.
        eapply map.disjoint_putmany_l in D1. destruct D1 as (D1a & D1b).
        split.
        - rewrite <-2map.putmany_assoc. f_equal. apply map.putmany_comm. exact D1b.
        - eapply map.disjoint_putmany_l. split. 1: assumption.
          apply map.disjoint_comm. assumption. }
      { cbn. rewrite word.unsigned_of_Z_nowrap by lia.
        replace (LittleEndian.split n (LittleEndian.combine n v)) with v.
        1: assumption. symmetry. apply LittleEndian.split_combine. }
      lazymatch goal with
      | HO: outcome _ _, H: forall _ _, outcome _ _ -> _ |- _ =>
          specialize H with (1 := HO); destruct H as (l' & Hp & HPost)
      end.
      fwd.
      unfold mcomp_sat, Primitives.mcomp_sat, primitivesParams, Bind, free.Monad_free.
      repeat step. unfold goodMachine. cbn -[String.append valid_machine].
      repeat match goal with
             | |- exists _, _  => eexists
             | |- _ /\ _ => split
             end.
      { eapply HPost.
        eapply map.split_empty_r. reflexivity. }
      { reflexivity. }
      { eapply MapEauto.only_differ_refl. }
      { MetricsToRiscv.solve_MetricLog. }
      { eassumption. }
      { assumption. }
      { assumption. }
      { assumption. }
      { reflexivity. }
      { rewrite of_list_list_diff. rewrite of_list_list_union.
        rewrite <- map.domain_is_of_list_keys.
        eapply subset_discard_diff_r. 2: eassumption.
        eapply subset_disjoint_l with (s3 := map.domain mL).
        - eapply subset_footpr_domain. wcancel_assumption.
        - pose_specialized_as write_step_addrs_ok A.
          repeat match goal with
                 | H: ?T |- _ => lazymatch T with
                                 | map.split _ _ _ => fail
                                 | map.ok _ => fail
                                 | word.ok _ => fail
                                 | disjoint _ _ => fail
                                 | subset _ _ \/ subset _ _ => fail
                                 | _ => clear H
                                 end
                 end.
          unfold map.split in *.
          repeat match goal with
                 | H: _ /\ _ |- _ => destruct H
                 | |- _ => progress subst
                 | H: map.disjoint (map.putmany _ _) _ |- _ =>
                     eapply map.disjoint_putmany_l in H
                 | H: map.disjoint _ (map.putmany _ _) |- _ =>
                     eapply map.disjoint_putmany_r in H
                 | H: disjoint (union _ _) _ |- _ =>
                     eapply disjoint_union_l_iff in H
                 | H: disjoint _ (union _ _) |- _ =>
                     eapply disjoint_union_r_iff in H
                 | |- _ => rewrite map.domain_putmany in *
                 end.
          eapply disjoint_union_r_iff. split.
          + destruct A as [A | A].
            * eapply subset_disjoint_r. 1: exact A. assumption.
            * eapply subset_disjoint_r. 1: exact A.
              eapply map.disjoint_to_domain_disjoint. assumption.
          + eapply map.disjoint_to_domain_disjoint. eapply map.disjoint_comm. assumption. }
      { reflexivity. }
      { reflexivity. }
      { eenough (sep (eq mKeep) _ (map.putmany mKeep mL)).
        1: wcancel_assumption.
        do 2 eexists. do 2 split.
        3: reflexivity.
        1: reflexivity.
        2: wcancel_assumption.
        clear -mem_ok word_ok D HmH.
        unfold map.split in *. fwd.
        eapply map.disjoint_putmany_l in Dp1. apply Dp1. }
      { reflexivity. }
      { cbn -[String.append].
        split.
        - pose_specialized_as write_step_addrs_ok A.
          rewrite of_list_list_diff, of_list_list_union.
          rewrite diff_union_r.
          apply subset_union_r_to_diff_l.
          rewrite diff_disjoint_same.
          2: {
            eapply subset_disjoint_l. 1: eassumption.
            lazymatch goal with
            | H: map.split mAll initialL_mem _ |- _ => destruct H as (? & D2)
            end.
            subst mAll.
            rewrite map.domain_putmany in *.
            destruct A as [A | A]; (eapply subset_disjoint_r; [exact A | ]).
            - lazymatch goal with
              | H: disjoint (union _ _) mmio_addrs |- _ => rename H into Dm
              end.
              eapply disjoint_union_l_iff in Dm.
              apply (proj1 Dm).
            - eapply map.disjoint_to_domain_disjoint. assumption. }
          eapply subset_trans. 1: eassumption.
          apply proj1 in D. apply proj1 in HmH. subst initialL_mem mH.
          rewrite ?map.domain_putmany.
          rewrite <- map.domain_is_of_list_keys.
          unfold subset, union, elem_of. clear. intros. intuition.
        - lazymatch goal with
          | H: map.split mAll _ _ |- _ => move H at bottom; rename H into HA
          end.
          eexists. split.
          + eexists. split. 1: eassumption.
            eexists. split.
            * split; [reflexivity | ].
              destruct HA as (? & HA). subst mAll.
              destruct D as (? & D). subst initialL_mem.
              destruct HmH as (? & HmH). subst mH.
              eapply map.disjoint_putmany_l in HA. apply proj1 in HA.
              eapply map.disjoint_putmany_l in HA. apply proj2 in HA.
              apply map.disjoint_comm. exact HA.
            * eapply map.split_empty_r. reflexivity.
          + destruct HA as (? & HA). subst mAll.
            destruct D as (? & D). subst initialL_mem.
            destruct HmH as (? & HmH). subst mH.
            eapply map.disjoint_putmany_l in HA. destruct HA as (HA1 & HA2).
            eapply map.disjoint_putmany_l in HA1. destruct HA1 as (HA1 & HA3).
            eapply map.disjoint_putmany_l in D. destruct D as (D1 & D2).
            eexists. split.
            * split. 1: reflexivity.
              apply map.disjoint_putmany_l; split; apply map.disjoint_putmany_r; split.
              all: (idtac + apply map.disjoint_comm); assumption.
            * lazymatch goal with
              | H: disjoint (map.domain _) mmio_addrs |- _ => rename H into Dm
              end.
              move Dm at bottom.
              rewrite ?map.domain_putmany in *.
              match goal with
              | H: disjoint ?s1 mmio_addrs |- disjoint ?s2 mmio_addrs =>
                  replace s2 with s1; [exact H| ]
              end.
              unfold union, elem_of.
              extensionality x.
              apply PropExtensionality.propositional_extensionality.
              clear. intuition. }
  Qed.

End MMIO.
