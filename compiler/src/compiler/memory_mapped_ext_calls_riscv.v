(* Based on riscv.Platform.MinimalMMIO and riscv.Platform.MetricMinimalMMIO,
   but with a different nonmem_load and nonmem_store *)

Require Import Coq.Strings.String.
Require coqutil.Datatypes.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import bedrock2.memory_mapped_ext_spec. (* import this early because bedrock2.Memory.load_bytes vs riscv.Platform.Memory.load_bytes *)
Require Import bedrock2.TraceInspection.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Utility.FreeMonad.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.MetricPrimitives.
Require Import Coq.Lists.List. Import ListNotations.
Require Export riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MaterializeRiscvProgram.
Require Export riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MetricLogging.
Require Export riscv.Platform.MetricMaterializeRiscvProgram.
Require Import coqutil.Map.Domain.
Require Import coqutil.Datatypes.ListSet.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.fwd.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* TODO move *)
Section split_mcomp_sane.

  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {Registers: map.map Register word}.
  Context {mem: map.map word byte}.

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgramWithLeakage M word}.
  Context {RVS: @Spec.Machine.RiscvMachine M word _ _ RVM}.
  Context {p: PrimitivesParams M MetricRiscvMachine}.

  Definition mcomp_nonempty{A: Type}(comp: M A): Prop :=
    forall (st: MetricRiscvMachine) (post: A -> MetricRiscvMachine -> Prop),
      valid_machine st ->
      mcomp_sat comp st post ->
      exists a st', post a st'.

  Definition mcomp_preserves_valid{A: Type}(comp: M A): Prop :=
    forall (st: MetricRiscvMachine) (post: A -> MetricRiscvMachine -> Prop),
      valid_machine st ->
      mcomp_sat comp st post ->
      mcomp_sat comp st (fun a st' => post a st' /\ valid_machine st').

  Definition mcomp_append_only{A: Type}(comp: M A): Prop :=
    forall (st: MetricRiscvMachine) (post: A -> MetricRiscvMachine -> Prop),
      valid_machine st ->
      mcomp_sat comp st post ->
      mcomp_sat comp st (fun a st' => post a st' /\ List.endswith st'.(getLog) st.(getLog)).

  Lemma build_mcomp_sane{A: Type}(comp: M A):
    mcomp_nonempty comp ->
    mcomp_preserves_valid comp ->
    mcomp_append_only comp ->
    mcomp_sane comp.
  Proof.
    unfold mcomp_nonempty, mcomp_preserves_valid, mcomp_append_only, mcomp_sane.
    intros NE PR AP. intros *. intros V C.
    split.
    - specialize PR with (1 := V) (2 := C).
      specialize NE with (1 := V) (2 := PR). cbv beta in NE.
      exact NE.
    - eapply PR. 1: exact V.
      eapply AP. 1: exact V.
      exact C.
  Qed.
End split_mcomp_sane.

Section Riscv.
  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {mem: map.map word byte} {Registers: map.map Register word}.
  Context {ext_calls: MemoryMappedExtCalls}.

  Import free.
  Import riscv.Platform.RiscvMachine.
  Local Open Scope string_scope. Local Open Scope Z_scope.

  Definition nonmem_load(n: nat)(kind: SourceType)(addr: word)(mach: RiscvMachine)
                        (post: HList.tuple byte n -> RiscvMachine -> Prop) :=
    let action := "memory_mapped_extcall_read" ++ String.of_nat (n * 8) in
    read_step n (getLog mach) addr (fun v mRcv =>
      forall m', map.split m' (getMem mach) mRcv ->
      post v
           (withLogItem ((map.empty, action, [addr]),
                         (mRcv, [word.of_Z (LittleEndian.combine n v)]))
           (withMem m' mach))).

  Definition load(n: nat)(ctxid: SourceType) a mach post :=
    (ctxid = Fetch -> isXAddr4 a mach.(getXAddrs)) /\
    match Memory.load_bytes n mach.(getMem) a with
    | Some v => post v mach
    | None => nonmem_load n ctxid a mach post
    end.

  Definition nonmem_store(n: nat)(ctxid: SourceType)(addr: word)(v: HList.tuple byte n)
                         (mach: RiscvMachine)(post: RiscvMachine -> Prop) :=
    let action := "memory_mapped_extcall_write" ++ String.of_nat (n * 8) in
    exists mKeep mGive, map.split (getMem mach) mKeep mGive /\
    write_step n (getLog mach) addr v mGive /\
    let invalidated := list_union word.eqb (footprint_list addr n) (map.keys mGive) in
    post (withXAddrs (list_diff word.eqb mach.(getXAddrs) invalidated)
         (withLogItem ((mGive, action, [addr; word.of_Z (LittleEndian.combine n v)]),
                       (map.empty, []))
         (withMem mKeep mach))).

  Definition store(n: nat)(ctxid: SourceType) a v mach post :=
    match Memory.store_bytes n mach.(getMem) a v with
    | Some m => post (withXAddrs (list_diff word.eqb mach.(getXAddrs) (footprint_list a n))
                        (withMem m mach))
    | None => nonmem_store n ctxid a v mach post
    end.

  Definition updatePc(mach: RiscvMachine): RiscvMachine :=
    withPc mach.(getNextPc) (withNextPc (word.add mach.(getNextPc) (word.of_Z 4)) mach).

  Definition getReg(regs: Registers)(reg: Z): word :=
    if ((0 <? reg) && (reg <? 32)) then
      match map.get regs reg with
      | Some x => x
      | None => word.of_Z 0
      end
    else word.of_Z 0.

  Definition setReg(reg: Z)(v: word)(regs: Registers): Registers :=
    if ((0 <? reg) && (reg <? 32)) then map.put regs reg v else regs.
  Print riscv_primitive.

  Definition interpret_action (a : riscv_primitive) (mach : RiscvMachine) :
    (primitive_result a -> RiscvMachine -> Prop) -> (RiscvMachine -> Prop) -> Prop :=
    match a with
    | GetRegister reg => fun (postF: word -> RiscvMachine -> Prop) postA =>
        let v := getReg mach.(getRegs) reg in
        postF v mach
    | SetRegister reg v => fun postF postA =>
        let regs := setReg reg v mach.(getRegs) in
        postF tt (withRegs regs mach)
    | GetPC => fun postF postA => postF mach.(getPc) mach
    | SetPC newPC => fun postF postA => postF tt (withNextPc newPC mach)
    | LoadByte ctxid a => fun postF postA => load 1 ctxid a mach postF
    | LoadHalf ctxid a => fun postF postA => load 2 ctxid a mach postF
    | LoadWord ctxid a => fun postF postA => load 4 ctxid a mach postF
    | LoadDouble ctxid a => fun postF postA => load 8 ctxid a mach postF
    | StoreByte ctxid a v => fun postF postA => store 1 ctxid a v mach (postF tt)
    | StoreHalf ctxid a v => fun postF postA => store 2 ctxid a v mach (postF tt)
    | StoreWord ctxid a v => fun postF postA => store 4 ctxid a v mach (postF tt)
    | StoreDouble ctxid a v => fun postF postA => store 8 ctxid a v mach (postF tt)
    | StartCycle => fun postF postA =>
        postF tt (withNextPc (word.add mach.(getPc) (word.of_Z 4)) mach)
    | EndCycleNormal => fun postF postA => postF tt (updatePc mach)
    | EndCycleEarly _ => fun postF postA => postA (updatePc mach) (* ignores postF containing the continuation *)
    | LeakEvent e => fun postF postA => postF tt (withLeakageEvent e mach)
    | MakeReservation _
    | ClearReservation _
    | CheckReservation _
    | GetCSRField _
    | SetCSRField _ _
    | GetPrivMode
    | SetPrivMode _
    | Fence _ _
        => fun postF postA => False
    end.

  Context {ext_calls_ok: MemoryMappedExtCallsOk ext_calls}.

  Lemma load_weaken_post n c a m (post1 post2:_->_->Prop)
    (H: forall r s, post1 r s -> post2 r s)
    : load n c a m post1 -> load n c a m post2.
  Proof.
    cbv [load nonmem_load].
    destruct (Memory.load_bytes n (getMem m) a).
    - intuition eauto.
    - intros. fwd. eauto using weaken_read_step.
  Qed.

  Lemma store_weaken_post n c a v m (post1 post2:_->Prop)
    (H: forall s, post1 s -> post2 s)
    : store n c a v m post1 -> store n c a v m post2.
  Proof.
    cbv [store nonmem_store].
    destruct (Memory.store_bytes n (getMem m) a).
    - eauto.
    - intros. fwd. eauto 10.
  Qed.

  Lemma interpret_action_weaken_post a (postF1 postF2: _ -> _ -> Prop) (postA1 postA2: _ -> Prop):
    (forall r s, postF1 r s -> postF2 r s) ->
    (forall s, postA1 s -> postA2 s) ->
    forall s, interpret_action a s postF1 postA1 -> interpret_action a s postF2 postA2.
  Proof.
    destruct a; cbn; try solve [intuition eauto].
    all : eauto using load_weaken_post, store_weaken_post.
  Qed.

  Definition interp_action(a: (MetricLog -> MetricLog) * riscv_primitive)
                          (metmach: MetricRiscvMachine)
                          (post : primitive_result (snd a) -> MetricRiscvMachine -> Prop) :=
    interpret_action (snd a) (metmach.(getMachine)) (fun r mach =>
      post r (mkMetricRiscvMachine mach (fst a (metmach.(getMetrics))))) (fun _ => False).

  Lemma interp_action_bind[A B: Type]: forall m (f: A -> free action result B) s post,
      interp interp_action m s (fun b s' => interp interp_action (f b) s' post) ->
      interp interp_action (bind m f) s post.
  Proof.
    intros.
    eapply free.interp_bind_ex_mid; intros.
    { eapply interpret_action_weaken_post; eauto; cbn; eauto. }
    eexists. split. 1: exact H.
    cbv beta. intros. assumption.
  Qed.

  Arguments Memory.load_bytes: simpl never.
  Arguments Memory.store_bytes: simpl never.
  Arguments LittleEndian.combine: simpl never.

  Global Instance primitivesParams:
    PrimitivesParams (free action result) MetricRiscvMachine :=
  {
    Primitives.mcomp_sat := @free.interp _ _ _ interp_action;
    Primitives.is_initial_register_value x := True;
    Primitives.nonmem_load := nonmem_load;
    Primitives.nonmem_store := nonmem_store;
    Primitives.valid_machine mach :=
      PropSet.subset (PropSet.of_list mach.(getXAddrs)) (map.domain mach.(getMem)) /\
      exists mExt, externally_owned_mem mach.(getLog) mExt /\
      exists mAll, map.split mAll mach.(getMem) mExt /\
      PropSet.disjoint (map.domain mAll) mmio_addrs;
  }.

  Global Instance satisfies_mcomp_sat_spec: mcomp_sat_spec primitivesParams.
  Proof.
    split; cbv [mcomp_sat primitivesParams free.Monad_free Bind Return].
    { symmetry. eapply free.interp_bind_ex_mid; intros.
      eapply interpret_action_weaken_post; eauto; cbn; eauto. }
    { symmetry. rewrite free.interp_ret; eapply iff_refl. }
  Qed.

  Lemma interp_action_weaken_post a (post1 post2:_->_->Prop)
    (H: forall r s, post1 r s -> post2 r s) s
    : interp_action a s post1 -> interp_action a s post2.
  Proof. eapply interpret_action_weaken_post; eauto. Qed.

  Context {mem_ok: map.ok mem}.

  Lemma load_nonempty n k a (mach: RiscvMachine) post mc mc':
    valid_machine {| getMachine := mach; getMetrics := mc |} ->
    load n k a mach (fun (v: HList.tuple byte n) (mach': RiscvMachine) =>
          post v {| getMachine := mach'; getMetrics := mc' |}) ->
    exists v (mach': MetricRiscvMachine), post v mach'.
  Proof.
    unfold valid_machine, primitivesParams.
    intros (HS & mExt & HO & mAll & HA & DM) HI.
    unfold load in HI. destruct HI as (HF & HI). destruct_one_match_hyp. 1: eauto.
    unfold nonmem_load in HI.
    eapply read_step_returns_owned_mem in HI. 2: exact HO.
    pose proof (read_step_nonempty _ _ _ _ HI) as P.
    destruct P as (v & mRcv & (N1 & N2)).
    destruct N2 as (mExt' & Sp).
    destruct mach.
    eexists. eexists (mkMetricRiscvMachine (mkRiscvMachine _ _ _ _ _ _ _) _).
    cbn -[HList.tuple String.append] in *.
    eapply N1. clear N1 HI.
    unfold map.split. split. 1: reflexivity.
    unfold map.split in Sp. destruct Sp as (? & D). subst mExt.
    apply proj2 in HA. eapply map.disjoint_putmany_r in HA. apply (proj2 HA).
  Qed.

  Lemma store_nonempty n k a val (mach: RiscvMachine) post mc mc' :
    valid_machine {| getMachine := mach; getMetrics := mc |} ->
    store n k a val mach (fun (mach': RiscvMachine) =>
          post {| getMachine := mach'; getMetrics := mc' |}) ->
    exists (mach': MetricRiscvMachine), post mach'.
  Proof.
    unfold valid_machine, primitivesParams.
    intros (HS & HD & (mExt & HO & DE)) HI.
    unfold store in HI. destruct_one_match_hyp. 1: eauto.
    unfold nonmem_store in HI. fwd. eauto.
  Qed.

  Lemma interp_action_nonempty: forall (a: (MetricLog -> MetricLog) * riscv_primitive),
      mcomp_nonempty (act a ret).
  Proof.
    unfold mcomp_nonempty, mcomp_sat. cbn -[valid_machine].
    intros. destruct a as (f & p). destruct st as (mach & mc).
    destruct p; cbn -[valid_machine HList.tuple] in *;
    repeat destruct_one_match;
    try solve [intuition eauto].
    1-4: eapply load_nonempty; eassumption.
    all: exists tt; eapply store_nonempty; eassumption.
  Qed.

  Lemma load_preserves_valid n k a (mach: RiscvMachine) post mc mc':
    valid_machine {| getMachine := mach; getMetrics := mc |} ->
    load n k a mach (fun (v: HList.tuple byte n) (mach': RiscvMachine) =>
          post v {| getMachine := mach'; getMetrics := mc' |}) ->
    load n k a mach (fun (v: HList.tuple byte n) (mach': RiscvMachine) =>
          post v {| getMachine := mach'; getMetrics := mc' |} /\
          valid_machine {| getMachine := mach'; getMetrics := mc' |}).
  Proof.
    unfold valid_machine, primitivesParams.
    intros (HS & mExt & HO & mAll & HA & DM) HI.
    unfold load in *. destruct HI as (HF & HI). split. 1: assumption.
    destruct mach.
    cbn -[HList.tuple String.append] in *.
    destruct_one_match. 1: eauto 10.
    unfold nonmem_load in *.
    cbn -[HList.tuple String.append] in *.
    eapply read_step_returns_owned_mem in HI. 2: exact HO.
    eapply weaken_read_step. 1: exact HI. clear HI. cbv beta. intros. fwd.
    rename mExt' into mExtNew.
    split. 1: solve [eauto].
    clear Hp0. unfold map.split in H0. destruct H0 as (? & D). subst m'.
    rewrite map.domain_putmany.
    split.
    - eapply PropSet.subset_trans. 1: eassumption.
      eapply PropSet.subset_union_rl.
      eapply PropSet.subset_refl.
    - eexists. split.
      + eexists. split. 1: exact HO.
        eexists. split. 1: eapply map.split_empty_r; reflexivity. eassumption.
      + unfold map.split in *. destruct HA as (? & HA). destruct Hp1 as (? & D1).
        subst.
        eexists. ssplit. 1: reflexivity.
        * eapply map.disjoint_putmany_l.
          eapply map.disjoint_putmany_r in HA. destruct HA as (HA1 & HA2).
          split. 2: eapply map.disjoint_comm. 1-2: assumption.
        * eapply PropSet.disjoint_sameset. 2: eassumption.
          rewrite ?map.domain_putmany.
          unfold PropSet.sameset.
          split;
            repeat apply PropSet.subset_union_l;
            eauto using PropSet.subset_union_rl, PropSet.subset_union_rr,
                        PropSet.subset_refl.
  Qed.

  Lemma store_preserves_valid n k a val (mach: RiscvMachine) post mc mc' :
    valid_machine {| getMachine := mach; getMetrics := mc |} ->
    store n k a val mach (fun (mach': RiscvMachine) =>
          post {| getMachine := mach'; getMetrics := mc' |}) ->
    store n k a val mach (fun (mach': RiscvMachine) =>
          post {| getMachine := mach'; getMetrics := mc' |} /\
          valid_machine {| getMachine := mach'; getMetrics := mc' |}).
  Proof.
    unfold valid_machine, primitivesParams.
    intros (HS & mExt & HO & mAll & HA & DM) HI.
    unfold store in *. destruct mach. cbn -[HList.tuple String.append] in *.
    destruct_one_match.
    - split. 1: assumption.
      clear HI.
      eapply Memory.store_bytes_preserves_domain in E.
      eapply map.same_domain_alt in E.
      split.
      + rewrite <- E. eapply PropSet.subset_trans. 2: eassumption. apply subset_of_list_diff.
      + eexists. split. 1: eassumption. eexists. split.
        * unfold map.split in *. split. 1: reflexivity.
          apply map.disjoint_from_domain_disjoint.
          apply proj2 in HA.
          apply map.disjoint_to_domain_disjoint in HA.
          rewrite <- E. exact HA.
        * unfold map.split in HA. apply proj1 in HA. subst mAll.
          rewrite map.domain_putmany in *. rewrite <- E. exact DM.
    - cbv [nonmem_store] in *. cbn -[HList.tuple String.append] in *.
      destruct HI as (mKeep & mGive & Sp & W & P).
      do 2 eexists. ssplit; try eassumption; clear P.
      + rewrite of_list_list_diff, of_list_list_union.
        destruct Sp as (? & Sp). subst getMem.
        rewrite map.domain_putmany in HS.
        rewrite <- map.domain_is_of_list_keys.
        clear -HS mem_ok.
        forget (PropSet.of_list getXAddrs) as X.
        forget (PropSet.of_list (footprint_list a n)) as F.
        forget (map.domain mKeep) as K.
        forget (map.domain mGive) as G.
        unfold PropSet.subset, PropSet.union, PropSet.diff, PropSet.elem_of,
          PropSet.set in *.
        forget (@word.rep _ word) as T. clear -HS. firstorder.
      + unfold map.split in *. destruct HA as (? & HA). destruct Sp as (? & Sp). subst.
        eexists. split.
        * eexists. split. 1: eassumption. eexists. split.
          2: eapply map.split_empty_r; reflexivity.
          unfold map.split. split. 1: reflexivity.
          eapply map.disjoint_putmany_l in HA. apply proj2 in HA.
          apply map.disjoint_comm. exact HA.
        * eexists. split.
          -- unfold map.split. split. 1: reflexivity.
             eapply map.disjoint_putmany_l in HA. destruct HA as (HA1 & HA2).
             eapply map.disjoint_putmany_r. split. 1: exact HA1. exact Sp.
          -- rewrite ?map.domain_putmany in *.
             match goal with
             | H: PropSet.disjoint ?s1 mmio_addrs |- PropSet.disjoint ?s2 mmio_addrs =>
                 replace s2 with s1; [exact H | ]
             end.
             clear.
             unfold PropSet.subset, PropSet.union, PropSet.elem_of, PropSet.set in *.
             extensionality k. eapply PropExtensionality.propositional_extensionality.
             intuition.
  Qed.

  Lemma interp_action_preserves_valid:
    forall (a: (MetricLog -> MetricLog) * riscv_primitive),
      mcomp_preserves_valid (act a ret).
  Proof.
    unfold mcomp_preserves_valid, mcomp_sat. cbn -[valid_machine].
    intros. destruct a as (f & p). destruct st as [ [ ] ].
    destruct p; cbn -[valid_machine HList.tuple] in *;
    repeat destruct_one_match;
    try solve [intuition eauto].
    1-4: eapply load_preserves_valid; eassumption.
    all: eapply store_preserves_valid; eassumption.
  Qed.

  Lemma interp_action_append_only:
    forall (a: (MetricLog -> MetricLog) * riscv_primitive), mcomp_append_only (act a ret).
  Proof.
    destruct a as (f & p). unfold mcomp_append_only.
    intros [ [ ] ] post V M; destruct p;
      cbn -[footprint_list HList.tuple] in *;
      cbv [load store nonmem_load nonmem_store] in *;
      cbn -[footprint_list HList.tuple] in *;
      repeat destruct_one_match;
      fwd;
      intuition eauto 10 using weaken_read_step, List.endswith_refl, List.endswith_cons_l.
  Qed.

  Global Instance primitivesSane: MetricPrimitivesSane primitivesParams.
  Proof.
    split; intros; eapply build_mcomp_sane; simpl;
      match goal with
      | |- mcomp_nonempty (act ?a ret) => eapply (interp_action_nonempty a)
      | |- mcomp_preserves_valid (act ?a ret) => eapply (interp_action_preserves_valid a)
      | |- mcomp_append_only (act ?a ret) => eapply (interp_action_append_only a)
      end.
  Qed.

  Lemma invalidateWrittenXAddrs_alt: forall n (a: word) xaddrs,
      invalidateWrittenXAddrs n a xaddrs = list_diff word.eqb xaddrs (footprint_list a n).
  Proof.
    induction n; intros.
    - reflexivity.
    - simpl. change (removeXAddr ?a ?l) with (List.removeb word.eqb a l).
      rewrite IHn. rewrite (word.add_comm (word.of_Z 1)).
      apply removeb_list_diff_comm.
  Qed.

  Ltac t :=
    match goal with
    | _ => progress subst
    | _ => progress fwd_step
    | _ => progress cbn -[Platform.Memory.load_bytes Platform.Memory.store_bytes
                          HList.tuple invalidateWrittenXAddrs footprint_list
                          LittleEndian.split_deprecated] in *
    | _ => progress cbv
             [id valid_register is_initial_register_value load store
                Platform.Memory.loadByte Platform.Memory.loadHalf
                Platform.Memory.loadWord Platform.Memory.loadDouble
                Platform.Memory.storeByte Platform.Memory.storeHalf
                Platform.Memory.storeWord Platform.Memory.storeDouble] in *
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | |- _ => rewrite <- invalidateWrittenXAddrs_alt
    | |- _ => solve [ intuition (eauto || blia) ]
    | H : _ \/ _ |- _ => destruct H
    | |- context[match ?x with _ => _ end] => destruct x eqn:?
    | |- _ => progress unfold getReg, setReg
    | |-_ /\ _ => split
    end.

  Global Instance primitivesParams_ok: MetricPrimitives primitivesParams.
  Proof.
    split; try exact _.
    all: cbv [mcomp_sat spec_load spec_store primitivesParams].
    all: intros; destruct initialL.
    all: repeat t.
    { destruct getMachine; eassumption. }
  Qed.

End Riscv.
