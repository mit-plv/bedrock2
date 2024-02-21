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
Require Import coqutil.Datatypes.ListSet.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.fwd.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

(* TODO move *)
Module map.
  Section WithMap.
    Context {key value} {map: map.map key value}.

    Definition domain(m: map): PropSet.set key := fun k => map.get m k <> None.

    Definition range(m: map): PropSet.set value := fun v => exists k, map.get m k = Some v.

    Context {ok: map.ok map}.
    Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.

    Lemma disjoint_from_domain_disjoint: forall m1 m2,
        PropSet.disjoint (domain m1) (domain m2) ->
        map.disjoint m1 m2.
    Proof.
      unfold PropSet.disjoint, map.disjoint, domain, PropSet.elem_of.
      intros.
      specialize (H k). destruct H as [H | H]; apply H; congruence.
    Qed.

    Lemma domain_putmany: forall m1 m2,
        domain (map.putmany m1 m2) = PropSet.union (domain m1) (domain m2).
    Proof.
      intros.
      extensionality k. eapply PropExtensionality.propositional_extensionality.
      unfold domain, PropSet.union, PropSet.elem_of.
      split; intros.
      - rewrite map.get_putmany_dec in H. destruct_one_match_hyp.
        + right. congruence.
        + left. assumption.
      - rewrite map.get_putmany_dec. destruct H; destruct_one_match; congruence.
    Qed.

  End WithMap.
End map.

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
      PropSet.disjoint (map.domain mach.(getMem)) (ext_call_addrs mach.(getLog));
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

  Axiom read_step_nonempty: forall n t a post,
      read_step n t a post -> exists v mRcv, post v mRcv.

  Axiom read_step_returns_owned_mem: forall n t a post,
      read_step n t a post ->
      exists m, externally_owned_mem t m /\
                read_step n t a (fun v mRcv => post v mRcv /\
                                               exists m', map.split m m' mRcv).

  Lemma shared_mem_addrs_to_ext_owned_domain{mem_ok: map.ok mem}: forall t m,
      externally_owned_mem t m -> shared_mem_addrs t = map.domain m.
  Proof.
    unfold shared_mem_addrs, map.domain. intros.
    extensionality addr. eapply PropExtensionality.propositional_extensionality.
    split; intros; fwd.
    - pose proof (externally_owned_mem_unique _ _ _ H H0p0). subst mShared. assumption.
    - eauto.
  Qed.

  Lemma ext_call_addrs_cons: forall mGive mRcv a args rets t,
      ext_call_addrs (cons ((mGive, a, args), (mRcv, rets)) t) =
      PropSet.diff (PropSet.union (map.domain mGive) (ext_call_addrs t)) (map.domain mRcv).
  Proof.
    unfold ext_call_addrs, shared_mem_addrs, PropSet.union, PropSet.diff, PropSet.elem_of.
    intros.
    extensionality addr. eapply PropExtensionality.propositional_extensionality.
    split; intros.
    - destruct H as [H | H].
      + split.
        * right. left. assumption.
        *
  Abort.

  Lemma load_total{mem_ok: map.ok mem} n k a (mach: RiscvMachine) post mc':
    PropSet.subset (PropSet.of_list mach.(getXAddrs)) (map.domain mach.(getMem)) ->
    PropSet.disjoint (map.domain mach.(getMem)) (ext_call_addrs mach.(getLog)) ->
    load n k a mach (fun (v: HList.tuple byte n) (mach': RiscvMachine) =>
          post v {| getMachine := mach'; getMetrics := mc' |}) ->
    exists v (mach': MetricRiscvMachine), post v mach' /\
      PropSet.subset (PropSet.of_list mach'.(getXAddrs)) (map.domain mach'.(getMem)) /\
      PropSet.disjoint (map.domain mach'.(getMem)) (ext_call_addrs mach'.(getLog)).
  Proof.
    intros HS HD HI.
    unfold load in HI. destruct HI as (HF & HI). destruct_one_match_hyp. 1: eauto.
    unfold nonmem_load in HI.
    eapply read_step_returns_owned_mem in HI. destruct HI as (m & EO & HI).
    pose proof (read_step_nonempty _ _ _ _ HI) as P.
    destruct P as (v & mRcv & (N1 & N2)).
    destruct N2 as (m' & Sp).
    destruct mach.
    eexists. eexists (mkMetricRiscvMachine (mkRiscvMachine _ _ _ _ _ _) _).
    cbn -[HList.tuple String.append] in *.
    ssplit.
    - eapply N1. clear N1 HI.
      unfold map.split. split. 1: reflexivity.
      unfold ext_call_addrs in HD.
      eapply PropSet.disjoint_union_r_iff in HD. apply proj2 in HD.
      erewrite shared_mem_addrs_to_ext_owned_domain in HD by eassumption.
      eapply map.shrink_disjoint_r.
      2: { eapply map.split_comm. exact Sp. }
      eapply map.disjoint_from_domain_disjoint.
      assumption.
    - rewrite map.domain_putmany.
      eapply PropSet.subset_union_rl.
      exact HS.
    - rewrite map.domain_putmany.
      clear N1 HI.
      eapply PropSet.disjoint_union_l_iff. split.
  Admitted.

  Lemma store_total{mem_ok: map.ok mem} n k a val (mach: RiscvMachine) post mc' :
    PropSet.subset (PropSet.of_list mach.(getXAddrs)) (map.domain mach.(getMem)) ->
    PropSet.disjoint (map.domain mach.(getMem)) (ext_call_addrs mach.(getLog)) ->
    store n k a val mach (fun (mach': RiscvMachine) =>
          post {| getMachine := mach'; getMetrics := mc' |}) ->
    exists (mach': MetricRiscvMachine), post mach' /\
      PropSet.subset (PropSet.of_list mach'.(getXAddrs)) (map.domain mach'.(getMem)) /\
      PropSet.disjoint (map.domain mach'.(getMem)) (ext_call_addrs mach'.(getLog)).
  Proof.
    intros HS HD HI.
  Admitted.

  Lemma interp_action_total{mem_ok: map.ok mem} a (mach: MetricRiscvMachine) post :
    PropSet.subset (PropSet.of_list mach.(getXAddrs)) (map.domain mach.(getMem)) ->
    PropSet.disjoint (map.domain mach.(getMem)) (ext_call_addrs mach.(getLog)) ->
    interp_action a mach post ->
    exists v (mach': MetricRiscvMachine), post v mach' /\
      PropSet.subset (PropSet.of_list mach'.(getXAddrs)) (map.domain mach'.(getMem)) /\
      PropSet.disjoint (map.domain mach'.(getMem)) (ext_call_addrs mach'.(getLog)).
  Proof.
    intros HS HD HI.
    only_destruct_RiscvMachine mach. cbn -[HList.tuple] in *.
    destruct a as (f & p). destruct p; cbn -[HList.tuple] in *;
    repeat destruct_one_match;
    try solve [intuition eauto using load_total, store_total].
    1-4: eapply load_total; try eassumption; eassumption.
    all: exists tt; eapply store_total; try eassumption; eassumption.
  Qed.

(*
  Lemma interp_action_preserves_valid{memOk: map.ok Mem} a s post :
    map.undef_on s.(getMachine).(getMem) isMMIOAddr ->
    PropSet.disjoint (PropSet.of_list s.(getMachine).(getXAddrs)) isMMIOAddr ->
    interp_action a s post ->
    interp_action a s (fun v s' =>
        post v s' /\
        map.undef_on s'.(getMem) isMMIOAddr /\
        PropSet.disjoint (PropSet.of_list s'.(getMachine).(getXAddrs)) isMMIOAddr).
  Proof.
    intros U D I.
    unshelve epose proof (MinimalMMIO.interpret_action_preserves_valid' _ _ _ U D I) as H0; eauto.
  Qed.
*)
  Lemma interp_action_appendonly' a s post :
    interp_action a s post ->
    interp_action a s (fun v s' => post v s' /\ List.endswith s'.(getLog) s.(getLog)).
  Proof. Admitted. (*eapply interpret_action_appendonly''; eauto. Qed.*)

  Global Instance primitivesSane{mem_ok: map.ok mem}: MetricPrimitivesSane primitivesParams.
  Proof.
    split; cbv [mcomp_sane valid_machine primitivesParams].
(*
      intros *; intros [U D] M;
      (split; [ exact (interp_action_total _ st _ U D M)
              | eapply interp_action_preserves_valid; try eassumption;
                eapply interp_action_appendonly'; try eassumption ]).
  Qed.
*)
  Admitted.

  (* TODO move *)
  Lemma removeb_list_diff_comm{A: Type}{aeqb: A -> A -> bool}{aeq_dec: EqDecider aeqb}:
    forall l r rs,
      List.removeb aeqb r (list_diff aeqb l rs) =
      list_diff aeqb (List.removeb aeqb r l) rs.
  Proof.
    induction l; intros.
    - simpl. rewrite list_diff_empty_l. reflexivity.
    - simpl. rewrite list_diff_cons.
      destr (aeqb r a); simpl; destr (find (aeqb a) rs).
      + apply IHl.
      + simpl. destr (aeqb a a). 2: congruence. simpl. apply IHl.
      + rewrite list_diff_cons. rewrite E0. apply IHl.
      + simpl. destr (negb (aeqb r a)). 2: congruence. rewrite list_diff_cons.
        rewrite E0. f_equal. apply IHl.
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

  Global Instance primitivesParams_ok{mem_ok: map.ok mem}:
    MetricPrimitives primitivesParams.
  Proof.
    split; try exact _.
    all: cbv [mcomp_sat spec_load spec_store primitivesParams].
    all: intros; destruct initialL.
    all: repeat t.
    { destruct getMachine; eassumption. }
  Qed.

End Riscv.
