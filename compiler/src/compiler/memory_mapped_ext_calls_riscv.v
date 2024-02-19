(* Based on riscv.Platform.MinimalMMIO and riscv.Platform.MetricMinimalMMIO,
   but with a different nonmem_load and nonmem_store *)

Require Import Coq.Strings.String.
Require coqutil.Datatypes.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import bedrock2.Semantics. (* For ext_spec. Import this early because bedrock2.Memory.load_bytes vs riscv.Platform.Memory.load_bytes *)
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
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.fwd.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section Riscv.
  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {mem: map.map word byte} {Registers: map.map Register word}.
  Context {ext_spec: ExtSpec}.

  Import free.
  Import riscv.Platform.RiscvMachine.
  Local Open Scope string_scope. Local Open Scope Z_scope.

  Definition nonmem_load(n: nat)(kind: SourceType)(addr: word)(mach: RiscvMachine)
                        (post: HList.tuple byte n -> RiscvMachine -> Prop) :=
    let mGive := map.empty in
    let action := "memory_mapped_extcall_read" ++ String.of_nat (n * 8) in
    ext_spec (getLog mach) mGive action [addr] (fun mRcv retvals =>
      exists v, retvals = [v] /\
      forall m', map.split m' (getMem mach) mRcv ->
      post (LittleEndian.split n (word.signed v))
           (withLogItem ((mGive, action, [addr]), (mRcv, [v])) (withMem m' mach))).

  Definition load(n: nat)(ctxid: SourceType) a mach post :=
    (ctxid = Fetch -> isXAddr4 a mach.(getXAddrs)) /\
    match Memory.load_bytes n mach.(getMem) a with
    | Some v => post v mach
    | None => nonmem_load n ctxid a mach post
    end.

  Definition nonmem_store(n: nat)(ctxid: SourceType)(addr: word)(val: HList.tuple byte n)
                         (mach: RiscvMachine)(post: RiscvMachine -> Prop) :=
    exists mKeep mGive, map.split (getMem mach) mKeep mGive /\
    exists v: word, LittleEndian.split n (word.signed v) = val /\
    let action := "memory_mapped_extcall_write" ++ String.of_nat (n * 8) in
    ext_spec (getLog mach) mGive action [addr; v]
      (fun mRcv retvals => mRcv = map.empty /\ retvals = []) /\
    post (withXAddrs (invalidateWrittenXAddrs n addr mach.(getXAddrs))
         (withLogItem ((mGive, action, [addr; v]), (map.empty, []))
         (withMem mKeep mach))).

  Definition store(n: nat)(ctxid: SourceType) a v mach post :=
    match Memory.store_bytes n mach.(getMem) a v with
    | Some m => post (withXAddrs (invalidateWrittenXAddrs n a mach.(getXAddrs))
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

  Context {ext_spec_ok: ext_spec.ok ext_spec}.

  Lemma load_weaken_post n c a m (post1 post2:_->_->Prop)
    (H: forall r s, post1 r s -> post2 r s)
    : load n c a m post1 -> load n c a m post2.
  Proof.
    cbv [load nonmem_load].
    destruct (Memory.load_bytes n (getMem m) a); intuition eauto.
    eapply ext_spec.weaken. 2: eassumption.
    unfold Morphisms.Proper, Morphisms.respectful, Morphisms.pointwise_relation, Basics.impl.
    clear -H. intros. fwd. eauto.
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

  Arguments Memory.load_bytes: simpl never.
  Arguments Memory.store_bytes: simpl never.
  Arguments LittleEndian.combine: simpl never.

  Axiom TODO_valid_machine_and_isMMIOAddr: Prop.

  Global Instance primitivesParams:
    PrimitivesParams (free action result) MetricRiscvMachine :=
  {
    Primitives.mcomp_sat := @free.interp _ _ _ interp_action;
    Primitives.is_initial_register_value x := True;
    Primitives.nonmem_load := nonmem_load;
    Primitives.nonmem_store := nonmem_store;
    Primitives.valid_machine mach := TODO_valid_machine_and_isMMIOAddr;
(*    map.undef_on mach.(getMem) isMMIOAddr /\
      PropSet.disjoint (PropSet.of_list mach.(getXAddrs)) isMMIOAddr; *)
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
  Lemma interp_action_appendonly' a s post :
    interp_action a s post ->
    interp_action a s (fun v s' => post v s' /\ List.endswith s'.(getLog) s.(getLog)).
  Proof. Admitted. (*eapply interpret_action_appendonly''; eauto. Qed.*)
(*
  Lemma interp_action_total{mem_ok: map.ok mem} a s post :
    map.undef_on s.(getMachine).(getMem) isMMIOAddr ->
    PropSet.disjoint (PropSet.of_list s.(getMachine).(getXAddrs)) isMMIOAddr ->
    interp_action a s post ->
    exists v s, post v s /\ map.undef_on s.(getMem) isMMIOAddr /\
                PropSet.disjoint (PropSet.of_list s.(getMachine).(getXAddrs)) isMMIOAddr.
  Proof.
    intros H D H1.
    unshelve epose proof (MinimalMMIO.interpret_action_total _ _ _ _ _ D H1) as H0; eauto.
    destruct H0 as (?&?&?&[[]|(?&?)]); eauto.
  Qed.
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

  Ltac t :=
    match goal with
    | _ => progress subst
    | _ => progress fwd_step
    | _ => progress cbn -[Platform.Memory.load_bytes Platform.Memory.store_bytes HList.tuple
                          LittleEndian.split_deprecated] in *
    | _ => progress cbv
             [id valid_register is_initial_register_value load store
                Platform.Memory.loadByte Platform.Memory.loadHalf
                Platform.Memory.loadWord Platform.Memory.loadDouble
                Platform.Memory.storeByte Platform.Memory.storeHalf
                Platform.Memory.storeWord Platform.Memory.storeDouble] in *
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
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
    all: cbv [mcomp_sat spec_load spec_store primitivesParams invalidateWrittenXAddrs].
    all: intros; destruct initialL.
    all: repeat t.
    destruct getMachine; eassumption.
  Qed.

End Riscv.
