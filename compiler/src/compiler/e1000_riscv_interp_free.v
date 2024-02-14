(* Based on riscv.Platform.MinimalMMIO and riscv.Platform.MetricMinimalMMIO,
   but with a different nonmem_load and nonmem_store *)
(* TODO actually adapt, this is mostly just copied *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.MetricPrimitives.
Require Import Coq.Lists.List. Import ListNotations.
Require Export riscv.Platform.RiscvMachine.
Require Export riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MinimalMMIO.
Require Import riscv.Platform.MetricLogging.
Require Export riscv.Platform.MetricMaterializeRiscvProgram.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Section Riscv.
  Context {width: Z} {BW: Bitwidth width} {word: word width} {word_ok: word.ok word}.
  Context {Mem: map.map word byte} {Registers: map.map Register word}.

  (* TODO remove *)
  Context {mmio_spec: MMIOSpec}.

  Local Notation M := (free action result).
  Import free.

  Definition signedByteTupleToReg{n: nat}(v: HList.tuple byte n): word :=
    word.of_Z (BitOps.signExtend (8 * Z.of_nat n) (LittleEndian.combine n v)).

  Definition mmioLoadEvent(addr: word){n: nat}(v: HList.tuple byte n): LogItem :=
    ((map.empty, "MMIOREAD"%string, [addr]), (map.empty, [signedByteTupleToReg v])).

  Definition mmioStoreEvent(addr: word){n: nat}(v: HList.tuple byte n): LogItem :=
    ((map.empty, "MMIOWRITE"%string, [addr; signedByteTupleToReg v]), (map.empty, [])).

  Definition nonmem_store(n: nat)(ctxid: SourceType) a v mach post :=
    isMMIOAddr a /\ isMMIOAligned n a /\
    post (withXAddrs (invalidateWrittenXAddrs n a mach.(getXAddrs))
         (withLogItem (@mmioStoreEvent a n v)
         mach)).

  Definition store(n: nat)(ctxid: SourceType) a v mach post :=
    match Memory.store_bytes n mach.(getMem) a v with
    | Some m => post (withXAddrs (invalidateWrittenXAddrs n a mach.(getXAddrs)) (withMem m mach))
    | None => nonmem_store n ctxid a v mach post
    end.

  Definition nonmem_load(n: nat)(ctxid: SourceType) a mach (post: _ -> _ -> Prop) :=
    isMMIOAddr a /\ isMMIOAligned n a
    (* there exists at least one valid MMIO read value (set is nonempty) *)
    /\ (exists v : HList.tuple byte n, MMIOReadOK n (getLog mach) a (signedByteTupleToReg v))
    (* ...and postcondition holds for all valid read values *)
    /\ forall v,
        MMIOReadOK n (getLog mach) a (signedByteTupleToReg v) ->
        post v (withLogItem (@mmioLoadEvent a n v) mach).

  Definition load(n: nat)(ctxid: SourceType) a mach post :=
    (ctxid = Fetch -> isXAddr4 a mach.(getXAddrs)) /\
    match Memory.load_bytes n mach.(getMem) a with
    | Some v => post v mach
    | None => nonmem_load n ctxid a mach post
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

  Definition MinimalMMIOPrimitivesParams:
    PrimitivesParams (free riscv_primitive primitive_result) RiscvMachine :=
  {|
    Primitives.mcomp_sat A m mach postF :=
      @free.interpret _ _ _ interpret_action A m mach postF (fun _ => False);
    Primitives.is_initial_register_value x := True;
    Primitives.nonmem_load := nonmem_load;
    Primitives.nonmem_store := nonmem_store;
    Primitives.valid_machine mach :=
      map.undef_on mach.(getMem) isMMIOAddr /\
      PropSet.disjoint (PropSet.of_list mach.(getXAddrs)) isMMIOAddr;
  |}.

  Lemma load_weaken_post n c a m (post1 post2:_->_->Prop)
    (H: forall r s, post1 r s -> post2 r s)
    : load n c a m post1 -> load n c a m post2.
  Proof.
    cbv [load nonmem_load].
    destruct (Memory.load_bytes n (getMem m) a); intuition eauto.
  Qed.

  Lemma store_weaken_post n c a v m (post1 post2:_->Prop)
    (H: forall s, post1 s -> post2 s)
    : store n c a v m post1 -> store n c a v m post2.
  Proof.
    cbv [store nonmem_store].
    destruct (Memory.store_bytes n (getMem m) a); intuition eauto.
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

  Global Instance MetricMinimalMMIOPrimitivesParams: PrimitivesParams M MetricRiscvMachine :=
  {
    Primitives.mcomp_sat := @free.interp _ _ _ interp_action;
    Primitives.is_initial_register_value x := True;
    Primitives.nonmem_load := Primitives.nonmem_load (PrimitivesParams := MinimalMMIOPrimitivesParams);
    Primitives.nonmem_store := Primitives.nonmem_store (PrimitivesParams := MinimalMMIOPrimitivesParams);
    Primitives.valid_machine mach :=
      map.undef_on mach.(getMem) isMMIOAddr /\
      PropSet.disjoint (PropSet.of_list mach.(getXAddrs)) isMMIOAddr;
  }.

  Global Instance MinimalMMIOSatisfies_mcomp_sat_spec: mcomp_sat_spec MetricMinimalMMIOPrimitivesParams.
  Proof.
    split; cbv [mcomp_sat MetricMinimalMMIOPrimitivesParams free.Monad_free Bind Return].
    { symmetry. eapply free.interp_bind_ex_mid; intros.
      eapply MinimalMMIO.interpret_action_weaken_post; eauto; cbn; eauto. }
    { symmetry. rewrite free.interp_ret; eapply iff_refl. }
  Qed.

  Lemma interp_action_weaken_post a (post1 post2:_->_->Prop)
    (H: forall r s, post1 r s -> post2 r s) s
    : interp_action a s post1 -> interp_action a s post2.
  Proof. eapply MinimalMMIO.interpret_action_weaken_post; eauto. Qed.
  Lemma interp_action_appendonly' a s post :
    interp_action a s post ->
    interp_action a s (fun v s' => post v s' /\ List.endswith s'.(getLog) s.(getLog)).
  Proof. eapply MinimalMMIO.interpret_action_appendonly''; eauto. Qed.
  Lemma interp_action_total{memOk: map.ok Mem} a s post :
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

  Global Instance MetricMinimalMMIOPrimitivesSane{memOk: map.ok Mem} :
    MetricPrimitivesSane MetricMinimalMMIOPrimitivesParams.
  Proof.
    split; cbv [mcomp_sane valid_machine MetricMinimalMMIOPrimitivesParams];
      intros *; intros [U D] M;
      (split; [ exact (interp_action_total _ st _ U D M)
              | eapply interp_action_preserves_valid; try eassumption;
                eapply interp_action_appendonly'; try eassumption ]).
  Qed.

  Global Instance MetricMinimalMMIOSatisfiesPrimitives{memOk: map.ok Mem}:
    MetricPrimitives MetricMinimalMMIOPrimitivesParams.
  Proof.
    split; try exact _.
    all : cbv [mcomp_sat spec_load spec_store MetricMinimalMMIOPrimitivesParams invalidateWrittenXAddrs].
    all: intros; destruct initialL;
      repeat match goal with
      | _ => progress subst
      | _ => Option.inversion_option
      | _ => progress cbn -[Memory.load_bytes Memory.store_bytes HList.tuple] in *
      | _ => progress cbv [id valid_register is_initial_register_value load store Memory.loadByte Memory.loadHalf Memory.loadWord Memory.loadDouble Memory.storeByte Memory.storeHalf Memory.storeWord Memory.storeDouble] in *
      | H : exists _, _ |- _ => destruct H
      | H : _ /\ _ |- _ => destruct H
      | |- _ => solve [ intuition (eauto || blia) ]
      | H : _ \/ _ |- _ => destruct H
      | |- context[match ?x with _ => _ end] => destruct x eqn:?
      | |- _ => progress unfold getReg, setReg
      | |-_ /\ _ => split
      end.
      (* setRegister *)
      destruct getMachine; eassumption.
  Qed.

End Riscv.
