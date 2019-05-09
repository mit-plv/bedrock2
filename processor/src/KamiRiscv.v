Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Kami.Lib.Word.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Encode.
Require Import coqutil.Word.LittleEndian.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import processor.KamiWord.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.Machine.
Require riscv.Platform.Memory.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Proofs.EncodeBound.
Require Import riscv.Proofs.DecodeEncode.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.Monads. Import MonadNotations.
Require Import riscv.Utility.runsToNonDet.
Require Import coqutil.Datatypes.PropSet.
Require Import riscv.Utility.MMIOTrace.
Require Import riscv.Platform.RiscvMachine.

Require Import Kami.Syntax Kami.Semantics Kami.Tactics.
Require Import Kami.Ex.MemTypes Kami.Ex.SC Kami.Ex.SCMMInl.
Require Import Kami.Ex.IsaRv32.

Require Import processor.KamiProc.
Require Import processor.FetchOk processor.DecExecOk.

Local Open Scope Z_scope.

Section Equiv.

  Instance W: Utility.Words := @KamiWord.WordsKami width width_cases.

  (* TODO not sure if we want to use ` or rather a parameter record *)
  Context {M: Type -> Type}.
  Context {Registers: map.map Register word}
          {mem: map.map word byte}
          (mcomp_sat:
             forall A: Type,
               M A -> RiscvMachine -> (A -> RiscvMachine -> Prop) -> Prop)
          {mm: Monad M}
          {rvm: RiscvProgram M word}.
  Arguments mcomp_sat {A}.

  (** * Processor, software machine, and states *)

  Variables (instrMemSizeLg: Z) (dataMemSize: nat).
  Hypothesis (HinstrMemBound: instrMemSizeLg <= width - 2).

  Local Definition kamiProc := @KamiProc.proc instrMemSizeLg.
  Local Definition KamiMachine := KamiProc.hst.
  Local Definition KamiSt := @KamiProc.st instrMemSizeLg.
  Local Notation kamiXAddrs := (kamiXAddrs instrMemSizeLg).
  Local Notation toKamiPc := (toKamiPc instrMemSizeLg).
  Local Notation convertInstrMem :=
    (@convertInstrMem mem instrMemSizeLg).
  Local Notation convertDataMem :=
    (@convertDataMem mem instrMemSizeLg dataMemSize).

  Definition iset: InstructionSet := RV32IM.

  (** * The Observable Behavior: MMIO events *)

  Definition signedByteTupleToReg{n: nat}(v: HList.tuple byte n): word :=
    word.of_Z (BitOps.signExtend (8 * Z.of_nat n) (LittleEndian.combine n v)).

  Definition mmioLoadEvent(m: mem)(addr: word)(n: nat)(v: HList.tuple byte n): LogItem :=
    ((m, MMInput, [addr]), (m, [signedByteTupleToReg v])).

  Definition mmioStoreEvent(m: mem)(addr: word)(n: nat)(v: HList.tuple byte n): LogItem :=
    ((m, MMOutput, [addr; signedByteTupleToReg v]), (m, [])).

  (* These two specify what happens on loads and stores which are outside the memory, eg MMIO *)
  (* TODO these will have to be more concrete *)
  Context (nonmem_load: forall (n: nat), SourceType -> word -> M (HList.tuple byte n)).
  Context (nonmem_store: forall (n: nat), SourceType -> word -> HList.tuple byte n -> M unit).

  Instance MinimalMMIOPrimitivesParams: PrimitivesParams M RiscvMachine := {
    Primitives.mcomp_sat := @mcomp_sat;

    (* any value can be found in an uninitialized register *)
    Primitives.is_initial_register_value x := True;

    Primitives.nonmem_load := nonmem_load;
    Primitives.nonmem_store := nonmem_store;
  }.

  Context {Pr: Primitives MinimalMMIOPrimitivesParams}.
  Context {RVS: riscv.Spec.Machine.RiscvMachine M word}.

  (* common event between riscv-coq and Kami *)
  Inductive Event: Type :=
  | MMInputEvent(addr v: word)
  | MMOutputEvent(addr v: word).

  (* note: memory can't change *)
  Inductive events_related: Event -> LogItem -> Prop :=
  | relate_MMInput: forall m addr v,
      events_related (MMInputEvent addr v) ((m, MMInput, [addr]), (m, [v]))
  | relate_MMOutput: forall m addr v,
      events_related (MMOutputEvent addr v) ((m, MMOutput, [addr; v]), (m, [])).

  Inductive traces_related: list Event -> list LogItem -> Prop :=
  | relate_nil:
      traces_related nil nil
  | relate_cons: forall e e' t t',
      events_related e e' ->
      traces_related t t' ->
      traces_related (e :: t) (e' :: t').

  (* "exists m', states_related (m, t) m'"
     might be simpler to use than
     "exists m' t', fromKami_withLog m t' = Some 2' /\ traces_related t t'"
     and require less unfolding/destructing *)
  Inductive states_related: KamiMachine * list Event -> RiscvMachine -> Prop :=
  | relate_states: forall t t' m riscvXAddrs kpc pc rf instrMem dataMem,
      traces_related t t' ->
      KamiProc.RegsToT m = Some (KamiProc.mk kpc rf instrMem dataMem) ->
      (forall addr, isXAddr addr riscvXAddrs -> isXAddr addr kamiXAddrs) ->
      kpc = toKamiPc pc ->
      states_related (m, t) {| getRegs := convertRegs rf;
                               getPc := pc;
                               getNextPc := word.add pc (word.of_Z 4);
                               getMem := map.putmany (convertInstrMem instrMem)
                                                     (convertDataMem dataMem);
                               getXAddrs := riscvXAddrs;
                               getLog := t'; |}.

  (* redefine mcomp_sat to simplify for the case where no answer is returned *)
  Definition mcomp_sat_unit(m: M unit)(initialL: RiscvMachine)(post: RiscvMachine -> Prop): Prop :=
    mcomp_sat m initialL (fun (_: unit) => post).

  (* list is kind of redundant (already in RiscvMachine.(getLog)))
     and should at most contain one event,
     but we still want it to appear in the signature so that we can easily talk about prefixes,
     and to match Kami's step signature *)
  Inductive riscvStep: RiscvMachine -> RiscvMachine -> list LogItem -> Prop :=
  | mk_riscvStep: forall initialL finalL t post,
      mcomp_sat_unit (run1 iset) initialL post ->
      post finalL ->
      finalL.(getLog) = t ++ initialL.(getLog) ->
      riscvStep initialL finalL t.

  Inductive star{S E: Type}(R: S -> S -> list E -> Prop): S -> S -> list E -> Prop :=
  | star_refl: forall (x: S),
      star R x x nil
  | star_step: forall (x y z: S) (t1 t2: list E),
      star R x y t1 ->
      R y z t2 ->
      star R x z (t2 ++ t1).

  (* temporal prefixes, new events are added in front of the head of the list *)
  Definition prefixes{E: Type}(traces: list E -> Prop): list E -> Prop :=
    fun prefix => exists rest, traces (rest ++ prefix).

  Definition riscvTraces(initial: RiscvMachine): list Event -> Prop :=
    fun t => exists final t', star riscvStep initial final t' /\ traces_related t t'.

  Definition post_to_traces(post: RiscvMachine -> Prop): list Event -> Prop :=
    fun t => exists final, post final /\ traces_related t final.(getLog).

  Definition runsTo: RiscvMachine -> (RiscvMachine -> Prop) -> Prop :=
    runsTo (mcomp_sat_unit (run1 iset)).

  Lemma bridge(init: RiscvMachine)(post: RiscvMachine -> Prop):
    runsTo init post ->
    subset (riscvTraces init) (prefixes (post_to_traces post)).
  Admitted.

  Definition KamiLabelR (klbl: Kami.Semantics.LabelT) (ev: list Event): Prop.
  Proof.
    refine (match FMap.M.find "mmioExec"%string klbl.(calls) with
            | Some sv => _
            | None => ev = nil
            end).
    destruct sv as [[argT retT] [argV retV]].
    destruct (decKind argT (Struct (RqFromProc (Z.to_nat width) rv32DataBytes)));
      [subst|exact False].
    destruct (decKind retT (Struct (RsToProc rv32DataBytes)));
      [subst|exact False].

    destruct (argV (Fin.FS Fin.F1)).
    - (* MMIO-store *)
      set (argV Fin.F1) as mmioAddr; simpl in mmioAddr.
      set (argV (Fin.FS (Fin.FS Fin.F1))) as mmioVal; simpl in mmioVal.
      exact (ev = [MMOutputEvent mmioAddr mmioVal]).
    - (* MMIO-load *)
      set (argV Fin.F1) as mmioAddr; simpl in mmioAddr.
      set (retV Fin.F1) as mmioVal; simpl in mmioVal.
      exact (ev = [MMInputEvent (argV Fin.F1) (retV Fin.F1)]).
  Defined.

  Definition kamiStep: KamiMachine -> KamiMachine -> list Event -> Prop :=
    fun km1 km2 tr =>
      exists kupd klbl,
        Step kamiProc km1 kupd klbl /\
        km2 = FMap.M.union kupd km1  /\
        KamiLabelR klbl tr.

  Inductive PHide: Prop -> Prop :=
  | PHidden: forall P: Prop, P -> PHide P.

  Ltac inv_bind H :=
    apply (proj2 (@spec_Bind _ _ _ _ MinimalMMIOPrimitivesParams mcomp_sat_ok _ _ _ _ _ _)) in H;
    let mid := fresh "mid" in
    destruct H as (mid & ? & ?).

  Ltac inv_getPC H :=
    match type of H with
    | _ _ _ ?mid =>
      apply spec_getPC with (post0:= mid) in H; simpl in H
    end.

  Ltac inv_bind_apply H :=
    match type of H with
    | ?mid _ _ =>
      repeat
        match goal with
        | [H0: forall _ _, mid _ _ -> _ |- _] => specialize (H0 _ _ H)
        end
    end.

  Ltac inv_loadWord H :=
    apply @spec_loadWord in H; [|assumption..]; simpl in H.

  Ltac inv_step H :=
    apply @spec_step in H; [|assumption..];
    unfold withNextPc, getNextPc, withRegs in H;
    simpl in H.

  (* TODO in bedrock2: differential memory in trace instead of whole memory ? *)
  Lemma kamiStep_sound:
    forall (m1 m2: KamiMachine) (m1': RiscvMachine) (t0 t: list Event)
           (post: RiscvMachine -> Prop),
      kamiStep m1 m2 t ->
      states_related (m1, t0) m1' ->
      mcomp_sat_unit (run1 iset) m1' post ->
      (* Either Kami doesn't proceed or riscv-coq simulates. *)
      (m1 = m2 \/
       exists m2', states_related (m2, t ++ t0) m2' /\ post m2').
  Proof.
    intros.
    destruct H as [kupd [klbl [? [? ?]]]]; subst.
    assert (PHide (Step kamiProc m1 kupd klbl)) by (constructor; assumption).
    kinvert.

    - (* [EmptyRule] step *)
      red in H3; rewrite <-H8 in H3; FMap.mred.
    - (* [EmptyMeth] step *)
      red in H3; rewrite <-H8 in H3; FMap.mred.
    - (* "pgmInit" *)
      exfalso.
      inversion_clear H0.
      kinv_action_dest; kinv_red.
      unfold KamiProc.RegsToT in H6.
      kinv_regmap_red.
      discriminate.
    - (* "pgmInitEnd" *)
      exfalso.
      inversion_clear H0.
      kinv_action_dest; kinv_red.
      unfold KamiProc.RegsToT in H6.
      kinv_regmap_red.
      discriminate.

    - (* "execLd" *) admit.
    - (* "execLdZ" *) admit.
    - (* "execSt" *) admit.
    - (* "execNm" *)
      right.

      (** Apply the Kami inversion lemma for the [execNm] rule. *)
      inversion H5; subst; clear H5 HAction.
      inversion H0; subst; clear H0.
      rename H9 into XAddrsSubset.
      destruct klbl as [annot defs calls]; simpl in *; subst.
      destruct annot; [|discriminate].
      inversion H7; subst; clear H7.
      inversion H2; subst; clear H2.
      eapply invert_Kami_execNm in H; eauto.
      unfold KamiProc.pc, KamiProc.rf, KamiProc.pgm, KamiProc.mem in H.
      destruct H as [km2 [? [? ?]]].
      simpl in H; subst.
      inversion_clear H3.

      (** Invert a riscv-coq step. *)
      move H1 at bottom.
      red in H1; unfold run1 in H1.

      inv_bind H1.
      inv_getPC H.
      inv_bind_apply H.
      inv_bind H1.
      inv_loadWord H1.

      destruct H1 as [IXA H1]; specialize (IXA eq_refl).
      apply XAddrsSubset in IXA.
      apply fetch_ok
        with (instrMem0:= instrMem)
             (dataMem0:= dataMem)
             (dataMemSize0:= dataMemSize) in IXA; auto.
      destruct IXA as (rinst & ? & ?).
      destruct H1; [|exfalso; destruct H1;
                     match type of H1 with
                     | ?t1 = _ => match type of H4 with
                                  | ?t2 = _ => change t1 with t2 in H1
                                  end
                     end; congruence].
      destruct H1 as (rinst' & ? & ?).
      match type of H1 with
      | ?t1 = _ => match type of H4 with
                   | ?t2 = _ => change t1 with t2 in H1
                   end
      end; rewrite H1 in H4.
      inversion H4; subst; clear H4.
      inv_bind_apply H7.

      (** Invert Kami decode/execute *)
      destruct H2
        as (kinst & npc & prf & dst & exec_val
            & ? & ? & ? & ? & ? & ?).
      subst prf.

      (* Relation between the two raw instructions *)
      assert (combine (byte:= @byte_Inst _ (@MachineWidth_XLEN W))
                      4 rinst =
              wordToZ kinst) as Hfetch by (subst kinst; assumption).
      simpl in H3, Hfetch; rewrite Hfetch in H3.

      (** Invert riscv-coq decode/execute *)
      match type of H3 with
      | context [decode ?i ?al] =>
        destruct (decode i al) eqn:Hdec;
          [(* IInstruction *)
          |(* MInstruction *) admit
          |(** TODO @samuelgruetter: remove the other cases except I and M --
            * execution with [iset] (= RV32IM) cannot have such cases.
            *)
          admit..]
      end.
      destruct iInstruction.
      21: { (* Case of Add *)
        apply invert_decode_Add in Hdec.
        destruct Hdec as [Hopc [Hrd [Hf3 [Hrs1 [Hrs2 Hf7]]]]].

        simpl in H3.
        (** TODO @samuelgruetter: using [Hdec] we should be able to derive
         * the relation among [inst], [rd], [rs1], and [rs2],
         * e.g., [bitSlice inst _ _ = rs1].
         *)

        inv_bind H3.
        inv_bind H3.
        apply spec_getRegister with (post0:= mid2) in H3.
        destruct H3; [|admit (** TODO @joonwonc: prove the value of `R0` is
                              * always zero in Kami steps. *)].
        simpl in H3; destruct H3.
        destruct_one_match_hyp; [rename w into v1|admit (** TODO: prove it never fails to read
                                       * a register value once the register
                                       * is valid. *)].
        inv_bind_apply H14.
        inv_bind H13.
        apply spec_getRegister with (post0:= mid3) in H13.
        destruct H13; [|admit (** TODO @joonwonc: ditto, about `R0` *)].
        simpl in H13; destruct H13.
        destruct_one_match_hyp; [rename w into v2|
                                 admit (** TODO: ditto, about valid register reads *)].
        inv_bind_apply H16.
        apply @spec_setRegister in H15; [|assumption..].
        destruct H15; [|admit (** TODO @joonwonc: writing to `R0` *)].
        simpl in H15; destruct H15.
        inv_bind_apply H17.
        inv_step H9.

        (** Construction *)
        eexists.
        split; [|eassumption].

        (* next rf *)
        match goal with
        | |- context [ riscv.Platform.RiscvMachine.mkRiscvMachine ?REGS _ _ _ _ ] =>
          replace REGS
            with (convertRegs
                    (evalExpr
                       (UpdateVector
                          (Var type
                               (SyntaxKind (Vector (Bit (Z.to_nat width)) rv32RfIdx))
                               rf) (Var type (SyntaxKind (Bit rv32RfIdx)) dst)
                          (Var type (SyntaxKind (Bit (Z.to_nat width))) exec_val))))
        end.
        2: { unfold evalExpr; fold evalExpr.
             subst exec_val.
             replace rd with (Word.wordToZ dst) in *
               by (subst dst rd;
                   apply kami_rv32GetDst_ok
                     with (instrMemSizeLg:= instrMemSizeLg); assumption).
             replace rs1
               with (Word.wordToZ (evalExpr (rv32GetSrc1 type kinst))) in *
               by (subst rs1;
                   apply kami_rv32GetSrc1_ok
                     with (instrMemSizeLg:= instrMemSizeLg); assumption).
             replace rs2
               with (Word.wordToZ (evalExpr (rv32GetSrc2 type kinst))) in *
               by (subst rs2;
                   apply kami_rv32GetSrc2_ok
                     with (instrMemSizeLg:= instrMemSizeLg); assumption).
             erewrite <-convertRegs_get
               with (instrMemSizeLg:= instrMemSizeLg) (v:= v1) by auto.
             erewrite <-convertRegs_get
               with (instrMemSizeLg:= instrMemSizeLg) (v:= v2) by auto.
             rewrite kami_rv32Exec_Add_ok;
               [|rewrite kami_getOpcode_ok
                   with (instrMemSizeLg:= instrMemSizeLg); assumption
                |rewrite kami_getFunct7_ok
                   with (instrMemSizeLg:= instrMemSizeLg); assumption
                |rewrite kami_getFunct3_ok
                   with (instrMemSizeLg:= instrMemSizeLg); assumption].
             apply convertRegs_put
               with (instrMemSizeLg:= instrMemSizeLg); assumption.
        }

        econstructor.
        - assumption.
        - rewrite H0, H12.
          reflexivity.
        - assumption.
        - subst.
          rewrite kami_rv32NextPc_op_ok; auto;
            [|rewrite kami_getOpcode_ok
                with (instrMemSizeLg:= instrMemSizeLg); assumption].
          rewrite <-toKamiPc_wplus_distr; auto.
      }
      all: admit.

    - (* "execNmZ" *) admit.

  Admitted.

  (* equivalent of [mcomp_sat (run1 iset)] for Kami:
     running one kami step satisfies the postcondition, no matter what non-deterministic
     step was chosen *)
  Definition kamiStep_sat(m1: KamiMachine)(post: KamiMachine * list Event -> Prop): Prop :=
    forall m2 t, kamiStep m1 m2 t -> post (m2, t).

(*
  Definition kamiRunsTo: KamiMachine -> (KamiMachine -> Prop) -> Prop :=
    runsToNonDet.runsTo kamiStep_sat.
  Lemma test: forall (m': RiscvMachine),
      runsTo
(State -> (State -> Prop) -> Prop)
runsToNonDet.runsTo
*)

  (* want to say, finally:
     "all kami impl traces are a prefix of a trace which satisfies post"

     so we need:
     "all kami spec traces are a prefix of a trace which satisfies post" *)

  Lemma kamiMultiStep_sound: forall (m1 m2: KamiMachine) (m1': RiscvMachine) (t: list Event)
                               (post: RiscvMachine -> Prop),
      star kamiStep m1 m2 t ->
      states_related (m1, nil) m1' ->
      runsTo m1' post ->
      exists m2', states_related (m2, t) m2' /\ post m2'.
  Proof.
  Abort. (* doesn't hold because kami might step less or more than riscv *)

  Definition is_silence_invariant(post: RiscvMachine -> Prop): Prop :=
    forall m: RiscvMachine,
      post m ->
      mcomp_sat_unit (run1 iset) m (fun m' => post m' /\ m'.(getLog) = m.(getLog)).

  (* note: only holds if the nondet machine never picks an arbitrary value of the empty set,
     which is the case for all riscv machines, but not for a more abstract runsTo,
     and also requires no memory-changing or invalid events *)
  Lemma pick_from_runsTo: forall init post,
      runsTo init post ->
      exists final, post final. (* /\ traces_related t final.(getLog).*) (* and steps there? *)
  Admitted.

End Equiv.
