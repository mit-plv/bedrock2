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

Local Open Scope Z_scope.

Definition kword (w: Z): Type := Kami.Lib.Word.word (Z.to_nat w).

Section Equiv.

  (* TODO not sure if we want to use ` or rather a parameter record *)
  Context {M: Type -> Type}.
  Instance W: Utility.Words := @KamiWord.WordsKami width width_cases.

  (** * Processor, software machine, and states *)

  (* [instrMemSizeLg] is the log number of instructions in the instruction cache.
   * If the instruction base address is just 0, then the address range for
   * the instructions is [0 -- 4 * 2^(instSize)].
   *)
  Variable instrMemSizeLg: Z.
  Local Definition instrMemSize: nat := Z.to_nat (Z.pow 2 instrMemSizeLg).

  Local Definition kamiProc := @KamiProc.proc instrMemSizeLg.
  Local Definition KamiMachine := KamiProc.hst.
  Local Definition KamiSt := @KamiProc.st instrMemSizeLg.

  Context {Registers: map.map Register word}
          {mem: map.map word byte}
          (mcomp_sat:
             forall A: Type,
               M A -> RiscvMachine -> (A -> RiscvMachine -> Prop) -> Prop)
          {mm: Monad M}
          {rvm: RiscvProgram M word}.
  Arguments mcomp_sat {A}.

  Definition iset: InstructionSet := RV32IM.

  (** * State mappings *)

  (* register file *)

  Definition convertRegs (rf: kword 5 -> kword width): Registers :=
    let kkeys := HList.tuple.unfoldn (wplus (natToWord 5 1)) 31 (natToWord 5 1) in
    let values := HList.tuple.map rf kkeys in
    let keys := HList.tuple.map (@wordToZ 5) kkeys in
    map.putmany_of_tuple keys values map.empty.

  Lemma convertRegs_get:
    forall rf r v,
      map.get (convertRegs rf) (Word.wordToZ r) = Some v ->
      v = rf r.
  Proof.
  Admitted.

  Lemma convertRegs_put:
    forall rf r v,
      convertRegs (fun w => if weq w r then v else rf w) =
      map.put (convertRegs rf) (Word.wordToZ r) v.
  Proof.
    intros.
    eapply map.map_ext.
    intros k.
  Admitted.

  (* pc *)

  Variable pad: nat.
  Hypothesis (Hpad: (2 + (Z.to_nat instrMemSizeLg) + pad = nwidth)%nat).

  Definition alignPc (kpc: Word.word (2 + Z.to_nat instrMemSizeLg)%nat): word :=
    eq_rec (2 + Z.to_nat instrMemSizeLg + pad)%nat
           Word.word (Word.combine kpc $ (0)) nwidth Hpad.

  (** joonwonc: well this is not true!
   * Need to know how riscv-coq ensures pc is correctly bound? *)
  Lemma alignPc_next:
    forall kpc,
      alignPc kpc ^+ $4 = alignPc (kpc ^+ $4).
  Proof.
  Admitted.

  (* instruction and data memory *)

  Variable dataMemSize: nat.
  Definition instrMemStart: kword instrMemSizeLg := Word.ZToWord _ 0.
  Definition dataMemStart: word := word.of_Z (Z.of_nat (4 * instrMemSize)).

  Definition word32_to_4bytes(w: kword 32): HList.tuple byte 4 :=
    LittleEndian.split 4 (word.unsigned w).

  (* TODO this structure might not be very proof friendly, use Memory.unchecked_store_byte_list
   instead *)
  Fixpoint unchecked_store_byte_tuple_list{n: nat}(a: word)(l: list (HList.tuple byte n))(m: mem): mem :=
    match l with
    | w :: rest =>
      let m' := unchecked_store_byte_tuple_list (word.add a (word.of_Z (Z.of_nat n))) rest m in
      Memory.unchecked_store_bytes n m' a w
    | nil => m
    end.

  Definition convertInstrMem (instrMem: kword instrMemSizeLg -> kword 32): mem :=
    let keys := List.unfoldn (Word.wplus (Word.ZToWord (Z.to_nat instrMemSizeLg) 1))
                             instrMemSize instrMemStart in
    let values := List.map (fun key => word32_to_4bytes (instrMem key)) keys in
    @unchecked_store_byte_tuple_list 4 (word.of_Z 0) values map.empty.

  Definition convertDataMem(dataMem: kword width -> kword width): mem :=
    let keys := List.unfoldn (word.add (word.of_Z (width / 8))) dataMemSize dataMemStart in
    let values := List.map (fun key => LittleEndian.split (Z.to_nat (width / 8))
                                                          (word.unsigned (dataMem key)))
                           keys in
    unchecked_store_byte_tuple_list dataMemStart values map.empty.

  Definition KamiSt_to_RiscvMachine
             (k: KamiSt) (t: list LogItem): RiscvMachine :=
    {| getRegs := convertRegs (KamiProc.rf k);
       getPc := alignPc (KamiProc.pc k);
       getNextPc := word.add (alignPc (KamiProc.pc k)) (word.of_Z 4);
       getMem := map.putmany (convertInstrMem (KamiProc.pgm k))
                             (convertDataMem (KamiProc.mem k));
       getLog := t;
    |}.

  Definition fromKami_withLog
             (k: KamiMachine) (t: list LogItem): option RiscvMachine :=
    match KamiProc.RegsToT k with
    | Some r => Some (KamiSt_to_RiscvMachine r t)
    | None => None
    end.

  (** * The Observable Behavior: MMIO events *)

  Definition signedByteTupleToReg{n: nat}(v: HList.tuple byte n): word :=
    word.of_Z (BitOps.signExtend (8 * Z.of_nat n) (LittleEndian.combine n v)).

  Definition mmioLoadEvent(m: mem)(addr: word)(n: nat)(v: HList.tuple byte n): LogItem :=
    ((m, MMInput, [addr]), (m, [signedByteTupleToReg v])).

  Definition mmioStoreEvent(m: mem)(addr: word)(n: nat)(v: HList.tuple byte n): LogItem :=
    ((m, MMOutput, [addr; signedByteTupleToReg v]), (m, [])).

  (* These two specify what happens on loads and stores which are outside the memory, eg MMIO *)
  (* TODO these will have to be more concrete *)
  Context (nonmem_load: forall (n: nat) (addr: word), M (HList.tuple byte n)).
  Context (nonmem_store: forall (n: nat) (addr: word) (v: HList.tuple byte n), M unit).

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
  | relate_states: forall t t' m pc rf instrMem dataMem,
      traces_related t t' ->
      KamiProc.RegsToT m = Some (KamiProc.mk pc rf instrMem dataMem) ->
      states_related (m, t) {| getRegs := convertRegs rf;
                               getPc := alignPc pc;
                               getNextPc := word.add (alignPc pc) (word.of_Z 4);
                               getMem := map.putmany (convertInstrMem instrMem)
                                                     (convertDataMem dataMem);
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

  Lemma invert_Kami_execNm:
    forall km1 kt1 kupd klbl,
      KamiProc.RegsToT km1 = Some kt1 ->
      Step kamiProc km1 kupd klbl ->
      klbl.(annot) = Some (Some "execNm"%string) ->
      exists kt2: KamiSt,
        klbl.(calls) = FMap.M.empty _ /\
        KamiProc.RegsToT (FMap.M.union kupd km1) = Some kt2 /\
        exists curInst npc prf dst exec_val,
          curInst = (KamiProc.pgm kt1) (split2 _ _ (KamiProc.pc kt1)) /\
          npc = evalExpr (rv32NextPc
                            _ _
                            (KamiProc.rf kt1) (KamiProc.pc kt1)
                            curInst) /\
          prf = KamiProc.rf kt1 /\
          dst = evalExpr (rv32GetDst _ curInst) /\
          exec_val = evalExpr
                       (rv32Exec
                          _ _
                          (KamiProc.rf kt1 (evalExpr (rv32GetSrc1 _ curInst)))
                          (KamiProc.rf kt1 (evalExpr (rv32GetSrc2 _ curInst)))
                          (KamiProc.pc kt1)
                          curInst) /\
          kt2 = {| KamiProc.pc := npc;
                   KamiProc.rf :=
                     evalExpr
                       (UpdateVector
                          (Var _ (SyntaxKind (Vector (Bit KamiProc.nwidth) rv32RfIdx)) prf)
                          (Var _ (SyntaxKind (Bit rv32RfIdx)) dst)
                          (Var _ (SyntaxKind (Bit KamiProc.nwidth)) exec_val));
                   KamiProc.pgm := KamiProc.pgm kt1;
                   KamiProc.mem := KamiProc.mem kt1 |}.
  Proof.
    intros.
    kinvert; try (repeat
                    match goal with
                    | [H: annot ?klbl = Some _ |- _] => rewrite H in *
                    | [H: (_ :: _)%struct = (_ :: _)%struct |- _] =>
                      inversion H; subst; clear H
                    end; discriminate).

    Opaque evalExpr.
    kinv_action_dest.
    unfold KamiProc.RegsToT in *.
    kregmap_red.
    destruct x1; try discriminate.
    destruct (FMap.M.find "mem"%string km1)
      as [[[kind|] memv]|]; try discriminate.
    destruct (decKind kind (Vector (Bit KamiProc.nwidth) KamiProc.nwidth));
      try discriminate.
    kregmap_red.
    inversion_clear H.
    eexists; split; [|split].
    - assumption.
    - reflexivity.
    - do 5 eexists.
      repeat (split; [reflexivity|]).
      reflexivity.
      Transparent evalExpr.

  Qed.

  (* TODO in bedrock2: differential memory in trace instead of whole memory ? *)
  Inductive PHide: Prop -> Prop :=
  | PHidden: forall P: Prop, P -> PHide P.

  Lemma fetch_ok:
    forall instrMem dataMem pc,
      Memory.loadWord
        (map.putmany (convertInstrMem instrMem) (convertDataMem dataMem))
        (alignPc pc) <> None.
  Proof.
  Admitted.

  Lemma fetch_consistent:
    forall instrMem dataMem pc inst,
      Memory.loadWord
        (map.putmany (convertInstrMem instrMem)
                     (convertDataMem dataMem)) (alignPc pc) = Some inst ->
      combine 4 inst =
      wordToZ (instrMem (split2 _ _ pc)).
  Proof.
  Admitted.

  Ltac lets_in_hyp_to_eqs :=
    repeat lazymatch goal with
           | |- (let x := ?a in ?b) = ?c -> ?Q =>
             change (let x := a in b = c -> Q); intro
           | x := bitSlice _ 25 26 |- _ =>
            (* shamtHi is the only field which another field depends on *)
             subst x
           | x := ?t : ?T |- _ =>
             pose proof (eq_refl t : x = t); clearbody x
           end.

  Ltac invert_decode_if_true G :=
    first [ apply Bool.andb_true_iff in G;
            let G1 := fresh G in let G2 := fresh G in destruct G as [G1 G2];
            invert_decode_if_true G1; invert_decode_if_true G2
          | apply Z.eqb_eq in G
          | idtac ].

  (* TODO rather than stating this as a lemma, write a tactic which
     infers & poses the conclusion *)
  Lemma invert_decode_Add: forall inst rd rs1 rs2: Z,
      decode RV32IM inst = IInstruction (Decode.Add rd rs1 rs2) ->
      bitSlice inst 0 7 = opcode_OP /\
      bitSlice inst 7 12 = rd /\
      bitSlice inst 12 15 = funct3_ADD /\
      bitSlice inst 15 20 = rs1 /\
      bitSlice inst 20 25 = rs2 /\
      bitSlice inst 25 32 = funct7_ADD.
  Proof.
    intros *.
    cbv beta delta [decode].
    lets_in_hyp_to_eqs.
    subst
      resultI
      resultM
      resultA
      resultF
      resultI64
      resultM64
      resultA64
      resultF64
      resultCSR.
    repeat match type of H with
    | context C [if ?a then ?b else ?c] =>
      ((let P := context C [ b ] in change P in H) ||
       (let P := context C [ c ] in change P in H))
    end.
    subst results.
    destruct (isValidI decodeI) eqn: VI;
    destruct (isValidM decodeM) eqn: VM;
    destruct (isValidCSR decodeCSR) eqn: VCSR.
    all: try (clear; simpl; discriminate).
    simpl.
    intro E.
    injection E. clear E.
    subst decodeI.
    intro E.
    repeat match type of E with
    | (if ?a then ?b else ?c) = ?d => destruct a; [discriminate E|]
    end.
    match type of E with
    | (if ?a then ?b else ?c) = ?d => destruct a eqn: G; cycle 1
    end.
    { (* more invalid cases *)
      repeat match type of E with
             | (if ?a then ?b else ?c) = ?d => destruct a; [discriminate E|]
             end.
      discriminate E.
    }
    (* the only valid case remains *)
    subst rd0 rs4 rs0.
    invert_decode_if_true G.
    assert (bitSlice inst 0 7 = opcode_OP) as R1 by congruence; revert R1.
    assert (bitSlice inst 12 15 = funct3_ADD) as R2 by congruence; revert R2.
    assert (bitSlice inst 25 32 = funct7_ADD) as R3 by congruence; revert R3.
    injection E.
    clear.
    (* if we automate this further, we might be able to infer the conclusion with a tactic
       rather than having to state it manually *)
    intros. auto.
  Qed.

  Ltac inv_bind H :=
    apply (@spec_Bind _ _ _ _ _ _ _ Pr) in H;
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

  Lemma kami_split_bitSlice_consistent_1:
    forall (i: nat) kinst,
      wordToZ (split1 i (32 - i) kinst) =
      bitSlice (wordToZ kinst) 0 (Z.of_nat i).
  Proof.
  Admitted.

  Lemma kami_split_bitSlice_consistent_2:
    forall (i j: nat) kinst,
      wordToZ (split2 i j kinst) =
      bitSlice (wordToZ kinst) (Z.of_nat i) (Z.of_nat (i + j)).
  Proof.
  Admitted.

  Lemma kami_split_bitSlice_consistent_3:
    forall (i j: nat) kinst,
      wordToZ
        (split2 i j (split1 (i + j) (32 - (i + j)) kinst)) =
      bitSlice (wordToZ kinst) (Z.of_nat i) (Z.of_nat (i + j)).
  Proof.
  Admitted.

  Lemma kami_getOpcode_ok:
    forall kinst,
      wordToZ
        (evalExpr
           (getOpcodeE (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) =
      bitSlice (wordToZ kinst) 0 7.
  Proof.
    intros.
    unfold getOpcodeE.
    unfold evalExpr; fold evalExpr.
    unfold evalUniBit.
    rewrite kami_split_bitSlice_consistent_1.
    reflexivity.
  Qed.

  Lemma kami_getFunct7_ok:
    forall kinst,
      wordToZ
        (evalExpr
           (getFunct7E (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) =
      bitSlice (wordToZ kinst) 25 32.
  Proof.
    intros.
    unfold getFunct7E.
    unfold evalExpr; fold evalExpr.
    unfold evalUniBit.
    rewrite kami_split_bitSlice_consistent_2.
    reflexivity.
  Qed.

  Lemma kami_getFunct3_ok:
    forall kinst,
      wordToZ
        (evalExpr
           (getFunct3E (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) =
      bitSlice (wordToZ kinst) 12 15.
  Proof.
    intros.
    unfold getFunct3E.
    unfold evalExpr; fold evalExpr.
    unfold evalUniBit.
    rewrite kami_split_bitSlice_consistent_3.
    reflexivity.
  Qed.

  Lemma kami_getRdE_ok:
    forall kinst,
      wordToZ
        (evalExpr (getRdE (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) =
      bitSlice (wordToZ kinst) 7 12.
  Proof.
    intros.
    unfold getRdE.
    unfold evalExpr; fold evalExpr.
    unfold evalUniBit.
    rewrite kami_split_bitSlice_consistent_3.
    reflexivity.
  Qed.

  Lemma kami_rv32GetDst_ok:
    forall kinst,
      bitSlice (wordToZ kinst) 0 7 = opcode_OP ->
      Word.wordToZ (evalExpr (rv32GetDst type kinst)) =
      bitSlice (wordToZ kinst) 7 12.
  Proof.
    intros.
    unfold rv32GetDst.
    unfold evalExpr; fold evalExpr.
    destruct (isEq _ _) as [Heq|Hne].
    - exfalso.
      pose proof (kami_getOpcode_ok kinst).
      rewrite Heq, H in H0; discriminate.
    - rewrite kami_getRdE_ok; reflexivity.
  Qed.

  Lemma kami_rv32GetSrc1_ok:
    forall kinst,
      Word.wordToZ (evalExpr (rv32GetSrc1 type kinst)) =
      bitSlice (wordToZ kinst) 15 20.
  Proof.
    intros.
    unfold rv32GetSrc1, getRs1E.
    unfold evalExpr; fold evalExpr.
    unfold evalUniBit.
    rewrite kami_split_bitSlice_consistent_3.
    reflexivity.
  Qed.

  Lemma kami_rv32GetSrc2_ok:
    forall kinst,
      Word.wordToZ (evalExpr (rv32GetSrc2 type kinst)) =
      bitSlice (wordToZ kinst) 20 25.
  Proof.
    intros.
    unfold rv32GetSrc2, getRs2E.
    unfold evalExpr; fold evalExpr.
    unfold evalUniBit.
    rewrite kami_split_bitSlice_consistent_3.
    reflexivity.
  Qed.

  (** TODO @joonwonc: ditto [invert_decode_Add]; better to have a tactic. *)
  Lemma kami_rv32Exec_Add_ok:
    forall v1 v2 pc kinst,
      wordToZ
        (evalExpr
           (getOpcodeE (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) =
      opcode_OP ->
      wordToZ
        (evalExpr (getFunct7E (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) =
      funct7_ADD ->
      wordToZ
        (evalExpr (getFunct3E (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) =
      funct3_ADD ->
      evalExpr (rv32Exec (Z.to_nat instrMemSizeLg) type v1 v2 pc kinst) =
      v1 ^+ v2.
  Proof.
    intros.
    unfold rv32Exec.
    unfold evalExpr; fold evalExpr.
    do 5 (destruct (isEq _ _); [rewrite e in H; discriminate|clear n]).
    do 3 (destruct (isEq _ _); [|exfalso; elim n; apply wordToZ_inj; assumption]).
    reflexivity.
  Qed.

  Lemma kami_rv32NextPc_op_ok:
    forall rf pc kinst,
      wordToZ
        (evalExpr
           (getOpcodeE (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) =
      opcode_OP ->
      evalExpr (rv32NextPc (Z.to_nat instrMemSizeLg) type rf pc kinst) =
      pc ^+ $4.
  Proof.
    intros.
    unfold rv32NextPc.
    unfold evalExpr; fold evalExpr.
    do 3 (destruct (isEq _ _); [rewrite e in H; discriminate|clear n]).
    unfold evalBinBit.
    unfold evalConstT.
    f_equal.
  Admitted.

  Lemma kamiStep_sound: forall (m1 m2: KamiMachine) (m1': RiscvMachine) (t: list Event)
                               (post: RiscvMachine -> Prop),
      kamiStep m1 m2 t ->
      states_related (m1, nil) m1' ->
      mcomp_sat_unit (run1 iset) m1' post ->
      (* Either Kami doesn't proceed or riscv-coq simulates. *)
      (m1 = m2 \/
       exists m2', states_related (m2, t) m2' /\ post m2').
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
      destruct H1; [|exfalso; destruct H1; eapply fetch_ok; eauto].
      destruct H1 as (rinst & ? & ?).
      inv_bind_apply H4.

      (** Invert Kami decode/execute *)
      destruct H2
        as (kinst & npc & prf & dst & exec_val
            & ? & ? & ? & ? & ? & ?).
      subst prf.

      (* Relation between the two raw instructions *)
      assert (combine (byte:= @byte_Inst _ (@MachineWidth_XLEN W))
                      4 rinst =
              wordToZ kinst) as Hfetch.
      { subst kinst.
        eapply fetch_consistent.
        eassumption.
      }
      simpl in H3, Hfetch. (* normalizes implicit arguments *)
      rewrite Hfetch in *.

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
        inv_bind_apply H13.
        inv_bind H12.
        apply spec_getRegister with (post0:= mid3) in H12.
        destruct H12; [|admit (** TODO @joonwonc: ditto, about `R0` *)].
        simpl in H12; destruct H12.
        destruct_one_match_hyp; [rename w into v2|
                                 admit (** TODO: ditto, about valid register reads *)].
        inv_bind_apply H15.
        apply @spec_setRegister in H14; [|assumption..].
        destruct H14; [|admit (** TODO @joonwonc: writing to `R0` *)].
        simpl in H14; destruct H14.
        inv_bind_apply H16.
        inv_step H7.

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
                             (SyntaxKind (Vector (Bit KamiProc.nwidth) rv32RfIdx))
                             rf) (Var type (SyntaxKind (Bit rv32RfIdx)) dst)
                        (Var type (SyntaxKind (Bit KamiProc.nwidth)) exec_val))))
        end.
        2: { unfold evalExpr; fold evalExpr.
             subst exec_val.
             replace rd with (Word.wordToZ dst) in *
               by (subst dst rd; apply kami_rv32GetDst_ok; assumption).
             replace rs1
               with (Word.wordToZ (evalExpr (rv32GetSrc1 type kinst))) in *
               by (subst rs1; apply kami_rv32GetSrc1_ok).
             replace rs2
               with (Word.wordToZ (evalExpr (rv32GetSrc2 type kinst))) in *
               by (subst rs2; apply kami_rv32GetSrc2_ok).
             rewrite <-convertRegs_get with (v:= v1) by auto.
             rewrite <-convertRegs_get with (v:= v2) by auto.
             rewrite kami_rv32Exec_Add_ok;
               [|rewrite kami_getOpcode_ok; assumption
                |rewrite kami_getFunct7_ok; assumption
                |rewrite kami_getFunct3_ok; assumption].
             apply convertRegs_put.
        }

        rewrite alignPc_next.
        constructor.
        - assumption.
        - rewrite H0, H11.
          do 2 f_equal.
          (* next pc *)
          subst npc.
          rewrite kami_rv32NextPc_op_ok
            by (rewrite kami_getOpcode_ok; assumption).
          reflexivity.
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

  (* Alternative approach to proving something from which impl_to_end_of_compiler would follow
     too, but without the intermediate lemmas. Can't see at the moment how this would work. *)
  Lemma simulate_multistep: forall (init final: KamiMachine) (t: list Event),
      star kamiStep init final t ->
      forall (post: RiscvMachine -> Prop),
      (forall m, post m -> exists t, traces_related t m.(getLog)) -> (* no malformed traces *)
      forall (init': RiscvMachine),
      fromKami_withLog init nil = Some init' ->
      runsTo init' post ->
      exists (rest : list Event) (final : RiscvMachine),
        post final /\ traces_related (rest ++ t) final.(getLog).
  Proof.
    induction 1; intros post C init' E R.
    - apply pick_from_runsTo in R. destruct R as (final & R).
      specialize (C final R). destruct C as [t C].
      exists t. exists final. rewrite app_nil_r. auto.
    - inversion R.
      + (* riscv-coq is done *)
        edestruct C as [t D]; [eassumption|].
        exists (firstn (length t - (length t2 + length t1)) t).
        eexists; split; eauto.
        replace (firstn (length t - (length t2 + length t1)) t ++ t2 ++ t1) with t by admit.
        exact D.

      (* what if the fake machine steps further than the riscv spec machine?
         Then it's supposed to be silent (creating no events).
         But where do we show that?
         -> Problem: from_Fake should take in trace to add  *)
  Abort.

End Equiv.
