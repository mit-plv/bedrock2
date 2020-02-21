Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.

Require Import coqutil.Z.Lia.

Require Import Kami.Kami.
Require Import Kami.Ex.MemTypes Kami.Ex.SC Kami.Ex.IsaRv32.
Require Import Kami.Ex.SCMMInl Kami.Ex.SCMMInv.
Require Import Kami.Ex.ProcMemCorrect.

Local Open Scope Z_scope.

Set Implicit Arguments.

Lemma wnot_idempotent:
  forall {sz} (w: word sz),
    wnot (wnot w) = w.
Proof.
  induction w; cbn; rewrite ?IHw, ?negb_involutive; eauto.
Qed.

Section Parametrized.
  Variables (addrSize maddrSize iaddrSize fifoSize instBytes dataBytes rfIdx: nat)
            (Hdb: {pdb & dataBytes = S pdb}).

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec addrSize instBytes dataBytes rfIdx)
            (ammio: AbsMMIO addrSize).

  Variable (procInit: ProcInit addrSize dataBytes rfIdx)
           (memInit: MemInit maddrSize).

  Definition pprocInl := scmmInl Hdb fetch dec exec ammio procInit memInit.
  Definition pproc := projT1 pprocInl.

  (** The auxiliary hardware state; this is for manipulating hardware state
   * without knowing much about Kami states.
   *)
  Record pst :=
    mk { pc: word addrSize;
         rf: word rfIdx -> word (dataBytes * BitsPerByte);
         pinit: bool;
         pgm: word iaddrSize -> word (instBytes * BitsPerByte);
         mem: word maddrSize -> word BitsPerByte
       }.

  Definition pRegsToT (r: Kami.Semantics.RegsT): option pst :=
    (mlet pcv: (Pc addrSize) <- r |> "pc" <| None;
    mlet rfv: (Vector (Data dataBytes) rfIdx) <- r |> "rf" <| None;
    mlet pinitv: Bool <- r |> "pinit" <| None;
    mlet pgmv: (Vector (Data instBytes) iaddrSize) <- r |> "pgm" <| None;
    mlet memv: (Vector (Bit BitsPerByte) maddrSize) <- r |> "mem" <| None;
    (Some {| pc := pcv; rf := rfv;
             pinit := pinitv; pgm := pgmv; mem := memv |}))%mapping.

  (** * Deriving facts from [scmm_inv] *)

  Lemma scmm_inv_derive_rf_zero:
    forall st,
      scmm_inv maddrSize rfIdx fetch st ->
      forall pcv rfv pinitv pgmv memv,
        pRegsToT st = Some (mk pcv rfv pinitv pgmv memv) ->
        forall idx, idx = $0 -> rfv idx = $0.
  Proof.
    intros; subst.
    inversion_clear H.
    unfold pRegsToT in H0.
    kregmap_red.
    inversion H0; subst; clear H0.
    assumption.
  Qed.

  (** * Inverting Kami rules for instruction executions *)

  Lemma pRegsToT_init:
    pRegsToT (initRegs (getRegInits pproc)) =
    Some {| pc := evalConstT (pcInit procInit);
            rf := evalConstT (rfInit procInit);
            pinit := false;
            pgm := evalVec (mapVec (@evalConstT _)
                                   (replicate (ConstBit (wzero _)) iaddrSize));
            mem := evalConstT memInit |}.
  Proof.
    simpl; unfold pRegsToT.
    Opaque decKind.
    simpl.
    kregmap_red.
    Transparent decKind.
    reflexivity.
  Qed.

  Ltac kinvert_more :=
    kinvert;
    try (repeat
           match goal with
           | [H: annot ?klbl = Some _ |- _] => rewrite H in *
           | [H: (_ :: _)%struct = (_ :: _)%struct |- _] =>
             inversion H; subst; clear H
           end; discriminate).

  Definition PgmInitNotMMIO :=
    Kami.Ex.SCMMInv.PgmInitNotMMIO fetch ammio.

  Lemma invert_Kami_pgmInit:
    forall (Hi: PgmInitNotMMIO) km1 kt1 kupd klbl,
      pRegsToT km1 = Some kt1 ->
      Step pproc km1 kupd klbl ->
      klbl.(annot) = Some (Some "pgmInit"%string) ->
      pinit kt1 = false /\
      klbl.(calls) = FMap.M.empty _ /\
      exists kt2,
        pRegsToT (FMap.M.union kupd km1) = Some kt2 /\
        pc kt2 = pc kt1 /\ rf kt2 = rf kt1 /\
        pinit kt2 = false /\ mem kt2 = mem kt1.
  Proof.
    intros.
    kinvert_more.
    kinv_action_dest.
    1: {
      exfalso.
      clear -Hi Heqic.
      unfold ilist.ilist_to_fun_m in Heqic; simpl in Heqic.
      specialize (Hi x0); simpl in Hi.
      congruence.
    }

    kinv_red.
    unfold pRegsToT in *.
    repeat
      (match goal with
       | [H: match (FMap.M.find ?key ?m) with
             | Some _ => _
             | None => _
             end = Some _ |- _] =>
         let Hkv := fresh "H" in
         let k := fresh "k" in
         let v := fresh "v" in
         destruct (FMap.M.find key m) as [[[k|] v]|] eqn:Hkv; try discriminate
       | [H: match (decKind ?k1 ?k2) with
             | left _ => _
             | right _ => _
             end = Some _ |- _] =>
         destruct (decKind k1 k2); try discriminate
       end; kregmap_red).

    inversion H; subst; clear H.
    simpl in *.
    split; [reflexivity|].
    repeat esplit.
    assumption.
  Qed.

  Definition KamiPgmInitFull
             (pgm: word iaddrSize -> word (instBytes * BitsPerByte))
             (mem: word maddrSize -> word BitsPerByte) :=
    forall iaddr,
      pgm iaddr =
      evalExpr (alignInst type (combineBytes dataBytes (evalExpr (toAddr type iaddr)) mem)).

  Lemma invert_Kami_pgmInitEnd:
    forall (Hi: PgmInitNotMMIO) km1 kt1 kupd klbl
           (Hinv: scmm_inv maddrSize rfIdx fetch km1),
      pRegsToT km1 = Some kt1 ->
      Step pproc km1 kupd klbl ->
      klbl.(annot) = Some (Some "pgmInitEnd"%string) ->
      pinit kt1 = false /\
      klbl.(calls) = FMap.M.empty _ /\
      exists pgmFull,
        KamiPgmInitFull pgmFull (mem kt1) /\
        pRegsToT (FMap.M.union kupd km1) =
        Some {| pc := pc kt1;
                rf := rf kt1;
                pinit := true;
                pgm := pgmFull;
                mem := mem kt1 |}.
  Proof.
    intros.
    kinvert_more.
    kinv_action_dest.
    1: {
      exfalso.
      clear -Hi Heqic.
      unfold ilist.ilist_to_fun_m in Heqic; simpl in Heqic.
      specialize (Hi x0); simpl in Hi.
      congruence.
    }

    inversion_clear Hinv.
    kinv_red.
    unfold pRegsToT in *.
    repeat
      (match goal with
       | [H: match (FMap.M.find ?key ?m) with
             | Some _ => _
             | None => _
             end = Some _ |- _] =>
         let Hkv := fresh "H" in
         let k := fresh "k" in
         let v := fresh "v" in
         destruct (FMap.M.find key m) as [[[k|] v]|] eqn:Hkv; try discriminate
       | [H: match (decKind ?k1 ?k2) with
             | left _ => _
             | right _ => _
             end = Some _ |- _] =>
         destruct (decKind k1 k2); try discriminate
       end; kregmap_red).

    inversion H; subst; clear H.
    simpl in *.
    repeat split; [assumption|].
    eexists; split; [|reflexivity].

    clear -e H19.
    red; intros.
    destruct (weq iaddr pinitOfsv);
      [subst; rewrite memLoadBytes_combineBytes; reflexivity|].
    apply H19; [reflexivity|].

    clear -e n.
    assert (pinitOfsv = wones _).
    { rewrite <-wnot_idempotent with (w:= pinitOfsv).
      rewrite e.
      apply wnot_zero.
    }
    subst.

    apply lt_wlt.
    rewrite wones_pow2_minus_one.
    pose proof (wordToNat_bound iaddr).
    pose proof (NatLib.pow2_zero iaddrSize).
    assert (#iaddr = NatLib.pow2 iaddrSize - 1 \/
            #iaddr < NatLib.pow2 iaddrSize - 1)%nat by omega.
    destruct H1; [|assumption].
    assert (natToWord iaddrSize (#iaddr) =
            natToWord iaddrSize (NatLib.pow2 iaddrSize - 1)) by congruence.
    rewrite natToWord_wordToNat, <-wones_natToWord in H2; subst.
    exfalso; auto.
  Qed.

  Lemma invert_Kami_execLd:
    forall km1 kt1 kupd klbl,
      pRegsToT km1 = Some kt1 ->
      Step pproc km1 kupd klbl ->
      klbl.(annot) = Some (Some "execLd"%string) ->
      pinit kt1 = true /\
      exists curInst ldAddr,
        curInst = (pgm kt1) (evalExpr (toIAddr _ (pc kt1))) /\
        evalExpr (getOptype _ curInst) = opLd /\
        ldAddr = evalExpr
                   (calcLdAddr
                      _ (evalExpr (getLdAddr _ curInst))
                      (rf kt1 (evalExpr (getLdSrc _ curInst)))) /\
        evalExpr (getLdDst _ curInst) <> $0 /\
        (evalExpr (isMMIO _ ldAddr) = true ->
         exists kt2 mmioLdRq mmioLdRs,
           klbl.(calls) =
           FMap.M.add
             "mmioExec"%string
             (existT SignT {| arg := Struct (RqFromProc addrSize dataBytes);
                              ret := Struct (RsToProc dataBytes) |}
                     (mmioLdRq, mmioLdRs))
             (FMap.M.empty _) /\
           mmioLdRq Fin.F1 = ldAddr /\
           mmioLdRq (Fin.FS Fin.F1) = false /\
           pRegsToT (FMap.M.union kupd km1) = Some kt2 /\
           kt2 = {| pc := evalExpr (getNextPc _ (rf kt1) (pc kt1) curInst);
                    rf :=
                      fun w =>
                        if weq w (evalExpr (getLdDst _ curInst))
                        then
                          evalExpr
                            (calcLdVal
                               _ (evalExpr
                                    (calcLdAddr
                                       _ (evalExpr (getLdAddr _ curInst))
                                       (rf kt1 (evalExpr (getLdSrc _ curInst)))))
                               (mmioLdRs Fin.F1)
                               (evalExpr (getLdType type curInst)))
                        else rf kt1 w;
                    pinit := true;
                    pgm := pgm kt1;
                    mem := mem kt1 |}) /\
        (evalExpr (isMMIO _ ldAddr) = false ->
         exists kt2,
           klbl.(calls) = FMap.M.empty _ /\
           pRegsToT (FMap.M.union kupd km1) = Some kt2 /\
           kt2 = {| pc := evalExpr (getNextPc _ (rf kt1) (pc kt1) curInst);
                    rf :=
                      fun w =>
                        if weq w (evalExpr (getLdDst _ curInst))
                        then
                          evalExpr
                            (calcLdVal
                               _ (evalExpr
                                    (calcLdAddr
                                       _ (evalExpr (getLdAddr _ curInst))
                                       (rf kt1 (evalExpr (getLdSrc _ curInst)))))
                               (combineBytes dataBytes ldAddr (mem kt1))
                               (evalExpr (getLdType type curInst)))
                        else rf kt1 w;
                    pinit := true;
                    pgm := pgm kt1;
                    mem := mem kt1 |}).
  Proof.
    intros.
    kinvert_more.
    kinv_action_dest.
    - unfold pRegsToT in *.
      kregmap_red.
      destruct (FMap.M.find "mem"%string km1) as [[[memk|] memv]|]; try discriminate.
      destruct (decKind memk _); try discriminate.
      kregmap_red.
      inversion H; subst; clear H.
      simpl in *.
      repeat esplit.
      + destruct (weq _ WO~0~0); [assumption|discriminate].
      + intro Hx; rewrite Hx in H9.
        rewrite (rewrite_weq eq_refl) in H9; discriminate.
      + FMap.mred; eassumption.
      + reflexivity.
      + reflexivity.
      + exfalso; clear -H Heqic.
        unfold ilist.ilist_to_fun_m in Heqic; simpl in Heqic.
        congruence.
      + exfalso; clear -H Heqic.
        unfold ilist.ilist_to_fun_m in Heqic; simpl in Heqic.
        congruence.

    - kinv_red.
      unfold pRegsToT in *.
      kregmap_red.
      inversion H; subst; clear H; simpl in *.
      split; [reflexivity|].
      do 2 eexists.
      repeat split.
      + assumption.
      + assumption.
      + intros; exfalso; clear -H Heqic.
        unfold ilist.ilist_to_fun_m in Heqic; simpl in Heqic.
        congruence.
      + intros; repeat esplit; try assumption.
        rewrite memLoadBytes_combineBytes; reflexivity.
  Qed.

  Lemma invert_Kami_execLdZ:
    forall km1 kt1 kupd klbl,
      pRegsToT km1 = Some kt1 ->
      Step pproc km1 kupd klbl ->
      klbl.(annot) = Some (Some "execLdZ"%string) ->
      pinit kt1 = true /\
      exists curInst ldAddr,
        curInst = (pgm kt1) (evalExpr (toIAddr _ (pc kt1))) /\
        ldAddr = evalExpr
                   (calcLdAddr
                      _ (evalExpr (getLdAddr _ curInst))
                      (rf kt1 (evalExpr (getLdSrc _ curInst)))) /\
        evalExpr (getLdDst _ curInst) = $0 /\
        (evalExpr (isMMIO _ ldAddr) = true ->
         exists kt2 mmioLdRq mmioLdRs,
           klbl.(calls) =
           FMap.M.add
             "mmioExec"%string
             (existT SignT {| arg := Struct (RqFromProc addrSize dataBytes);
                              ret := Struct (RsToProc dataBytes) |}
                     (mmioLdRq, mmioLdRs))
             (FMap.M.empty _) /\
           mmioLdRq Fin.F1 = ldAddr /\
           mmioLdRq (Fin.FS Fin.F1) = false /\
           pRegsToT (FMap.M.union kupd km1) = Some kt2 /\
           kt2 = {| pc := evalExpr (getNextPc _ (rf kt1) (pc kt1) curInst);
                    rf := rf kt1;
                    pinit := true;
                    pgm := pgm kt1;
                    mem := mem kt1 |}) /\
        (evalExpr (isMMIO _ ldAddr) = false ->
         exists kt2,
           klbl.(calls) = FMap.M.empty _ /\
           pRegsToT (FMap.M.union kupd km1) = Some kt2 /\
           kt2 = {| pc := evalExpr (getNextPc _ (rf kt1) (pc kt1) curInst);
                    rf := rf kt1;
                    pinit := true;
                    pgm := pgm kt1;
                    mem := mem kt1 |}).
  Proof.
    intros.
    kinvert_more.
    kinv_action_dest.
    - unfold pRegsToT in *.
      kregmap_red.
      destruct (FMap.M.find "mem"%string km1) as [[[memk|] memv]|]; try discriminate.
      destruct (decKind memk _); try discriminate.
      kregmap_red.
      inversion H; subst; clear H.
      simpl in *.
      repeat esplit.
      + destruct (weq _ _) in H9; [assumption|discriminate].
      + FMap.mred; eassumption.
      + reflexivity.
      + reflexivity.
      + exfalso; clear -H Heqic.
        unfold ilist.ilist_to_fun_m in Heqic; simpl in Heqic.
        congruence.
    - kinv_red.
      unfold pRegsToT in *.
      kregmap_red.
      inversion H; subst; clear H; simpl in *.
      split; [reflexivity|].
      do 2 eexists.
      repeat split.
      + assumption.
      + intros; exfalso; clear -H Heqic.
        unfold ilist.ilist_to_fun_m in Heqic; simpl in Heqic.
        congruence.
      + intros; repeat esplit; assumption.
  Qed.

  Lemma invert_Kami_execSt:
    forall km1 kt1 kupd klbl,
      pRegsToT km1 = Some kt1 ->
      Step pproc km1 kupd klbl ->
      klbl.(annot) = Some (Some "execSt"%string) ->
      pinit kt1 = true /\
      exists curInst stAddr stByteEn stVal,
        curInst = (pgm kt1) (evalExpr (toIAddr _ (pc kt1))) /\
        stAddr = evalExpr
                   (calcStAddr
                      _ (evalExpr (getStAddr _ curInst))
                      (rf kt1 (evalExpr (getStSrc _ curInst)))) /\
        stByteEn = evalExpr (calcStByteEn _ curInst) /\
        stVal = rf kt1 (evalExpr (getStVSrc _ curInst)) /\
        (evalExpr (isMMIO _ stAddr) = true ->
         exists kt2 mmioStRq mmioStRs,
           klbl.(calls) =
           FMap.M.add
             "mmioExec"%string
             (existT SignT {| arg := Struct (RqFromProc addrSize dataBytes);
                              ret := Struct (RsToProc dataBytes) |}
                     (mmioStRq, mmioStRs))
             (FMap.M.empty _) /\
           mmioStRq Fin.F1 = stAddr /\
           mmioStRq (Fin.FS Fin.F1) = true /\
           mmioStRq (Fin.FS (Fin.FS Fin.F1)) = stByteEn /\
           mmioStRq (Fin.FS (Fin.FS (Fin.FS Fin.F1))) = stVal /\
           pRegsToT (FMap.M.union kupd km1) = Some kt2 /\
           kt2 = {| pc := evalExpr (getNextPc _ (rf kt1) (pc kt1) curInst);
                    rf := rf kt1;
                    pinit := true;
                    pgm := pgm kt1;
                    mem := mem kt1 |}) /\
        (evalExpr (isMMIO _ stAddr) = false ->
         exists kt2,
           klbl.(calls) = FMap.M.empty _ /\
           pRegsToT (FMap.M.union kupd km1) = Some kt2 /\
           kt2 = {| pc := evalExpr (getNextPc _ (rf kt1) (pc kt1) curInst);
                    rf := rf kt1;
                    pinit := true;
                    pgm := pgm kt1;
                    mem := updateBytes dataBytes stAddr stVal
                                       (eq_rect _ (fun n => Fin.t n -> bool)
                                                stByteEn _ (projT2 Hdb))
                                       (mem kt1)
                 |}).
  Proof.
    intros.
    kinvert_more.
    kinv_action_dest.
    - unfold pRegsToT in *.
      kregmap_red.
      destruct (FMap.M.find "mem"%string km1) as [[[memk|] memv]|]; try discriminate.
      destruct (decKind memk _); try discriminate.
      kregmap_red.
      inversion H; subst; clear H.
      simpl in *.
      repeat esplit.
      + FMap.mred; eassumption.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + exfalso; clear -H Heqic.
        unfold ilist.ilist_to_fun_m in Heqic; simpl in Heqic.
        congruence.
      + exfalso; clear -H Heqic.
        unfold ilist.ilist_to_fun_m in Heqic; simpl in Heqic.
        congruence.
    - kinv_red.
      unfold pRegsToT in *.
      kregmap_red.
      inversion H; subst; clear H; simpl in *.
      repeat split.
      do 4 eexists.
      repeat split.
      + intros; exfalso; clear -H Heqic.
        unfold ilist.ilist_to_fun_m in Heqic; simpl in Heqic.
        congruence.
      + intros; repeat esplit; try assumption.
        f_equal.
        cbv [ilist.ilist_to_fun_m]; simpl.
        destruct Hdb as [pdb ?]; subst dataBytes.
        setoid_rewrite memStoreBytes_updateBytes.
        reflexivity.
  Qed.

End Parametrized.

Definition width: Z := 32.
Definition width_cases: width = 32 \/ width = 64 := or_introl eq_refl.
Local Notation nwidth := (Z.to_nat width).

Section PerInstAddr.
  Context {instrMemSizeLg memSizeLg: Z}.
  Hypothesis (Hiaddr: 3 <= instrMemSizeLg <= 30).

  Local Notation ninstrMemSizeLg := (Z.to_nat instrMemSizeLg).
  Local Notation nmemSizeLg := (Z.to_nat memSizeLg).

  Lemma width_inst_valid:
    nwidth = (2 + ninstrMemSizeLg + (nwidth - (2 + ninstrMemSizeLg)))%nat.
  Proof.
    change 2%nat with (Z.to_nat 2).
    rewrite <-Z2Nat.inj_add by blia.
    rewrite <-Z2Nat.inj_sub by blia.
    rewrite <-Z2Nat.inj_add by (unfold width; blia).
    f_equal; blia.
  Qed.

  Local Definition pcInitVal: ConstT (Pc nwidth) :=
    ConstBit $0.

  Local Definition rfInitVal: ConstT (Vector (Data rv32DataBytes) rv32RfIdx) :=
    ConstVector (replicate (ConstBit $0) _).

  Definition procInit: ProcInit nwidth rv32DataBytes rv32RfIdx :=
    {| pcInit := pcInitVal; rfInit := rfInitVal |}.
  Variables (memInit: MemInit nmemSizeLg)
            (rv32MMIO: AbsMMIO nwidth).

  Definition procInl :=
    pprocInl (existT _ _ eq_refl) (rv32Fetch _ _ width_inst_valid)
             (rv32Dec _) (rv32Exec _)
             rv32MMIO procInit memInit.
  Definition proc: Kami.Syntax.Modules := projT1 procInl.

  Definition hst := Kami.Semantics.RegsT.
  Definition KamiMachine := hst.

  (** Abstract hardware state *)
  Definition st :=
    @pst nwidth nmemSizeLg ninstrMemSizeLg rv32InstBytes rv32DataBytes rv32RfIdx.

  Definition RegsToT (r: hst): option st :=
    pRegsToT nwidth nmemSizeLg ninstrMemSizeLg rv32InstBytes rv32DataBytes rv32RfIdx r.

  (** Refinement from [p4mm] to [proc] (as a spec) *)

  Definition getBTBIndex ty
             (pc: fullType ty (SyntaxKind (Bit nwidth))): (Bit 3) @ ty :=
    (UniBit (ConstExtract 2 3 27) #pc)%kami_expr.

  Definition getBTBTag ty
             (pc: fullType ty (SyntaxKind (Bit nwidth))): (Bit (nwidth - 3)) @ ty :=
    {UniBit (Trunc 2 _) #pc, UniBit (TruncLsb 5 27) #pc}%kami_expr.

  Definition p4mm: Kami.Syntax.Modules :=
    p4mm (existT _ _ eq_refl)
         (rv32Fetch _ _ width_inst_valid)
         (rv32Dec _) (rv32Exec _)
         rv32MMIO getBTBIndex getBTBTag
         procInit memInit.

  Theorem proc_correct: p4mm <<== proc.
  Proof.
    ketrans.
    - apply p4mm_correct. (* [p4mm] refines [scmm] *)
    - apply (projT2 procInl). (* [scmm] refines [projT1 scmmInl], the inlined module. *)
  Qed.

End PerInstAddr.

Require Import coqutil.Z.HexNotation.

(* NOTE: this definition should be consistent to the one in
 * [riscv-coq/src/riscv/Platform/FE310ExtSpec.v]. *)
Definition Kx n := ZToWord nwidth (Ox n).
Instance kami_FE310_AbsMMIO: AbsMMIO (Z.to_nat width) :=
  {| isMMIO :=
       fun _ addr =>
         ((UniBit (Trunc 2 30) # (addr) == $$(WO~0~0))
            && (($$(Kx"00020000") <= #addr) && (#addr <= $$(Kx"00022000"))
                || ($$(Kx"10008000") <= #addr) && (#addr <= $$(Kx"10010000"))
                || ($$(Kx"10012000") <= #addr) && (#addr <= $$(Kx"10013000"))
                || ($$(Kx"10013000") <= #addr) && (#addr <= $$(Kx"10014000"))))%kami_expr
  |}.

