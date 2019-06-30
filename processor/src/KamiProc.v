Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.

Require Import Kami.
Require Import Kami.Ex.MemTypes Kami.Ex.SC Kami.Ex.IsaRv32.
Require Import Kami.Ex.SCMMInl Kami.Ex.SCMMInv.
Require Import Kami.Ex.ProcMemCorrect.

Local Open Scope Z_scope.

Set Implicit Arguments.

Lemma wnot_idempotent:
  forall {sz} (w: word sz),
    wnot (wnot w) = w.
Proof.
Admitted.

Section Parametrized.
  Variables addrSize iaddrSize fifoSize instBytes dataBytes rfIdx: nat.

  Variables (fetch: AbsFetch addrSize iaddrSize instBytes dataBytes)
            (dec: AbsDec addrSize instBytes dataBytes rfIdx)
            (exec: AbsExec iaddrSize instBytes dataBytes rfIdx)
            (ammio: AbsMMIO addrSize).

  Variable (procInit: ProcInit iaddrSize dataBytes rfIdx)
           (memInit: MemInit addrSize dataBytes).

  Definition pprocInl := scmmInl fetch dec exec ammio procInit memInit.
  Definition pproc := projT1 pprocInl.

  (** The auxiliary hardware state; this is for manipulating hardware state
   * without knowing much about Kami states.
   *)
  Record pst :=
    mk { pc: word (2 + iaddrSize);
         rf: word rfIdx -> word (dataBytes * BitsPerByte);
         pinit: bool;
         pgm: word iaddrSize -> word (instBytes * BitsPerByte);
         mem: word addrSize -> word (dataBytes * BitsPerByte)
       }.

  Definition pRegsToT (r: Kami.Semantics.RegsT): option pst :=
    (mlet pcv: (Pc iaddrSize) <- r |> "pc" <| None;
       mlet rfv: (Vector (Data dataBytes) rfIdx) <- r |> "rf" <| None;
       mlet pinitv: Bool <- r |> "pinit" <| None;
       mlet pgmv: (Vector (Data instBytes) iaddrSize) <- r |> "pgm" <| None;
       mlet memv: (Vector (Data dataBytes) addrSize) <- r |> "mem" <| None;
       (Some {| pc := pcv; rf := rfv;
                pinit := pinitv; pgm := pgmv; mem := memv |}))%mapping.

  (** * Inverting Kami rules for instruction executions *)

  Local Definition iaddrSizeZ: Z := Z.of_nat iaddrSize.

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
             (mem: word addrSize -> word (dataBytes * BitsPerByte)) :=
    forall iaddr,
      pgm iaddr =
      evalExpr (alignInst type (mem (evalExpr (alignAddr type iaddr)))).

  Lemma invert_Kami_pgmInitEnd:
    forall (Hi: PgmInitNotMMIO) km1 kt1 kupd klbl
           (Hinv: scmm_inv rfIdx fetch km1),
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

    clear -e H18.
    red; intros.
    destruct (weq iaddr pinitOfsv); [subst; reflexivity|].
    apply (H18 eq_refl).

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
        curInst = (pgm kt1) (split2 _ _ (pc kt1)) /\
        ldAddr = evalExpr
                   (calcLdAddr
                      _ (evalExpr (getLdAddr _ curInst))
                      (rf kt1 (evalExpr (getLdSrc _ curInst)))) /\
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
                        then mmioLdRs Fin.F1
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
                        then mem kt1 ldAddr
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
      + FMap.mred; eassumption.
      + reflexivity.
      + reflexivity.
      + exfalso; clear -H Heqic; congruence.
      + exfalso; clear -H Heqic; congruence.
    - kinv_red.
      unfold pRegsToT in *.
      kregmap_red.
      inversion H; subst; clear H; simpl in *.
      split; [reflexivity|].
      do 2 eexists.
      repeat split.
      + intros; exfalso; clear -H Heqic; congruence.
      + intros; repeat esplit; assumption.
  Qed.

  Lemma invert_Kami_execLdZ:
    forall km1 kt1 kupd klbl,
      pRegsToT km1 = Some kt1 ->
      Step pproc km1 kupd klbl ->
      klbl.(annot) = Some (Some "execLdZ"%string) ->
      pinit kt1 = true /\
      exists curInst ldAddr,
        curInst = (pgm kt1) (split2 _ _ (pc kt1)) /\
        ldAddr = evalExpr
                   (calcLdAddr
                      _ (evalExpr (getLdAddr _ curInst))
                      (rf kt1 (evalExpr (getLdSrc _ curInst)))) /\
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
      + FMap.mred; eassumption.
      + reflexivity.
      + reflexivity.
      + exfalso; clear -H Heqic; congruence.
    - kinv_red.
      unfold pRegsToT in *.
      kregmap_red.
      inversion H; subst; clear H; simpl in *.
      split; [reflexivity|].
      do 2 eexists.
      repeat split.
      + intros; exfalso; clear -H Heqic; congruence.
      + intros; repeat esplit; assumption.
  Qed.

  Lemma invert_Kami_execSt:
    forall km1 kt1 kupd klbl,
      pRegsToT km1 = Some kt1 ->
      Step pproc km1 kupd klbl ->
      klbl.(annot) = Some (Some "execSt"%string) ->
      pinit kt1 = true /\
      exists curInst stAddr stVal,
        curInst = (pgm kt1) (split2 _ _ (pc kt1)) /\
        stAddr = evalExpr
                   (calcStAddr
                      _ (evalExpr (getStAddr _ curInst))
                      (rf kt1 (evalExpr (getStSrc _ curInst)))) /\
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
           mmioStRq (Fin.FS (Fin.FS Fin.F1)) = stVal /\
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
                    mem :=
                      fun w =>
                        if weq w stAddr then stVal else mem kt1 w |}).
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
      + exfalso; clear -H Heqic; congruence.
      + exfalso; clear -H Heqic; congruence.
    - kinv_red.
      unfold pRegsToT in *.
      kregmap_red.
      inversion H; subst; clear H; simpl in *.
      repeat split.
      do 3 eexists.
      repeat split.
      + intros; exfalso; clear -H Heqic; congruence.
      + intros; repeat esplit; assumption.
  Qed.

  Lemma invert_Kami_execNm:
    forall km1 kt1 kupd klbl,
      pRegsToT km1 = Some kt1 ->
      Step pproc km1 kupd klbl ->
      klbl.(annot) = Some (Some "execNm"%string) ->
      pinit kt1 = true /\
      klbl.(calls) = FMap.M.empty _ /\
      exists kt2,
        pRegsToT (FMap.M.union kupd km1) = Some kt2 /\
        exists curInst execVal,
          curInst = (pgm kt1) (split2 _ _ (pc kt1)) /\
          execVal = evalExpr
                      (doExec
                         _
                         (rf kt1 (evalExpr (getSrc1 _ curInst)))
                         (rf kt1 (evalExpr (getSrc2 _ curInst)))
                         (pc kt1)
                         curInst) /\
          kt2 = {| pc := evalExpr (getNextPc _ (rf kt1) (pc kt1) curInst);
                   rf :=
                     fun w =>
                       if weq w (evalExpr (getDst type curInst))
                       then execVal else rf kt1 w;
                   pinit := true;
                   pgm := pgm kt1;
                   mem := mem kt1 |}.
  Proof.
    intros.
    kinvert_more.
    kinv_action_dest.
    unfold pRegsToT in *.
    kregmap_red.
    destruct (FMap.M.find "mem"%string km1) as [[[memk|] memv]|]; try discriminate.
    destruct (decKind memk _); try discriminate.
    kregmap_red.
    inversion H; subst; clear H.
    repeat esplit.
    assumption.
  Qed.

End Parametrized.

Definition width: Z := 32.
Definition width_cases: width = 32 \/ width = 64 := or_introl eq_refl.
Local Notation nwidth := (Z.to_nat width).

Instance rv32MMIO: AbsMMIO nwidth :=
  {| isMMIO := cheat _ |}.

Section PerInstAddr.
  Context {instrMemSizeLg: Z}.
  Local Notation ninstrMemSizeLg := (Z.to_nat instrMemSizeLg).

  Local Definition pcInitVal: ConstT (Pc ninstrMemSizeLg) :=
    ConstBit $0.

  Local Definition rfInitVal: ConstT (Vector (Data rv32DataBytes) rv32RfIdx) :=
    ConstVector (replicate (ConstBit $0) _).

  Definition procInit: ProcInit ninstrMemSizeLg rv32DataBytes rv32RfIdx :=
    {| pcInit := pcInitVal; rfInit := rfInitVal |}.
  Variable (memInit: MemInit nwidth rv32DataBytes).

  Definition predictNextPc ty (ppc: fullType ty (SyntaxKind (Pc ninstrMemSizeLg))) :=
    (#ppc + $4)%kami_expr.

  Definition procInl :=
    pprocInl (rv32Fetch _ _) (rv32Dec _) (rv32Exec _) rv32MMIO procInit memInit.
  Definition proc: Kami.Syntax.Modules := projT1 procInl.

  Definition hst := Kami.Semantics.RegsT.

  (** Abstract hardware state *)
  Definition st :=
    @pst nwidth ninstrMemSizeLg rv32InstBytes rv32DataBytes rv32RfIdx.

  Definition RegsToT (r: hst): option st :=
    pRegsToT nwidth ninstrMemSizeLg rv32InstBytes rv32DataBytes rv32RfIdx r.

  (** Refinement from [p4mm] to [proc] (as a spec) *)

  Definition p4mm: Kami.Syntax.Modules :=
    p4mm 1 (rv32Fetch _ _) (rv32Dec _) (rv32Exec _) rv32MMIO
         predictNextPc procInit memInit.

  Theorem proc_correct: p4mm <<== proc.
  Proof.
    ketrans.
    - apply p4mm_correct. (* [p4mm] refines [scmm] *)
    - apply (projT2 procInl). (* [scmm] refines [projT1 scmmInl], the inlined module. *)
  Qed.

End PerInstAddr.
