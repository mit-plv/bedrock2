Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.

Require Import coqutil.Z.Lia.

Require Import Kami.Kami.
Require Import Kami.Ex.MemTypes Kami.Ex.SC Kami.Ex.IsaRv32.
Require Import Kami.Ex.SCMMInl Kami.Ex.SCMMInv.
Require Import Kami.Ex.ProcMemCorrect.

Require Import processor.KamiWord.

Local Open Scope Z_scope.

Set Implicit Arguments.

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
    mk { pc: Word.word addrSize;
         rf: Word.word rfIdx -> Word.word (dataBytes * BitsPerByte);
         pinit: bool;
         pgm: Word.word iaddrSize -> Word.word (instBytes * BitsPerByte);
         mem: Word.word maddrSize -> Word.word BitsPerByte
       }.

  Definition pRegsToT (r: Kami.Semantics.RegsT): option pst :=
    (mlet pcv: (Pc addrSize) <- r |> "pc" <| None;
    mlet rfv: (Vector (Data dataBytes) rfIdx) <- r |> "rf" <| None;
    mlet pinitv: Bool <- r |> "pinit" <| None;
    mlet pgmv: (Vector (Data instBytes) iaddrSize) <- r |> "pgm" <| None;
    mlet memv: (Vector (Bit BitsPerByte) maddrSize) <- r |> "mem" <| None;
    (Some {| pc := pcv; rf := rfv;
             pinit := pinitv; pgm := pgmv; mem := memv |}))%mapping.

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
             (pgm: Word.word iaddrSize -> Word.word (instBytes * BitsPerByte))
             (mem: Word.word maddrSize -> Word.word BitsPerByte) :=
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
            #iaddr < NatLib.pow2 iaddrSize - 1)%nat by blia.
    destruct H1; [|assumption].
    assert (natToWord iaddrSize (#iaddr) =
            natToWord iaddrSize (NatLib.pow2 iaddrSize - 1)) by congruence.
    rewrite natToWord_wordToNat, <-wones_natToWord in H2; subst.
    exfalso; auto.
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

#[global] Instance kami_AbsMMIO (memSizeLg: N): AbsMMIO (Z.to_nat width) :=
  {| isMMIO :=
       fun _ addr => ($$(NToWord _ (2 ^ memSizeLg)) <= #addr)%kami_expr
  |}.
