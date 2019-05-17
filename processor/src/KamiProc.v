Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.

Require Import Kami.
Require Import Kami.Ex.MemTypes Kami.Ex.SC Kami.Ex.IsaRv32 Kami.Ex.SCMMInl.
Require Import Kami.Ex.ProcMemCorrect.

Local Open Scope Z_scope.

Set Implicit Arguments.

Section Parametrized.
  Variables addrSize iaddrSize fifoSize instBytes dataBytes rfIdx: nat.

  (* External abstract ISA: decoding and execution *)
  Variables (getOptype: OptypeT instBytes)
            (getLdDst: LdDstT instBytes rfIdx)
            (getLdAddr: LdAddrT addrSize instBytes)
            (getLdSrc: LdSrcT instBytes rfIdx)
            (calcLdAddr: LdAddrCalcT addrSize dataBytes)
            (getStAddr: StAddrT addrSize instBytes)
            (getStSrc: StSrcT instBytes rfIdx)
            (calcStAddr: StAddrCalcT addrSize dataBytes)
            (getStVSrc: StVSrcT instBytes rfIdx)
            (getSrc1: Src1T instBytes rfIdx)
            (getSrc2: Src2T instBytes rfIdx)
            (getDst: DstT instBytes rfIdx)
            (exec: ExecT iaddrSize instBytes dataBytes)
            (getNextPc: NextPcT iaddrSize instBytes dataBytes rfIdx)
            (alignAddr: AlignAddrT addrSize)
            (isMMIO: IsMMIOT addrSize).

  Variable (init: ProcInit iaddrSize dataBytes rfIdx).

  Definition pprocInl :=
    scmmInl getOptype getLdDst getLdAddr getLdSrc calcLdAddr
            getStAddr getStSrc calcStAddr getStVSrc
            getSrc1 getSrc2 getDst exec getNextPc alignAddr
            isMMIO init.

  Definition pproc := projT1 pprocInl.

  (** The auxiliary hardware state; this is for manipulating hardware state
   * without knowing much about Kami states.
   *)
  Record pst :=
    mk { pc: word (2 + iaddrSize);
         rf: word rfIdx -> word (dataBytes * BitsPerByte);
         pgm: word iaddrSize -> word (instBytes * BitsPerByte);
         mem: word addrSize -> word (dataBytes * BitsPerByte)
       }.

  Definition pRegsToT (r: Kami.Semantics.RegsT): option pst :=
    (mlet pinit: Bool <- r |> "pinit" <| None;
       if pinit
       then (mlet pcv: (Pc iaddrSize) <- r |> "pc" <| None;
               mlet rfv: (Vector (Data dataBytes) rfIdx) <- r |> "rf" <| None;
               mlet pgmv: (Vector (Data instBytes) iaddrSize) <- r |> "pgm" <| None;
               mlet memv: (Vector (Data dataBytes) addrSize) <- r |> "mem" <| None;
               (Some {| pc := pcv;
                        rf := rfv;
                        pgm := pgmv;
                        mem := memv |}))
       else None)%mapping.

  (** * Inverting Kami rules for instruction executions *)

  Local Definition iaddrSizeZ: Z := Z.of_nat iaddrSize.

  Lemma invert_Kami_execLd_memory:
    forall km1 kt1 kupd klbl,
      pRegsToT km1 = Some kt1 ->
      Step pproc km1 kupd klbl ->
      klbl.(annot) = Some (Some "execLd"%string) ->
      exists curInst ldAddr,
        curInst = (pgm kt1) (split2 _ _ (pc kt1)) /\
        ldAddr =
        evalExpr
          (alignAddr
             _ (evalExpr
                  (calcLdAddr
                     _ (evalExpr (getLdAddr _ curInst))
                     (rf kt1 (evalExpr (getLdSrc _ curInst)))))) /\
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
                    pgm := pgm kt1;
                    mem := mem kt1 |}).
  Proof.
    intros.
    kinvert; try (repeat
                    match goal with
                    | [H: annot ?klbl = Some _ |- _] => rewrite H in *
                    | [H: (_ :: _)%struct = (_ :: _)%struct |- _] =>
                      inversion H; subst; clear H
                    end; discriminate).
    do 2 eexists; repeat split.
    kinv_action_dest.
    - unfold pRegsToT in *.
      kregmap_red.
      destruct (FMap.M.find "mem"%string km1)
        as [[[kind|] memv]|]; try discriminate.
      destruct (decKind kind _); try discriminate.
      kregmap_red.
      inversion H; subst; clear H.
      simpl in *.
      clear -H3 Heqic.
      congruence.
    - kinv_red.
      unfold pRegsToT in *.
      kregmap_red.
      inversion H; subst; clear H; simpl in *.
      eexists; split; [|split].
      + assumption.
      + reflexivity.
      + reflexivity.
  Qed.

  Lemma invert_Kami_execNm:
    forall km1 kt1 kupd klbl,
      pRegsToT km1 = Some kt1 ->
      Step pproc km1 kupd klbl ->
      klbl.(annot) = Some (Some "execNm"%string) ->
      exists kt2,
        klbl.(calls) = FMap.M.empty _ /\
        pRegsToT (FMap.M.union kupd km1) = Some kt2 /\
        exists curInst execVal,
          curInst = (pgm kt1) (split2 _ _ (pc kt1)) /\
          execVal = evalExpr
                      (exec
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
                   pgm := pgm kt1;
                   mem := mem kt1 |}.
  Proof.
    intros.
    kinvert; try (repeat
                    match goal with
                    | [H: annot ?klbl = Some _ |- _] => rewrite H in *
                    | [H: (_ :: _)%struct = (_ :: _)%struct |- _] =>
                      inversion H; subst; clear H
                    end; discriminate).
    kinv_action_dest.
    unfold pRegsToT in *.
    kregmap_red.
    destruct (FMap.M.find "mem"%string km1)
      as [[[kind|] memv]|]; try discriminate.
    destruct (decKind kind _); try discriminate.
    kregmap_red.
    inversion H; subst; clear H.
    repeat esplit.
    assumption.
  Qed.
  
End Parametrized.

Definition width: Z := 32.
Definition width_cases: width = 32 \/ width = 64 := or_introl eq_refl.
Local Notation nwidth := (Z.to_nat width).

Definition isMMIO: IsMMIOT nwidth := cheat _.

Section PerInstAddr.
  Context {instrMemSizeLg: Z}.
  Local Notation ninstrMemSizeLg := (Z.to_nat instrMemSizeLg).

  Definition procInit: ProcInit ninstrMemSizeLg rv32DataBytes rv32RfIdx :=
    {| pcInit := getDefaultConst _;
       rfInit := getDefaultConst _ |}.

  Definition predictNextPc ty (ppc: fullType ty (SyntaxKind (Pc ninstrMemSizeLg))) :=
    (#ppc + $4)%kami_expr.

  Definition procInl :=
    pprocInl
      rv32GetOptype rv32GetLdDst (rv32GetLdAddr _) rv32GetLdSrc (rv32CalcLdAddr _)
      (rv32GetStAddr _) rv32GetStSrc (rv32CalcStAddr _) rv32GetStVSrc
      rv32GetSrc1 rv32GetSrc2 rv32GetDst (rv32Exec _)
      (rv32NextPc _) (rv32AlignAddr _)
      isMMIO procInit.

  Definition proc: Kami.Syntax.Modules := projT1 procInl.

  Definition hst := Kami.Semantics.RegsT.

  (** Abstract hardware state *)
  Definition st :=
    @pst nwidth ninstrMemSizeLg rv32InstBytes rv32DataBytes rv32RfIdx.

  Definition RegsToT (r: hst): option st :=
    pRegsToT nwidth ninstrMemSizeLg rv32InstBytes rv32DataBytes rv32RfIdx r.

  (** Refinement from [p4mm] to [proc] (as a spec) *)

  Definition p4mm: Kami.Syntax.Modules :=
    p4mm 1 rv32GetOptype
         rv32GetLdDst (rv32GetLdAddr _) rv32GetLdSrc (rv32CalcLdAddr _)
         (rv32GetStAddr _) rv32GetStSrc (rv32CalcStAddr _) rv32GetStVSrc
         rv32GetSrc1 rv32GetSrc2 rv32GetDst (rv32Exec _)
         (rv32NextPc _) (rv32AlignAddr _)
         predictNextPc isMMIO procInit.

  Theorem proc_correct: p4mm <<== proc.
  Proof.
    ketrans.
    - apply p4mm_correct. (* [p4mm] refines [scmm] *)
    - apply (projT2 procInl). (* [scmm] refines [projT1 scmmInl], the inlined module. *)
  Qed.

End PerInstAddr.
