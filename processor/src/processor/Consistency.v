Require Import String BinInt.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Byte.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Kami.Lib.Word.
Require Import Kami.Syntax Kami.Semantics.
Require Import Kami.Ex.IsaRv32.
Require Import coqutil.Word.LittleEndian.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.

(* In order to just use [word] as a typeclass [processor.KamiWord] should
 * be imported before importing [riscv.Utility.Utility]. *)
Require Import processor.KamiWord.

Require Import riscv.Utility.Utility.
Require riscv.Platform.Memory.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Spec.Decode.

Require Import processor.KamiProc.

Local Open Scope Z_scope.

Lemma evalExpr_bit_eq_rect:
  forall n1 n2 (Hn: n1 = n2) e,
    evalExpr (eq_rect n1 (fun sz => Expr type (SyntaxKind (Bit sz))) e n2 Hn) =
    eq_rect n1 Word.word (evalExpr e) n2 Hn.
Proof.
  intros; subst.
  do 2 rewrite <-(Eqdep_dec.eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

#[global] Instance word: word 32 := @KamiWord.wordW width.
#[global] Instance word_ok: word.ok word := @KamiWord.wordWok width width_cases.

Section FetchOk.
  Fixpoint alignedXAddrsRange (base: nat) (n: nat): XAddrs (width := width) :=
    match n with
    | O => nil
    | S n' => $(base + n') :: alignedXAddrsRange base n'
    end.

  Lemma alignedXAddrsRange_bound:
    forall base n a,
      In a (alignedXAddrsRange base n) ->
      (wordToN a < N.of_nat (base + n))%N.
  Proof.
    induction n; [simpl; intros; exfalso; auto|].
    unfold alignedXAddrsRange; fold alignedXAddrsRange.
    intros; destruct H.
    - subst.
      apply N.le_lt_trans with (m:= N.of_nat (base + n)); [|blia].
      rewrite wordToN_nat.
      apply N.compare_ge_iff.
      rewrite <-Nnat.Nat2N.inj_compare.
      apply Nat.compare_ge_iff.
      apply wordToNat_natToWord_le.
    - etransitivity; [eauto|blia].
  Qed.

  Context {mem: map.map word byte}.

  (* [instrMemSizeLg] is the log number of instructions in the instruction cache.
   * If the instruction base address is just 0, then the address range for
   * the instructions is [0 -- 4 * 2^(instrMemSizeLg)].
   *)
  Variables instrMemSizeLg memSizeLg: Z.
  Hypothesis (HinstrMemBound: 3 <= instrMemSizeLg <= width - 2).
  Local Notation ninstrMemSizeLg := (Z.to_nat instrMemSizeLg).
  Local Notation nmemSizeLg := (Z.to_nat memSizeLg).
  Local Notation nwidth := (Z.to_nat width).
  Local Notation width_inst_valid := (width_inst_valid HinstrMemBound).

  Definition instrMemSize: nat := NatLib.pow2 (2 + Z.to_nat instrMemSizeLg).

  Definition pc_related (kpc rpc: kword width): Prop :=
    kpc = rpc.

  Definition AddrAligned (addr: kword width) :=
    split1 2 (nwidth - 2) addr = WO~0~0.

  (* set of executable addresses in the kami processor *)
  Definition kamiXAddrs: XAddrs :=
    alignedXAddrsRange 0 instrMemSize.

  Lemma AddrAligned_plus4:
    forall rpc: KamiWord.word _,
      AddrAligned rpc ->
      AddrAligned (word.add rpc (word.of_Z 4)).
  Proof.
    cbv [AddrAligned word.add wordW KamiWord.word].
    intros.
    rewrite <-H.
    apply split1_wplus_silent.
    reflexivity.
  Qed.

  Lemma kamiXAddrs_isXAddr1_bound:
    forall a,
      isXAddr1 a kamiXAddrs ->
      (wordToN a < NatLib.Npow2 (2 + Z.to_nat instrMemSizeLg))%N.
  Proof.
    cbv [isXAddr1]; intros.
    apply alignedXAddrsRange_bound in H.
    simpl in H.
    unfold instrMemSize in H.
    rewrite <-NatLib.pow2_N in H.
    assumption.
  Qed.

  Lemma kamiXAddrs_isXAddr4_bound:
    forall a,
      isXAddr4 a kamiXAddrs ->
      (wordToN a < NatLib.Npow2 (2 + Z.to_nat instrMemSizeLg))%N.
  Proof.
    intros.
    apply kamiXAddrs_isXAddr1_bound.
    apply H.
  Qed.

  Definition mem_related (kmem: kword memSizeLg -> kword 8)
             (rmem : mem): Prop :=
    forall addr: kword width,
      map.get rmem addr =
      if Z.ltb (kunsigned addr) (Z.pow 2 memSizeLg)
      then Some (byte.of_Z (uwordToZ (kmem (evalZeroExtendTrunc _ addr))))
      else None.

  Definition RiscvXAddrsSafe
             (kmemi: kword instrMemSizeLg -> kword width)
             (kmemd: kword memSizeLg -> kword 8)
             (xaddrs: XAddrs) :=
    forall rpc,
      isXAddr4 rpc xaddrs ->
      isXAddr4 rpc kamiXAddrs /\
      (AddrAligned rpc ->
       forall kpc,
         pc_related kpc rpc ->
         Kami.Ex.SC.combineBytes 4%nat rpc kmemd =
         kmemi (evalExpr (IsaRv32.rv32ToIAddr _ _ width_inst_valid _ kpc))).

  Lemma rv32ToAddr_rv32ToIAddr_consistent:
    forall rpc,
      (wordToN rpc < NatLib.Npow2 (2 + Z.to_nat instrMemSizeLg))%N ->
      AddrAligned rpc ->
      rpc =
      evalExpr
        (IsaRv32.rv32ToAddr
           _ _ width_inst_valid type
           (evalExpr (IsaRv32.rv32ToIAddr _ _ width_inst_valid type rpc))).
  Proof.
    intros.
    cbv [IsaRv32.rv32ToAddr IsaRv32.rv32ToIAddr].
    unfold eq_rect_r; rewrite evalExpr_bit_eq_rect.
    cbv [evalExpr evalBinBit evalUniBit].
    cbv [evalConstT].

    apply wordToN_inj.
    rewrite wordToN_eq_rect.
    do 2 rewrite wordToN_combine.
    do 2 rewrite wordToN_wzero.
    rewrite N.mul_0_r, N.add_0_r, N.add_0_l.
    rewrite wordToN_split2.
    rewrite wordToN_split1.
    rewrite wordToN_eq_rect.
    rewrite N.mod_small by assumption.

    red in H0.
    rewrite <-(Word.combine_split 2 (nwidth - 2) rpc) in *.
    remember (split1 2 (nwidth - 2) rpc) as rpc1; clear Heqrpc1.
    remember (split2 2 (nwidth - 2) rpc) as rpc2; clear Heqrpc2.
    rewrite split1_combine in H0; subst.
    change (BinInt.Z.to_nat width) with (2 + (BinInt.Z.to_nat width - 2))%nat.

    rewrite wordToN_combine.
    rewrite wordToN_wzero.
    rewrite N.add_0_l.
    rewrite N.mul_comm at 2.
    rewrite N.div_mul by discriminate.
    reflexivity.
  Qed.

  Hypothesis (Hkmem: 2 + instrMemSizeLg < memSizeLg <= width).

  Lemma getmany_of_tuple_combineBytes_consistent:
    forall kmem rmem rpc,
      mem_related kmem rmem ->
      isXAddr4 rpc kamiXAddrs ->
      exists rinst : HList.tuple byte 4,
        map.getmany_of_tuple rmem (Memory.footprint rpc 4) = Some rinst /\
        combine 4 rinst = kunsigned (SC.combineBytes 4 rpc kmem : kword 32).
  Proof.
    intros.

    assert (Z.pow 2 (Z.of_nat (2 + ninstrMemSizeLg)) < Z.pow 2 memSizeLg) as Hkmemp
        by (apply Z.pow_lt_mono_r; blia).

    assert (Z.ltb (kunsigned rpc) (Z.pow 2 memSizeLg) = true) as Hrpc0.
    { destruct H0 as [? _].
      apply kamiXAddrs_isXAddr1_bound in H0.
      destruct (Z.ltb_spec (kunsigned rpc) (Z.pow 2 memSizeLg)); [reflexivity|].
      apply N2Z.inj_lt in H0.
      rewrite NatLib.Z_of_N_Npow2 in H0.
      cbv [kunsigned] in H1.
      blia.
    }

    assert (Z.ltb (kunsigned (rpc ^+ ZToWord _ 1)) (Z.pow 2 memSizeLg) = true) as Hrpc1.
    { destruct H0 as [_ [? _]].
      cbv [word.add word wordW KamiWord.word] in H0.
      cbv [word.of_Z kofZ] in H0.
      apply kamiXAddrs_isXAddr1_bound in H0.
      destruct (Z.ltb_spec (kunsigned (rpc ^+ ZToWord _ 1)) (Z.pow 2 memSizeLg)); [reflexivity|].
      apply N2Z.inj_lt in H0.
      rewrite NatLib.Z_of_N_Npow2 in H0.
      cbv [kunsigned] in H1.
      blia.
    }

    assert (Z.ltb (kunsigned (rpc ^+ ZToWord _ 1 ^+ ZToWord _ 1))
                  (Z.pow 2 memSizeLg) = true) as Hrpc2.
    { destruct H0 as [_ [_ [? _]]].
      cbv [word.add word wordW KamiWord.word] in H0.
      cbv [word.of_Z kofZ] in H0.
      apply kamiXAddrs_isXAddr1_bound in H0.
      rewrite <-wplus_assoc.
      change (ZToWord nwidth 1 ^+ ZToWord nwidth 1) with (ZToWord nwidth 2).
      destruct (Z.ltb_spec (kunsigned (rpc ^+ ZToWord _ 2)) (Z.pow 2 memSizeLg)); [reflexivity|].
      apply N2Z.inj_lt in H0.
      rewrite NatLib.Z_of_N_Npow2 in H0.
      cbv [kunsigned] in H1.
      blia.
    }

    assert (Z.ltb (kunsigned (rpc ^+ ZToWord _ 1 ^+ ZToWord _ 1 ^+ ZToWord _ 1))
                  (Z.pow 2 memSizeLg) = true) as Hrpc3.
    { destruct H0 as [_ [_ [_ ?]]].
      cbv [word.add word wordW KamiWord.word] in H0.
      cbv [word.of_Z kofZ] in H0.
      apply kamiXAddrs_isXAddr1_bound in H0.
      rewrite <-wplus_assoc.
      change (ZToWord nwidth 1 ^+ ZToWord nwidth 1) with (ZToWord nwidth 2).
      rewrite <-wplus_assoc.
      change (ZToWord nwidth 1 ^+ ZToWord nwidth 2) with (ZToWord nwidth 3).
      destruct (Z.ltb_spec (kunsigned (rpc ^+ ZToWord _ 3)) (Z.pow 2 memSizeLg)); [reflexivity|].
      apply N2Z.inj_lt in H0.
      rewrite NatLib.Z_of_N_Npow2 in H0.
      cbv [kunsigned] in H1.
      blia.
    }

    cbv [Memory.footprint HList.tuple.unfoldn].
    eexists; split.
    - pose proof (H rpc); rewrite Hrpc0 in H1.
      pose proof (H (rpc ^+ ZToWord _ 1)); rewrite Hrpc1 in H2.
      pose proof (H (rpc ^+ ZToWord _ 1 ^+ ZToWord _ 1)); rewrite Hrpc2 in H3.
      pose proof (H (rpc ^+ ZToWord _ 1 ^+ ZToWord _ 1 ^+ ZToWord _ 1)); rewrite Hrpc3 in H4.

      instantiate (1:= {| PrimitivePair.pair._1 := _;
                          PrimitivePair.pair._2 := _ |}).
      erewrite map.build_getmany_of_tuple_Some; [reflexivity|apply H1|].
      cbv [PrimitivePair.pair._2].
      instantiate (1:= {| PrimitivePair.pair._1 := _;
                          PrimitivePair.pair._2 := _ |}).
      erewrite map.build_getmany_of_tuple_Some; [reflexivity|apply H2|].
      cbv [PrimitivePair.pair._2].
      instantiate (1:= {| PrimitivePair.pair._1 := _;
                          PrimitivePair.pair._2 := _ |}).
      erewrite map.build_getmany_of_tuple_Some; [reflexivity|apply H3|].
      cbv [PrimitivePair.pair._2].
      instantiate (1:= {| PrimitivePair.pair._1 := _;
                          PrimitivePair.pair._2 := _ |}).
      erewrite map.build_getmany_of_tuple_Some; [reflexivity|apply H4|].
      cbv [PrimitivePair.pair._2].
      reflexivity.

    - cbv [combine PrimitivePair.pair._1 PrimitivePair.pair._2
                   word.unsigned KamiWord.word kunsigned
                   SC.combineBytes].
      rewrite Z_of_wordToN_combine_alt with (sz1:= 8%nat) (sz2:= 24%nat).
      rewrite Z_of_wordToN_combine_alt with (sz1:= 8%nat) (sz2:= 16%nat).
      rewrite Z_of_wordToN_combine_alt with (sz1:= 8%nat) (sz2:= 8%nat).
      rewrite Z_of_wordToN_combine_alt with (sz1:= 8%nat) (sz2:= 0%nat).
      rewrite !byte.unsigned_of_Z.
      cbv [byte.wrap].
      change (@uwordToZ (BinInt.Z.to_nat 8)) with (@word.unsigned 8 _).
      rewrite !(@Properties.word.wrap_unsigned 8 _ word8ok).
      reflexivity.
  Qed.

  Lemma fetch_ok:
    forall (kmemi: kword instrMemSizeLg -> kword width)
           (kmemd: kword memSizeLg -> kword 8)
           (kpc: kword width)
           (xaddrs: XAddrs)
           (Hxs: RiscvXAddrsSafe kmemi kmemd xaddrs)
           (rmemd: mem)
           (rpc: kword width),
      isXAddr4 (width := width) rpc xaddrs ->
      AddrAligned rpc ->
      pc_related kpc rpc ->
      mem_related kmemd rmemd ->
      exists (rinst: HList.tuple byte 4),
        Memory.load_bytes 4 rmemd rpc = Some rinst /\
        combine 4 rinst = kunsigned (kmemi (evalExpr (IsaRv32.rv32ToIAddr
                                                        _ _ width_inst_valid
                                                        _ kpc))).
  Proof.
    intros.
    specialize (Hxs _ H); destruct Hxs.
    specialize (H4 H0 _ H1).
    rewrite <-H4.
    eapply getmany_of_tuple_combineBytes_consistent; assumption.
  Qed.

End FetchOk.

Section DecExecOk.
  Variables (instrMemSizeLg: Z).
  Hypothesis (HinstrMemBound: 3 <= instrMemSizeLg <= width - 2).

  Local Definition kamiProc := @KamiProc.proc instrMemSizeLg.
  Local Definition KamiSt := @KamiProc.st instrMemSizeLg.

  (** * Register file mapping *)

  Context {Registers: map.map Z word}
          (Registers_ok : map.ok Registers).

  Definition regs_related (krf: kword 5 -> kword width)
             (rrf: Registers): Prop :=
    forall w, w <> $0 -> map.get rrf (Z.of_N (wordToN w)) = Some (krf w).

  Lemma regs_related_get:
    forall krf (Hkrf0: krf $0 = $0) rrf,
      regs_related krf rrf ->
      forall w z,
        Z.of_N (wordToN w) = z ->
        krf w =
        (if Z.eq_dec z 0 then kofZ 0
         else
           match map.get rrf z with
           | Some x => x
           | None => kofZ 0
           end).
  Proof.
    intros.
    destruct (Z.eq_dec _ _).
    - subst; destruct (weq w $0); subst; [assumption|].
      exfalso.
      rewrite <-N2Z.inj_0 in e.
      apply N2Z.inj in e.
      rewrite <-wordToN_wzero with (sz:= 5%nat) in e.
      apply wordToN_inj in e; auto.
    - subst; rewrite H; [reflexivity|].
      intro; subst; auto.
  Qed.

  Lemma regs_related_put krf rrf kv rv kk rk
        (Hrf: regs_related krf rrf)
        (Hk: Z.of_N (wordToN kk) = rk)
        (Hv: kv = rv):
    regs_related
      (fun w : Word.word rv32RfIdx => if weq w kk then kv else krf w)
      (map.put rrf rk rv).
  Proof.
    rewrite <-Hv.
    cbv [regs_related].
    intros i Hi.
    destruct (weq (sz:= rv32RfIdx) i kk).
    - subst; apply map.get_put_same.
    - rewrite map.get_put_diff.
      + apply Hrf; auto.
      + subst; intro.
        apply N2Z.inj, wordToN_inj in H; auto.
  Qed.

End DecExecOk.
