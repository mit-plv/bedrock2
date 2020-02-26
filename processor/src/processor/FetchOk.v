Require Import String BinInt.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Byte.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Kami.Lib.Word.
Require Import Kami.Syntax Kami.Semantics.
Require Import coqutil.Word.LittleEndian.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.

(* In order to just use [word] as a typeclass [processor.KamiWord] should
 * be imported before importing [riscv.Utility.Utility]. *)
Require Import processor.KamiWord.
Require Import riscv.Utility.Utility.

Require riscv.Platform.Memory.
Require Import riscv.Platform.RiscvMachine.

Require Import processor.KamiProc.

Local Open Scope Z_scope.

Lemma wordToN_eq_rect:
  forall sz (w: Word.word sz) nsz Hsz,
    wordToN (eq_rect _ Word.word w nsz Hsz) = wordToN w.
Proof.
  intros; subst; simpl; reflexivity.
Qed.

Lemma Z_pow_add_lor:
  forall n m p: Z,
    0 <= n < 2 ^ p -> 0 <= m -> 0 <= p ->
    (n + 2 ^ p * m)%Z = Z.lor n (2 ^ p * m).
Proof.
  intros.
  apply eq_sym, or_to_plus.
  rewrite Z.mul_comm, <-Z.shiftl_mul_pow2 by assumption.
  replace n with (Z.land n (Z.ones p)).
  - bitblast.Z.bitblast.
    rewrite Z.testbit_neg_r with (n:= l) by blia.
    apply Bool.andb_false_r.
  - destruct (Z.eq_dec n 0); [subst; apply Z.land_0_l|].
    assert (0 < n) by blia.
    rewrite Z.land_ones_low; [reflexivity|blia|].
    apply Z.log2_lt_pow2; blia.
Qed.

Lemma Z_of_wordToN_combine_alt:
  forall sz1 (w1: Word.word sz1) sz2 (w2: Word.word sz2),
    Z.of_N (wordToN (Word.combine w1 w2)) =
    Z.lor (Z.of_N (wordToN w1)) (Z.shiftl (Z.of_N (wordToN w2)) (Z.of_N (N.of_nat sz1))).
Proof.
  intros.
  rewrite wordToN_combine, N2Z.inj_add, N2Z.inj_mul.
  assert (0 <= Z.of_N (wordToN w1) < 2 ^ (Z.of_N (N.of_nat sz1))).
  { split; [apply N2Z.is_nonneg|].
    clear.
    induction w1; [simpl; blia|].
    unfold wordToN; fold wordToN.
    destruct b.
    { rewrite N2Z.inj_succ, N2Z.inj_mul, Nnat.Nat2N.inj_succ.
      rewrite N2Z.inj_succ.
      rewrite Z.pow_succ_r by blia; blia.
    }
    { rewrite N2Z.inj_mul, Nnat.Nat2N.inj_succ.
      rewrite N2Z.inj_succ.
      rewrite Z.pow_succ_r by blia; blia.
    }
  }
  assert (0 <= Z.of_N (wordToN w2)) by blia.
  assert (0 <= Z.of_N (N.of_nat sz1)) by blia.

  replace (Z.of_N (NatLib.Npow2 sz1)) with (Z.pow 2 (Z.of_N (N.of_nat sz1))).
  - generalize dependent (Z.of_N (wordToN w1)).
    generalize dependent (Z.of_N (wordToN w2)).
    generalize dependent (Z.of_N (N.of_nat sz1)).
    intros p ? z1 ? z2 ?.
    rewrite Z.shiftl_mul_pow2 by assumption.
    rewrite Z.mul_comm with (n:= z1).
    apply Z_pow_add_lor; assumption.
  - clear; induction sz1; [reflexivity|].
    rewrite Nnat.Nat2N.inj_succ, N2Z.inj_succ.
    unfold NatLib.Npow2; fold NatLib.Npow2.
    rewrite Z.pow_succ_r by blia; blia.
Qed.

Lemma evalExpr_bit_eq_rect:
  forall n1 n2 (Hn: n1 = n2) e,
    evalExpr (eq_rect n1 (fun sz => Expr type (SyntaxKind (Bit sz))) e n2 Hn) =
    eq_rect n1 Word.word (evalExpr e) n2 Hn.
Proof.
  intros; subst.
  do 2 rewrite <-(Eqdep_dec.eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Lemma Z_lor_of_N:
  forall n m,
    Z.lor (Z.of_N n) (Z.of_N m) = Z.of_N (N.lor n m).
Proof.
  intros.
  cbv [Z.lor N.lor].
  destruct n, m; reflexivity.
Qed.

Lemma Z_shiftl_of_N:
  forall n sh,
    Z.shiftl (Z.of_N n) (Z.of_N sh) = Z.of_N (N.shiftl n sh).
Proof.
  intros.
  destruct n; [simpl; apply Z.shiftl_0_l|].
  simpl.
  cbv [Z.shiftl Pos.shiftl].
  destruct sh; simpl; [reflexivity|].
  revert p.
  induction p0; intros; auto.
  - simpl; do 2 rewrite IHp0; reflexivity.
  - simpl; do 2 rewrite IHp0; reflexivity.
Qed.

Lemma ZToWord_zero:
  forall n, ZToWord n 0 = wzero n.
Proof.
  destruct n; intros; [shatterer|].
  apply wordToZ_inj.
  rewrite wordToZ_ZToWord.
  - rewrite wordToZ_wzero; reflexivity.
  - split.
    + blia.
    + change 0 with (Z.of_nat 0).
      apply Nat2Z.inj_lt.
      apply NatLib.zero_lt_pow2.
Qed.

Lemma combine_wplus_wzero:
  forall sz1 (wb: Word.word sz1) sz2 (w1 w2: Word.word sz2),
    Word.combine wb w1 ^+ Word.combine (wzero sz1) w2 =
    Word.combine wb (w1 ^+ w2).
Proof.
  induction wb; intros; [reflexivity|].
  simpl; rewrite <-wplus_WS_0.
  rewrite IHwb; reflexivity.
Qed.

Lemma split1_wplus_silent:
  forall sz1 sz2 (w1 w2: Word.word (sz1 + sz2)),
    split1 sz1 sz2 w2 = wzero _ ->
    split1 sz1 sz2 (w1 ^+ w2) = split1 sz1 sz2 w1.
Proof.
  intros.
  pose proof (word_combinable _ _ w1).
  destruct H0 as [w11 [w12 ?]].
  pose proof (word_combinable _ _ w2).
  destruct H1 as [w21 [w22 ?]].
  subst; rewrite split1_combine in H; subst.
  rewrite combine_wplus_wzero.
  do 2 rewrite split1_combine.
  reflexivity.
Qed.

Section FetchOk.

  Local Hint Resolve (@KamiWord.WordsKami width width_cases): typeclass_instances.
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

  Fixpoint alignedXAddrsRange (base: nat) (n: nat): XAddrs :=
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

  (* set of executable addresses in the kami processor *)
  Definition kamiXAddrs: XAddrs :=
    alignedXAddrsRange 0 instrMemSize.

  Lemma AddrAligned_plus4:
    forall rpc,
      AddrAligned rpc ->
      AddrAligned (word.add rpc (word.of_Z 4)).
  Proof.
    cbv [AddrAligned word.add word WordsKami wordW KamiWord.word].
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

  Lemma wordToN_split1 a b w :
    wordToN (@split1 a b w) = BinNat.N.modulo (wordToN w) (NatLib.Npow2 a).
  Proof.
    pose proof wordToNat_split1 a b w as HH.
    eapply Nnat.Nat2N.inj_iff in HH.
    rewrite wordToN_nat, HH; f_equal; clear HH.
    rewrite wordToN_nat, NatLib.pow2_N.
    generalize (#w); intro.
    remember (NatLib.pow2 a) as pa eqn:Ha.
    pose proof NatLib.pow2_zero a.
    pose proof mod_Zmod n pa ltac:(Lia.lia).
    pose proof Znat.N2Z.inj_mod (BinNat.N.of_nat n) (BinNat.N.of_nat pa) ltac:(blia).
    rewrite Znat.nat_N_Z in *.
    Lia.lia.
  Qed.

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
        combine 4 rinst = kunsigned (width:= 32) (SC.combineBytes 4 rpc kmem).
  Proof.
    intros.

    assert (Z.pow 2 (Z.of_nat (2 + ninstrMemSizeLg)) < Z.pow 2 memSizeLg) as Hkmemp
        by (apply Z.pow_lt_mono_r; Lia.lia).

    assert (Z.ltb (kunsigned rpc) (Z.pow 2 memSizeLg) = true) as Hrpc0.
    { destruct H0 as [? _].
      apply kamiXAddrs_isXAddr1_bound in H0.
      destruct (Z.ltb_spec (kunsigned rpc) (Z.pow 2 memSizeLg)); [reflexivity|].
      apply N2Z.inj_lt in H0.
      rewrite NatLib.Z_of_N_Npow2 in H0.
      cbv [kunsigned] in H1.
      Lia.lia.
    }

    assert (Z.ltb (kunsigned (rpc ^+ ZToWord _ 1)) (Z.pow 2 memSizeLg) = true) as Hrpc1.
    { destruct H0 as [_ [? _]].
      cbv [word.add word WordsKami wordW KamiWord.word] in H0.
      cbv [word.of_Z kofZ] in H0.
      apply kamiXAddrs_isXAddr1_bound in H0.
      destruct (Z.ltb_spec (kunsigned (rpc ^+ ZToWord _ 1)) (Z.pow 2 memSizeLg)); [reflexivity|].
      apply N2Z.inj_lt in H0.
      rewrite NatLib.Z_of_N_Npow2 in H0.
      cbv [kunsigned] in H1.
      Lia.lia.
    }

    assert (Z.ltb (kunsigned (rpc ^+ ZToWord _ 1 ^+ ZToWord _ 1))
                  (Z.pow 2 memSizeLg) = true) as Hrpc2.
    { destruct H0 as [_ [_ [? _]]].
      cbv [word.add word WordsKami wordW KamiWord.word] in H0.
      cbv [word.of_Z kofZ] in H0.
      apply kamiXAddrs_isXAddr1_bound in H0.
      rewrite <-wplus_assoc.
      change (ZToWord nwidth 1 ^+ ZToWord nwidth 1) with (ZToWord nwidth 2).
      destruct (Z.ltb_spec (kunsigned (rpc ^+ ZToWord _ 2)) (Z.pow 2 memSizeLg)); [reflexivity|].
      apply N2Z.inj_lt in H0.
      rewrite NatLib.Z_of_N_Npow2 in H0.
      cbv [kunsigned] in H1.
      Lia.lia.
    }

    assert (Z.ltb (kunsigned (rpc ^+ ZToWord _ 1 ^+ ZToWord _ 1 ^+ ZToWord _ 1))
                  (Z.pow 2 memSizeLg) = true) as Hrpc3.
    { destruct H0 as [_ [_ [_ ?]]].
      cbv [word.add word WordsKami wordW KamiWord.word] in H0.
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
      Lia.lia.
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
                   word.unsigned WordsKami KamiWord.word kunsigned
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
      isXAddr4 rpc xaddrs ->
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
