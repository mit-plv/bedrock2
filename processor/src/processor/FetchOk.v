Require Import String BinInt.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
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

Section FetchOk.

  Local Hint Resolve (@KamiWord.WordsKami width width_cases): typeclass_instances.
  Context {mem: map.map word byte}.

  (* [instrMemSizeLg] is the log number of instructions in the instruction cache.
   * If the instruction base address is just 0, then the address range for
   * the instructions is [0 -- 4 * 2^(instrMemSizeLg)].
   *)
  Variable instrMemSizeLg: Z.
  Hypothesis (HinstrMemBound: 3 <= instrMemSizeLg <= width - 2).
  Local Notation ninstrMemSizeLg := (Z.to_nat instrMemSizeLg).
  Local Notation nwidth := (Z.to_nat width).
  Definition instrMemSize: nat := Z.to_nat (Z.pow 2 instrMemSizeLg).
  Definition dataMemSize: nat := Z.to_nat (Z.pow 2 width).

  Definition pc_related (kpc: Word.word (2 + Z.to_nat instrMemSizeLg))
             (rpc: kword width): Prop :=
    wordToN kpc = wordToN rpc.

  Definition AddrAligned (addr: kword width) :=
    split1 2 (nwidth - 2) addr = WO~0~0.

  Definition alignedXAddr (base: kword (width - 2)) (n: nat): word :=
    Word.combine WO~0~0 (base ^+ natToWord (nwidth - 2)%nat n).

  Definition alignedXAddrs (base: kword (width - 2)) (n: nat): XAddrs :=
    [alignedXAddr base n; alignedXAddr base n ^+ $1;
       alignedXAddr base n ^+ $2; alignedXAddr base n ^+ $3].

  Fixpoint alignedXAddrsRange (base: kword (width - 2)) (n: nat): XAddrs :=
    match n with
    | O => nil
    | S n' => alignedXAddrs base n' ++ alignedXAddrsRange base n'
    end.

  (* Lemma makeAlignedXAddrs_AddrAligned: *)
  (*   forall base n x, *)
  (*     In x (makeAlignedXAddrs base n) -> *)
  (*     AddrAligned x. *)
  (* Proof. *)
  (*   induction n; intros; [exfalso; auto|]. *)
  (*   destruct H. *)
  (*   - subst; reflexivity. *)
  (*   - auto. *)
  (* Qed. *)

  (* set of executable addresses in the kami processor *)
  Definition kamiXAddrs: XAddrs :=
    (* addXAddrRange (wzero _) instrMemSize nil. *)
    alignedXAddrsRange (wzero _) instrMemSize.

  (* Corollary kamiXAddrs_In_AddrAligned: *)
  (*   forall addr, In addr kamiXAddrs -> AddrAligned addr. *)
  (* Proof. *)
  (*   intros. *)
  (*   eapply makeAlignedXAddrs_AddrAligned; eassumption. *)
  (* Qed. *)

  Lemma pc_related_preserves_AddrAligned:
    forall kpc rpc,
      pc_related kpc rpc -> AddrAligned rpc ->
      split1 2 _ kpc = WO~0~0.
  Proof.
    unfold pc_related, AddrAligned; intros.

    pose proof (Word.combine_split 2 ninstrMemSizeLg kpc).
    rewrite <-H1 in H.
    remember (split1 2 ninstrMemSizeLg kpc) as kpcl; clear Heqkpcl.
    remember (split2 2 ninstrMemSizeLg kpc) as kpcr; clear Heqkpcr.
    clear H1 kpc.

    pose proof (Word.combine_split 2 (nwidth - 2) rpc).
    rewrite <-H1 in H.
    remember (split1 2 (nwidth - 2) rpc) as rpcl; clear Heqrpcl.
    remember (split2 2 (nwidth - 2) rpc) as rpcr; clear Heqrpcr.
    clear H1 rpc; subst rpcl.

    rewrite wordToN_combine in H.
    change (Z.to_nat width) with (2 + (nwidth - 2))%nat in H.
    rewrite wordToN_combine in H.

    change (NatLib.Npow2 2) with 4%N in H.
    do 2 rewrite N.mul_comm with (n:= 4%N) in H.
    
    apply f_equal with (f:= fun x => N.modulo x 4%N) in H.
    do 2 rewrite N.mod_add in H by discriminate.
    do 2 rewrite N.mod_small in H by apply wordToN_bound.
    apply wordToN_inj; assumption.
  Qed.

  Definition mem_related (kmem: kword width -> kword 8)
             (rmem: mem): Prop :=
    forall addr: kword width,
      map.get rmem addr = Some (kmem addr).

  Definition RiscvXAddrsSafe
             (kmemi: kword instrMemSizeLg -> kword width)
             (kmemd: kword width -> kword 8)
             (xaddrs: XAddrs) :=
    forall rpc,
      isXAddr4 rpc xaddrs ->
      isXAddr4 rpc kamiXAddrs /\
      (AddrAligned rpc ->
       forall kpc,
         pc_related kpc rpc ->
         Kami.Ex.SC.combineBytes 4%nat rpc kmemd =
         kmemi (split2 2 _ kpc)).

  Lemma rv32AlignAddr_consistent:
    forall rpc kpc,
      AddrAligned rpc ->
      pc_related kpc rpc ->
      evalExpr
        (IsaRv32.rv32AlignAddr
           32%nat (Z.to_nat instrMemSizeLg)
           (width_inst_valid HinstrMemBound)
           type (split2 2 (Z.to_nat instrMemSizeLg) kpc)) = rpc.
  Proof.
    intros.
    cbv [IsaRv32.rv32AlignAddr].
    unfold eq_rect_r; rewrite evalExpr_bit_eq_rect.
    cbv [evalExpr evalBinBit evalUniBit].
    cbv [evalConstT].

    apply wordToN_inj.
    rewrite wordToN_eq_rect.
    do 2 rewrite wordToN_combine.
    do 2 rewrite ZToWord_zero.
    do 2 rewrite wordToN_wzero.
    rewrite N.mul_0_r, N.add_0_r, N.add_0_l.

    rewrite <-H0.
    rewrite <-(Word.combine_split 2 ninstrMemSizeLg kpc) at 2.

    pose proof (pc_related_preserves_AddrAligned _ _ H0 H).
    rewrite H1.
    rewrite wordToN_combine.
    reflexivity.
  Qed.

  Lemma getmany_of_tuple_combineBytes_consistent:
    forall kmem rmem rpc,
      mem_related kmem rmem ->
      exists rinst : HList.tuple byte 4,
        map.getmany_of_tuple rmem (Memory.footprint rpc 4) = Some rinst /\
        combine 4 rinst = kunsigned (width:= 32) (SC.combineBytes 4 rpc kmem).
  Proof.
    intros.
    cbv [Memory.footprint HList.tuple.unfoldn].
    eexists; split.
    - instantiate (1:= {| PrimitivePair.pair._1 := _;
                          PrimitivePair.pair._2 := _ |}).
      erewrite map.build_getmany_of_tuple_Some; [reflexivity|apply H|].
      cbv [PrimitivePair.pair._2].
      instantiate (1:= {| PrimitivePair.pair._1 := _;
                          PrimitivePair.pair._2 := _ |}).
      erewrite map.build_getmany_of_tuple_Some; [reflexivity|apply H|].
      cbv [PrimitivePair.pair._2].
      instantiate (1:= {| PrimitivePair.pair._1 := _;
                          PrimitivePair.pair._2 := _ |}).
      erewrite map.build_getmany_of_tuple_Some; [reflexivity|apply H|].
      cbv [PrimitivePair.pair._2].
      instantiate (1:= {| PrimitivePair.pair._1 := _;
                          PrimitivePair.pair._2 := _ |}).
      erewrite map.build_getmany_of_tuple_Some; [reflexivity|apply H|].
      cbv [PrimitivePair.pair._2].
      reflexivity.

    - cbv [combine PrimitivePair.pair._1 PrimitivePair.pair._2
                   word.unsigned byte WordsKami word8 KamiWord.word kunsigned
                   SC.combineBytes].
      rewrite Z_of_wordToN_combine_alt with (sz1:= 8%nat) (sz2:= 24%nat).
      rewrite Z_of_wordToN_combine_alt with (sz1:= 8%nat) (sz2:= 16%nat).
      rewrite Z_of_wordToN_combine_alt with (sz1:= 8%nat) (sz2:= 8%nat).
      rewrite Z_of_wordToN_combine_alt with (sz1:= 8%nat) (sz2:= 0%nat).
      reflexivity.
  Qed.

  Lemma fetch_ok:
    forall (kmemi: kword instrMemSizeLg -> kword width)
           (kmemd: kword width -> kword 8)
           (kpc: Word.word (2 + Z.to_nat instrMemSizeLg))
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
        combine 4 rinst = kunsigned (kmemi (split2 2 _ kpc)).
  Proof.
    intros.
    specialize (Hxs _ H); destruct Hxs.
    specialize (H4 H0 _ H1).
    rewrite <-H4.
    eapply getmany_of_tuple_combineBytes_consistent.
    assumption.
  Qed.

End FetchOk.
