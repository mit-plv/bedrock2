Require Import String.
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

Lemma evalExpr_bit_eq_rect:
  forall n1 n2 (Hn: n1 = n2) e,
    evalExpr (eq_rect n1 (fun sz => Expr type (SyntaxKind (Bit sz))) e n2 Hn) =
    eq_rect n1 Word.word (evalExpr e) n2 Hn.
Proof.
  intros; subst.
  do 2 rewrite <-(Eqdep_dec.eq_rect_eq_dec eq_nat_dec).
  reflexivity.
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
    #kpc = #rpc.

  Definition AddrAligned (addr: kword width) :=
    split1 2 _ addr = WO~0~0.

  Definition mem_related (kmem: kword width -> kword width)
             (rmem: mem): Prop :=
    forall addr val,
      AddrAligned addr ->
      Memory.load_bytes 4 rmem addr = Some val /\
      combine 4 val = wordToZ (kmem addr).

  (* set of executable addresses in the kami processor *)
  Definition kamiXAddrs: XAddrs :=
    addXAddrRange (wzero _) instrMemSize nil.

  Lemma kamiXAddrs_In_prop:
    forall addr,
      In addr kamiXAddrs ->
      exists saddr: Word.word ninstrMemSizeLg,
        addr =
        eq_rect (2 + ninstrMemSizeLg + (32 - (2 + ninstrMemSizeLg)))%nat
                Word.word
                (Word.combine (Word.combine WO~0~0 saddr) (ZToWord _ 0))
                nwidth
                (eq_sym (width_inst_valid HinstrMemBound)).
  Proof.
    unfold kamiXAddrs; intros.
    assert (exists saddr: Word.word ninstrMemSizeLg,
               wzero (BinInt.Z.to_nat width) =
               eq_rect (2 + ninstrMemSizeLg + (32 - (2 + ninstrMemSizeLg)))%nat
                       Word.word
                       (Word.combine (Word.combine WO~0~0 saddr) (ZToWord _ 0))
                       nwidth
                       (eq_sym (width_inst_valid HinstrMemBound))).
    { exists (wzero _).
      apply wordToZ_inj.
      rewrite wordToZ_eq_rect.
      rewrite ZToWord_zero.
      rewrite combine_wzero.
      rewrite (width_inst_valid HinstrMemBound).
      reflexivity.
    }

    generalize dependent (wzero (BinInt.Z.to_nat width)).
    induction instrMemSize; intros; [exfalso; auto|].
    destruct H; [subst; assumption|].
    eapply IHn; [eassumption|].
    destruct H0 as [saddr ?]; subst.

    exists (saddr ^+ $1).
    change (word.of_Z 4) with (ZToWord nwidth 4).
    replace (ZToWord nwidth 4)
      with (eq_rect
              (2 + ninstrMemSizeLg + (32 - (2 + ninstrMemSizeLg)))%nat
              Word.word (ZToWord _ 4) nwidth
              (eq_sym (width_inst_valid HinstrMemBound))).
    2: {
      apply wordToZ_inj.
      rewrite wordToZ_eq_rect.
      rewrite (width_inst_valid HinstrMemBound).
      reflexivity.
    }
    cbv [word.add word WordsKami wordW KamiWord.word].
    rewrite <-eq_rect_wplus.

    f_equal.
    case TODO_joonwon.

  Qed.

  Definition RiscvXAddrsSafe
             (kmemi: kword instrMemSizeLg -> kword width)
             (kmemd: kword width -> kword width)
             (xaddrs: XAddrs) :=
    forall kpc rpc,
      isXAddr rpc xaddrs ->
      pc_related kpc rpc ->
      kmemd rpc = kmemi (split2 2 _ kpc).

  Lemma rv32AlignAddr_consistent:
    forall rpc kpc,
      In rpc kamiXAddrs ->
      pc_related kpc rpc ->
      rpc = evalExpr
              (IsaRv32.rv32AlignAddr
                 32%nat (Z.to_nat instrMemSizeLg)
                 (width_inst_valid HinstrMemBound)
                 type (split2 2 (Z.to_nat instrMemSizeLg) kpc)).
  Proof.
    intros.
    cbv [IsaRv32.rv32AlignAddr].
    unfold eq_rect_r; rewrite evalExpr_bit_eq_rect.
    cbv [evalExpr evalBinBit evalUniBit].
    cbv [evalConstT].

    apply kamiXAddrs_In_prop in H.
    destruct H as [saddr ?].
    rewrite H at 1.
    repeat f_equal.

    subst.
    red in H0.
    rewrite wordToNat_eq_rect in H0.
    case TODO_joonwon.
  Qed.

  Lemma fetch_ok:
    forall (kmemi: kword instrMemSizeLg -> kword width)
           (kmemd: kword width -> kword width)
           (kpc: Word.word (2 + Z.to_nat instrMemSizeLg))
           (xaddrs: XAddrs)
           (Hxs: RiscvXAddrsSafe kmemi kmemd xaddrs)
           (rmemd: mem)
           (rpc: kword width),
      isXAddr rpc xaddrs ->
      pc_related kpc rpc ->
      mem_related kmemd rmemd ->
      exists (rinst: HList.tuple byte 4),
        Memory.load_bytes 4 rmemd rpc = Some rinst /\
        combine 4 rinst = wordToZ (kmemi (split2 2 _ kpc)).
  Proof.
    case TODO_joonwon.
  Qed.

End FetchOk.
