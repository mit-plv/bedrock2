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

  Instance W: Utility.Words := @KamiWord.WordsKami width width_cases.
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

  Definition word32_to_4bytes (w: kword 32): HList.tuple byte 4 :=
    LittleEndian.split 4 (word.unsigned w).

  (* TODO this structure might not be very proof friendly,
   * use Memory.unchecked_store_byte_list instead *)
  Fixpoint unchecked_store_byte_tuple_list{n: nat}(a: word)(l: list (HList.tuple byte n))(m: mem): mem :=
    match l with
    | w :: rest =>
      let m' := unchecked_store_byte_tuple_list (word.add a (word.of_Z (Z.of_nat n))) rest m in
      Memory.unchecked_store_bytes n m' a w
    | nil => m
    end.

  (* set of executable addresses in the kami processor *)
  Definition kamiXAddrs: XAddrs :=
    addXAddrRange (wzero _) instrMemSize nil.

  Definition convertInstrMem (instrMem: kword instrMemSizeLg -> kword 32): mem :=
    let keys := List.unfoldn (Word.wplus (Word.ZToWord ninstrMemSizeLg 1))
                             instrMemSize (wzero _) in
    let values := List.map (fun key => word32_to_4bytes (instrMem key)) keys in
    @unchecked_store_byte_tuple_list 4 (wzero _) values map.empty.

  Definition convertDataMem (dataMem: kword width -> kword width): mem :=
    let keys := List.unfoldn (word.add (word.of_Z (width / 8)))
                             dataMemSize (wzero _) in
    let values := List.map
                    (fun key => LittleEndian.split (Z.to_nat (width / 8))
                                                   (word.unsigned (dataMem key)))
                    keys in
    unchecked_store_byte_tuple_list (wzero _) values map.empty.

  Definition toKamiPc (pc: kword width): Word.word (2 + ninstrMemSizeLg) :=
    split1 _ _ (eq_rec nwidth Word.word pc _ (width_inst_valid HinstrMemBound)).

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
    cbv [word.add word W WordsKami wordW KamiWord.word].
    rewrite <-eq_rect_wplus.

    f_equal.
    case TODO_joonwon.

  Qed.

  Lemma rv32AlignAddr_toKamiPc_consistent:
    forall addr,
      In addr kamiXAddrs ->
      addr = evalExpr
               (IsaRv32.rv32AlignAddr
                  32%nat (Z.to_nat instrMemSizeLg)
                  (width_inst_valid HinstrMemBound)
                  type (split2 2 (Z.to_nat instrMemSizeLg) (toKamiPc addr))).
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
    unfold toKamiPc.
    unfold eq_rec.
    rewrite eq_rect_2.
    rewrite split1_combine.
    rewrite split2_combine.
    reflexivity.
  Qed.

  Definition RiscvXAddrsSafe
             (instrMem: kword instrMemSizeLg -> kword width)
             (dataMem: kword width -> kword width)
             (riscvXAddrs: XAddrs) :=
    forall addr,
      isXAddr addr riscvXAddrs ->
      dataMem addr =
      instrMem (split2 2 _ (toKamiPc addr)).

  Lemma fetch_ok:
    forall (instrMem: kword instrMemSizeLg -> kword width)
           (dataMem: kword width -> kword width)
           (riscvXAddrs: XAddrs)
           (Hxs: RiscvXAddrsSafe instrMem dataMem riscvXAddrs)
           (pc: kword width),
      isXAddr pc riscvXAddrs ->
      exists (inst: HList.tuple byte 4),
        Memory.loadWord (convertDataMem dataMem) pc = Some inst /\
        combine 4 inst =
        wordToZ (instrMem (split2 2 _ (toKamiPc pc))).
  Proof.
    case TODO_joonwon.
  Qed.

End FetchOk.
