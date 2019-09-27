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

Section FetchOk.

  Instance W: Utility.Words := @KamiWord.WordsKami width width_cases.
  Context {mem: map.map word byte}.

  (* [instrMemSizeLg] is the log number of instructions in the instruction cache.
   * If the instruction base address is just 0, then the address range for
   * the instructions is [0 -- 4 * 2^(instrMemSizeLg)].
   *)
  Variable instrMemSizeLg: Z.
  Hypothesis (HinstrMemBound: 3 <= instrMemSizeLg <= width - 2).
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
  Definition kamiXAddrs: XAddrs := addXAddrRange (wzero _) instrMemSize nil.

  Definition convertInstrMem (instrMem: kword instrMemSizeLg -> kword 32): mem :=
    let keys := List.unfoldn (Word.wplus (Word.ZToWord (Z.to_nat instrMemSizeLg) 1))
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

  Lemma instrMemSizeLg_bound_split:
    (Z.to_nat width = (2 + Z.to_nat instrMemSizeLg)
                      + (Z.to_nat width - (2 + Z.to_nat instrMemSizeLg)))%nat.
  Proof.
    change 2%nat with (Z.to_nat 2).
    rewrite <-Z2Nat.inj_add by blia.
    rewrite <-Z2Nat.inj_sub by blia.
    rewrite <-Z2Nat.inj_add by blia.
    f_equal; blia.
  Qed.
                                              
  Definition toKamiPc (pc: kword width):
    Word.word (2 + Z.to_nat instrMemSizeLg).
    unfold kword in pc.
    rewrite instrMemSizeLg_bound_split in pc.
    exact (split1 _ _ pc).
  Defined.

  Lemma toKamiPc_wplus_distr:
    forall w1 w2,
      toKamiPc w1 ^+ toKamiPc w2 = toKamiPc (w1 ^+ w2).
  Proof.
    unfold toKamiPc; intros.
    case TODO.
  Qed.

  Lemma kamiXAddrs_In_prop:
    forall addr,
      In addr kamiXAddrs ->
      exists saddr: Word.word 30, addr = Word.combine WO~0~0 saddr.
  Proof.
    unfold kamiXAddrs; intros.
    assert (exists saddr: Word.word 30,
               wzero (BinInt.Z.to_nat width) = Word.combine WO~0~0 saddr).
    { exists (wzero _); reflexivity. }

    generalize dependent (wzero (BinInt.Z.to_nat width)).
    induction instrMemSize; simpl; intros; [exfalso; auto|].
    destruct H; [subst; assumption|].
    eapply IHn; [eassumption|].
    destruct H0 as [iaddr ?]; subst.

    eexists.
    match goal with
    | |- _ ^+ ?w = _ => replace w with (Word.combine WO~0~0 (natToWord 30 1))
    end.
    - simpl.
      unfold Pos.to_nat; simpl.
      do 2 rewrite <-wplus_WS_0'.
      reflexivity.
    - reflexivity.    
  Qed.

  Lemma kamiXAddrs_toKamiPc_aligned:
    forall addr,
      In addr kamiXAddrs ->
      exists iaddr, toKamiPc addr = Word.combine WO~0~0 iaddr.
  Proof.
    intros.
    apply kamiXAddrs_In_prop in H.
    destruct H as [saddr ?]; subst.

    unfold toKamiPc.
    case TODO.
    
  Qed.

  Lemma rv32AlignAddr_toKamiPc_consistent:
    forall addr iaddr,
      toKamiPc addr = Word.combine WO~0~0 iaddr ->
      addr = evalExpr (IsaRv32.rv32AlignAddr 32%nat (Z.to_nat instrMemSizeLg) type iaddr).
  Proof.
    case TODO.
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
    case TODO.
  Qed.

End FetchOk.
