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
    split1 2 (nwidth - 2) addr = WO~0~0.

  Definition makeAlignedXAddr (base: kword (width - 2)) (n: nat): word :=
    Word.combine WO~0~0 (base ^+ natToWord (nwidth - 2)%nat n).

  Fixpoint makeAlignedXAddrs (base: kword (width - 2)) (n: nat): XAddrs :=
    match n with
    | O => nil
    | S n' => makeAlignedXAddr base n :: makeAlignedXAddrs base n'
    end.

  Lemma makeAlignedXAddrs_AddrAligned:
    forall base n x,
      In x (makeAlignedXAddrs base n) ->
      AddrAligned x.
  Proof.
    induction n; intros; [exfalso; auto|].
    destruct H.
    - subst; reflexivity.
    - auto.
  Qed.

  (* set of executable addresses in the kami processor *)
  Definition kamiXAddrs: XAddrs :=
    (* addXAddrRange (wzero _) instrMemSize nil. *)
    makeAlignedXAddrs (wzero _) instrMemSize.

  Corollary kamiXAddrs_In_AddrAligned:
    forall addr, In addr kamiXAddrs -> AddrAligned addr.
  Proof.
    intros.
    eapply makeAlignedXAddrs_AddrAligned; eassumption.
  Qed.

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

    rewrite wordToNat_combine in H.
    change (Z.to_nat width) with (2 + (nwidth - 2))%nat in H.
    rewrite wordToNat_combine in H.

    change (NatLib.pow2 2) with 4%nat in H.
    do 2 rewrite Nat.mul_comm with (n:= 4%nat) in H.
    apply f_equal with (f:= fun x => Nat.modulo x 4%nat) in H.
    do 2 rewrite Nat.mod_add in H by discriminate.
    do 2 rewrite Nat.mod_small in H by apply wordToNat_bound.
    apply wordToNat_inj; assumption.
  Qed.

  Definition mem_related (kmem: kword width -> kword width)
             (rmem: mem): Prop :=
    forall addr,
      AddrAligned addr ->
      exists val,
        Memory.load_bytes 4 rmem addr = Some val /\
        combine 4 val = kunsigned (kmem addr).

  Definition RiscvXAddrsSafe
             (kmemi: kword instrMemSizeLg -> kword width)
             (kmemd: kword width -> kword width)
             (xaddrs: XAddrs) :=
    forall rpc,
      isXAddr4 rpc xaddrs ->
      AddrAligned rpc /\
      (forall kpc, pc_related kpc rpc ->
                   kmemd rpc = kmemi (split2 2 _ kpc)).

  Lemma rv32AlignAddr_consistent:
    forall rpc kpc,
      In rpc kamiXAddrs ->
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

    apply wordToNat_inj.
    rewrite wordToNat_eq_rect.
    do 2 rewrite wordToNat_combine.
    do 2 rewrite ZToWord_zero.
    do 2 rewrite wordToNat_wzero.
    rewrite Nat.mul_0_r, Nat.add_0_r, Nat.add_0_l.

    rewrite <-H0.
    rewrite <-(Word.combine_split 2 ninstrMemSizeLg kpc) at 2.

    apply kamiXAddrs_In_AddrAligned in H.
    pose proof (pc_related_preserves_AddrAligned _ _ H0 H).
    rewrite H1.
    rewrite wordToNat_combine.
    reflexivity.
  Qed.

  Lemma fetch_ok:
    forall (kmemi: kword instrMemSizeLg -> kword width)
           (kmemd: kword width -> kword width)
           (kpc: Word.word (2 + Z.to_nat instrMemSizeLg))
           (xaddrs: XAddrs)
           (Hxs: RiscvXAddrsSafe kmemi kmemd xaddrs)
           (rmemd: mem)
           (rpc: kword width),
      isXAddr4 rpc xaddrs ->
      pc_related kpc rpc ->
      mem_related kmemd rmemd ->
      exists (rinst: HList.tuple byte 4),
        Memory.load_bytes 4 rmemd rpc = Some rinst /\
        combine 4 rinst = kunsigned (kmemi (split2 2 _ kpc)).
  Proof.
    intros.
    specialize (Hxs _ H); destruct Hxs.
    specialize (H3 _ H0).
    specialize (H1 _ H2).
    destruct H1 as (rinst & ? & ?).
    exists rinst.
    split; [assumption|].
    congruence.
  Qed.

End FetchOk.
