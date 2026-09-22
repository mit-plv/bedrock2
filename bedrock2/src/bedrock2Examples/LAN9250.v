Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax bedrock2.NotationsCustomEntry.
Require Import coqutil.Z.prove_Zeq_bitwise.
Require Import bedrock2Examples.SPI.

From coqutil Require Import letexists.
Require Import bedrock2.AbsintWordToZ.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Z.Lia.

Require Import ZArith.BinInt.
From coqutil Require Import Datatypes.String.
Import List.ListNotations.
Local Open Scope Z_scope. Local Open Scope string_scope. Local Open Scope list_scope.

Local Notation MMIOWRITE := "MMIOWRITE".
Local Notation MMIOREAD := "MMIOREAD".

Definition lan9250_readword := func! (addr) ~> (ret, err) {
    SPI_CSMODE_ADDR = ($0x10024018);
    io! ret = MMIOREAD(SPI_CSMODE_ADDR);
    ret = (ret | $2);
    output! MMIOWRITE(SPI_CSMODE_ADDR, ret);

    (* manually register-allocated, apologies for variable reuse *)
    unpack! ret, err = spi_xchg($0x0b);        require !err; (* FASTREAD *)
    unpack! ret, err = spi_xchg(addr >> $8);     require !err;
    unpack! ret, err = spi_xchg(addr & $0xff); require !err;
    unpack! ret, err = spi_xchg(err);                    require !err; (* dummy *)

    unpack! ret, err = spi_xchg(err);                    require !err; (* read *)
    unpack! addr, err = spi_xchg(err);                   require !err; (* read *)
    ret = (ret | (addr << $8));
    unpack! addr, err = spi_xchg(err);                   require !err; (* read *)
    ret = (ret | (addr << $16));
    unpack! addr, err = spi_xchg(err);                   require !err; (* read *)
    ret = (ret | (addr << $24));

    io! addr = $MMIOREAD(SPI_CSMODE_ADDR);
    addr = (addr & coq:(Z.lnot 2));
    output! $MMIOWRITE(SPI_CSMODE_ADDR, addr)
  }.

Definition lan9250_writeword := func! (addr, data) ~> err {
    SPI_CSMODE_ADDR = $0x10024018;
    io! ret = $MMIOREAD(SPI_CSMODE_ADDR);
    ret = (ret | $2);
    output! $MMIOWRITE(SPI_CSMODE_ADDR, ret);

    (* manually register-allocated, apologies for variable reuse *)
    Oxff = $0xff;
    eight = $8;
    unpack! ret, err = spi_xchg($0x02); require !err; (* FASTREAD *)
    unpack! ret, err = spi_xchg(addr >> eight);   require !err;
    unpack! ret, err = spi_xchg(addr & Oxff);     require !err;

    unpack! ret, err = spi_xchg(data & Oxff);     require !err; (* write *)
    data = (data >> eight);
    unpack! ret, err = spi_xchg(data & Oxff);     require !err; (* write *)
    data = (data >> eight);
    unpack! ret, err = spi_xchg(data & Oxff);     require !err; (* write *)
    data = (data >> eight);
    unpack! ret, err = spi_xchg(data);     require !err; (* write *)

    io! addr = $MMIOREAD(SPI_CSMODE_ADDR);
    addr = (addr & coq:(Z.lnot 2));
    output! $MMIOWRITE(SPI_CSMODE_ADDR, addr)
  }.

Definition MAC_CSR_DATA : Z := 0x0A8.
Definition MAC_CSR_CMD : Z := 0x0A4.
Definition BYTE_TEST : Z := 0x64.

Definition lan9250_mac_write := func! (addr, data) ~> err {
    unpack! err = lan9250_writeword($MAC_CSR_DATA, data);
    require !err;
unpack! err = lan9250_writeword($MAC_CSR_CMD, coq:(Z.shiftl 1 31)|addr);
    require !err;
          unpack! data, err = lan9250_readword($BYTE_TEST)
          (* while (lan9250_readword(0xA4) >> 31) { } // Wait until BUSY (= MAX_CSR_CMD >> 31) goes low *)
  }.

Definition lan9250_wait_for_boot := func! () ~> err {
  err = ($0);
  byteorder = ($0);
  i = ($lightbulb_spec.patience); while (i) { i = (i - $1);
          unpack! byteorder, err = lan9250_readword($0x64);
    if err { i = (i^i) }
    else if (byteorder == $0x87654321) { i = (i^i) }
    else { err = ($-1) }
  }
}.

Definition lan9250_init := func! () ~> err {
    unpack! err = lan9250_wait_for_boot();
    require !err;
          unpack! hw_cfg, err = lan9250_readword($lightbulb_spec.HW_CFG);
    require !err;
    hw_cfg = (hw_cfg | coq:(Z.shiftl 1 20)); (* mustbeone *)
    hw_cfg = (hw_cfg & coq:(Z.lnot (Z.shiftl 1 21))); (* mustbezero *)
    unpack! err = lan9250_writeword($lightbulb_spec.HW_CFG, hw_cfg);
    require !err;

    (* 20: full duplex; 18: promiscuous; 2, 3: TXEN/RXEN *)
        unpack! err = lan9250_mac_write($1, coq:(Z.lor (Z.shiftl 1 20) (Z.lor (Z.shiftl 1 18) (Z.lor (Z.shiftl 1 3) (Z.shiftl 1 2)))));
    require !err;
          unpack! err = lan9250_writeword($0x070, coq:(Z.lor (Z.shiftl 1 2) (Z.shiftl 1 1)))
  }.

Local Definition TX_DATA_FIFO := 32.
Definition lan9250_tx := func! (p, l) ~> err {
  (* A: first segment, last segment, length *)
  unpack! err = lan9250_writeword($TX_DATA_FIFO, $(2^13)|$(2^12)|l); require !err;
  (* B: length *)
  unpack! err = lan9250_writeword($TX_DATA_FIFO, l); require !err;
  while ($3 < l) {
    unpack! err = lan9250_writeword($TX_DATA_FIFO, load4(p));
    if err { l = $0 } else { p = p + $4; l = l - $4 } } }.

Require Import bedrock2.LeakageProgramLogic bedrock2.LeakageWeakestPrecondition bedrock2.LeakageSemantics.
Require Import bedrock2.FE310CSemantics.
Require Import coqutil.Word.Bitwidth.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.TracePredicate. Import TracePredicateNotations.
Require bedrock2Examples.lightbulb_spec.
Require Import bedrock2.ZnWords.
Require Import coqutil.Byte coqutil.Word.LittleEndianList.

Import coqutil.Map.Interface.
Import lightbulb_spec.
Import LeakageLoops.
Local Open Scope bool_scope.

Section WithParameters.
  Local Notation word := (bits 32).
  Context {mem: map.map word Byte.byte}.
  Context {mem_ok: map.ok mem}.
  Context {pick_sp: PickSp}.

  Import lightbulb_spec.
  Local Notation OP := lightbulb_spec.OP.
  Local Notation patience := lightbulb_spec.patience.
  Local Notation mmio_trace_abstraction_relation := (@mmio_trace_abstraction_relation mem).
  Local Notation only_mmio_satisfying := (@only_mmio_satisfying mem).

  (* Leakage.  Every MMIO access leaks its address (FE310CSemantics), and the
     driver only branches on error flags and on words read from the device, so
     the leakage of each function is a function of the abstract I/O trace [ioh]
     that its specification already exposes (and of the address argument, which
     is public).  The leakage functions below recover the I/O segment of each
     call by parsing the trace chronologically ([rev ioh]: chip select, the SPI
     exchanges, chip deselect) and apply the callees' leakage functions to those
     segments; a call that times out is the last one and gets the rest of the
     trace.  For the parse to be determined, the timeout branches of the
     specifications describe the trace precisely ([lan9250_txn_timeout] and the
     predicates built from it) instead of the previous [any +++ spi_timeout],
     which follows from them ([lan9250_txn_timeout_any] etc.). *)

  Definition some_spi_xchg : list OP -> Prop := existsl (fun tx => existsl (fun rx => spi_xchg tx rx)).
  Definition some_spi_xchg_timeout : list OP -> Prop := existsl spi_xchg_timeout.

  (* n exchanges, the last of which times out *)
  Fixpoint spi_xchgs_timeout (n : nat) : list OP -> Prop :=
    match n with
    | O => fun _ => False
    | S n => some_spi_xchg_timeout ||| (some_spi_xchg +++ spi_xchgs_timeout n)
    end.
  (* a LAN9250 transaction of [n] exchanges (8 for a read, 7 for a write), aborted by a timeout *)
  Definition lan9250_txn_timeout (n : nat) : list OP -> Prop := spi_begin +++ spi_xchgs_timeout n.

  Definition bit31 (v : word) : bool := negb (Z.eqb (Z.shiftr (Zmod.unsigned v) 31) 0).
  Definition is_ld (addr : word) (full : bool) (e : OP) : bool :=
    match e with
    | (s, a, v) => String.eqb s "ld" && Zmod.eqb a addr && Bool.eqb (bit31 v) full
    end.

  Fixpoint skip_while (p : OP -> bool) (l : list OP) : list OP * list OP :=
    match l with
    | e :: l => if p e then let '(x, r) := skip_while p l in (e :: x, r) else ([], e :: l)
    | [] => ([], [])
    end.

  Definition parse_spi_write (l : list OP) : option (list OP * byte * list OP) :=
    let '(fulls, l) := skip_while (is_ld SPI_TX_FIFO_ADDR true) l in
    match l with
    | ("ld", a, v) :: ("st", a', b) :: l =>
        if Zmod.eqb a SPI_TX_FIFO_ADDR && negb (bit31 v) && Zmod.eqb a' SPI_TX_FIFO_ADDR
        then Some (fulls ++ [("ld", a, v); ("st", a', b)], byte.of_Z (Zmod.unsigned b), l)
        else None
    | _ => None
    end.

  Definition parse_spi_read (l : list OP) : option (list OP * byte * list OP) :=
    let '(empties, l) := skip_while (is_ld SPI_RX_FIFO_ADDR true) l in
    match l with
    | ("ld", a, v) :: l =>
        if Zmod.eqb a SPI_RX_FIFO_ADDR && negb (bit31 v)
        then Some (empties ++ [("ld", a, v)], byte.of_Z (Zmod.unsigned v), l)
        else None
    | _ => None
    end.

  Definition parse_spi_xchg (l : list OP) : option (list OP * byte * byte * list OP) :=
    match parse_spi_write l with
    | Some (w, tx, l) =>
        match parse_spi_read l with
        | Some (r, rx, l) => Some (w ++ r, tx, rx, l)
        | None => None
        end
    | None => None
    end.

  Definition parse_csmode (l : list OP) : option (list OP * list OP) :=
    match l with
    | ("ld", a, v) :: ("st", a', v') :: l =>
        if Zmod.eqb a SPI_CSMODE_ADDR && Zmod.eqb a' SPI_CSMODE_ADDR
        then Some ([("ld", a, v); ("st", a', v')], l) else None
    | _ => None
    end.

  Fixpoint parse_spi_xchgs (n : nat) (l : list OP) : option (list OP * list byte * list byte * list OP) :=
    match n with
    | O => Some ([], [], [], l)
    | S n =>
        match parse_spi_xchg l with
        | Some (x, tx, rx, l) =>
            match parse_spi_xchgs n l with
            | Some (xs, txs, rxs, l) => Some (x ++ xs, tx :: txs, rx :: rxs, l)
            | None => None
            end
        | None => None
        end
    end.

  (* one LAN9250 transaction: chip select, [n] exchanges, chip deselect *)
  Definition parse_lan9250_txn (n : nat) (l : list OP) : option (list OP * list byte * list byte * list OP) :=
    match parse_csmode l with
    | Some (b, l) =>
        match parse_spi_xchgs n l with
        | Some (xs, txs, rxs, l) =>
            match parse_csmode l with
            | Some (e, l) => Some (b ++ xs ++ e, txs, rxs, l)
            | None => None
            end
        | None => None
        end
    | None => None
    end.

  (* ---- lemmas ---- *)

  Lemma skip_while_app p x r
    (Hx : Forall (fun e => p e = true) x)
    (Hr : match r with [] => True | e :: _ => p e = false end)
    : skip_while p (x ++ r) = (x, r).
  Proof.
    induction Hx; cbn [skip_while List.app].
    { destruct r as [|e r]; cbn [skip_while]; trivial. rewrite Hr. trivial. }
    { rewrite H, IHHx. trivial. }
  Qed.

  Lemma kleene_rev_Forall (P : list OP -> Prop) (p : OP -> bool)
    (HP : forall l, P l -> exists e, l = [e] /\ p e = true)
    l (H : P^* l) : Forall (fun e => p e = true) (rev l).
  Proof.
    induction H; cbn.
    { constructor. }
    { rewrite rev_app_distr. eapply Forall_app; split; trivial.
      destruct (HP _ H) as (?&?&?); subst; cbn; auto. }
  Qed.

  Lemma spi_write_full_bit31 l : spi_write_full l -> exists e, l = [e] /\ is_ld SPI_TX_FIFO_ADDR true e = true.
  Proof.
    intros (v&Hl&Hv). cbv [one] in Hl. subst. eexists; split; trivial.
    cbv [is_ld bit31]. rewrite (proj2 (Z.eqb_neq _ _) Hv).
    destruct (Zmod.eqb_spec SPI_TX_FIFO_ADDR SPI_TX_FIFO_ADDR); [reflexivity|congruence].
  Qed.

  Lemma spi_read_empty_bit31 l : spi_read_empty l -> exists e, l = [e] /\ is_ld SPI_RX_FIFO_ADDR true e = true.
  Proof.
    intros (v&Hl&Hv). cbv [one] in Hl. subst. eexists; split; trivial.
    cbv [is_ld bit31]. rewrite (proj2 (Z.eqb_neq _ _) Hv).
    destruct (Zmod.eqb_spec SPI_RX_FIFO_ADDR SPI_RX_FIFO_ADDR); [reflexivity|congruence].
  Qed.

  Local Ltac rw31 :=
    repeat match goal with H : Z.shiftr (Zmod.unsigned _) 31 = 0 |- _ => rewrite H end.

  Local Ltac dstr :=
    repeat match goal with
      | H : concat _ _ _ |- _ => destruct H as (?&?&?&?&?); subst
      | H : one _ _ |- _ => cbv [one] in H; subst
      | H : existsl _ _ |- _ => destruct H
      | H : exists _, _ |- _ => destruct H
      | H : _ /\ _ |- _ => destruct H
      | _ => progress subst
      end.

  Lemma parse_spi_write_ok tx (x r : list OP) (H : spi_write tx x) :
    parse_spi_write (rev x ++ r) = Some (rev x, tx, r).
  Proof.
    cbv [spi_write] in H. dstr.
    cbv [spi_write_ready spi_write_enqueue] in *. dstr.
    cbv [parse_spi_write].
    rewrite !rev_app_distr; cbn [rev List.app]. rewrite <-!app_assoc; cbn [List.app].
    rewrite skip_while_app.
    2: eapply kleene_rev_Forall; eauto using spi_write_full_bit31.
    2: { cbv [is_ld bit31]. rw31. cbn [Z.eqb negb Bool.eqb]. rewrite Bool.andb_false_r. trivial. }
    cbv [bit31]. rw31. cbn [Z.eqb negb].
    destruct (Zmod.eqb_spec SPI_TX_FIFO_ADDR SPI_TX_FIFO_ADDR); [|congruence]. cbn [andb].
    rewrite bits.unsigned_of_Z, Z.mod_small, byte.of_Z_unsigned; trivial.
    pose proof byte.unsigned_range tx. lia.
  Qed.

  Lemma parse_spi_read_ok rx (x r : list OP) (H : spi_read rx x) :
    parse_spi_read (rev x ++ r) = Some (rev x, rx, r).
  Proof.
    cbv [spi_read] in H. dstr.
    cbv [spi_read_dequeue] in *. dstr.
    cbv [parse_spi_read].
    rewrite !rev_app_distr; cbn [rev List.app]. rewrite <-!app_assoc; cbn [List.app].
    rewrite skip_while_app.
    2: eapply kleene_rev_Forall; eauto using spi_read_empty_bit31.
    2: { cbv [is_ld bit31]. rw31. cbn [Z.eqb negb Bool.eqb]. rewrite Bool.andb_false_r. trivial. }
    cbv [bit31]. rw31. cbn [Z.eqb negb].
    destruct (Zmod.eqb_spec SPI_RX_FIFO_ADDR SPI_RX_FIFO_ADDR); [|congruence]. cbn [andb].
    trivial.
  Qed.

  Lemma parse_spi_xchg_ok tx rx (x r : list OP) (H : spi_xchg tx rx x) :
    parse_spi_xchg (rev x ++ r) = Some (rev x, tx, rx, r).
  Proof.
    cbv [spi_xchg] in H. dstr.
    cbv [parse_spi_xchg]. rewrite rev_app_distr, <-app_assoc.
    erewrite parse_spi_write_ok by eassumption.
    erewrite parse_spi_read_ok by eassumption.
    trivial.
  Qed.

  Lemma parse_spi_write_timeout (x : list OP) (H : spi_write_timeout x) : parse_spi_write (rev x) = None.
  Proof.
    destruct H as [H _]. cbv [parse_spi_write].
    rewrite <-(app_nil_r (rev x)), skip_while_app; trivial.
    eapply kleene_rev_Forall; eauto using spi_write_full_bit31.
  Qed.

  Lemma parse_spi_read_timeout (x : list OP) (H : spi_read_timeout x) : parse_spi_read (rev x) = None.
  Proof.
    destruct H as [H _]. cbv [parse_spi_read].
    rewrite <-(app_nil_r (rev x)), skip_while_app; trivial.
    eapply kleene_rev_Forall; eauto using spi_read_empty_bit31.
  Qed.

  Lemma parse_spi_xchg_timeout tx (x : list OP) (H : spi_xchg_timeout tx x) : parse_spi_xchg (rev x) = None.
  Proof.
    cbv [spi_xchg_timeout choice] in H. cbv [parse_spi_xchg]. destruct H as [H|H].
    { rewrite parse_spi_write_timeout; trivial. }
    { dstr. rewrite rev_app_distr. erewrite parse_spi_write_ok by eassumption. cbv beta iota.
      rewrite parse_spi_read_timeout; trivial. }
  Qed.

  Lemma parse_csmode_ok_begin (x r : list OP) (H : spi_begin x) : parse_csmode (rev x ++ r) = Some (rev x, r).
  Proof.
    cbv [spi_begin] in H. dstr. cbn [rev List.app parse_csmode].
    destruct (Zmod.eqb_spec SPI_CSMODE_ADDR SPI_CSMODE_ADDR); [|congruence]. trivial.
  Qed.

  Lemma parse_csmode_ok_end (x r : list OP) (H : spi_end x) : parse_csmode (rev x ++ r) = Some (rev x, r).
  Proof.
    cbv [spi_end] in H. dstr. cbn [rev List.app parse_csmode].
    destruct (Zmod.eqb_spec SPI_CSMODE_ADDR SPI_CSMODE_ADDR); [|congruence]. trivial.
  Qed.

  Lemma some_spi_xchg_deaf tx x : spi_xchg_deaf tx x -> some_spi_xchg x.
  Proof. intros (?&?). eexists _, _; eassumption. Qed.
  Lemma some_spi_xchg_mute rx x : spi_xchg_mute rx x -> some_spi_xchg x.
  Proof. intros (?&?). eexists _, _; eassumption. Qed.
  Lemma some_spi_xchg_dummy x : spi_xchg_dummy x -> some_spi_xchg x.
  Proof. intros (?&?&?). eexists _, _; eassumption. Qed.

  Local Ltac parse_txn_ok :=
    cbv [some_spi_xchg existsl] in *; dstr;
    cbv [parse_lan9250_txn]; rewrite !rev_app_distr, <-!app_assoc;
    erewrite parse_csmode_ok_begin by eassumption; cbv beta iota;
    cbn [parse_spi_xchgs];
    repeat (erewrite parse_spi_xchg_ok by eassumption; cbv beta iota);
    erewrite parse_csmode_ok_end by eassumption; cbv beta iota;
    rewrite <-!app_assoc, ?app_nil_r.

  (* a successful read transaction: begin, 8 exchanges, end *)
  Lemma parse_lan9250_txn8_ok (x r x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : list OP)
    (Hx : x = x9 ++ x8 ++ x7 ++ x6 ++ x5 ++ x4 ++ x3 ++ x2 ++ x1 ++ x0)
    (H0 : spi_begin x0) (H9 : spi_end x9)
    (H1 : some_spi_xchg x1) (H2 : some_spi_xchg x2) (H3 : some_spi_xchg x3) (H4 : some_spi_xchg x4)
    (H5 : some_spi_xchg x5) (H6 : some_spi_xchg x6) (H7 : some_spi_xchg x7) (H8 : some_spi_xchg x8)
    : exists txs rxs, parse_lan9250_txn 8 (rev x ++ r) = Some (rev x, txs, rxs, r).
  Proof. subst x. parse_txn_ok. eauto. Qed.

  (* a successful write transaction: begin, 7 exchanges, end *)
  Lemma parse_lan9250_txn7_ok (x r x0 x1 x2 x3 x4 x5 x6 x7 x8 : list OP)
    (Hx : x = x8 ++ x7 ++ x6 ++ x5 ++ x4 ++ x3 ++ x2 ++ x1 ++ x0)
    (H0 : spi_begin x0) (H8 : spi_end x8)
    (H1 : some_spi_xchg x1) (H2 : some_spi_xchg x2) (H3 : some_spi_xchg x3) (H4 : some_spi_xchg x4)
    (H5 : some_spi_xchg x5) (H6 : some_spi_xchg x6) (H7 : some_spi_xchg x7)
    : exists txs rxs, parse_lan9250_txn 7 (rev x ++ r) = Some (rev x, txs, rxs, r).
  Proof. subst x. parse_txn_ok. eauto. Qed.

  Lemma parse_lan9250_fastread4 a v (x r L : list OP) (HL : L = rev x ++ r) (H : lan9250_fastread4 a v x) :
    exists txs r1 r2 r3 r4 b0 b1 b2 b3,
      parse_lan9250_txn 8 L = Some (rev x, txs, [r1; r2; r3; r4; b0; b1; b2; b3], r) /\
      Zmod.unsigned v = le_combine [b0; b1; b2; b3].
  Proof.
    subst L. cbv [lan9250_fastread4 spi_xchg_deaf spi_xchg_mute spi_xchg_dummy existsl] in H. dstr.
    parse_txn_ok. eauto 20.
  Qed.

  Lemma parse_lan9250_write4 a v (x r L : list OP) (HL : L = rev x ++ r) (H : lan9250_write4 a v x) :
    exists txs rxs, parse_lan9250_txn 7 L = Some (rev x, txs, rxs, r).
  Proof.
    subst L. cbv [lan9250_write4 spi_xchg_deaf existsl] in H. dstr.
    parse_txn_ok. eauto.
  Qed.

  Lemma lan9250_fastread4_nonempty a v (x : list OP) : lan9250_fastread4 a v x -> x <> [].
  Proof.
    intros H. cbv [lan9250_fastread4 spi_end existsl] in H. dstr.
    rewrite <-!app_assoc. cbn [List.app]. discriminate.
  Qed.
  Lemma lan9250_boot_attempt_nonempty (x : list OP) : lan9250_boot_attempt x -> x <> [].
  Proof. intros (v&H&_). eapply lan9250_fastread4_nonempty; eassumption. Qed.
  Lemma multiple_boot_attempt_length n (th : list OP) :
    multiple lan9250_boot_attempt n th -> (n <= length th)%nat.
  Proof.
    revert th; induction n; intros th H; cbn [multiple] in H; [lia|].
    destruct H as (l1&l2&->&H1&H2). rewrite length_app. specialize (IHn _ H2).
    pose proof (lan9250_boot_attempt_nonempty _ H1). destruct l1; [congruence|]. cbn [length]. lia.
  Qed.
  Lemma kleene_multiple' (P : list OP -> Prop) (l : list OP) : kleene P l -> exists n, multiple P n l.
  Proof.
    induction 1 as [|l1 l2 H1 H2 (n&IH)]; [exists O; reflexivity|].
    exists (S n); cbn [multiple]. exists l1, l2. auto.
  Qed.

  Lemma parse_spi_xchgs_timeout n (x : list OP) (H : spi_xchgs_timeout n x) : parse_spi_xchgs n (rev x) = None.
  Proof.
    revert x H; induction n; cbn [spi_xchgs_timeout parse_spi_xchgs]; intros x H; [contradiction|].
    cbv [choice some_spi_xchg_timeout some_spi_xchg existsl] in H. destruct H as [H|H].
    { destruct H. erewrite parse_spi_xchg_timeout by eassumption. trivial. }
    { dstr. rewrite rev_app_distr. erewrite parse_spi_xchg_ok by eassumption. cbv beta iota. rewrite IHn; trivial. }
  Qed.

  Lemma parse_lan9250_txn_timeout n (x : list OP) (H : lan9250_txn_timeout n x) : parse_lan9250_txn n (rev x) = None.
  Proof.
    cbv [lan9250_txn_timeout] in H. dstr.
    cbv [parse_lan9250_txn]. rewrite rev_app_distr.
    erewrite parse_csmode_ok_begin by eassumption. cbv beta iota.
    rewrite parse_spi_xchgs_timeout; trivial.
  Qed.

  (* weakening to the old form *)
  Lemma spi_xchgs_timeout_any n x : spi_xchgs_timeout n x -> (any +++ spi_timeout) x.
  Proof.
    revert x; induction n; cbn [spi_xchgs_timeout]; intros x H; [contradiction|].
    cbv [choice some_spi_xchg_timeout existsl] in H. destruct H as [[? H]|H].
    { eauto using spi_xchg_timeout_any. }
    { dstr. eauto using any_app_more. }
  Qed.
  Lemma lan9250_txn_timeout_any n x : lan9250_txn_timeout n x -> (any +++ spi_timeout) x.
  Proof. cbv [lan9250_txn_timeout]; intros; dstr; eauto using spi_xchgs_timeout_any, any_app_more. Qed.

  (* leakage of a sequence of spi_xchg calls, each described by the leakage of
     evaluating its argument, the argument, and the leakage after a successful call *)
  Fixpoint spi_xchg_calls_leak (fx : list OP -> leakage)
    (calls : list (leakage * leakage)) (l : list OP) (acc : leakage) : leakage * option (list OP) :=
    match calls with
    | [] => (acc, Some l)
    | (pre, post) :: calls =>
        match parse_spi_xchg l with
        | Some (x, _, _, l) => spi_xchg_calls_leak fx calls l (post ++ fx (rev x) ++ leak_unit :: pre ++ acc)
        | None => (leak_bool true :: fx (rev l) ++ leak_unit :: pre ++ acc, None)
        end
    end.

  Local Notation cs := (leak_list [SPI_CSMODE_ADDR]).
  Local Notation "$ z" := (bits.of_Z 32 z) (at level 9, format "$ z").

  Definition lan9250_readword_leak fx (a : word) (ioh : list OP) : leakage :=
    match parse_csmode (rev ioh) with
    | Some (_, l) =>
      match spi_xchg_calls_leak fx
        [ ([], [leak_bool false]);
          ([leak_word $8], [leak_bool false]);
          ([], [leak_bool false]);
          ([], [leak_bool false]);
          ([], [leak_bool false]);
          ([], [leak_word $8; leak_bool false]);
          ([], [leak_word $16; leak_bool false]);
          ([], [leak_word $24; leak_bool false]) ]
        l [cs; cs] with
      | (acc, Some _) => cs :: cs :: acc
      | (acc, None) => acc
      end
    | None => []
    end.


  Definition lan9250_writeword_leak fx (a : word) (ioh : list OP) : leakage :=
    match parse_csmode (rev ioh) with
    | Some (_, l) =>
      match spi_xchg_calls_leak fx
        [ ([], [leak_bool false]);
          ([leak_word $8], [leak_bool false]);
          ([], [leak_bool false]);
          ([], [leak_word $8; leak_bool false]);
          ([], [leak_word $8; leak_bool false]);
          ([], [leak_word $8; leak_bool false]);
          ([], [leak_bool false]) ]
        l [cs; cs] with
      | (acc, Some _) => cs :: cs :: acc
      | (acc, None) => acc
      end
    | None => []
    end.

  (* a call's I/O segment and the rest, when the call succeeded *)
  Definition parse_lan9250_seg (n : nat) (l : list OP) : option (list OP * list OP) :=
    match parse_lan9250_txn n l with
    | Some (x, _, _, l) => Some (x, l)
    | None => None
    end.
  Fixpoint parse_lan9250_segs (ns : list nat) (l : list OP) : option (list OP * list OP) :=
    match ns with
    | [] => Some ([], l)
    | n :: ns =>
        match parse_lan9250_seg n l with
        | Some (x, l) =>
            match parse_lan9250_segs ns l with
            | Some (y, l) => Some (x ++ y, l)
            | None => None
            end
        | None => None
        end
    end.

  (* leakage of a sequence of calls of the LAN9250 driver functions, each
     described by the parser of its I/O segment, the callee's leakage function
     applied to that segment, and the leakage after a successful call; a call
     that fails is the last one and gets the whole remaining segment *)
  Fixpoint lan9250_calls_leak (calls : list ((list OP -> option (list OP * list OP)) * (list OP -> leakage) * leakage))
    (l : list OP) (acc : leakage) : leakage * option (list OP) :=
    match calls with
    | [] => (acc, Some l)
    | (parse, fc, post) :: calls =>
        match parse l with
        | Some (x, l) => lan9250_calls_leak calls l (post ++ fc (rev x) ++ leak_unit :: acc)
        | None => (leak_bool true :: fc (rev l) ++ leak_unit :: acc, None)
        end
    end.

  Definition lan9250_mac_write_timeout (a v : word) : list OP -> Prop :=
    lan9250_txn_timeout 7 |||
    (lan9250_write4 $168 v +++ lan9250_txn_timeout 7) |||
    (lan9250_write4 $168 v +++ lan9250_write4 $164 (Zmod.or $(2^31) a) +++ lan9250_txn_timeout 8).

  Definition lan9250_mac_write_leak (fw fr : word -> list OP -> leakage) (a : word) (ioh : list OP) : leakage :=
    match lan9250_calls_leak [(parse_lan9250_seg 7, fw $MAC_CSR_DATA, [leak_bool false]); (parse_lan9250_seg 7, fw $MAC_CSR_CMD, [leak_bool false])]
            (rev ioh) [] with
    | (acc, Some l) => fr $BYTE_TEST (rev l) ++ leak_unit :: acc
    | (acc, None) => acc
    end.

  Definition patience_nat : nat := Z.to_nat patience.
  Lemma patience_nat_spec : Z.of_nat patience_nat = patience.
  Proof. cbv [patience_nat]. rewrite Znat.Z2Nat.id; [reflexivity|]. cbv [patience]; lia. Qed.
  Lemma patience_nat_eq : Z.to_nat patience = patience_nat. Proof. reflexivity. Qed.
  Global Opaque patience_nat.

  Lemma Zmod_eqb_true_iff {m} (a b : Zmod m) : Zmod.eqb a b = true <-> a = b.
  Proof. destruct (Zmod.eqb_spec a b); intuition congruence. Qed.
  Lemma Zmod_eqb_false_iff {m} (a b : Zmod m) : Zmod.eqb a b = false <-> a <> b.
  Proof. destruct (Zmod.eqb_spec a b); intuition congruence. Qed.

  (* the word read by a successful lan9250_readword, from the parsed exchanges *)
  Definition lan9250_txn_value (rxs : list byte) : word := bits.of_Z 32 (le_combine (skipn 4 rxs)).
  Lemma lan9250_txn_value_eq r1 r2 r3 r4 b0 b1 b2 b3 (v : word)
    (H : Zmod.unsigned v = le_combine [b0; b1; b2; b3]) :
    lan9250_txn_value [r1; r2; r3; r4; b0; b1; b2; b3] = v.
  Proof. cbv [lan9250_txn_value]. cbn [skipn]. rewrite <-H. apply Zmod.of_Z_unsigned. Qed.

  (* lan9250_wait_for_boot: up to [i] more attempts; the loop condition of this
     iteration has been leaked already *)
  Fixpoint lan9250_wait_for_boot_loop (fr : word -> list OP -> leakage) (i : nat) (l : list OP) (acc : leakage) : leakage :=
    match i with
    | O => acc
    | S i =>
      match parse_lan9250_txn 8 l with
      | None => leak_bool false :: leak_bool true :: fr $0x64 (rev l) ++ leak_unit :: acc
      | Some (x, _, rxs, l) =>
        let acc := fr $0x64 (rev x) ++ leak_unit :: acc in
        if Zmod.eqb (lan9250_txn_value rxs) $0x87654321
        then leak_bool false :: leak_bool true :: leak_bool false :: acc
        else let acc := leak_bool false :: leak_bool false :: acc in
             match i with
             | O => leak_bool false :: acc
             | S _ => lan9250_wait_for_boot_loop fr i l (leak_bool true :: acc)
             end
      end
    end.
  Definition lan9250_wait_for_boot_leak fr (ioh : list OP) : leakage :=
    lan9250_wait_for_boot_loop fr patience_nat (rev ioh) [leak_bool true].

  (* fewer than [patience] failed attempts, then a read that timed out *)
  Definition lan9250_wait_for_boot_timeout (ioh : list OP) : Prop :=
    exists n, (n < patience_nat)%nat /\ (multiple lan9250_boot_attempt n +++ lan9250_txn_timeout 8) ioh.

  (* the I/O segment of a successful lan9250_wait_for_boot: failed attempts, then the boot word *)
  Fixpoint parse_lan9250_wait_for_boot (fuel : nat) (l : list OP) : option (list OP * list OP) :=
    match fuel with
    | O => None
    | S fuel =>
      match parse_lan9250_txn 8 l with
      | None => None
      | Some (x, _, rxs, l) =>
          if Zmod.eqb (lan9250_txn_value rxs) $0x87654321 then Some (x, l)
          else match parse_lan9250_wait_for_boot fuel l with
               | Some (y, l) => Some (x ++ y, l)
               | None => None
               end
      end
    end.

  Definition parse_lan9250_mac_write : list OP -> option (list OP * list OP) := parse_lan9250_segs [7; 7; 8]%nat.

  Local Notation MAC_CR_VALUE := (Z.lor (Z.shiftl 1 20) (Z.lor (Z.shiftl 1 18) (Z.lor (Z.shiftl 1 3) (Z.shiftl 1 2)))).

  Definition lan9250_init_leak (fwfb : list OP -> leakage) (fr fw fmw : word -> list OP -> leakage) (ioh : list OP) : leakage :=
    let l := rev ioh in
    match parse_lan9250_wait_for_boot (S (length l)) l with
    | None => leak_bool true :: fwfb (rev l) ++ [leak_unit]
    | Some (x, l) =>
      match lan9250_calls_leak
              [(parse_lan9250_seg 8, fr $HW_CFG, [leak_bool false]);
               (parse_lan9250_seg 7, fw $HW_CFG, [leak_bool false]);
               (parse_lan9250_mac_write, fmw $1, [leak_bool false])]
              l (leak_bool false :: fwfb (rev x) ++ [leak_unit]) with
      | (acc, Some l) => fw $0x070 (rev l) ++ leak_unit :: acc
      | (acc, None) => acc
      end
    end.

  Definition lan9250_init_timeout (ioh : list OP) : Prop :=
    lan9250_wait_for_boot_timeout ioh \/
    (lan9250_wait_for_boot_trace +++ lan9250_txn_timeout 8) ioh \/
    exists cfg0,
      let cfg' := Zmod.or cfg0 1048576 in
      let cfg := Zmod.and cfg' (bits.of_Z 32 (-2097153)) in
      (lan9250_wait_for_boot_trace +++ lan9250_fastread4 $HW_CFG cfg0 +++ lan9250_txn_timeout 7) ioh \/
      (lan9250_wait_for_boot_trace +++ lan9250_fastread4 $HW_CFG cfg0 +++ lan9250_write4 $HW_CFG cfg +++
         lan9250_mac_write_timeout $1 $MAC_CR_VALUE) ioh \/
      (lan9250_wait_for_boot_trace +++ lan9250_fastread4 $HW_CFG cfg0 +++ lan9250_write4 $HW_CFG cfg +++
         lan9250_mac_write_trace $1 $MAC_CR_VALUE +++ lan9250_txn_timeout 7) ioh.

  (* lan9250_tx's loop: [n] more words to write from [p] *)
  Fixpoint lan9250_tx_loop (fw : word -> list OP -> leakage) (n : nat) (p : word) (l : list OP) (acc : leakage) : leakage :=
    match n with
    | O => leak_bool false :: acc
    | S n =>
      let acc := leak_word p :: leak_bool true :: acc in
      match parse_lan9250_seg 7 l with
      | None => leak_bool false :: leak_bool true :: fw $TX_DATA_FIFO (rev l) ++ leak_unit :: acc
      | Some (x, l) => lan9250_tx_loop fw n (Zmod.add p $4) l (leak_bool false :: fw $TX_DATA_FIFO (rev x) ++ leak_unit :: acc)
      end
    end.
  Definition lan9250_tx_leak (fw : word -> list OP -> leakage) (p l : word) (ioh : list OP) : leakage :=
    match lan9250_calls_leak
            [(parse_lan9250_seg 7, fw $TX_DATA_FIFO, [leak_bool false]);
             (parse_lan9250_seg 7, fw $TX_DATA_FIFO, [leak_bool false])]
            (rev ioh) [] with
    | (acc, Some rest) => lan9250_tx_loop fw (Z.to_nat (Zmod.unsigned l / 4)) p rest acc
    | (acc, None) => acc
    end.

  Fixpoint lan9250_writepacket_timeout (bs : list byte) : list OP -> Prop :=
    match bs with
    | b0 :: b1 :: b2 :: b3 :: bs =>
        lan9250_txn_timeout 7 |||
        (lan9250_write4 $TX_DATA_FIFO $(le_combine [b0; b1; b2; b3]) +++ lan9250_writepacket_timeout bs)
    | _ => fun _ => False
    end.
  Definition lan9250_send_timeout (send : list byte) : list OP -> Prop :=
    lan9250_txn_timeout 7 |||
    (lan9250_write4 $TX_DATA_FIFO (Zmod.or (Zmod.or $(2^13) $(2^12)) $(Z.of_nat (length send))) +++ lan9250_txn_timeout 7) |||
    (lan9250_write4 $TX_DATA_FIFO (Zmod.or (Zmod.or $(2^13) $(2^12)) $(Z.of_nat (length send))) +++
     lan9250_write4 $TX_DATA_FIFO $(Z.of_nat (length send)) +++ lan9250_writepacket_timeout send).

  (* the previous, weaker description of the timeout traces *)
  Lemma lan9250_mac_write_timeout_any a v (x : list OP) :
    lan9250_mac_write_timeout a v x -> (any +++ spi_timeout) x.
  Proof.
    cbv [lan9250_mac_write_timeout choice]; intros [[H|H]|H]; dstr;
      eauto using lan9250_txn_timeout_any, any_app_more.
  Qed.
  Lemma lan9250_wait_for_boot_timeout_any (x : list OP) :
    lan9250_wait_for_boot_timeout x -> (any +++ spi_timeout) x.
  Proof. intros (n&_&H); dstr; eauto using lan9250_txn_timeout_any, any_app_more. Qed.
  Lemma lan9250_init_timeout_any (x : list OP) :
    lan9250_init_timeout x -> (any +++ spi_timeout) x.
  Proof.
    cbv [lan9250_init_timeout]; intros [H|[H|(cfg0&[H|[H|H]])]]; dstr;
      eauto using lan9250_txn_timeout_any, lan9250_mac_write_timeout_any,
        lan9250_wait_for_boot_timeout_any, any_app_more.
  Qed.
  Lemma lan9250_writepacket_timeout_any : forall bs (x : list OP),
    lan9250_writepacket_timeout bs x -> (any +++ spi_timeout) x.
  Proof.
    fix IH 1. intros bs x H.
    destruct bs as [|b0 [|b1 [|b2 [|b3 bs]]]]; cbn [lan9250_writepacket_timeout] in H; try contradiction.
    cbv [choice] in H. destruct H as [H|H]; dstr; eauto using lan9250_txn_timeout_any, any_app_more, (IH bs).
  Qed.
  Lemma lan9250_send_timeout_any bs (x : list OP) :
    lan9250_send_timeout bs x -> (any +++ spi_timeout) x.
  Proof.
    cbv [lan9250_send_timeout choice]; intros [[H|H]|H]; dstr;
      eauto using lan9250_txn_timeout_any, lan9250_writepacket_timeout_any, any_app_more.
  Qed.

  Lemma parse_csmode_cons a a' v v' r (Ha : a = SPI_CSMODE_ADDR) (Ha' : a' = SPI_CSMODE_ADDR) :
    parse_csmode (("ld", a, v) :: ("st", a', v') :: r) = Some ([("ld", a, v); ("st", a', v')], r).
  Proof.
    subst. cbv [parse_csmode].
    destruct (Zmod.eqb_spec SPI_CSMODE_ADDR SPI_CSMODE_ADDR); [reflexivity|congruence].
  Qed.

  Lemma spi_begin_intro a v w (Ha : a = SPI_CSMODE_ADDR) (Hw : w = Zmod.or v SPI_CSMODE_HOLD) :
    spi_begin [("st", a, w); ("ld", a, v)].
  Proof.
    subst. cbv [spi_begin existsl concat one]. exists v.
    exists [("ld", SPI_CSMODE_ADDR, v)], [("st", SPI_CSMODE_ADDR, Zmod.or v SPI_CSMODE_HOLD)].
    split; [reflexivity|]; split; reflexivity.
  Qed.

  Lemma spi_end_intro a v w (Ha : a = SPI_CSMODE_ADDR) (Hw : w = Zmod.and v (bits.of_Z 32 (Z.lnot (Zmod.unsigned SPI_CSMODE_HOLD)))) :
    spi_end [("st", a, w); ("ld", a, v)].
  Proof.
    subst. cbv [spi_end existsl concat one]. exists v.
    exists [("ld", SPI_CSMODE_ADDR, v)], [("st", SPI_CSMODE_ADDR, Zmod.and v (bits.of_Z 32 (Z.lnot (Zmod.unsigned SPI_CSMODE_HOLD))))].
    split; [reflexivity|]; split; reflexivity.
  Qed.

  Ltac spi_csmode_solve := (eapply spi_begin_intro || eapply spi_end_intro); reflexivity.

  Ltac txn_timeout_solve :=
    cbv [lan9250_txn_timeout concat];
    lazymatch goal with |- exists l1 l2, ?ioh = _ /\ _ =>
      lazymatch ioh with (?X ++ [?s]) ++ [?l] =>
        exists (s :: l :: nil), X; split; [rewrite <-!app_assoc; reflexivity|]
      end
    end;
    split; [spi_csmode_solve|];
    repeat (cbn [spi_xchgs_timeout]; cbv [choice];
      ((right; eapply concat_app; [cbv [some_spi_xchg existsl]; eexists _, _; eassumption|])
       || (left; cbv [some_spi_xchg_timeout existsl]; eexists; eassumption))).

  Ltac leak_normalize :=
    repeat match goal with x := _ |- _ => subst x end;
    rewrite ?rev_app_distr; cbn [rev List.app]; rewrite <-?app_assoc; cbn [List.app].

  Ltac leak_parse_txn :=
    repeat first
      [ progress (rewrite parse_csmode_cons by reflexivity; cbv beta iota)
      | progress (erewrite parse_spi_xchg_ok by eassumption; cbv beta iota)
      | progress (erewrite parse_spi_xchg_timeout by eassumption; cbv beta iota)
      | progress (erewrite parse_lan9250_txn_timeout by eassumption; cbv beta iota)
      | progress (match goal with
                  | H : lan9250_write4 ?a ?v ?x |- context [parse_lan9250_txn 7 ?L] =>
                      let Hp := fresh in
                      first [ destruct (parse_lan9250_write4 a v x _ L eq_refl H) as (?&?&Hp)
                            | destruct (parse_lan9250_write4 a v x [] L (eq_sym (app_nil_r L)) H) as (?&?&Hp) ];
                      rewrite Hp; clear Hp
                  | H : lan9250_fastread4 ?a ?v ?x |- context [parse_lan9250_txn 8 ?L] =>
                      let Hp := fresh in
                      first [ destruct (parse_lan9250_fastread4 a v x _ L eq_refl H) as (?&?&?&?&?&?&?&?&?&Hp&?)
                            | destruct (parse_lan9250_fastread4 a v x [] L (eq_sym (app_nil_r L)) H) as (?&?&?&?&?&?&?&?&?&Hp&?) ];
                      rewrite Hp; clear Hp
                  end; cbv beta iota) ].

  Ltac leak_finish :=
    rewrite ?rev_involutive, ?app_nil_r; cbn [leak_binop];
    repeat progress (rewrite <-?app_assoc; cbn [List.app]);
    (reflexivity || align_trace).

  Lemma parse_lan9250_mac_write_ok a v (x r L : list OP) (HL : L = rev x ++ r) (H : lan9250_mac_write_trace a v x) :
    parse_lan9250_mac_write L = Some (rev x, r).
  Proof.
    subst L. destruct H as (w&H). dstr.
    cbv [parse_lan9250_mac_write]; cbn [parse_lan9250_segs]; cbv [parse_lan9250_seg].
    rewrite ?rev_app_distr, <-?app_assoc.
    leak_parse_txn. rewrite <-?app_assoc, ?app_nil_r. reflexivity.
  Qed.

  Lemma parse_lan9250_mac_write_timeout a v (x L : list OP) (HL : L = rev x) (H : lan9250_mac_write_timeout a v x) :
    parse_lan9250_mac_write L = None.
  Proof.
    subst L. cbv [lan9250_mac_write_timeout choice] in H.
    cbv [parse_lan9250_mac_write]; cbn [parse_lan9250_segs]; cbv [parse_lan9250_seg].
    destruct H as [[H|H]|H]; dstr; rewrite ?rev_app_distr, <-?app_assoc; leak_parse_txn; reflexivity.
  Qed.

  Lemma parse_lan9250_wait_for_boot_attempts n (th : list OP) (H : multiple lan9250_boot_attempt n th) :
    forall fuel (l : list OP), (n <= fuel)%nat ->
    parse_lan9250_wait_for_boot fuel (rev th ++ l) =
    match parse_lan9250_wait_for_boot (fuel - n) l with
    | Some (y, l') => Some (rev th ++ y, l')
    | None => None
    end.
  Proof.
    revert th H; induction n; intros th H fuel l Hf; cbn [multiple] in H.
    { subst th. cbn [rev List.app]. rewrite Nat.sub_0_r.
      destruct (parse_lan9250_wait_for_boot fuel l) as [[y l']|]; reflexivity. }
    { destruct H as (l1&l2&->&(v&Hfr&Hne)&H2).
      destruct fuel as [|fuel]; [lia|]. cbn [parse_lan9250_wait_for_boot].
      rewrite rev_app_distr, <-app_assoc.
      leak_parse_txn.
      erewrite lan9250_txn_value_eq by eassumption.
      rewrite (proj2 (Zmod_eqb_false_iff _ _)).
      2: { intro X; apply Hne; subst; rewrite bits.unsigned_of_Z; reflexivity. }
      rewrite (IHn _ H2) by lia. replace (S fuel - S n)%nat with (fuel - n)%nat by lia.
      destruct (parse_lan9250_wait_for_boot (fuel - n) l) as [[y l']|]; [|reflexivity].
      rewrite app_assoc. reflexivity. }
  Qed.

  Lemma parse_lan9250_wait_for_boot_ok (x r L : list OP) (HL : L = rev x ++ r)
    (H : lan9250_wait_for_boot_trace x) fuel (Hf : (length x < fuel)%nat) :
    parse_lan9250_wait_for_boot fuel L = Some (rev x, r).
  Proof.
    subst L. destruct H as (l1&l2&->&Hk&Hfr).
    destruct (kleene_multiple' _ _ Hk) as (n&Hn).
    pose proof (multiple_boot_attempt_length _ _ Hn). rewrite length_app in Hf.
    rewrite rev_app_distr, <-app_assoc.
    rewrite (parse_lan9250_wait_for_boot_attempts _ _ Hn) by lia.
    destruct (fuel - n)%nat eqn:E; [lia|].
    cbn [parse_lan9250_wait_for_boot].
    leak_parse_txn.
    erewrite lan9250_txn_value_eq by eassumption.
    rewrite (proj2 (Zmod_eqb_true_iff _ _) eq_refl).
    rewrite <-?app_assoc. reflexivity.
  Qed.

  Lemma parse_lan9250_wait_for_boot_timeout (x L : list OP) (HL : L = rev x) (H : lan9250_wait_for_boot_timeout x)
    fuel (Hf : (length x <= fuel)%nat) :
    parse_lan9250_wait_for_boot fuel L = None.
  Proof.
    subst L. destruct H as (n&Hn&l1&l2&->&Hm&Hto).
    pose proof (multiple_boot_attempt_length _ _ Hm). rewrite length_app in Hf.
    rewrite rev_app_distr.
    rewrite (parse_lan9250_wait_for_boot_attempts _ _ Hm) by lia.
    destruct (fuel - n)%nat; [reflexivity|].
    cbn [parse_lan9250_wait_for_boot].
    erewrite parse_lan9250_txn_timeout by eassumption. reflexivity.
  Qed.

  Lemma parse_lan9250_boot_timeout (x L : list OP) (HL : L = rev x) (H : lan9250_boot_timeout x)
    fuel (Hf : (length x <= fuel)%nat) :
    parse_lan9250_wait_for_boot fuel L = None.
  Proof.
    subst L. cbv [lan9250_boot_timeout] in H. rewrite patience_nat_eq in H.
    pose proof (multiple_boot_attempt_length _ _ H).
    rewrite <-(app_nil_r (rev x)).
    rewrite (parse_lan9250_wait_for_boot_attempts _ _ H) by lia.
    destruct (fuel - patience_nat)%nat; [reflexivity|].
    cbn [parse_lan9250_wait_for_boot]. cbv [parse_lan9250_txn parse_csmode]. reflexivity.
  Qed.

  Ltac leak_parse :=
    repeat first
      [ progress leak_parse_txn
      | progress (match goal with
                  | H : lan9250_mac_write_trace ?a ?v ?x |- context [parse_lan9250_mac_write ?L] =>
                      rewrite (parse_lan9250_mac_write_ok a v x _ L eq_refl H)
                  | H : lan9250_mac_write_timeout ?a ?v ?x |- context [parse_lan9250_mac_write ?L] =>
                      rewrite (parse_lan9250_mac_write_timeout a v x L eq_refl H)
                  end; cbv beta iota) ].

  Ltac wfb_parse :=
    first
      [ match goal with H : lan9250_wait_for_boot_trace ?x |- context [parse_lan9250_wait_for_boot ?fuel ?L] =>
          rewrite (parse_lan9250_wait_for_boot_ok x _ L eq_refl H fuel) by (rewrite ?length_app, ?length_rev; cbn [length]; lia) end
      | match goal with H : lan9250_wait_for_boot_timeout ?x |- context [parse_lan9250_wait_for_boot ?fuel ?L] =>
          rewrite (parse_lan9250_wait_for_boot_timeout x L eq_refl H fuel) by (rewrite ?length_rev; lia) end
      | match goal with H : lan9250_boot_timeout ?x |- context [parse_lan9250_wait_for_boot ?fuel ?L] =>
          rewrite (parse_lan9250_boot_timeout x L eq_refl H fuel) by (rewrite ?length_rev; lia) end ].

  Ltac init_leak_solve :=
    cbv [lan9250_init_leak parse_lan9250_seg parse_lan9250_segs]; leak_normalize;
    wfb_parse; cbv beta iota;
    cbn [lan9250_calls_leak]; leak_parse; leak_finish.

  Ltac init_timeout_solve :=
    cbv [lan9250_init_timeout]; rewrite ?app_nil_r;
    first [ solve [left; eassumption]
          | solve [right; left; eapply concat_app; eassumption]
          | right; right; eexists; cbv zeta;
            first [ solve [left; repeat eapply concat_app; eassumption]
                  | solve [right; left; repeat eapply concat_app; eassumption]
                  | solve [right; right; repeat eapply concat_app; eassumption] ] ].

  Ltac init_trace_solve :=
    cbv [lan9250_init_trace]; rewrite ?app_nil_r; eexists; cbv zeta; repeat eapply concat_app; eauto.

  Ltac leak_solve :=
    cbv [lan9250_readword_leak lan9250_writeword_leak lan9250_mac_write_leak
         parse_lan9250_seg parse_lan9250_segs parse_lan9250_mac_write]; leak_normalize;
    cbn [spi_xchg_calls_leak lan9250_calls_leak]; leak_parse; leak_finish.


  Lemma lan9250_fastread4_intro (a v cs0 cs1 ca w0 w1 : word)
    tx0 tx1 tx2 tx3 tx4 tx5 tx6 tx7 (b0 b1 b2 b3 b4 b5 b6 b7 : byte) x0 x1 x2 x3 x4 x5 x6 x7
    (H0 : spi_xchg tx0 b0 x0) (H1 : spi_xchg tx1 b1 x1) (H2 : spi_xchg tx2 b2 x2) (H3 : spi_xchg tx3 b3 x3)
    (H4 : spi_xchg tx4 b4 x4) (H5 : spi_xchg tx5 b5 x5) (H6 : spi_xchg tx6 b6 x6) (H7 : spi_xchg tx7 b7 x7)
    (Hca : ca = SPI_CSMODE_ADDR)
    (Hw0 : w0 = Zmod.or cs0 SPI_CSMODE_HOLD)
    (Hw1 : w1 = Zmod.and cs1 (bits.of_Z 32 (-3)))
    (Htx0 : tx0 = LAN9250_FASTREAD)
    (Htx1 : byte.unsigned tx1 = Zmod.unsigned (Zmod.sru a 8))
    (Htx2 : byte.unsigned tx2 = Zmod.unsigned (Zmod.and a 255))
    (Hv : Zmod.unsigned v = le_combine [b4; b5; b6; b7]) :
    lan9250_fastread4 a v
      ((((((((((([("st", ca, w1)] ++ [("ld", ca, cs1)]) ++ x7) ++ x6) ++ x5) ++ x4) ++ x3) ++ x2) ++ x1) ++ x0)
        ++ [("st", ca, w0)]) ++ [("ld", ca, cs0)]).
  Proof.
    subst ca w0 w1 tx0. cbv [lan9250_fastread4]. exists tx2, tx1, b4, b5, b6, b7.
    split; [|split; [|split]]; [|exact Htx1|exact Htx2|exact Hv].
    cbv [spi_xchg_deaf spi_xchg_mute spi_xchg_dummy existsl].
    rewrite <-!app_assoc; cbn [List.app].
    repeat lazymatch goal with
      | |- concat _ _ (?e1 :: ?e2 :: ?R) => exists R, [e1; e2]; split; [reflexivity|split]
      | |- concat _ _ (?x ++ ?R) => exists R, x; split; [reflexivity|split]
      end.
    all : try solve [eexists; eassumption | eexists; eexists; eassumption].
    { eapply spi_begin_intro; reflexivity. }
    { eapply spi_end_intro; [reflexivity|]. cbv [SPI_CSMODE_HOLD]. rewrite bits.unsigned_of_Z. reflexivity. }
  Qed.

  Lemma lan9250_write4_intro (a v cs0 cs1 ca w0 w1 : word)
    tx0 tx1 tx2 tx3 tx4 tx5 tx6 (b0 b1 b2 b3 b4 b5 b6 : byte) x0 x1 x2 x3 x4 x5 x6
    (H0 : spi_xchg tx0 b0 x0) (H1 : spi_xchg tx1 b1 x1) (H2 : spi_xchg tx2 b2 x2) (H3 : spi_xchg tx3 b3 x3)
    (H4 : spi_xchg tx4 b4 x4) (H5 : spi_xchg tx5 b5 x5) (H6 : spi_xchg tx6 b6 x6)
    (Hca : ca = SPI_CSMODE_ADDR)
    (Hw0 : w0 = Zmod.or cs0 SPI_CSMODE_HOLD)
    (Hw1 : w1 = Zmod.and cs1 (bits.of_Z 32 (-3)))
    (Htx0 : tx0 = LAN9250_WRITE)
    (Htx1 : byte.unsigned tx1 = Zmod.unsigned (Zmod.sru a 8))
    (Htx2 : byte.unsigned tx2 = Zmod.unsigned (Zmod.and a 255))
    (Hv : Zmod.unsigned v = le_combine [tx3; tx4; tx5; tx6]) :
    lan9250_write4 a v
      (((((((((([("st", ca, w1)] ++ [("ld", ca, cs1)]) ++ x6) ++ x5) ++ x4) ++ x3) ++ x2) ++ x1) ++ x0)
        ++ [("st", ca, w0)]) ++ [("ld", ca, cs0)]).
  Proof.
    subst ca w0 w1 tx0. cbv [lan9250_write4]. exists tx2, tx1, tx3, tx4, tx5, tx6.
    split; [|split; [|split]]; [|exact Htx1|exact Htx2|exact Hv].
    cbv [spi_xchg_deaf existsl].
    rewrite <-!app_assoc; cbn [List.app].
    repeat lazymatch goal with
      | |- concat _ _ (?e1 :: ?e2 :: ?R) => exists R, [e1; e2]; split; [reflexivity|split]
      | |- concat _ _ (?x ++ ?R) => exists R, x; split; [reflexivity|split]
      end.
    all : try solve [eexists; eassumption].
    { eapply spi_begin_intro; reflexivity. }
    { eapply spi_end_intro; [reflexivity|]. cbv [SPI_CSMODE_HOLD]. rewrite bits.unsigned_of_Z. reflexivity. }
  Qed.

  Global Instance spec_of_lan9250_readword : spec_of "lan9250_readword" :=
    fnspec! exists f, "lan9250_readword" a ~> ret err,
    { requires k dstr m := 0x0 <= Zmod.unsigned a < 0x400;
      ensures k' t' m' := m' = m /\
        exists iol, t' = iol ++ dstr /\
        exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
          (Zmod.unsigned err <> 0 /\ lan9250_txn_timeout 8 ioh)
          (Zmod.unsigned err = 0 /\ lightbulb_spec.lan9250_fastread4 a ret ioh) /\
        k' = f a ioh ++ k }.

  Local Ltac split_if :=
    lazymatch goal with
      |- LeakageWeakestPrecondition.cmd _ ?c _ _ _ _ ?post =>
      let c := eval hnf in c in
          lazymatch c with
          | cmd.cond _ _ _ => letexists; letexists; split; [solve[repeat straightline]|split]
          end
    end.

  Ltac evl := (* COQBUG(has_variable) *)
    repeat match goal with
      | |- context G[string_dec ?x ?y] =>
          let e := eval cbv in (string_dec x y) in
          let goal := context G [e] in
          change goal
      | |- context G[?a mod 2 ^ Z.log2 32] =>
          requireZcst a;
          let e := eval cbv in (a mod 2 ^ Z.log2 32) in
          let goal := context G [e] in
          change goal
      | |- context G[Zmod.unsigned ?x] =>
          let x := rdelta x in
          let x := lazymatch x with Zmod.of_Z _ ?x => x end in
          let x := rdelta x in
          let x := rdelta x in
          requireZcst x;
          let x := eval cbv in x in
          let goal := context G [x] in
          change goal
      | |- context G [app nil ?xs] =>
        let goal := context G [ xs ] in
        change goal
    end.

  Ltac trace_alignment :=
    repeat (eapply lightbulb_spec.align_trace_app
      || eapply lightbulb_spec.align_trace_cons
      || exact (eq_refl (app nil _))).

  Ltac mmio_trace_abstraction :=
    repeat match goal with
    | |- mmio_trace_abstraction_relation _ _ => cbv [lightbulb_spec.mmio_trace_abstraction_relation]
    | |- Forall2 lightbulb_spec.mmio_event_abstraction_relation _ _ =>
        eassumption || eapply Forall2_app || eapply Forall2_nil || eapply Forall2_cons
    | |- lightbulb_spec.mmio_event_abstraction_relation _ _ =>
        (left + right); eexists _, _; split; exact eq_refl
    end.

  Import Word.Properties.

  Ltac lan9250_body :=
    repeat match goal with
    | H :  _ /\ _ \/ ?Y /\ _, G : not ?X |- _ =>
        constr_eq X Y; let Z := fresh in destruct H as [|[Z ?]]; [|case (G Z)]
    | H :  not ?Y /\ _ \/ _ /\ _, G : ?X |- _ =>
        constr_eq X Y; let Z := fresh in destruct H as [[Z ?]|]; [case (Z G)|]
    | _ => progress cbv [MMIOREAD MMIOWRITE]
    | _ => progress cbv [SPI_CSMODE_ADDR]
    | |- _ /\ _ => split
    | |- context G[string_dec ?x ?x] =>
        let e := eval cbv in (string_dec x x) in
        let goal := context G [e] in
        change goal
    | |- context G[string_dec ?x ?y] =>
        unshelve erewrite (_ : string_dec x y = right _); [ | exact eq_refl | ]
    | _ => straightline_cleanup
    | |- LeakageWeakestPrecondition.cmd _ (cmd.interact _ _ _) _ _ _ _ _ => eapply LeakageWeakestPreconditionProperties.interact_nomem
    | |- leakage_ext_spec _ _ _ _ _ =>
  letexists; split; [exact eq_refl|]; split; [split; trivial|]
    | |- leakage_ext_spec _ _ _ _ _ =>
  letexists; letexists; split; [exact eq_refl|]; split; [split; trivial|]

    | H: ?x = 0 |-  _ => rewrite H
    | |- ?F ?a ?b ?c =>
        match F with LeakageWeakestPrecondition.get => idtac end;
        let f := (eval cbv beta delta [LeakageWeakestPrecondition.get] in F) in
        change (f a b c); cbv beta
    | _ => straightline
    | _ => straightline_call
    | _ => split_if
  end.


  Ltac isMMIOAddr_solve :=
    repeat match goal with x := _ |- _ => subst x end;
    cbv [isMMIOAddr SPI_CSMODE_ADDR];
    rewrite !bits.unsigned_of_Z;
    trivial; cbv -[Z.le Z.lt]; lia.

  Ltac trace_witnesses :=
    try (
      repeat match goal with x := _ ++ _ |- _ => subst x end;
      eexists; split;
      [ repeat match goal with
        |- context G [cons ?a ?b] =>
          assert_fails (idtac; match b with nil => idtac end);
          let goal := context G [(app (cons a nil) b)] in
          change goal
        end;
      rewrite !app_assoc;
      repeat eapply (fun A => f_equal2 (@List.app A)); eauto |]);
    try (
      eexists; split; [
      repeat (eassumption || eapply Forall2_app || eapply Forall2_nil || eapply Forall2_cons) |]);
    try ((left + right); eexists _, _; split; exact eq_refl).

  Ltac lan9250_timeout_branch := split; [left; split; [eassumption|txn_timeout_solve]|leak_solve].
  Ltac lan9250_success_branch := split; [right; split; [reflexivity|]|leak_solve].

  Lemma lan9250_readword_ok : program_logic_goal_for_function! lan9250_readword.
  Proof.
    straightline.
    instantiate (1 := lan9250_readword_leak f).
    Time repeat straightline.

    lan9250_body.
    all: try (eexists _, _; split; trivial).
    all: try (exact eq_refl).
    all: auto.
    1,2,13,14:
      repeat match goal with x := _ |- _ => subst x end;
      cbv [isMMIOAddr SPI_CSMODE_ADDR];
      rewrite !bits.unsigned_of_Z;
      trivial; cbv -[Z.le Z.lt]; lia.

    all : try (
      repeat match goal with x := _ ++ _ |- _ => subst x end;
      eexists; split;
      [ repeat match goal with
        |- context G [cons ?a ?b] =>
          assert_fails (idtac; match b with nil => idtac end);
          let goal := context G [(app (cons a nil) b)] in
          change goal
        end;
      rewrite !app_assoc;
      repeat eapply (fun A => f_equal2 (@List.app A)); eauto |]).

    all : try (
      eexists; split; [
      repeat (eassumption || eapply Forall2_app || eapply Forall2_nil || eapply Forall2_cons) |]).
    all : try ((left + right); eexists _, _; split; exact eq_refl).

    all : try (split; [left; split; [eassumption|txn_timeout_solve]|leak_solve]).
    all : try (split; [right; split; [reflexivity|]|leak_solve]).
    { evl. rewrite Zmod.unsigned_sru by lia.
      rewrite Z.shiftr_div_pow2 by lia.
      generalize dependent a; clear; intros.
      change 0x400 with (4*256) in *.
      Z.div_mod_to_equations. lia. }
    { rewrite bits.unsigned_and. evl.
      change 255 with (Z.ones 8).
      rewrite Z.land_ones;
      Z.div_mod_to_equations; lia. }
    repeat match goal with x := _ |- _ => subst x end.
    eapply lan9250_fastread4_intro; try eassumption; try reflexivity.
    { evl. rewrite byte.unsigned_of_Z; cbv [byte.wrap]; rewrite Z.mod_small; trivial.
      rewrite Zmod.unsigned_sru by lia. rewrite Z.shiftr_div_pow2 by lia.
      generalize dependent a; clear; intros.
      change 0x400 with (4*256) in *.
      Z.div_mod_to_equations. lia. }
    { rewrite byte.unsigned_of_Z; cbv [byte.wrap]; rewrite Z.mod_small; trivial.
      rewrite bits.unsigned_and. evl.
      change 255 with (Z.ones 8); rewrite Z.land_ones by lia.
      Z.div_mod_to_equations. lia. }
    repeat match goal with x := _ |- _ => subst x end.
    cbv [LittleEndianList.le_combine].

    repeat rewrite ?bits.unsigned_or, <-?Z.lor_assoc by (rewrite ?bits.unsigned_of_Z; exact eq_refl).
    change (Z.shiftl 0 8) with 0 in *; rewrite Z.lor_0_r.
    rewrite !Z.shiftl_lor, !Z.shiftl_shiftl in * by lia.
    repeat f_equal.

    (* little-endian word conversion, automatable (bitwise Z and word) *)
    all : try rewrite Zmod.unsigned_slu by (rewrite ?bits.unsigned_of_Z; exact eq_refl).
    all : rewrite ?bits.unsigned_of_Z.
    all : repeat match goal with |- context G [?a mod ?b] => let goal := context G [a] in change goal end.
    all : repeat match goal with |- context[Byte.byte.unsigned ?x] => is_var x; replace (Byte.byte.unsigned x) with (Byte.byte.wrap (Byte.byte.unsigned x)) by eapply Byte.byte.wrap_unsigned; set (Byte.byte.unsigned x) as X; clearbody X end.
    all : change (8+8) with 16.
    all : change (8+16) with 24.
    all : cbv [Byte.byte.wrap].
    all : clear.
    all : rewrite ?Z.shiftl_mul_pow2 by lia.
    all : try (Z.div_mod_to_equations; lia).
  Qed.

  Global Instance spec_of_lan9250_writeword : spec_of "lan9250_writeword" :=
    fnspec! exists f, "lan9250_writeword" a v ~> err,
    { requires k t m := 0x0 <= Zmod.unsigned a < 0x400;
      ensures k' t' m' := m' = m /\
        exists iol, t' = iol ++ t /\
        exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
          (Zmod.unsigned err <> 0 /\ lan9250_txn_timeout 7 ioh)
          (Zmod.unsigned err = 0 /\ lightbulb_spec.lan9250_write4 a v ioh) /\
        k' = f a ioh ++ k }.

  Ltac spi_arg_bound a v :=
    match goal with |- Zmod.unsigned ?x < _ => let H := unsigned.zify_expr x in rewrite H end;
    repeat match goal with x := _ |- _ => subst x end;
    repeat match goal with H : Zmod.unsigned ?w < _ |- _ => revert H end;
    evl; intros;
    pose proof (bits.unsigned_range v width_nonneg); pose proof (bits.unsigned_range a width_nonneg);
    Z.div_mod_to_equations; lia.

  Lemma lan9250_writeword_ok : program_logic_goal_for_function! lan9250_writeword.
  Proof.
    straightline.
    instantiate (1 := lan9250_writeword_leak f).
    repeat straightline.
    lan9250_body.
    all: try (eexists _, _; split; trivial).
    all: try (exact eq_refl).
    all: auto.
    all: try match goal with |- isMMIOAddr _ => isMMIOAddr_solve end.
    all: try match goal with |- Zmod.unsigned _ < _ => spi_arg_bound a v end.
    all: trace_witnesses.
    all: try lan9250_timeout_branch.
    all: try lan9250_success_branch.
    repeat match goal with x := _ |- _ => subst x end.
    eapply lan9250_write4_intro; try eassumption; try reflexivity.
    { evl. rewrite byte.unsigned_of_Z; cbv [byte.wrap]; rewrite Z.mod_small; trivial.
      rewrite Zmod.unsigned_sru by lia. rewrite Z.shiftr_div_pow2 by lia.
      generalize dependent a; clear; intros.
      change 0x400 with (4*256) in *.
      Z.div_mod_to_equations. lia. }
    { rewrite byte.unsigned_of_Z; cbv [byte.wrap]; rewrite Z.mod_small; trivial.
      rewrite bits.unsigned_and. evl.
      change 255 with (Z.ones 8); rewrite Z.land_ones by lia.
      Z.div_mod_to_equations. lia. }
    { evl. cbv [le_combine].
      rewrite !byte.unsigned_of_Z; cbv [byte.wrap].
      rewrite ?bits.unsigned_and, ?Zmod.unsigned_sru, ?bits.unsigned_of_Z by lia.
      pose proof (bits.unsigned_range v width_nonneg).
      set (Zmod.unsigned v) as X in *; clearbody X.
      change 255 with (Z.ones 8).
      rewrite <-!Z.land_ones by lia.
      prove_Zeq_bitwise. }
  Qed.

  Global Instance spec_of_lan9250_mac_write : spec_of "lan9250_mac_write" :=
    fnspec! exists f, "lan9250_mac_write" a v ~> err,
    { requires k t m := 0 <= Zmod.unsigned a < 2^31;
      ensures k' t' m' := m' = m /\
        exists iol, t' = iol ++ t /\
        exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
          (Zmod.unsigned err <> 0 /\ lan9250_mac_write_timeout a v ioh)
          (Zmod.unsigned err = 0 /\ lan9250_mac_write_trace a v ioh) /\
        k' = f a ioh ++ k }.

  Ltac mac_write_timeout_solve :=
    cbv [lan9250_mac_write_timeout choice]; rewrite ?app_nil_r;
    solve [ left; left; eassumption
          | left; right; eapply concat_app; eassumption
          | right; eapply concat_app; [eapply concat_app|]; eassumption ].

  Lemma lan9250_tx_loop_acc fw n p (l : list OP) acc :
    lan9250_tx_loop fw n p l acc = lan9250_tx_loop fw n p l [] ++ acc.
  Proof.
    revert p l acc; induction n; intros; cbn [lan9250_tx_loop]; [reflexivity|].
    destruct (parse_lan9250_seg 7 l) as [[x l']|]; cbn [List.app]; [|rewrite <-app_assoc; reflexivity].
    rewrite IHn. erewrite (IHn _ _ (leak_bool false :: _)). leak_finish.
  Qed.

  Lemma Z_to_nat_div4_succ a : 4 <= a -> Z.to_nat (a / 4) = S (Z.to_nat ((a - 4) / 4)).
  Proof.
    intros. rewrite <-Znat.Z2Nat.inj_succ by (apply Z.div_pos; lia). f_equal.
    Z.div_mod_to_equations. lia.
  Qed.



  Lemma lan9250_write4_ext a v v' (x : list OP) : lan9250_write4 a v x -> v = v' -> lan9250_write4 a v' x.
  Proof. intros; subst; assumption. Qed.

  (* the trace predicates write the packet length as [of_Z (length bs)] while the
     code passes the word [l]; [ZnWords] bridges the two *)
  Ltac write4_eassumption :=
    lazymatch goal with
    | |- lan9250_write4 ?a ?v ?x =>
        first [ eassumption
              | eapply lan9250_write4_ext;
                [ eassumption
                | f_equal; try match goal with H : Zmod.unsigned _ = Z.of_nat (length _) |- _ => clear -H end; ZnWords ] ]
    | _ => eassumption
    end.

  Ltac send_timeout_solve :=
    cbv [lan9250_send_timeout choice]; rewrite ?app_nil_r;
    first [ solve [left; left; eassumption]
          | solve [left; right; eapply concat_app; write4_eassumption]
          | solve [right; eapply concat_app; [eapply concat_app|]; write4_eassumption] ].

  (* pull a nonempty accumulator out of the loop's leakage (once per occurrence) *)
  Ltac tx_loop_acc_out :=
    repeat match goal with
      | |- context [lan9250_tx_loop ?fw ?n ?p ?l ?acc] =>
          lazymatch acc with [] => fail | _ => rewrite (lan9250_tx_loop_acc fw n p l acc) end
      end.

  Ltac send_solve :=
    cbv [lightbulb_spec.lan9250_send]; rewrite ?app_nil_r;
    solve [eapply concat_app; [eapply concat_app|]; write4_eassumption].

  Ltac tx_leak_solve :=
    cbv [lan9250_tx_leak parse_lan9250_seg]; leak_normalize;
    cbn [lan9250_calls_leak]; leak_parse; tx_loop_acc_out; leak_finish.

  (* the packet is a multiple of 4 bytes long: expose the next word *)
  Ltac packet_head bs :=
    do 4 (destruct bs as [|?b bs]; cbn [List.length] in *; try (exfalso; ZnWords));
    cbn [List.firstn List.skipn lan9250_writepacket lan9250_writepacket_timeout] in *.

  Ltac writepacket_solve :=
    lazymatch goal with
    | |- lan9250_writepacket ?bs _ => packet_head bs; rewrite ?app_nil_r; solve [eauto using concat_app]
    | |- lan9250_writepacket_timeout ?bs _ =>
        packet_head bs; cbv [choice]; rewrite ?app_nil_r;
        first [ solve [left; eassumption] | solve [right; eapply concat_app; eassumption] ]
    end.

  (* one iteration of the loop's leakage: the count is [S] of the next count *)
  Ltac tx_loop_leak_solve :=
    leak_normalize;
    repeat match goal with |- context [Zmod.unsigned (Zmod.sub ?l (bits.of_Z 32 4))] =>
      replace (Zmod.unsigned (Zmod.sub l (bits.of_Z 32 4))) with (Zmod.unsigned l - 4) by ZnWords end;
    match goal with |- _ = lan9250_tx_loop _ (Z.to_nat (?a / 4)) _ _ _ ++ _ =>
      rewrite (Z_to_nat_div4_succ a) by ZnWords end;
    cbn [lan9250_tx_loop]; cbv [parse_lan9250_seg]; leak_parse; tx_loop_acc_out; leak_finish.

  Local Ltac slv := solve [ trivial | eauto 2 using TracePredicate.any_app_more | assumption | lia | trace_alignment | mmio_trace_abstraction ].

  Ltac t :=
    match goal with
    | _ => slv
    | _ => progress evl

    | H :  _ /\ _ \/ ?Y /\ _, G : not ?X |- _ =>
        constr_eq X Y; let Z := fresh in destruct H as [|[Z ?]]; [|case (G Z)]
    | H :  not ?Y /\ _ \/ _ /\ _, G : ?X |- _ =>
        constr_eq X Y; let Z := fresh in destruct H as [[Z ?]|]; [case (Z G)|]
    | |- exists x, _ /\ _ => eexists; split; [repeat f_equal; slv|]
    | |- ?A /\ _ \/ ?B /\ _ =>
        match goal with
        | H: A |- _ => left  | H: not B |- _ => left
        | H: B |- _ => right | H: not A |- _ => right
        end
    | |- lan9250_mac_write_timeout _ _ _ => mac_write_timeout_solve
    | |- lan9250_mac_write_trace _ _ _ => solve [eexists; rewrite ?app_nil_r; eauto using concat_app]
    | |- _ = lan9250_mac_write_leak _ _ _ _ ++ _ => solve [leak_solve]
    | H : not ?P, G : ?P |- _ => case (H G)
    | H : (_ /\ _ \/ _ /\ _) \/ _ /\ _ |- ?G =>
        lazymatch G with
        | context [LeakageWeakestPrecondition.cmd _ _ _ _ _ _ _] => fail
        | _ => destruct H as [[H|H]|H]
        end
    | |- (_ /\ _ \/ _ /\ _) \/ _ /\ _ =>
        solve [ left; left; split; [assumption | init_timeout_solve]
              | left; right; split; [assumption | rewrite ?app_nil_r; assumption]
              | right; split; [first [assumption|reflexivity] | init_trace_solve] ]
    | |- _ = lan9250_init_leak _ _ _ _ _ ++ _ => solve [init_leak_solve]
    | |- lan9250_send_timeout _ _ => send_timeout_solve
    | |- lightbulb_spec.lan9250_send _ _ => send_solve
    | |- lan9250_writepacket _ _ => writepacket_solve
    | |- lan9250_writepacket_timeout _ _ => writepacket_solve
    | |- _ = lan9250_tx_loop _ _ _ _ _ ++ _ => solve [tx_loop_leak_solve]
    | |- _ = lan9250_tx_leak _ _ _ _ ++ _ => solve [tx_leak_solve]

    | |- _ /\ _ => split; [repeat t|]

    | _ => straightline
    | _ => straightline_call; [  solve[repeat t].. | ]
    | _ => split_if; [  solve[repeat t].. | ]
    | |- LeakageWeakestPrecondition.cmd _ (cmd.interact _ _ _) _ _ _ _ _ => eapply LeakageWeakestPreconditionProperties.interact_nomem; [  solve[repeat t].. | ]
    end.

  Lemma lan9250_mac_write_ok : program_logic_goal_for_function! lan9250_mac_write.
  Proof.
    straightline.
    instantiate (1 := lan9250_mac_write_leak f f0).
    repeat match goal with
      | _ => straightline
      | _ => straightline_call
      | _ => split_if
      | _ => rewrite bits.unsigned_of_Z
      | |- context G [?a mod 2 ^ 32] =>
          requireZcst a;
          let t := eval cbv in (a mod 2 ^ 32) in
          let g := context G [t] in
          change g
      | |- _ <= _ < _ => lia
      | |- _ /\ _ => split
    end.

    all : repeat t.
    all : repeat match goal with H : _ \/ _ |- _ => destruct H end; repeat t.
  Qed.


  Ltac pose_ranges :=
    repeat match goal with
      | x : word |- _ =>
          lazymatch goal with
          | _ : 0 <= Zmod.unsigned x < _ |- _ => fail
          | _ => pose proof (bits.unsigned_range x width_nonneg)
          end
      end.

  Ltac wfb_lia :=
    pose proof patience_nat_spec;
    repeat match goal with x := _ : word |- _ => subst x end;
    repeat match goal with
      | H : context [Zmod.unsigned (Zmod.sub ?x (bits.of_Z 32 1))] |- _ =>
          rewrite Zmod.unsigned_sub, bits.unsigned_of_Z in H; change (1 mod 2 ^ 32) with 1 in H
      | |- context [Zmod.unsigned (Zmod.sub ?x (bits.of_Z 32 1))] =>
          rewrite Zmod.unsigned_sub, bits.unsigned_of_Z; change (1 mod 2 ^ 32) with 1
      end;
    pose_ranges;
    repeat match goal with
      | H : context [(?a - 1) mod 2 ^ 32] |- _ => rewrite (Z.mod_small (a - 1)) in H by lia
      | |- context [(?a - 1) mod 2 ^ 32] => rewrite (Z.mod_small (a - 1)) by lia
      end;
    lia.

  (* decide the [byteorder == 0x87654321] test from the branch hypothesis *)
  Ltac unsigned_01_absurd H :=
    exfalso; first
      [ apply H; first [ apply Zmod.unsigned_0 | rewrite bits.unsigned_of_Z; reflexivity ]
      | first [ rewrite bits.unsigned_1 in H by lia | rewrite bits.unsigned_of_Z in H ]; discriminate ].
  Ltac wfb_branch_eqb :=
    repeat match goal with v := ?B |- _ => lazymatch B with if Zmod.eqb _ _ then _ else _ => subst v end end;
    match goal with
    | H : Zmod.unsigned (if Zmod.eqb ?a ?b then _ else _) <> 0 |- _ =>
        let E := fresh "E" in case_eq (Zmod.eqb a b); intro E; rewrite E in H; cbv beta iota in H;
        [ apply Zmod_eqb_true_iff in E | unsigned_01_absurd H ]
    | H : Zmod.unsigned (if Zmod.eqb ?a ?b then _ else _) = 0 |- _ =>
        let E := fresh "E" in case_eq (Zmod.eqb a b); intro E; rewrite E in H; cbv beta iota in H;
        [ unsigned_01_absurd H | apply Zmod_eqb_false_iff in E ]
    end.

  Ltac wfb_timeout_solve :=
    cbv [lan9250_wait_for_boot_timeout]; rewrite ?app_nil_r;
    match goal with H : multiple _ ?n _, HI : Z.of_nat ?n + Zmod.unsigned ?I = patience |- _ =>
      exists n; split; [wfb_lia | eapply concat_app; eassumption]
    end.

  (* the leakage at an exit of the loop, from the invariant's continuation equation *)
  Ltac wfb_leak_solve :=
    cbv [lan9250_wait_for_boot_leak]; leak_normalize;
    match goal with HA : forall l, lan9250_wait_for_boot_loop _ _ (rev _ ++ l) _ = _ |- _ => rewrite HA end;
    match goal with |- context [(patience_nat - ?n)%nat] =>
      replace (patience_nat - n)%nat with (S (patience_nat - S n)) by wfb_lia end;
    cbn [lan9250_wait_for_boot_loop];
    leak_parse;
    try (erewrite lan9250_txn_value_eq by eassumption; wfb_branch_eqb; cbv beta iota);
    try match goal with |- context [(patience_nat - S ?n)%nat] =>
      first [ replace (patience_nat - S n)%nat with 0%nat by wfb_lia
            | replace (patience_nat - S n)%nat with (S (patience_nat - S (S n))) by wfb_lia ]; cbv beta iota end;
    leak_finish.

  Global Instance spec_of_lan9250_wait_for_boot : spec_of "lan9250_wait_for_boot" :=
    fnspec! exists f, "lan9250_wait_for_boot" ~> err,
    { requires k t m := True;
      ensures k' t' m' := m' = m /\
        exists iol, t' = iol ++ t /\
        exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
          (Zmod.unsigned err <> 0 /\ lan9250_wait_for_boot_timeout ioh \/
           Zmod.unsigned err <> 0 /\ lan9250_boot_timeout ioh)
          (Zmod.unsigned err = 0 /\ lan9250_wait_for_boot_trace ioh) /\
        k' = f ioh ++ k }.

  Lemma lan9250_wait_for_boot_ok : program_logic_goal_for_function! lan9250_wait_for_boot.
  Proof.
    straightline.
    instantiate (1 := lan9250_wait_for_boot_leak f).
    repeat straightline.
    refine ((atleastonce ["err"; "i"; "byteorder"] (fun v K T M ERR I BUSY =>
       v = Zmod.unsigned I /\ Zmod.unsigned I <> 0 /\ M = m /\
       exists tl, T = tl++t /\
       exists th, mmio_trace_abstraction_relation th tl /\
       exists n, (multiple (lan9250_boot_attempt) n) th /\
       Z.of_nat n + Zmod.unsigned I = patience /\
       exists A, K = A ++ k /\
       forall l, lan9250_wait_for_boot_loop f patience_nat (rev th ++ l) [leak_bool true]
                 = lan9250_wait_for_boot_loop f (patience_nat - n) l A
            ))
            _ _ _ _ _ _);
      cbn [reconstruct map.putmany_of_list HList.tuple.to_list
           HList.hlist.foralls HList.tuple.foralls
           HList.hlist.existss HList.tuple.existss
           HList.hlist.apply  HList.tuple.apply
           HList.hlist
           List.repeat Datatypes.length
           HList.polymorphic_list.repeat HList.polymorphic_list.length
           PrimitivePair.pair._1 PrimitivePair.pair._2] in *; repeat straightline.
    { exact (Z.lt_wf 0). }
    { exfalso. subst i. match goal with H : Zmod.unsigned _ = 0 |- _ => rewrite bits.unsigned_of_Z in H; inversion H end. }
    { subst i; repeat t.
      exists O; cbn [multiple]; split; trivial.
      split; [try rewrite bits.unsigned_of_Z; cbv [patience]; reflexivity|].
      exists [leak_bool true]; split; [reflexivity|]. intros l. rewrite Nat.sub_0_r. reflexivity. }
    { straightline_call.
      { rewrite bits.unsigned_of_Z.
        repeat match goal with
        | |- context G [?a mod 2 ^ 32] =>
            requireZcst a;
            let t := eval cbv in (a mod 2 ^ 32) in
            let g := context G [t] in
            change g
        end.
        clear; lia. }
      repeat straightline.
      split_if.
      { repeat (t; []); split.
        { intro X. exfalso. eapply X. subst i. rewrite bits.unsigned_xor.
          rewrite Z.lxor_nilpotent. exact eq_refl. }
        repeat t.
        { left; left; split; [assumption|wfb_timeout_solve]. }
        { wfb_leak_solve. } }
      repeat straightline.
      split_if; repeat t.
      { exfalso. match goal with H : Zmod.unsigned i <> 0 |- _ => eapply H end. subst i.
        rewrite bits.unsigned_xor. rewrite Z.lxor_nilpotent. exact eq_refl. }
      { right. split; trivial.
        cbv [lan9250_wait_for_boot_trace].
        rewrite app_nil_r.
        eapply concat_app; eauto using kleene_multiple.
        wfb_branch_eqb. subst. eassumption. }
      { wfb_leak_solve. }
      { eexists. split.
        1: split; [exact eq_refl|].
        2: { pose_ranges. subst v. wfb_lia. }
        repeat t.
        rewrite app_nil_r.
        eexists (S _). split.
        { eapply multiple_expand_right, concat_app; eauto.
          wfb_branch_eqb. eexists. split; eauto.
          intro X. apply E. eapply Zmod.unsigned_inj; rewrite bits.unsigned_of_Z.
          setoid_rewrite X. exact eq_refl. }
        split.
        { rewrite Znat.Nat2Z.inj_succ. wfb_lia. }
        repeat match goal with x := _ |- _ => subst x end.
        match goal with |- exists A, ?K = A ++ k /\ _ =>
          let rec strip K := lazymatch K with
            | ?l ++ k => l
            | k => constr:(@nil leakage_event)
            | ?x :: ?rest => let r := strip rest in constr:(x :: r)
            | ?l ++ ?rest => let r := strip rest in constr:(l ++ r)
            end in
          let A' := strip K in exists A'
        end.
        split; [leak_finish|].
        intros l.
        match goal with HA : forall l, lan9250_wait_for_boot_loop _ _ (rev _ ++ l) _ = _ |- _ =>
          rewrite rev_app_distr, <-app_assoc, HA end.
        match goal with |- context [(patience_nat - ?n)%nat] =>
          replace (patience_nat - n)%nat with (S (patience_nat - S n)) by wfb_lia end.
        cbn [lan9250_wait_for_boot_loop].
        leak_parse.
        erewrite lan9250_txn_value_eq by eassumption. wfb_branch_eqb. cbv beta iota.
        match goal with |- context [(patience_nat - S ?n)%nat] =>
          replace (patience_nat - S n)%nat with (S (patience_nat - S (S n))) by wfb_lia end.
        cbv beta iota.
        leak_finish. }
      { left. right.
        split. { intro X. subst err. rewrite bits.unsigned_of_Z in X. inversion X. }
        rewrite app_nil_r.
        cbv [lan9250_boot_timeout]. rewrite patience_nat_eq.
        match goal with H : multiple _ ?n _ |- _ => replace patience_nat with (S n) by wfb_lia end.
        eapply multiple_expand_right, concat_app; eauto.
        wfb_branch_eqb. eexists. split; eauto.
        intro X. apply E. eapply Zmod.unsigned_inj; rewrite bits.unsigned_of_Z.
        setoid_rewrite X. exact eq_refl. }
      { wfb_leak_solve. } }
  Qed.

  Global Instance spec_of_lan9250_init : spec_of "lan9250_init" :=
    fnspec! exists f, "lan9250_init" ~> err,
    { requires k t m := True;
      ensures k' t' m' := m' = m /\
        exists iol, t' = iol ++ t /\
        exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
          (Zmod.unsigned err <> 0 /\ lan9250_init_timeout ioh \/
           Zmod.unsigned err <> 0 /\ lan9250_boot_timeout ioh)
          (Zmod.unsigned err = 0 /\ lan9250_init_trace ioh) /\
        k' = f ioh ++ k }.

  Lemma lan9250_init_ok : program_logic_goal_for_function! lan9250_init.
  Proof.
    straightline.
    instantiate (1 := lan9250_init_leak f f0 f3 f2).
    repeat t.
    all : repeat match goal with H : _ /\ _ \/ _ /\ _ |- _ => destruct H as [H|H]; destruct H end; repeat t.
  Qed.

  Import LeakageWeakestPrecondition SeparationLogic Array Scalars LeakageProgramLogic.Coercions.
  Local Notation spi_timeout := (lightbulb_spec.spi_timeout).
  Local Notation lan9250_send := (lightbulb_spec.lan9250_send).
  Global Instance spec_of_lan9250_tx : spec_of "lan9250_tx" :=
    fnspec! exists f, "lan9250_tx" p l / bs R ~> err,
    { requires k t m := Zmod.unsigned l = length bs /\
       Zmod.unsigned l mod 4 = 0 /\
       (array ptsto (bits.of_Z 32 1) p bs * R)%sep m;
     ensures k' t' m' := m' = m /\
      exists iol, t' = iol ++ t /\
      exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
        (Zmod.unsigned err <> 0 /\ lan9250_send_timeout bs ioh)
        (Zmod.unsigned err = 0 /\ lan9250_send bs ioh) /\
      k' = f p l ioh ++ k }.

  Import symmetry autoforward.

  Local Ltac no_call :=
    lazymatch goal with
    | |- LeakageSemantics.call _ _ _ _ _ _ _ => fail
    | |- _ => idtac
    end.

  Local Ltac original_esplit := esplit.
  Local Ltac esplit := no_call; original_esplit.

  Lemma lan9250_tx_ok : program_logic_goal_for_function! lan9250_tx.
  Proof.
    straightline.
    instantiate (1 := lan9250_tx_leak f).
    repeat straightline.
    straightline_call; [ZnWords|].
    repeat straightline.
    split_if.
    { repeat t. }
    repeat straightline.
    straightline_call; [ZnWords|].
    repeat straightline.
    split_if.
    { repeat t. }
    repeat straightline.
    refine (LeakageLoops.tailrec_earlyout
      (HList.polymorphic_list.cons (list Byte.byte) (HList.polymorphic_list.cons (mem -> Prop) HList.polymorphic_list.nil))
      ["p";"l";"err"]
      (fun v bs R k t m p l err => PrimitivePair.pair.mk (
         Zmod.unsigned l = length bs /\
         Zmod.unsigned l mod 4 = 0 /\
        (array ptsto (bits.of_Z 32 1) p bs * R)%sep m /\
        v = Zmod.unsigned l /\
        err = 0 :> Z
      )
      (fun K T M P L ERR =>
         M = m /\ exists iol, T = iol ++ t /\
        exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
        (Zmod.unsigned ERR <> 0 /\ lan9250_writepacket_timeout bs ioh)
        (Zmod.unsigned ERR = 0 /\ lightbulb_spec.lan9250_writepacket bs ioh) /\
        K = lan9250_tx_loop f (Z.to_nat (Zmod.unsigned l / 4)) p (rev ioh) [] ++ k
         )
      ) _ (Z.lt_wf 0) _ _ _ _ _ _);
    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
    { repeat straightline. }
    all: cbn [PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
    { repeat straightline; eauto. }
    { repeat straightline.
      2: {
        eapply (word.if_zero _ width_pos) in H13.
        autoforward with typeclass_instances in H13.
        destruct x5; cbn [List.length] in *; [|exfalso; ZnWords].
        Tactics.ssplit; trivial. repeat t.
        leak_normalize.
        match goal with H : Zmod.unsigned x8 = _ |- _ => rewrite H end.
        change (Z.to_nat (Z.of_nat 0 / 4)) with 0%nat.
        cbn [lan9250_tx_loop]. leak_finish. }
      subst br.
      revert H13. match goal with |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) eqn:E end; intro H13.
      2: { contradiction H13. rewrite Zmod.unsigned_0; trivial. }
      pose proof (bits.unsigned_range x8 width_nonneg) as Hl. rewrite H6 in Hl.
      eapply (f_equal (Zmod.of_Z (2 ^ 32))) in H6. rewrite Zmod.of_Z_unsigned in H6.
      rewrite bits.unsigned_of_Z in E; rewrite Z.mod_small in E by lia.
      subst x8.
      rewrite <-(firstn_skipn 4 x5) in H12.
      seprewrite_in @array_append H12.
      seprewrite_in @scalar32_of_bytes H12.
      { autoforward with typeclass_instances in E. rewrite firstn_length. ZnWords. }
      eexists; eexists; split; repeat straightline.
      straightline_call; repeat straightline.
      { ZnWords. }
      seprewrite_in (symmetry! @scalar32_of_bytes) H12.
      { autoforward with typeclass_instances in E. rewrite firstn_length. ZnWords. }
      autoforward with typeclass_instances in E.
      split_if.
      { repeat straightline.
        seprewrite_in (symmetry! @array_append) H12.
        rewrite (firstn_skipn 4 x5) in H12.
        repeat straightline.
        left. repeat t. }
      repeat straightline.
      right; repeat straightline.
      subst l p.
      rewrite bits.unsigned_1, Z.mul_1_l, firstn_length, min_l in H12 by ZnWords.
      progress change (Z.of_nat 4) with 4%Z in H12.
      eexists _, _, _; split; intuition eauto.
      3: ecancel_assumption.
      1: rewrite skipn_length; ZnWords.
      1: ZnWords.
      split; repeat t; [ ZnWords .. |].
      intuition idtac; repeat t. }
    repeat straightline.
    repeat t.
    all : repeat match goal with H : _ /\ _ \/ _ /\ _ |- _ => destruct H as [H|H]; destruct H end; repeat t.
    Unshelve.
    all : try constructor.
  Qed.

  Require Import Utf8.
  Import Map.Separation.
  Local Notation bytes := (array ptsto (bits.of_Z 32 1)).
  Implicit Type l : word.
  Instance spec_of_lan9250_tx' : spec_of "lan9250_tx" :=
    fnspec! exists f, "lan9250_tx" p l / bs ~> err,
    { requires k t m := m =*> bytes p bs ∧ l = length bs :> Z ∧ l mod 4 = 0 :> Z;
      ensures k' t' m' := m' = m ∧ ∃ t'', t' = t'' ++ t ∧ only_mmio_satisfying (fun h =>
       ((0 <> err ∧ lan9250_send_timeout bs h) ∨ (0 = err ∧ lan9250_send bs h)) ∧ k' = f p l h ++ k) t'' }.

  Lemma lan9250_tx_ok' : program_logic_goal_for_function! lan9250_tx.
  Proof.
    cbv [program_logic_goal_for]. intros functions EnvContains.
    pose proof (lan9250_tx_ok functions EnvContains) as Hok. cbv [program_logic_goal_for] in Hok.
    intros.
    let rec go := lazymatch type of Hok with
      | ?A -> ?B => specialize (Hok ltac:(assumption)); go
      | _ => idtac end in go.
    destruct Hok as [f Hf]. exists f.
    intros p l bs k t m (Hm&Hl&Hmod). case Hm as [R Hm].
    eapply LeakageWeakestPreconditionProperties.Proper_call; [|eapply Hf; Tactics.ssplit; eauto].
    repeat intro.
    repeat match goal with
           | H : exists _, _ |- _ =>  case H as []
           | H : _ /\ _ |- _ =>  case H as []
           end; subst.
    eexists; split; [reflexivity|]. split; [reflexivity|].
    eexists; split; [reflexivity|].
    eexists; split; [eassumption|].
    split; [|reflexivity].
    match goal with H : _ \/ _ |- _ => case H as [[]|[]]; [left|right]; split; intuition try congruence end.
  Qed.
End WithParameters.

(* Callers that only know the previous, weaker description of the timeout
   traces (lightbulb.v) recover it by [eauto], in one step. *)
#[export] Hint Extern 1 ((any +++ lightbulb_spec.spi_timeout) _) =>
  solve [ eapply lan9250_txn_timeout_any; eassumption
        | eapply lan9250_mac_write_timeout_any; eassumption
        | eapply lan9250_wait_for_boot_timeout_any; eassumption
        | eapply lan9250_init_timeout_any; eassumption
        | eapply lan9250_writepacket_timeout_any; eassumption
        | eapply lan9250_send_timeout_any; eassumption ] : core.
