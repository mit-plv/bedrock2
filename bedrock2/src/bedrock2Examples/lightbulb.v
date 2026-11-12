Require Import Coq.micromega.Lia.
Require Import coqutil.Z.Lia.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry coqutil.Macros.WithBaseName.
Require Import bedrock2.FE310CSemantics.
Require Import coqutil.Macros.symmetry.
Require Import coqutil.Byte.
Require Import bedrock2Examples.SPI.
Require Import bedrock2Examples.LAN9250.
From coqutil Require Import Word.Bitwidth Map.Interface.
From coqutil.Tactics Require Import letexists eabstract.
From bedrock2 Require Import FE310CSemantics Semantics WeakestPrecondition ProgramLogic Array Scalars.
From bedrock2 Require Import LeakageSemantics LeakageWeakestPrecondition.
From bedrock2.Map Require Import Separation SeparationLogic.
Require bedrock2.SepAutoArray bedrock2.SepCalls.
Require coqutil.Word.LittleEndianList.
Require bedrock2.LeakageProgramLogic bedrock2.LeakageLoops bedrock2.LeakageWeakestPreconditionProperties.
Import ZArith.
Local Open Scope Z_scope.

Section WithParameters.
  Import Syntax BinInt String List.ListNotations ZArith.
  Local Notation word := (bits 32).
  Context {mem: map.map word Byte.byte}.
  Context {mem_ok: map.ok mem}.
  Context {pick_sp: LeakageSemantics.PickSp}.
  Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

  Definition lightbulb_loop := func! (p_addr) ~> err {
      unpack! bytesWritten, err = recvEthernet(p_addr);
      if !err { (* success, packet *)
        unpack! err = lightbulb_handle(p_addr, bytesWritten);
        err = $0 (* bad packet continue anyway *)
      } else if !(err ^ $1) { (* success, no packet *)
        err = $0
      }
    }.

  Definition recvEthernet := func! (buf) ~> (num_bytes, err) {
      num_bytes = $0;
      unpack! read, err = lan9250_readword(coq:(0x7C)); (* RX_FIFO_INF *)
      require !err else { err = $-1 };
      require (read & coq:((2^8-1)*2^16)) else { err = $1 }; (* nonempty *)
      unpack! read, err = lan9250_readword($0x40); (* RX_STATUS_FIFO_PORT *)
      require !err else { err = $-1 };

      num_bytes = read >> $16 & coq:(2^14-1);
      (* round up to next word *)
      num_bytes = (num_bytes + coq:(4-1)) >> $2;
      num_bytes = num_bytes + num_bytes;
      num_bytes = num_bytes + num_bytes;

      require (num_bytes < coq:(1520 + 1)) else { err = $2 };

      i = $0; while (i < num_bytes) {
        unpack! read, err = lan9250_readword($0);
        if err { err = $-1; i = num_bytes }
        else { store4(buf + i, read); i = i + $4 }
      }
    }.

  Definition lightbulb_handle := func! (packet, len) ~> r {
      r = $42;
      require (r < len) else { r = $-1 };

      Oxff = $0xff;
      ethertype = (((load1(packet + $12))&Oxff) << $8) | ((load1(packet + $13))&Oxff);
      r = coq:(1536 - 1);
      require (r < ethertype) else { r = $-1 };

      r = $23;
      r = packet + r;
      protocol = (load1(r))&Oxff;
      r = $0x11;
      require (protocol == r) else { r = $-1 };

      r = $42;
      r = packet + r;
      command = (load1(r))&Oxff;
      command = command&$1;

      r = $0x1001200c;
      io! mmio_val = MMIOREAD(r);
      mmio_val = mmio_val & coq:(Z.clearbit (2^32-1) 23);
      output! MMIOWRITE(r, mmio_val | command << $23);

      r = $0
    }.

  Definition lightbulb_init := func! {
      output! MMIOWRITE($0x10012038, coq:((Z.shiftl (0xf) 2)));
      output! MMIOWRITE($0x10012008, coq:((Z.shiftl 1 23)));
      unpack! err = lan9250_init()
    }.

  Import Datatypes List.
  Local Notation bytes := (array scalar8 (bits.of_Z 32 1)).
  Local Infix "*" := (sep).
  Local Infix "*" := (sep) : type_scope.

  Import TracePredicate. Import TracePredicateNotations.
  Import Word.Properties.
  Import lightbulb_spec.

  (* recvEthernet's specification is a leakage specification (LeakageSemantics),
     like those of the LAN9250 driver it calls; the other functions of this
     file keep plain specifications and proofs.

     Its I/O segment on a SPI timeout, precisely (the previous
     [(any +++ spi_timeout) ioh] follows, see [recvEthernet_timeout_any]): the
     read of RX_FIFO_INF, of RX_STATUS_FIFO_PORT, or of a packet word timed
     out, after the previous reads succeeded. *)
  Local Notation "$ z" := (bits.of_Z 32 z) (at level 9, format "$ z").
  Definition recvEthernet_timeout (ioh : list OP) : Prop :=
    lan9250_txn_timeout 8 ioh \/
    (exists info, (lan9250_fastread4 $124 info +++ lan9250_txn_timeout 8) ioh /\
       Zmod.unsigned (Zmod.and info $((2^8-1)*2^16)) <> 0) \/
    (exists info status recv,
       (lan9250_fastread4 $124 info +++ lan9250_fastread4 $64 status +++
        lan9250_readpacket recv +++ lan9250_txn_timeout 8) ioh /\
       Zmod.unsigned (Zmod.and info $((2^8-1)*2^16)) <> 0 /\
       Zmod.unsigned (lan9250_decode_length status) < 1521).

  Lemma recvEthernet_timeout_any ioh : recvEthernet_timeout ioh -> (any +++ spi_timeout) ioh.
  Proof.
    intros [H|[(?&H&_)|(?&?&?&H&_)]].
    { eauto using lan9250_txn_timeout_any. }
    all: repeat match goal with H : (_ +++ _) _ |- _ => destruct H as (?&?&?&?&?); subst end.
    all: first [ solve [rewrite <-?app_assoc; eauto 6 using lan9250_txn_timeout_any, any_app_more]
               | solve [rewrite ?app_assoc; eauto 6 using lan9250_txn_timeout_any, any_app_more] ].
  Qed.

  (* Leakage of recvEthernet, as a function of the buffer address and the
     abstract I/O segment [ioh] (newest event first), given the leakage function
     [fr] of lan9250_readword: the I/O segment of each read is recovered by
     parsing the trace chronologically ([rev ioh]) with LAN9250's parsers, the
     control flow is determined by the words read (in the trace), and a read
     that times out is the last one and gets the rest of the trace.  Events are
     accumulated newest first. *)

  (* the word read by a lan9250_fastread4 transaction, from its received bytes *)
  Definition lan9250_txn_word (rxs : list byte) : word :=
    match rxs with
    | [_; _; _; _; b0; b1; b2; b3] => $(LittleEndianList.le_combine [b0; b1; b2; b3])
    | _ => $0
    end.

  (* the packet loop: [n] more words to read into [p]; per iteration the loop
     test, the call, the branch on the error, and the store's address *)
  Fixpoint recvEthernet_loop (fr : word -> list OP -> leakage) (n : nat) (p : word) (l : list OP) (acc : leakage) : leakage :=
    match n with
    | O => leak_bool false :: acc
    | S n =>
      let acc := leak_bool true :: acc in
      match parse_lan9250_seg 8 l with
      | None => leak_bool false :: leak_bool true :: fr $0 (List.rev l) ++ leak_unit :: acc
      | Some (x, l) => recvEthernet_loop fr n (Zmod.add p $4) l (leak_word p :: leak_bool false :: fr $0 (List.rev x) ++ leak_unit :: acc)
      end
    end.

  Definition recvEthernet_leak (fr : word -> list OP -> leakage) (p : word) (ioh : list OP) : leakage :=
    let l := List.rev ioh in
    match parse_lan9250_txn 8 l with
    | None => leak_bool true :: fr $124 ioh ++ [leak_unit]
    | Some (x1, _, rxs1, l) =>
      let info := lan9250_txn_word rxs1 in
      let acc := leak_bool false :: fr $124 (List.rev x1) ++ [leak_unit] in
      if Zmod.eqb (Zmod.and info $((2^8-1)*2^16)) $0
      then leak_bool false :: acc
      else
        let acc := leak_bool true :: acc in
        match parse_lan9250_txn 8 l with
        | None => leak_bool true :: fr $64 (List.rev l) ++ leak_unit :: acc
        | Some (x2, _, rxs2, l) =>
          let num_bytes := lan9250_decode_length (lan9250_txn_word rxs2) in
          let acc := leak_word $2 :: leak_word $16 :: leak_bool false :: fr $64 (List.rev x2) ++ leak_unit :: acc in
          if Z.ltb (Zmod.unsigned num_bytes) 1521
          then recvEthernet_loop fr (Z.to_nat (Zmod.unsigned num_bytes / 4)) p l (leak_bool true :: acc)
          else leak_bool false :: acc
        end
    end.

  Lemma recvEthernet_loop_acc fr n : forall p (l : list OP) acc,
    recvEthernet_loop fr n p l acc = recvEthernet_loop fr n p l [] ++ acc.
  Proof.
    induction n; intros; cbn [recvEthernet_loop].
    { reflexivity. }
    destruct (parse_lan9250_seg 8 l) as [[x l']|].
    { rewrite IHn. rewrite (IHn _ l' (_ :: _ :: _ ++ _ :: _ :: nil)).
      repeat progress (rewrite <-?List.app_assoc; cbn [List.app]). reflexivity. }
    { repeat progress (rewrite <-?List.app_assoc; cbn [List.app]). reflexivity. }
  Qed.


  (* [recvEthernet_leak] on the I/O segments the specification describes *)
  Lemma parse_fastread4_word a v (x r L : list OP) (HL : L = List.rev x ++ r) (H : lan9250_fastread4 a v x) :
    exists txs rxs, parse_lan9250_txn 8 L = Some (List.rev x, txs, rxs, r) /\ lan9250_txn_word rxs = v.
  Proof.
    destruct (parse_lan9250_fastread4 a v x r L HL H) as (txs&r1&r2&r3&r4&b0&b1&b2&b3&Hp&Hv).
    exists txs, [r1;r2;r3;r4;b0;b1;b2;b3]. split; [exact Hp|].
    cbv [lan9250_txn_word]. rewrite <-Hv. apply Zmod.of_Z_unsigned.
  Qed.

  Lemma recvEthernet_leak_timeout1 fr p (ioh : list OP) (H : lan9250_txn_timeout 8 ioh) :
    recvEthernet_leak fr p ioh = leak_bool true :: fr $124 ioh ++ [leak_unit].
  Proof. cbv [recvEthernet_leak]. rewrite (parse_lan9250_txn_timeout 8 ioh H). reflexivity. Qed.

  Lemma recvEthernet_leak_no_packet fr p info (x1 : list OP) (H1 : lan9250_fastread4 $124 info x1)
    (Hz : Zmod.unsigned (Zmod.and info $((2^8-1)*2^16)) = 0) :
    recvEthernet_leak fr p x1 = leak_bool false :: leak_bool false :: fr $124 x1 ++ [leak_unit].
  Proof.
    cbv [recvEthernet_leak].
    destruct (parse_fastread4_word _ _ _ [] _ (eq_sym (List.app_nil_r _)) H1) as (?&?&Hp&Hw).
    rewrite Hp, Hw. cbv zeta. rewrite List.rev_involutive.
    destruct (Zmod.eqb_spec (Zmod.and info $((2^8-1)*2^16)) $0) as [_|Hne]; [reflexivity|].
    exfalso; apply Hne; apply Zmod.unsigned_inj; rewrite Hz, bits.unsigned_of_Z; reflexivity.
  Qed.

  Lemma recvEthernet_leak_timeout2 fr p info (x1 x2 : list OP) (H1 : lan9250_fastread4 $124 info x1)
    (Hnz : Zmod.unsigned (Zmod.and info $((2^8-1)*2^16)) <> 0) (H2 : lan9250_txn_timeout 8 x2) :
    recvEthernet_leak fr p (x2 ++ x1) =
      leak_bool true :: fr $64 x2 ++ leak_unit :: leak_bool true :: leak_bool false :: fr $124 x1 ++ [leak_unit].
  Proof.
    cbv [recvEthernet_leak]. rewrite List.rev_app_distr.
    destruct (parse_fastread4_word _ _ _ (List.rev x2) _ eq_refl H1) as (?&?&Hp&Hw).
    rewrite Hp, Hw. cbv zeta. rewrite !List.rev_involutive.
    destruct (Zmod.eqb_spec (Zmod.and info $((2^8-1)*2^16)) $0) as [He|_].
    { exfalso; apply Hnz; rewrite He, bits.unsigned_of_Z; reflexivity. }
    rewrite (parse_lan9250_txn_timeout 8 x2 H2). reflexivity.
  Qed.

  Lemma recvEthernet_leak_status fr p info status (x1 x2 l : list OP) (H1 : lan9250_fastread4 $124 info x1)
    (Hnz : Zmod.unsigned (Zmod.and info $((2^8-1)*2^16)) <> 0) (H2 : lan9250_fastread4 $64 status x2) :
    recvEthernet_leak fr p (l ++ x2 ++ x1) =
      let num_bytes := lan9250_decode_length status in
      let acc := leak_word $2 :: leak_word $16 :: leak_bool false :: fr $64 x2 ++ leak_unit ::
                 leak_bool true :: leak_bool false :: fr $124 x1 ++ [leak_unit] in
      if Z.ltb (Zmod.unsigned num_bytes) 1521
      then recvEthernet_loop fr (Z.to_nat (Zmod.unsigned num_bytes / 4)) p (List.rev l) [] ++ leak_bool true :: acc
      else leak_bool false :: acc.
  Proof.
    cbv [recvEthernet_leak]. rewrite !List.rev_app_distr, <-!List.app_assoc.
    destruct (parse_fastread4_word _ _ _ (List.rev x2 ++ List.rev l) _ eq_refl H1) as (?&?&Hp1&Hw1).
    rewrite Hp1, Hw1. cbv zeta. rewrite !List.rev_involutive.
    destruct (Zmod.eqb_spec (Zmod.and info $((2^8-1)*2^16)) $0) as [He|_].
    { exfalso; apply Hnz; rewrite He, bits.unsigned_of_Z; reflexivity. }
    destruct (parse_fastread4_word _ _ _ (List.rev l) _ eq_refl H2) as (?&?&Hp2&Hw2).
    rewrite Hp2, Hw2. cbv zeta. rewrite !List.rev_involutive.
    destruct (Z.ltb _ _); [rewrite recvEthernet_loop_acc|]; reflexivity.
  Qed.

  Instance spec_of_recvEthernet : spec_of "recvEthernet" := fun functions => exists f,
    forall p_addr (buf:list byte) R k m t,
      (array scalar8 (bits.of_Z 32 1) p_addr buf * R) m ->
      length buf = 1520%nat ->
      LeakageWeakestPrecondition.call functions "recvEthernet" k t m [p_addr] (fun k' t' m' rets =>
        exists bytes_written err, rets = [bytes_written; err] /\
        exists iol, t' = iol ++ t /\
        exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
          (Zmod.unsigned err = 0 /\
            exists recv buf, (bytes p_addr recv * bytes (Zmod.add p_addr bytes_written) buf * R) m' /\ lan9250_recv recv ioh /\
            Zmod.unsigned bytes_written + Z.of_nat (length buf) = 1520%Z /\
            Z.of_nat (length recv) = Zmod.unsigned bytes_written)
          (Zmod.unsigned err <> 0 /\ exists buf, (array scalar8 (bits.of_Z 32 1) p_addr buf * R) m' /\ length buf = 1520%nat /\ (
             Zmod.unsigned err = 1 /\ lan9250_recv_no_packet ioh \/
             Zmod.unsigned err = 2 /\ lan9250_recv_packet_too_long ioh \/
             Zmod.unsigned err = 2^32-1 /\ recvEthernet_timeout ioh
            )) /\
        k' = f p_addr ioh ++ k
        ).

  Instance spec_of_lightbulb : spec_of "lightbulb_handle" := fun functions =>
    forall p_addr (buf:list byte) (len:word) R m t,
      (array scalar8 (bits.of_Z 32 1) p_addr buf * R) m ->
      Zmod.unsigned len = Z.of_nat (List.length buf) ->
      WeakestPrecondition.call functions "lightbulb_handle" t m [p_addr; len]
        (fun t' m' rets => exists v, rets = [v] /\ m' = m /\
        exists iol, t' = iol ++ t /\
        exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
          (exists cmd, lightbulb_packet_rep cmd buf /\ gpio_set 23 cmd ioh /\ Zmod.unsigned v = 0)
          (not (exists cmd, lightbulb_packet_rep cmd buf) /\ ioh = nil /\ Zmod.unsigned v <> 0)
        ).

  Instance spec_of_lightbulb_loop : spec_of "lightbulb_loop" := fun functions =>
    forall p_addr buf R m t,
      (bytes p_addr buf * R) m ->
      Z.of_nat (length buf) = 1520 ->
      WeakestPrecondition.call functions "lightbulb_loop" t m [p_addr]
        (fun t' m' rets => exists v, rets = [v] /\
        (exists buf, (bytes p_addr buf * R) m' /\
        Z.of_nat (length buf) = 1520) /\
        exists iol, t' = iol ++ t /\
        exists ioh, mmio_trace_abstraction_relation ioh iol /\ (
          (exists packet cmd, (lan9250_recv packet +++ gpio_set 23 cmd) ioh /\ lightbulb_packet_rep cmd packet /\ Zmod.unsigned v = 0) \/
          (exists packet, (lan9250_recv packet) ioh /\ not (exists cmd, lightbulb_packet_rep cmd packet) /\ Zmod.unsigned v = 0) \/
          (lan9250_recv_no_packet ioh /\ Zmod.unsigned v = 0) \/
          (lan9250_recv_packet_too_long ioh /\ Zmod.unsigned v <> 0) \/
          ((TracePredicate.any +++ (spi_timeout)) ioh /\ Zmod.unsigned v <> 0)
        )).

  Instance spec_of_lightbulb_init : spec_of "lightbulb_init" := fun functions =>
    forall m t,
      WeakestPrecondition.call functions "lightbulb_init" t m nil
        (fun t' m' rets => rets = [] /\ m' = m /\
          exists iol, t' = iol ++ t /\
          exists ioh, mmio_trace_abstraction_relation ioh iol /\
          BootSeq ioh
        ).

  Import bedrock2.AbsintWordToZ.
  Import WeakestPreconditionProperties.

  Local Ltac seplog_use_array_load1 H i :=
    let iNat := eval cbv in (Z.to_nat i) in
    let H0 := fresh in pose proof H as H0;
    unshelve SeparationLogic.seprewrite_in @array_index_nat_inbounds H0;
      [exact iNat|exact Byte.x00|lia|];
    replace ((Zmod.unsigned (bits.of_Z 32 1) * Z.of_nat iNat)%Z) with i in * by (rewrite bits.unsigned_of_Z_small by lia; exact eq_refl).
  Local Ltac trans_ltu :=
    match goal with
    | H : Zmod.unsigned ?v <> 0 |- _ =>
        let v := rdelta.rdelta v in
        let __ := lazymatch v with if Z.ltb _ _ then Zmod.one else Zmod.zero => I end in
        eapply Properties.word.if_nonzero in H; eapply Z.ltb_lt in H
    | H : Zmod.unsigned ?v = 0 |- _ =>
        let v := rdelta.rdelta v in
        let __ := lazymatch v with if Z.ltb _ _ then Zmod.one else Zmod.zero => I end in
        eapply (Properties.word.if_zero _ width_pos) in H; eapply Z.ltb_nlt in H
  end.
  Local Ltac split_if :=
    lazymatch goal with
      |- WeakestPrecondition.cmd _ ?c _ _ _ ?post =>
      let c := eval hnf in c in
          lazymatch c with
          | cmd.cond _ _ _ => letexists; split; [solve[repeat straightline]|split]
          end
    end.

  Local Hint Mode map.map - - : typeclass_instances. (* COQBUG https://github.com/coq/coq/issues/14707 *)

  (* The specifications of lan9250_* (LAN9250.v) are leakage specifications;
     the proofs below use their plain consequences [lan9250_*_plain_spec] (the
     previous specifications), taken as hypotheses by lightbulb_init_ok and
     recvEthernet_ok, which is what ProgramLogic.straightline_call would do with
     plain spec_of instances. *)
  Local Ltac straightline_call_lan9250 :=
    lazymatch goal with
    | |- WeakestPrecondition.call ?functions ?callee _ _ _ _ =>
      let Hcall := lazymatch callee with
                   | "lan9250_readword" => lazymatch goal with H: lan9250_readword_plain_spec functions |- _ => H end
                   | "lan9250_init" => lazymatch goal with H: lan9250_init_plain_spec functions |- _ => H end
                   end in
      eapply WeakestPreconditionProperties.Proper_call; cycle -1;
        [ eapply Hcall | try eabstract (solve [Morphisms.solve_proper]) .. ];
        [ .. | intros ? ? ? ?]
    end.
  Local Ltac straightline_call := first [ straightline_call_lan9250 | ProgramLogic.straightline_call ].

  (* [program_logic_goal_for_function! lightbulb_init], with lan9250_init's
     plain specification. *)
  Lemma lightbulb_init_ok : forall functions,
    program_logic_goal_for lightbulb_init
      (forall (EnvContains : map.get functions "lightbulb_init" = Some lightbulb_init),
       lan9250_init_plain_spec functions -> spec_of_lightbulb_init functions).
  Proof.
    repeat straightline.
    eapply WeakestPreconditionProperties.interact_nomem; repeat straightline.
    (* mmio *)
    1: letexists; letexists; split; [exact eq_refl|]; split; [split; trivial|].
    { subst addr val; cbv [isMMIOAddr];
      rewrite !bits.unsigned_of_Z; split; trivial.
      cbv -[Z.le Z.lt]. lia. }
    repeat straightline.

    repeat (eauto || straightline || split_if || eapply interact_nomem || trans_ltu).

    letexists; letexists; split; [exact eq_refl|]; split; [split; trivial|].
    { subst addr0 val0; cbv [isMMIOAddr];
      rewrite !bits.unsigned_of_Z; split; trivial.
      cbv -[Z.le Z.lt]. lia. }
    repeat straightline.

    repeat (eauto || straightline || split_if || eapply interact_nomem || trans_ltu).

    straightline_call; repeat straightline.
    eexists; split; trivial.

    1: repeat (eapply align_trace_cons || exact (eq_sym (List.app_nil_l _)) || eapply align_trace_app).

    eexists; split; cbv [mmio_trace_abstraction_relation].
    1:repeat (eapply List.Forall2_cons || eapply List.Forall2_nil || eapply List.Forall2_app; eauto).
    1,2 : match goal with
    |- mmio_event_abstraction_relation _ _ =>
        (left+right); eexists _, _; split; exact eq_refl
    end.

    cbv [BootSeq].
    eapply concat_app.
    { eapply (concat_app _ _ [_] [_]); exact eq_refl. }

    cbv [choice]; intuition idtac.
  Qed.

  (* [program_logic_goal_for_function! lightbulb_loop], with the function list
     assumed free of stackalloc (recvEthernet's specification is a leakage
     specification, used through ProgramLogic.straightline_call_from_leakage). *)
  Lemma lightbulb_loop_ok : forall functions,
    program_logic_goal_for lightbulb_loop
      (forall (EnvContains : map.get functions "lightbulb_loop" = Some lightbulb_loop),
       spec_of_recvEthernet functions -> spec_of_lightbulb functions ->
       SemanticsRelations.stackalloc_free_env functions ->
       spec_of_lightbulb_loop functions).
  Proof.
    repeat (match goal with H : or _ _ |- _ => destruct H; intuition idtac end
          || straightline || straightline_call || split_if || ecancel_assumption || eauto || lia).
    all : split; [shelve|].
    all : eexists; split.
    all: repeat (eapply align_trace_cons || exact (eq_sym (List.app_nil_l _)) || eapply align_trace_app).
    all : eexists; split.
    all : try subst err; rewrite ?bits.unsigned_of_Z.
    all : repeat (eapply List.Forall2_cons || eapply List.Forall2_nil || eapply List.Forall2_app || eauto 15 using concat_app).
    all: try subst v.
    all: repeat match goal with
         | H : Zmod.unsigned (Zmod.xor ?x _) <> 0, E : Zmod.unsigned ?x = _ |- _ =>
             rewrite bits.unsigned_xor, E, bits.unsigned_of_Z in H; solve [case (H eq_refl)]
         | H : Zmod.unsigned (Zmod.xor ?x _) = 0, E : Zmod.unsigned ?x = _ |- _ =>
             rewrite bits.unsigned_xor, E, bits.unsigned_of_Z in H; solve [inversion H]
         end.
    (* SPI timeout: recvEthernet's precise timeout trace, weakened *)
    all: try solve [ right; right; right; right; split;
                     [ eapply recvEthernet_timeout_any; eassumption | assumption ] ].

    Unshelve.
    all : try match goal with H : context [bytes (Zmod.add _ _) _] |- _ => seprewrite_in @bytearray_index_merge H end.
    all : try (eexists; split; [ ecancel_assumption | ]).
    all : try rewrite List.length_app.
    all : lia.
  Qed.

  Local Ltac prove_ext_spec :=
    lazymatch goal with
    | |- ext_spec _ _ _ _ _ => split; [shelve|]; split; [trivial|]
    end.

  Local Ltac zify_unsigned :=
    repeat match goal with
    | |- context[Zmod.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H; pose proof H
    | G : context[Zmod.unsigned ?e] |- _ => let H := unsigned.zify_expr e in rewrite H in G; pose proof H
    end;
    repeat match goal with H:absint_eq ?x ?x |- _ => clear H end;
    repeat match goal with H:?A |- _ => clear H; match goal with G:A |- _ => idtac end end.

  Lemma byte_mask_byte (b : byte) : Zmod.and (bits.of_Z 32 (byte.unsigned b)) (bits.of_Z 32 255) = bits.of_Z 32 (byte.unsigned b) :> word.
  Proof.
    eapply Zmod.unsigned_inj; rewrite bits.unsigned_and.
    rewrite !bits.unsigned_of_Z.
    pose proof byte.unsigned_range b.
    rewrite <-!(Z.land_ones _ 32) by (cbv; congruence).
    rewrite <-byte.wrap_unsigned at 2. cbv [byte.wrap].
    change (Z.land 255 (Z.ones 32)) with (Z.ones 8).
    rewrite <-Z.land_ones by lia.
    Z.bitwise. Btauto.btauto.
  Qed.

  Lemma lightbulb_handle_ok : program_logic_goal_for_function! lightbulb_handle.
  Proof.
    repeat (eauto || straightline || split_if || eapply interact_nomem || prove_ext_spec || trans_ltu).
    all: subst r.
    1: replace (Zmod.unsigned (bits.of_Z 32 42)) with 42 in * by ZnWords.ZnWords.
    2: {
      eexists nil; split; eauto.
      eexists nil; split; cbv [mmio_trace_abstraction_relation]; eauto using List.Forall2_nil.
      right; repeat split; eauto.
      { intros (?&?&?). ZnWords.ZnWords. }
      intros HX; rewrite ?bits.unsigned_of_Z in HX; inversion HX. }

    seplog_use_array_load1 H 12.
    seplog_use_array_load1 H 13.
    seplog_use_array_load1 H 23.
    seplog_use_array_load1 H 42.
    unshelve (repeat (eauto || straightline || split_if || eapply interact_nomem || prove_ext_spec)).

    1: letexists; split; [exact eq_refl|]; split; [split; trivial|].
    { subst addr r; cbv [isMMIOAddr];
      rewrite !bits.unsigned_of_Z; split; trivial.
      cbv -[Z.le Z.lt]. lia. }
    1: repeat straightline.
    1: repeat straightline; eapply interact_nomem; repeat straightline.
    1: letexists; letexists; split; [exact eq_refl|]; split; [split; trivial|].
    { subst addr r; cbv [isMMIOAddr];
      rewrite !bits.unsigned_of_Z; split; trivial.
      cbv -[Z.le Z.lt]. lia. }
    1: repeat straightline.

    1: repeat (eauto || straightline || split_if || eapply interact_nomem || prove_ext_spec || trans_ltu).

    all : eexists; split.
    all: repeat (eapply align_trace_cons || exact (eq_sym (List.app_nil_l _))).
    all : eexists; split.

    all : repeat (eapply List.Forall2_cons || eapply List.Forall2_nil).
    all :
    try match goal with
    |- mmio_event_abstraction_relation _ _ =>
        (left+right); eexists _, _; split; exact eq_refl
    end.

    all : repeat trans_ltu;
    repeat match goal with
    | H : Zmod.unsigned ?v <> 0 |- _ =>
        let v := rdelta.rdelta v in
        let __ := lazymatch v with if Zmod.eqb _ _ then Zmod.one else Zmod.zero => I end in
        eapply Properties.word.if_nonzero in H; eapply Zmod.eqb_eq in H
    | H : Zmod.unsigned ?v = 0 |- _ =>
        let v := rdelta.rdelta v in
        let __ := lazymatch v with if Zmod.eqb _ _ then Zmod.one else Zmod.zero => I end in
        eapply (Properties.word.if_zero _ width_pos) in H; eapply word.eqb_false in H
    end;
    repeat match goal with x := _ |- _ => subst x end;
    repeat match goal with H : _ |- _ => rewrite !byte_mask_byte in H end.
    all : repeat straightline.

    1: {
      left.
      eexists; repeat split.
      all : rewrite ?bits.unsigned_of_Z in H6.
      all : try eassumption.
      1: lia.
      cbv [gpio_set one existsl concat].
      eexists _, ([_]), ([_]); repeat split; repeat f_equal.
      eapply Zmod.unsigned_inj.
      rewrite ?byte_mask_byte.
      rewrite ?bits.unsigned_and.
      rewrite bits.unsigned_1 by lia.
      change 1 with (Z.ones 1).
      rewrite Z.land_ones, Z.bit0_mod by lia.
      rewrite !bits.unsigned_of_Z.
      rewrite 2(Z.mod_small _ (2^32)); try exact eq_refl.
      1: match goal with |- 0 <= byte.unsigned ?x < _ => pose proof byte.unsigned_range x end; lia.
      clear; Z.div_mod_to_equations; lia. }

    (* parse failures *)
    all : right; repeat split; eauto.
    2,4: rewrite bits.unsigned_of_Z; intro X; inversion X.
    all : intros (?&?&?&?&?).
    { rewrite bits.unsigned_of_Z in H6; contradiction. }
    { apply H6. rewrite bits.unsigned_of_Z. exact H8. }

    Unshelve.
    all : intros; exact True.
  Qed.

  Import bedrock2.ZnWords.
  Import bedrock2.SepAutoArray bedrock2.SepCalls.

  (* recvEthernet is proved in the leakage program logic: its specification
     and lan9250_readword's are leakage specifications. *)
  Import bedrock2.LeakageProgramLogic.

  Local Ltac split_if_leakage :=
    lazymatch goal with
      |- LeakageWeakestPrecondition.cmd _ ?c _ _ _ _ ?post =>
      let c := eval hnf in c in
          lazymatch c with
          | cmd.cond _ _ _ => letexists; letexists; split; [solve[repeat straightline]|split]
          end
    end.

  (* [straightline] on the loop's [enforce] goal, without its eabstract (slow) *)
  Local Ltac loop_again :=
    lazymatch goal with
    | |- Markers.unique (Markers.left ?G) =>
      change G;
      unshelve (idtac; repeat match goal with
                       | |- Markers.split (?P /\ Markers.right ?Q) =>
                         split; [solve [repeat straightline] | change Q]
                       | |- exists _, _ => letexists
                       end); []
    end.

  (* the callee's timeout-or-success disjunction, against the branch taken *)
  Local Ltac dispatch_call_result :=
    repeat match goal with
    | x := ?y |- _ => is_var y; subst x
    | H :  _ /\ _ \/ ?Y /\ _, G : not ?X |- _ => constr_eq X Y; let Z := fresh in destruct H as [|[Z ?]]; [|case (G Z)]
    | H :  not ?Y /\ _ \/ _ /\ _, G : ?X |- _ => constr_eq X Y; let Z := fresh in destruct H as [[Z ?]|]; [case (Z G)|]
    | H : _ /\ _ |- _ => destruct H
    end.

  Local Ltac subst_leakage := repeat match goal with x := _ : leakage |- _ => subst x end.
  Local Ltac leak_finish :=
    subst_leakage; cbn [leak_binop];
    rewrite ?List.rev_involutive, ?List.app_nil_r;
    repeat progress (rewrite <-?List.app_assoc; cbn [List.app]);
    reflexivity.

  (* the packet loop: [i] words read so far, [n] bytes in total *)
  Lemma to_nat_div4_S (n i : word) (Hlt : Zmod.unsigned i < Zmod.unsigned n)
    (Hmod : Zmod.unsigned i mod 4 = Zmod.unsigned n mod 4) :
    Z.to_nat (Zmod.unsigned (Zmod.sub n i) / 4) =
    S (Z.to_nat (Zmod.unsigned (Zmod.sub n (Zmod.add i (bits.of_Z 32 4))) / 4)).
  Proof.
    pose proof (bits.unsigned_range n width_nonneg); pose proof (bits.unsigned_range i width_nonneg).
    rewrite !Zmod.unsigned_sub, !Zmod.unsigned_add, !bits.unsigned_of_Z.
    change (4 mod 2 ^ 32) with 4.
    rewrite (Z.mod_small (Zmod.unsigned i + 4)) by (Z.div_mod_to_equations; lia).
    rewrite !Z.mod_small by (Z.div_mod_to_equations; lia).
    rewrite <-Znat.Z2Nat.inj_succ by (Z.div_mod_to_equations; lia).
    f_equal. Z.div_mod_to_equations. lia.
  Qed.

  Lemma unsigned_add4 (n i : word) (Hlt : Zmod.unsigned i < Zmod.unsigned n)
    (Hmod : Zmod.unsigned i mod 4 = Zmod.unsigned n mod 4) :
    Zmod.unsigned (Zmod.add i (bits.of_Z 32 4)) = Zmod.unsigned i + 4.
  Proof.
    pose proof (bits.unsigned_range n width_nonneg); pose proof (bits.unsigned_range i width_nonneg).
    rewrite Zmod.unsigned_add, bits.unsigned_of_Z. change (4 mod 2 ^ 32) with 4.
    apply Z.mod_small. Z.div_mod_to_equations; lia.
  Qed.

  Lemma lan9250_readpacket_word (w : word) bs :
    lan9250_readpacket (LittleEndianList.le_split 4 (Zmod.unsigned w) ++ bs) =
    (lan9250_fastread4 $0 w +++ lan9250_readpacket bs).
  Proof.
    pose proof (LittleEndianList.length_le_split 4 (Zmod.unsigned w)) as Hl.
    destruct (LittleEndianList.le_split 4 (Zmod.unsigned w)) as [|b0 [|b1 [|b2 [|b3 [|]]]]] eqn:E;
      cbn [length] in Hl; try discriminate Hl.
    cbn [List.app lan9250_readpacket]. rewrite <-E, LittleEndianList.le_combine_split.
    change (Z.of_nat 4 * 8) with 32. rewrite bits.mod_to_Z, Zmod.of_Z_unsigned. reflexivity.
  Qed.

  (* one step of the packet loop, as rewrite rules: unfolding it with cbn in
     the middle of recvEthernet_ok makes the kernel check of the proof take
     hours *)
  Lemma recvEthernet_loop_S fr n p l acc :
    recvEthernet_loop fr (S n) p l acc =
    match parse_lan9250_seg 8 l with
    | None => leak_bool false :: leak_bool true :: fr $0 (List.rev l) ++ leak_unit :: leak_bool true :: acc
    | Some (x, l) => recvEthernet_loop fr n (Zmod.add p $4) l (leak_word p :: leak_bool false :: fr $0 (List.rev x) ++ leak_unit :: leak_bool true :: acc)
    end.
  Proof. reflexivity. Qed.

  Lemma recvEthernet_loop_O fr p l acc : recvEthernet_loop fr O p l acc = leak_bool false :: acc.
  Proof. reflexivity. Qed.

  Lemma recvEthernet_loop_timeout fr n p l acc (H : parse_lan9250_txn 8 l = None) :
    recvEthernet_loop fr (S n) p l acc =
    leak_bool false :: leak_bool true :: fr $0 (List.rev l) ++ leak_unit :: leak_bool true :: acc.
  Proof. rewrite recvEthernet_loop_S. cbv [parse_lan9250_seg]. rewrite H. reflexivity. Qed.

  Lemma recvEthernet_loop_word fr n p l acc x txs rxs l' (H : parse_lan9250_txn 8 l = Some (x, txs, rxs, l')) :
    recvEthernet_loop fr (S n) p l acc =
    recvEthernet_loop fr n (Zmod.add p $4) l' (leak_word p :: leak_bool false :: fr $0 (List.rev x) ++ leak_unit :: leak_bool true :: acc).
  Proof. rewrite recvEthernet_loop_S. cbv [parse_lan9250_seg]. rewrite H. reflexivity. Qed.

  (* [program_logic_goal_for_function! recvEthernet], in the leakage program logic. *)
  Lemma recvEthernet_ok : forall functions,
    LeakageProgramLogic.program_logic_goal_for recvEthernet
      (forall (EnvContains : map.get functions "recvEthernet" = Some recvEthernet),
       spec_of_lan9250_readword functions ->
       spec_of_recvEthernet functions).
  Proof.
    straightline. straightline.
    instantiate (1 := recvEthernet_leak f).
    repeat (straightline || split_if_leakage || LeakageProgramLogic.straightline_call || ZnWords).
    3: {
    refine (LeakageLoops.tailrec_earlyout
      (HList.polymorphic_list.cons (list byte) (HList.polymorphic_list.cons (mem -> Prop) HList.polymorphic_list.nil))
      ["buf";"num_bytes";"i";"read";"err"]
      (fun v scratch R k t m buf num_bytes_loop i read err => PrimitivePair.pair.mk (
        Zmod.unsigned err = 0 /\ Zmod.unsigned i <= Zmod.unsigned num_bytes /\
        v = Zmod.unsigned i /\ (bytes (Zmod.add buf i) scratch * R) m /\
        List.length scratch = Z.to_nat (Zmod.unsigned (Zmod.sub num_bytes i)) /\
        Zmod.unsigned i mod 4 = Zmod.unsigned num_bytes mod 4 /\
        num_bytes_loop = num_bytes)
      (fun K T M BUF NUM_BYTES I READ ERR =>
         NUM_BYTES = num_bytes_loop /\
         exists RECV, (bytes (Zmod.add buf i) RECV * R) M /\
         List.length RECV = List.length scratch /\
         exists iol, T = iol ++ t /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\
         (Zmod.unsigned ERR = 0 /\ lan9250_readpacket RECV ioh \/
          Zmod.unsigned ERR = 2^32-1 /\ exists recv, (lan9250_readpacket recv +++ lan9250_txn_timeout 8) ioh) /\
         K = recvEthernet_loop f (Z.to_nat (Zmod.unsigned (Zmod.sub num_bytes i) / 4)) (Zmod.add buf i) (List.rev ioh) [] ++ k)
      )
      _ (Z.gt_wf (Zmod.unsigned num_bytes)) _ _ _ _ _ _);
    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
    { repeat straightline. }
    { (* Hpre *)
      repeat (split; [trivial||ZnWords|]).
      replace (Zmod.add p_addr i) with p_addr by (subst i; ring).
      progress trans_ltu.
      scancel_asm.
      Tactics.ssplit.
      all : trivial; try listZnWords. }
    { (* Hbody *)
      repeat (loop_again || straightline).
      { LeakageProgramLogic.straightline_call; [ ZnWords | ].
        repeat straightline.
        split_if_leakage; [ intro | intro ].
        all: dispatch_call_result.
        (* SPI timeout: break *)
        { repeat (loop_again || straightline).
          left.
          repeat (loop_again || straightline).
          { subst br0. rewrite Z.ltb_irrefl. apply Zmod.unsigned_0. }
          eexists; split; [ eassumption | ].
          split; [ reflexivity | ].
          eexists; split; [ reflexivity | ].
          eexists; split; [ eassumption | ].
          split.
          { right; split; [ subst err; rewrite bits.unsigned_of_Z; reflexivity | ].
            exists nil, nil, x16; split; [ rewrite List.app_nil_r; reflexivity | split; [ reflexivity | eassumption ] ]. }
          trans_ltu.
          match goal with Hlt : Zmod.unsigned ?i < Zmod.unsigned ?n, Hmod : Zmod.unsigned ?i mod 4 = Zmod.unsigned ?n mod 4 |- _ =>
            rewrite (to_nat_div4_S n i Hlt Hmod) end.
          match goal with Ht : lan9250_txn_timeout 8 ?x |- _ =>
            rewrite (recvEthernet_loop_timeout _ _ _ _ _ (parse_lan9250_txn_timeout 8 x Ht)) end.
          leak_finish. }
        (* store *)
        repeat straightline.
        try trans_ltu.
        match goal with
          | H: context[Zmod.unsigned (Zmod.sub ?a ?b)] |- _ =>
              pose proof (bits.unsigned_range a width_nonneg);
              pose proof (bits.unsigned_range b width_nonneg);
              let H := fresh in
              pose proof Zmod.unsigned_sub a b as H;
              rewrite Z.mod_small in H by lia
        end.
        match goal with H10 : _ ?a0 |- store _ ?a0 _ _ _ => rewrite <- (List.firstn_skipn 4 _) in H10;
          SeparationLogic.seprewrite_in (symmetry! @bytearray_index_merge) H10 end.
        { instantiate (1:= bits.of_Z 32 4).
          rewrite bits.unsigned_of_Z.
          rewrite List.firstn_length_le; [exact eq_refl|]. Z.div_mod_to_equations. lia. }
        do 2 straightline.
        match goal with H12:_|-_ => seprewrite_in @scalar32_of_bytes H12 end.
        { eapply List.firstn_length_le; Z.div_mod_to_equations; lia. }
        straightline.
        (* after store *)
        repeat (loop_again || straightline).
        right.
        lazymatch goal with |- Markers.unique (Markers.left ?G) => change G end.
        do 2 letexists. exists (Zmod.unsigned i).
        cbv [Markers.split Markers.right].
        split; [ | split ].
        { (* loop invariant for the next iteration *)
          repeat (split; [ solve [ assumption | reflexivity | ZnWords ] | ]).
          split.
          { (* memory *)
            match goal with |- (bytes (?b + ?i) _ * _) _ => replace (Zmod.add b i) with (Zmod.add (Zmod.add b x11) (bits.of_Z 32 4)) by (subst i; ring) end.
            ecancel_assumption. }
          split.
          { match goal with |- length ?x = _ => subst x end.
            rewrite List.length_skipn. ZnWords. }
          split; [ subst i; rewrite (unsigned_add4 num_bytes) by assumption; Z.div_mod_to_equations; lia | reflexivity ]. }
        { repeat match goal with x := _ : Z |- _ => subst x end.
          subst i; rewrite (unsigned_add4 num_bytes) by assumption; Z.div_mod_to_equations; lia. }
        { (* the postcondition of the rest of the loop gives this iteration's *)
          intros K T M ? ? ? ? ? (HNB & RECV & HM & HL & iol & HT & ioh & Hrel & Hcase & HK).
          split; [ exact HNB | ].
          exists (LittleEndianList.le_split 4 (Zmod.unsigned x10) ++ RECV).
          split.
          { match goal with x := sep _ _ |- _ => subst x end.
            cbv [scalar32 truncated_word truncate_word truncate_Z truncated_scalar] in HM; extract_ex1_and_emp_in_hyps.
            seprewrite_in (symmetry! @array1_iff_eq_of_list_word_at) HM.
            { rewrite LittleEndianList.length_le_split. cbv; discriminate. }
            replace (Zmod.add x9 i) with (Zmod.add (Zmod.add x9 x11) (bits.of_Z 32 4)) in HM by (subst i; ring).
            change (bytes_per access_size.four) with 4%nat in HM.
            subst a.
            SeparationLogic.seprewrite_in (@bytearray_index_merge) HM.
            { rewrite bits.unsigned_of_Z, LittleEndianList.length_le_split. exact eq_refl. }
            ecancel_assumption. }
          split.
          { rewrite List.length_app, LittleEndianList.length_le_split, HL.
            match goal with x := List.skipn _ _ |- _ => subst x end.
            rewrite List.length_skipn. ZnWords. }
          exists (iol ++ x15); split.
          { subst T a0. rewrite List.app_assoc. reflexivity. }
          exists (ioh ++ x16); split.
          { eapply List.Forall2_app; eassumption. }
          split.
          { destruct Hcase as [[? ?]|[? [recv (l1 & l2 & -> & Hp & Ht)]]]; [left|right]; split; try assumption.
            { rewrite lan9250_readpacket_word. eapply concat_app; eassumption. }
            { exists (LittleEndianList.le_split 4 (Zmod.unsigned x10) ++ recv), (l1 ++ x16), l2.
              split; [ rewrite List.app_assoc; reflexivity | ].
              split; [ | assumption ].
              rewrite lan9250_readpacket_word. eapply concat_app; eassumption. } }
          { subst K i a.
            match goal with Hlt : Zmod.unsigned x11 < Zmod.unsigned num_bytes, Hmod : Zmod.unsigned x11 mod 4 = Zmod.unsigned num_bytes mod 4 |- _ =>
              rewrite (to_nat_div4_S num_bytes x11 Hlt Hmod) end.
            rewrite List.rev_app_distr.
            destruct (parse_fastread4_word _ _ _ (List.rev ioh) _ eq_refl H18) as (?&?&Hp&_).
            rewrite (recvEthernet_loop_word _ _ _ _ _ _ _ _ _ Hp).
            rewrite (recvEthernet_loop_acc _ _ _ _ (_ :: _)).
            replace (Zmod.add x9 (Zmod.add x11 (bits.of_Z 32 4))) with (Zmod.add (Zmod.add x9 x11) (bits.of_Z 32 4)) by ring.
            leak_finish. } } }
      (* loop exit *)
      { repeat trans_ltu.
        eexists; split; [ eassumption | ].
        split; [ reflexivity | ].
        exists nil; split; [ reflexivity | ].
        exists nil; split; [ constructor | ].
        match goal with H : length ?x = Z.to_nat _ |- _ =>
          assert (x = nil) as -> by (destruct x; [ reflexivity | exfalso; cbn [length] in H; ZnWords ]) end.
        split.
        { left; split; [ assumption | reflexivity ]. }
        match goal with |- context [recvEthernet_loop _ ?n] => replace n with O by (ZnWords) end.
        rewrite recvEthernet_loop_O. leak_finish. }
    }
    (* after the loop *)
    { repeat straightline.
      dispatch_call_result.
      subst i.
      subst_leakage.
      progress replace (Z.to_nat (Zmod.unsigned (Zmod.sub p_addr p_addr) / 1)) with O in * by ZnWords.
      change (bits.of_Z 32 0) with (@Zmod.zero (2^32)) in *.
      rewrite ?Zmod.add_0_r, ?Zmod.sub_0_r, ?Z.mul_1_l, ?Nat.add_0_l, ?Z2Nat.id, ?Zmod.of_Z_unsigned in * by apply (bits.unsigned_range _ width_nonneg).
      cbn [List.firstn List.skipn seps array] in *.
      repeat trans_ltu.
      change (Zmod.unsigned (bits.of_Z 32 1521)) with 1521 in *.
      match goal with H : lan9250_fastread4 _ ?s x6 |- _ =>
        assert (Hnb : num_bytes = lan9250_decode_length s)
          by (repeat match goal with x := _ : word |- _ => subst x end; reflexivity) end.
      repeat match goal with x := Zmod.and _ _ |- _ => subst x end.
      repeat match goal with x := _ ++ _ |- _ => subst x end.
      exists (x13 ++ x5 ++ x1); split; [ rewrite <-!List.app_assoc; reflexivity | ].
      exists (x14 ++ x6 ++ x2); split; [ repeat eapply List.Forall2_app; eassumption | ].
      split.
      { match goal with H : _ /\ _ \/ _ /\ _ |- _ => destruct H as [[Herr Hpkt]|[Herr [recv Hto]]] end; [left|right].
        { (* success *)
          split; [ assumption | ].
          eexists _, _; split; [ ecancel_assumption | ].
          split.
          { eexists _, _; split; [ repeat eapply concat_app; eassumption | ].
            split.
            { match goal with H : Zmod.unsigned (Zmod.and _ _) <> 0 |- _ => revert H end.
              rewrite bits.unsigned_and, bits.unsigned_of_Z. exact id. }
            rewrite <-Hnb.
            match goal with H : length x12 = _ |- _ => rewrite H end.
            rewrite List.length_firstn. ZnWords. }
          split.
          { rewrite List.length_skipn. ZnWords. }
          match goal with H : length x12 = _ |- _ => rewrite H end.
          rewrite List.length_firstn. ZnWords. }
        { (* SPI timeout while reading the packet *)
          split; [ rewrite Herr; cbv; discriminate | ].
          match goal with H : (bytes p_addr x12 * _) m0 |- _ =>
            SeparationLogic.seprewrite_in @bytearray_index_merge H;
            [ match goal with H : length x12 = _ |- _ => rewrite H end; rewrite List.length_firstn; ZnWords | ] end.
          eexists; split; [ ecancel_assumption | ].
          split.
          { rewrite List.length_app, List.length_skipn.
            match goal with H : length x12 = _ |- _ => rewrite H end.
            rewrite List.length_firstn. ZnWords. }
          right; right; split; [ exact Herr | ].
          right; right.
          destruct Hto as (l1 & l2 & -> & Hr & Ht).
          eexists _, _, recv; split; [ | split ].
          { rewrite <-List.app_assoc. eapply concat_app; [ | exact Ht ].
            eapply concat_app; [ | exact Hr ].
            eapply concat_app; eassumption. }
          { match goal with H : Zmod.unsigned (Zmod.and _ _) <> 0 |- _ => exact H end. }
          { rewrite <-Hnb. assumption. } } }
      { (* leakage *)
        erewrite recvEthernet_leak_status by eassumption.
        cbv zeta. rewrite <-Hnb, Zmod.add_0_r, Zmod.sub_0_r.
        match goal with H : Zmod.unsigned num_bytes < 1521 |- _ => rewrite (proj2 (Z.ltb_lt _ _) H) end.
        leak_finish. } }
    }
    (* the early returns *)
    all: dispatch_call_result.
    all: subst_leakage.
    all: repeat match goal with x := _ ++ _ |- _ => subst x end.
    all: repeat match goal with x := Zmod.and _ _ |- _ => subst x end.
    { (* the read of RX_FIFO_INF timed out *)
      exists x1; split; [ reflexivity | ].
      exists x2; split; [ assumption | ].
      split.
      { right. split; [ subst err; rewrite bits.unsigned_of_Z; cbv; discriminate | ].
        exists buf; split; [ assumption | ]; split; [ assumption | ].
        right; right; split; [ subst err; rewrite bits.unsigned_of_Z; reflexivity | ].
        left; assumption. }
      { erewrite recvEthernet_leak_timeout1 by eassumption. leak_finish. } }
    { (* the read of RX_STATUS_FIFO_PORT timed out *)
      exists (x5 ++ x1); split; [ rewrite <-List.app_assoc; reflexivity | ].
      exists (x6 ++ x2); split; [ eapply List.Forall2_app; eassumption | ].
      split.
      { right. split; [ subst err; rewrite bits.unsigned_of_Z; cbv; discriminate | ].
        exists buf; split; [ assumption | ]; split; [ assumption | ].
        right; right; split; [ subst err; rewrite bits.unsigned_of_Z; reflexivity | ].
        right; left. eexists; split; [ eapply concat_app; eassumption | ].
        match goal with H : Zmod.unsigned (Zmod.and _ _) <> 0 |- _ => exact H end. }
      { erewrite recvEthernet_leak_timeout2 by eassumption. leak_finish. } }
    { (* packet too long *)
      exists (x5 ++ x1); split; [ rewrite <-List.app_assoc; reflexivity | ].
      exists (x6 ++ x2); split; [ eapply List.Forall2_app; eassumption | ].
      repeat trans_ltu.
      change (Zmod.unsigned (bits.of_Z 32 1521)) with 1521 in *.
      match goal with H : lan9250_fastread4 _ ?s x6 |- _ =>
        assert (Hnb : num_bytes = lan9250_decode_length s)
          by (repeat match goal with x := _ : word |- _ => subst x end; reflexivity) end.
      split.
      { right. split; [ subst err; rewrite bits.unsigned_of_Z; cbv; discriminate | ].
        exists buf; split; [ assumption | ]; split; [ assumption | ].
        right; left; split; [ subst err; rewrite bits.unsigned_of_Z; reflexivity | ].
        eexists _, _; split; [ eapply concat_app; eassumption | ].
        split.
        { match goal with H : Zmod.unsigned (Zmod.and _ _) <> 0 |- _ => revert H end.
          rewrite bits.unsigned_and, bits.unsigned_of_Z. exact id. }
        { rewrite <-Hnb. lia. } }
      { change (x6 ++ x2) with ([] ++ x6 ++ x2).
        erewrite recvEthernet_leak_status by eassumption.
        cbv zeta. rewrite <-Hnb.
        match goal with H : ~ (Zmod.unsigned num_bytes < 1521) |- _ => rewrite (proj2 (Z.ltb_nlt _ _) H) end.
        leak_finish. } }
    { (* no packet *)
      exists x1; split; [ reflexivity | ].
      exists x2; split; [ assumption | ].
      split.
      { right. split; [ subst err; rewrite bits.unsigned_of_Z; cbv; discriminate | ].
        exists buf; split; [ assumption | ]; split; [ assumption | ].
        left; split; [ subst err; rewrite bits.unsigned_of_Z; reflexivity | ].
        eexists; split; [ eassumption | ]. assumption. }
      { erewrite recvEthernet_leak_no_packet by eassumption. leak_finish. } }
  Qed.


End WithParameters.

Section Link.
  Import Syntax BinInt String List.ListNotations ZArith.
  Local Notation word := (bits 32).
  Context {mem: map.map word Byte.byte}.
  Context {mem_ok: map.ok mem}.
  Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
  Import SPI.

  Definition function_impls := map.of_list
    &[,lightbulb_init; lan9250_init; lan9250_wait_for_boot; lan9250_mac_write;
    lightbulb_loop; lightbulb_handle; recvEthernet;  lan9250_writeword; lan9250_readword;
    spi_xchg; spi_write; spi_read].

  Local Ltac specapply s := eapply s; [reflexivity|..].

  (* The specifications of spi_* (SPI.v) and lan9250_* (LAN9250.v) are leakage
     specifications; the plain proofs above use the plain consequences
     [lan9250_*_plain_spec], which need the function list to be free of
     stackalloc and some stack-pointer oracle (any one: the plain
     specifications do not mention it). *)
  Local Instance lightbulb_pick_sp : LeakageSemantics.PickSp := fun _ => bits.of_Z 32 0.

  Lemma function_impls_stackalloc_free : SemanticsRelations.stackalloc_free_env function_impls.
  Proof. eapply SemanticsRelations.stackalloc_free_env_of_list. exact eq_refl. Qed.

  Lemma link_lightbulb_loop : spec_of_lightbulb_loop function_impls.
  Proof.
    repeat first
      [ exact function_impls_stackalloc_free
      | eapply lan9250_init_plain_spec_of_leakage
      | specapply lightbulb_loop_ok | specapply lightbulb_init_ok
      | specapply recvEthernet_ok | specapply lightbulb_handle_ok
      | specapply lan9250_init_ok | specapply lan9250_wait_for_boot_ok | specapply lan9250_mac_write_ok
      | specapply lan9250_readword_ok | specapply lan9250_writeword_ok
      | specapply spi_xchg_ok | specapply spi_write_ok | specapply spi_read_ok ].
  Qed.
  Lemma link_lightbulb_init : spec_of_lightbulb_init function_impls.
  Proof.
    repeat first
      [ exact function_impls_stackalloc_free
      | eapply lan9250_init_plain_spec_of_leakage
      | specapply lightbulb_loop_ok | specapply lightbulb_init_ok
      | specapply recvEthernet_ok | specapply lightbulb_handle_ok
      | specapply lan9250_init_ok | specapply lan9250_wait_for_boot_ok | specapply lan9250_mac_write_ok
      | specapply lan9250_readword_ok | specapply lan9250_writeword_ok
      | specapply spi_xchg_ok | specapply spi_write_ok | specapply spi_read_ok ].
  Qed.
End Link.
