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
From bedrock2.Map Require Import Separation SeparationLogic.
Require bedrock2.SepAutoArray bedrock2.SepCalls.
Import ZArith.
Local Open Scope Z_scope.

Section WithParameters.
  Import Syntax BinInt String List.ListNotations ZArith.
  Local Notation word := (bits 32).
  Context {mem: map.map word Byte.byte}.
  Context {mem_ok: map.ok mem}.
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

  Instance spec_of_recvEthernet : spec_of "recvEthernet" := fun functions =>
    forall p_addr (buf:list byte) R m t,
      (array scalar8 (bits.of_Z 32 1) p_addr buf * R) m ->
      length buf = 1520%nat ->
      WeakestPrecondition.call functions "recvEthernet" t m [p_addr] (fun t' m' rets =>
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
             Zmod.unsigned err = 2^32-1 /\ TracePredicate.concat TracePredicate.any (spi_timeout) ioh
            ))
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

  Lemma lightbulb_init_ok : program_logic_goal_for_function! lightbulb_init.
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

  Lemma lightbulb_loop_ok : program_logic_goal_for_function! lightbulb_loop.
  Proof.
    repeat (match goal with H : or _ _ |- _ => destruct H; intuition idtac end
          || straightline || straightline_call || split_if || ecancel_assumption || eauto || lia).
    all : split; [shelve|].
    all : eexists; split.
    all: repeat (eapply align_trace_cons || exact (eq_sym (List.app_nil_l _)) || eapply align_trace_app).
    all : eexists; split.
    all : try subst err; rewrite ?bits.unsigned_of_Z.
    all : repeat (eapply List.Forall2_cons || eapply List.Forall2_nil || eapply List.Forall2_app || eauto 15 using concat_app).
    { subst v. rewrite bits.unsigned_xor, H10, bits.unsigned_of_Z in H4. case (H4 eq_refl). }
    { subst v. rewrite bits.unsigned_xor, H9, bits.unsigned_of_Z in H4. inversion H4. }
    { subst v. rewrite bits.unsigned_xor, H9, bits.unsigned_of_Z in H4. inversion H4. }

    Unshelve.
    all : eexists; split; [ eauto | ].
    all : try seprewrite_in @bytearray_index_merge H6; eauto.
    all : try rewrite List.app_length.
    all : try lia.
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
    1: replace (Zmod.unsigned (bits.of_Z 32 42)) with 42 in * by ZnWords.zlia.
    2: {
      eexists nil; split; eauto.
      eexists nil; split; cbv [mmio_trace_abstraction_relation]; eauto using List.Forall2_nil.
      right; repeat split; eauto.
      { intros (?&?&?). ZnWords.zlia. }
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

  Lemma recvEthernet_ok : program_logic_goal_for_function! recvEthernet.
  Proof.
    straightline.
    rename H into Hcall; clear H0 H1. rename H2 into H. rename H3 into H0.
    repeat (straightline || split_if || straightline_call || eauto 99 || prove_ext_spec || zlia).

    3: {

    refine (Loops.tailrec_earlyout
      (HList.polymorphic_list.cons (list byte) (HList.polymorphic_list.cons (mem -> Prop) HList.polymorphic_list.nil))
      ["buf";"num_bytes";"i";"read";"err"]
      (fun v scratch R t m buf num_bytes_loop i read err => PrimitivePair.pair.mk (
        Zmod.unsigned err = 0 /\ Zmod.unsigned i <= Zmod.unsigned num_bytes /\
        v = Zmod.unsigned i /\ (bytes (Zmod.add buf i) scratch * R) m /\
        List.length scratch = Z.to_nat (Zmod.unsigned (Zmod.sub num_bytes i)) /\
        Zmod.unsigned i mod 4 = Zmod.unsigned num_bytes mod 4 /\
        num_bytes_loop = num_bytes)
      (fun T M BUF NUM_BYTES I READ ERR =>
         NUM_BYTES = num_bytes_loop /\
         exists RECV, (bytes (Zmod.add buf i) RECV * R) M /\
         List.length RECV = List.length scratch /\
         exists iol, T = iol ++ t /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\
         (Zmod.unsigned ERR = 0 /\ lan9250_readpacket RECV ioh \/
          Zmod.unsigned ERR = 2^32-1 /\ TracePredicate.concat TracePredicate.any (spi_timeout) ioh ) )
      )
      _ _ _ _ _ _ _ _);
    (* TODO wrap this into a tactic with the previous refine? *)
    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *;
      [ repeat (straightline || split_if || eapply interact_nomem || eauto 99) .. | ].
    { exact (Z.gt_wf (Zmod.unsigned num_bytes)). }

    {
      repeat (split; [trivial||zlia|]).
      replace (Zmod.add p_addr i) with p_addr by (subst i; ring).
      progress trans_ltu.

      scancel_asm.
      Tactics.ssplit.
      all : trivial; try zlia.
    }

      { straightline_call; repeat straightline.
        { rewrite bits.unsigned_of_Z. cbv; clear. intuition congruence. }
        split_if; do 6 straightline.

        (* SPI timeout, break loop *)
        { straightline.
          straightline.
          straightline.
          straightline.
          (* [repeat straightline] hangs *)
          do 5 eexists; split; [repeat straightline|]; [].
          left.
          repeat straightline.
          { subst br0. rewrite Z.ltb_irrefl. apply Zmod.unsigned_0. }
          eexists; split; eauto.
          split; eauto.
          eexists; split.
          { subst a; eauto. }
          eexists; split; eauto.
          right; split.
          { subst err. rewrite bits.unsigned_of_Z. exact eq_refl. }
          intuition eauto. }

        (* store *)
        do 4 straightline.
        trans_ltu.
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
        do 3 straightline.
        (* TODO straightline hangs in Loops.enforce *)
        do 5 letexists. split. { repeat straightline. }
        right. do 3 letexists.
        repeat split; repeat straightline; repeat split.
        { intuition idtac. }
        { subst i.
          rewrite Zmod.unsigned_add; rewrite Z.mod_small;
          replace (Zmod.unsigned (bits.of_Z 32 4)) with 4.
          2,4: rewrite bits.unsigned_of_Z; exact eq_refl.
          1,2: try (Z.div_mod_to_equations; lia). }
        { replace (Zmod.add x9 i)
            with (Zmod.add (Zmod.add x9 x11) (bits.of_Z 32 4)) by (subst i; ring).
          ecancel_assumption. }
        { match goal with x1 := _ |- _ => subst x1; rewrite List.length_skipn end.
          zlia. }
        { zlia. }
        { zlia. }
        { zlia. }

        { letexists; repeat split.
          { repeat match goal with x := _ |- _ => is_var x; subst x end; subst.
            cbv [scalar32 truncated_word truncate_word truncate_Z truncated_scalar] in *; extract_ex1_and_emp_in_hyps.
            seprewrite_in (symmetry! @array1_iff_eq_of_list_word_at) H25. { cbv; discriminate. }
            progress replace (Zmod.add x9 (Zmod.add x11 4)) with
                    (Zmod.add (Zmod.add x9 x11) (bits.of_Z 32 4)) in * by ring.
            SeparationLogic.seprewrite_in (@bytearray_index_merge) H25.
            { rewrite bits.unsigned_of_Z; exact eq_refl. } { ecancel_assumption. } }
          { subst RECV. rewrite List.app_length, LittleEndianList.length_le_split.
            rewrite H26. subst x22. rewrite List.length_skipn. simpl bytes_per.
            enough ((4 <= length x7)%nat) by lia.
            Z.div_mod_to_equations; lia. }
          cbv [truncate_word truncate_Z] in *.
          repeat match goal with x := _ |- _ => is_var x; subst x end; subst.
          eexists; split.
          { rewrite List.app_assoc; eauto. }
          eexists; split.
          { eapply List.Forall2_app; eauto.  }
          destruct H29; [left|right]; repeat (straightline || split || eauto using TracePredicate.any_app_more).
          eapply TracePredicate.concat_app; eauto.
          unshelve erewrite (_ : LittleEndianList.le_combine _ = Zmod.unsigned x10); rewrite ?Zmod.of_Z_unsigned; try solve [intuition idtac].
          {
            etransitivity.
            1: eapply (LittleEndianList.le_combine_split 4).
            eapply bits.mod_to_Z. } } }

      { eexists; split; eauto. split; eauto. exists nil; split; eauto.
        eexists; split; [constructor|].
        left. split; eauto.
        enough (Hlen : length x7 = 0%nat) by (destruct x7; try solve[inversion Hlen]; exact eq_refl).
        PreOmega.zify.
        rewrite H13.
        subst br.
        destruct (Z.ltb (Zmod.unsigned x11) (Zmod.unsigned num_bytes)) eqn:HJ.
        { rewrite bits.unsigned_1 in H11 by lia. inversion H11. }
        eapply Z.ltb_nlt in HJ.
        zlia. }
      repeat straightline.

      subst i.
      progress replace (Z.to_nat (Zmod.unsigned (Zmod.sub p_addr p_addr) / 1)) with O in * by zlia.
      rewrite ?Zmod.add_0_r, ?Zmod.sub_0_r, ?Z.mul_1_l, ?Nat.add_0_l, ?Z2Nat.id, ?Zmod.of_Z_unsigned in * by apply (bits.unsigned_range _ width_nonneg).

      eexists; split.
      1: { repeat match goal with |- context [?x] => match type of x with list _ => subst x end end.
        repeat rewrite List.app_assoc. f_equal. }
      eexists; split.
      1:repeat eapply List.Forall2_app; eauto.
      destruct H14; [left|right]; repeat straightline; repeat split; eauto.
      { progress trans_ltu.
        cbn [List.firstn array] in *.
        replace (Zmod.unsigned (bits.of_Z 32 1521)) with 1521 in *
          by (rewrite bits.unsigned_of_Z; exact eq_refl).
        eexists _, _; repeat split.
        { cbn [seps] in *. SeparationLogic.ecancel_assumption. }
        { generalize dependent x2. generalize dependent x6. intros.
          destruct H5; repeat straightline; try contradiction.
          destruct H9; repeat straightline; try contradiction.
          eexists _, _; split.
          { rewrite <-!List.app_assoc. eauto using TracePredicate.concat_app. }
          split; [zify_unsigned; eauto|].
        { cbv beta delta [lan9250_decode_length].
          rewrite H11. rewrite List.firstn_length, Znat.Nat2Z.inj_min.
          replace (Zmod.sub num_bytes (bits.of_Z 32 0)) with num_bytes by ring; cbn [List.skipn].
          rewrite ?Znat.Z2Nat.id by eapply (bits.unsigned_range _ width_nonneg).
          transitivity (Zmod.unsigned num_bytes); [zlia|exact eq_refl]. } }
        { pose proof (bits.unsigned_range num_bytes width_nonneg).
          rewrite List.length_skipn. lia. }
        rewrite H11, List.firstn_length_le, ?Znat.Z2Nat.id; cbn [List.skipn].
        all: try zlia.
        }
      { repeat match goal with H : _ |- _ => rewrite H; intro HX; solve[inversion HX] end. }
      { progress trans_ltu;
        progress replace (Zmod.unsigned (bits.of_Z 32 1521)) with 1521 in * by
          (rewrite bits.unsigned_of_Z; exact eq_refl).
        all : cbn [seps array List.firstn List.skipn] in *.
        eexists _; split; eauto; repeat split; try lia.
        { SeparationLogic.seprewrite_in @bytearray_index_merge H10.
          { rewrite H11, List.firstn_length. zlia. }
          eassumption. }
        { 1:rewrite List.app_length, List.length_skipn, H11, List.firstn_length.
          replace (Zmod.sub num_bytes (bits.of_Z 32 0)) with num_bytes by ring.
          enough (Z.to_nat (Zmod.unsigned num_bytes) <= length buf)%nat by zlia.
          rewrite ?Znat.Z2Nat.id by eapply (bits.unsigned_range _ width_nonneg); lia. }
        right. right. split; eauto using TracePredicate.any_app_more. } }

    all: eexists; split;
      [repeat match goal with |- context [?x] => match type of x with list _ => subst x end end;
      rewrite ?List.app_assoc; eauto|].
    all: eexists; split;
      [repeat eapply List.Forall2_app; eauto|].
    all:
      right; subst err;
      split; [intro HX; rewrite bits.unsigned_of_Z in HX; inversion HX|].
    all : repeat ((eexists; split; [solve[eauto]|]) || (split; [solve[eauto]|])).
    all : rewrite !bits.unsigned_of_Z.

    (* two cases of SPI timeout *)
    { left; split; [exact eq_refl|] || right.
      left; split; [exact eq_refl|] || right.
            split; [exact eq_refl|].
        intuition eauto using TracePredicate.any_app_more. }
    { left; split; [exact eq_refl|] || right.
      left; split; [exact eq_refl|] || right.
            split; [exact eq_refl|].
        intuition eauto using TracePredicate.any_app_more. }
    { left; split; [exact eq_refl|] || right.
      left; split; [exact eq_refl|].
      eexists _, _; split.
      1:eapply TracePredicate.concat_app; try intuition eassumption.
      subst v0.

      destruct (Z.ltb (Zmod.unsigned num_bytes) (Zmod.unsigned (bits.of_Z 32 1521))) eqn:?.
      all : rewrite bits.unsigned_of_Z in Heqb; rewrite ?bits.unsigned_1, ?Zmod.unsigned_0 in H6 by lia; try inversion H6.
      eapply Z.ltb_nlt in Heqb; revert Heqb.
      repeat match goal with |- context [?x] => match type of x with _ => subst x end end.
      cbv [lan9250_decode_length]. split. 2: rewrite !shamt_of_Z_small in Heqb by lia; cbn in *; lia.
      subst v. rewrite bits.unsigned_and, bits.unsigned_of_Z in H2. eapply H2. }
    { left.
      split; [exact eq_refl|].
      eexists; split; intuition eauto. }
  Defined.

  Import SPI.

  Definition function_impls := map.of_list
    &[,lightbulb_init; lan9250_init; lan9250_wait_for_boot; lan9250_mac_write;
    lightbulb_loop; lightbulb_handle; recvEthernet;  lan9250_writeword; lan9250_readword;
    spi_xchg; spi_write; spi_read].

  Local Ltac specapply s := eapply s; [reflexivity|..].

  Lemma link_lightbulb_loop : spec_of_lightbulb_loop function_impls.
  Proof.
    specapply lightbulb_loop_ok;
    (specapply recvEthernet_ok || specapply lightbulb_handle_ok);
        specapply lan9250_readword_ok; specapply spi_xchg_ok;
        (specapply spi_write_ok || specapply spi_read_ok).
  Qed.
  Lemma link_lightbulb_init : spec_of_lightbulb_init function_impls.
  Proof.
    specapply lightbulb_init_ok; specapply lan9250_init_ok;
    try (specapply lan9250_wait_for_boot_ok || specapply lan9250_mac_write_ok);
    (specapply lan9250_readword_ok || specapply lan9250_writeword_ok);
        specapply spi_xchg_ok;
        (specapply spi_write_ok || specapply spi_read_ok).
  Qed.
End WithParameters.
