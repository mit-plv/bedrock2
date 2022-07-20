Require Import coqutil.Z.Lia.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.FE310CSemantics.
Require Import coqutil.Macros.symmetry.
Require Import coqutil.Byte.
Require Import bedrock2Examples.SPI.
Require Import bedrock2Examples.LAN9250.
From coqutil Require Import Z.div_mod_to_equations.
From coqutil Require Import Word.Interface Map.Interface.
From coqutil.Tactics Require Import letexists eabstract.
From bedrock2 Require Import FE310CSemantics Semantics WeakestPrecondition ProgramLogic Array Scalars.
From bedrock2.Map Require Import Separation SeparationLogic.
Import ZArith.
Local Open Scope Z_scope.

Section WithParameters.
  Import Syntax BinInt String List.ListNotations ZArith.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

  Definition lightbulb_loop :=
    ("lightbulb_loop", (["p_addr"], ["err"], bedrock_func_body:(
      unpack! bytesWritten, err = recvEthernet(p_addr);
      if !err { (* success, packet *)
        unpack! err = lightbulb_handle(p_addr, bytesWritten);
        err = $0 (* bad packet continue anyway *)
      } else if !(err ^ $1) { (* success, no packet *)
        err = $0
      }
    ))).

  Definition recvEthernet :=
    ("recvEthernet", (["buf"], ["num_bytes";"err"], bedrock_func_body:(
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
      ))).

  Definition lightbulb_handle :=
    ("lightbulb_handle", (["packet";"len"], ["r"], bedrock_func_body:(
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
    ))).

  Definition lightbulb_init : func :=
    ("lightbulb_init", ([], [], bedrock_func_body:(
      output! MMIOWRITE($0x10012038, coq:((Z.shiftl (0xf) 2)));
      output! MMIOWRITE($0x10012008, coq:((Z.shiftl 1 23)));
      unpack! err = lan9250_init()
    ))).

  Import Datatypes List.
  Local Notation bytes := (array scalar8 (word.of_Z 1)).
  Local Infix "*" := (sep).
  Local Infix "*" := (sep) : type_scope.

  Import TracePredicate. Import TracePredicateNotations.
  Import Word.Properties.
  Import lightbulb_spec.

  Instance spec_of_recvEthernet : spec_of "recvEthernet" := fun functions =>
    forall p_addr (buf:list byte) R m t,
      (array scalar8 (word.of_Z 1) p_addr buf * R) m ->
      length buf = 1520%nat ->
      WeakestPrecondition.call functions "recvEthernet" t m [p_addr] (fun t' m' rets =>
        exists bytes_written err, rets = [bytes_written; err] /\
        exists iol, t' = iol ++ t /\
        exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
          (word.unsigned err = 0 /\
            exists recv buf, (bytes p_addr recv * bytes (word.add p_addr bytes_written) buf * R) m' /\ lan9250_recv _ recv ioh /\
            word.unsigned bytes_written + Z.of_nat (length buf) = 1520%Z /\
            Z.of_nat (length recv) = word.unsigned bytes_written)
          (word.unsigned err <> 0 /\ exists buf, (array scalar8 (word.of_Z 1) p_addr buf * R) m' /\ length buf = 1520%nat /\ (
             word.unsigned err = 1 /\ lan9250_recv_no_packet _ ioh \/
             word.unsigned err = 2 /\ lan9250_recv_packet_too_long _ ioh \/
             word.unsigned err = 2^32-1 /\ TracePredicate.concat TracePredicate.any (spi_timeout word) ioh
            ))
        ).

  Instance spec_of_lightbulb : spec_of "lightbulb_handle" := fun functions =>
    forall p_addr (buf:list byte) (len:word) R m t,
      (array scalar8 (word.of_Z 1) p_addr buf * R) m ->
      word.unsigned len = Z.of_nat (List.length buf) ->
      WeakestPrecondition.call functions "lightbulb_handle" t m [p_addr; len]
        (fun t' m' rets => exists v, rets = [v] /\ m' = m /\
        exists iol, t' = iol ++ t /\
        exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
          (exists cmd, lightbulb_packet_rep _ cmd buf /\ gpio_set _ 23 cmd ioh /\ word.unsigned v = 0)
          (not (exists cmd, lightbulb_packet_rep _ cmd buf) /\ ioh = nil /\ word.unsigned v <> 0)
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
          (exists packet cmd, (lan9250_recv _ packet +++ gpio_set _ 23 cmd) ioh /\ lightbulb_packet_rep _ cmd packet /\ word.unsigned v = 0) \/
          (exists packet, (lan9250_recv _ packet) ioh /\ not (exists cmd, lightbulb_packet_rep _ cmd packet) /\ word.unsigned v = 0) \/
          (lan9250_recv_no_packet _ ioh /\ word.unsigned v = 0) \/
          (lan9250_recv_packet_too_long _ ioh /\ word.unsigned v <> 0) \/
          ((TracePredicate.any +++ (spi_timeout word)) ioh /\ word.unsigned v <> 0)
        )).

  Instance spec_of_lightbulb_init : spec_of "lightbulb_init" := fun functions =>
    forall m t,
      WeakestPrecondition.call functions "lightbulb_init" t m nil
        (fun t' m' rets => rets = [] /\ m' = m /\
          exists iol, t' = iol ++ t /\
          exists ioh, mmio_trace_abstraction_relation ioh iol /\
          BootSeq _ ioh
        ).

  Require Import bedrock2.AbsintWordToZ.
  Import WeakestPreconditionProperties.

  Local Ltac seplog_use_array_load1 H i :=
    let iNat := eval cbv in (Z.to_nat i) in
    let H0 := fresh in pose proof H as H0;
    unshelve SeparationLogic.seprewrite_in @array_index_nat_inbounds H0;
      [exact iNat|exact Byte.x00|blia|];
    replace ((word.unsigned (word.of_Z 1) * Z.of_nat iNat)%Z) with i in * by (rewrite word.unsigned_of_Z; exact eq_refl).
  Local Ltac trans_ltu :=
    match goal with
    | H : word.unsigned ?v <> 0 |- _ =>
        let v := rdelta.rdelta v in
        let __ := lazymatch v with if word.ltu _ _ then word.of_Z 1 else word.of_Z 0 => I end in
        eapply Properties.word.if_nonzero in H; rewrite word.unsigned_ltu in H; eapply Z.ltb_lt in H
    | H : word.unsigned ?v = 0 |- _ =>
        let v := rdelta.rdelta v in
        let __ := lazymatch v with if word.ltu _ _ then word.of_Z 1 else word.of_Z 0 => I end in
        eapply Word.Properties.word.if_zero in H; rewrite word.unsigned_ltu in H; eapply Z.ltb_nlt in H
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
      rewrite !word.unsigned_of_Z; split; trivial.
      cbv -[Z.le Z.lt]. blia. }
    1: repeat straightline; split; trivial.

    1: repeat (eauto || straightline || split_if || eapply interact_nomem || trans_ltu).

    1: letexists; letexists; split; [exact eq_refl|]; split; [split; trivial|].
    { subst addr0 val0; cbv [isMMIOAddr];
      rewrite !word.unsigned_of_Z; split; trivial.
      cbv -[Z.le Z.lt]. blia. }
    1: repeat straightline; split; trivial.

    1: repeat (eauto || straightline || split_if || eapply interact_nomem || trans_ltu).

    straightline_call; repeat straightline.
    eexists; split; trivial.

    eexists; split.
    1: repeat (eapply align_trace_cons || exact (eq_sym (List.app_nil_l _)) || eapply align_trace_app).

    eexists; split; cbv [mmio_trace_abstraction_relation].
    1:repeat (eapply List.Forall2_cons || eapply List.Forall2_refl || eapply List.Forall2_app; eauto).
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
          || straightline || straightline_call || split_if || ecancel_assumption || eauto || blia).
    all : eexists; split; [solve[eauto]|].
    all : split; [shelve|].
    all : eexists; split.
    all: repeat (eapply align_trace_cons || exact (eq_sym (List.app_nil_l _)) || eapply align_trace_app).
    all : eexists; split.
    all : try subst err; rewrite ?word.unsigned_of_Z.
    all : repeat (eapply List.Forall2_cons || eapply List.Forall2_refl || eapply List.Forall2_app || eauto 15 using concat_app).
    { subst v. rewrite word.unsigned_xor_nowrap, H10, word.unsigned_of_Z in H4. case (H4 eq_refl). }
    { subst v. rewrite word.unsigned_xor_nowrap, H9, word.unsigned_of_Z in H4. inversion H4. }
    { subst v. rewrite word.unsigned_xor_nowrap, H9, word.unsigned_of_Z in H4. inversion H4. }

    Unshelve.
    all : eexists; split; [ eauto | ].
    all : try seprewrite_in @bytearray_index_merge H6; eauto.
    all : try rewrite List.app_length.
    all : try blia.
  Qed.

  Local Ltac prove_ext_spec :=
    lazymatch goal with
    | |- ext_spec _ _ _ _ _ => split; [shelve|]; split; [trivial|]
    end.

  Local Ltac zify_unsigned :=
    repeat match goal with
    | |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H; pose proof H
    | G : context[word.unsigned ?e] |- _ => let H := unsigned.zify_expr e in rewrite H in G; pose proof H
    end;
    repeat match goal with H:absint_eq ?x ?x |- _ => clear H end;
    repeat match goal with H:?A |- _ => clear H; match goal with G:A |- _ => idtac end end.

  Lemma byte_mask_byte (b : byte) : word.and (word.of_Z (byte.unsigned b)) (word.of_Z 255) = word.of_Z (byte.unsigned b) :> word.
  Proof.
    eapply word.unsigned_inj; rewrite word.unsigned_and_nowrap.
    rewrite !word.unsigned_of_Z.
    pose proof byte.unsigned_range b.
    cbv [word.wrap].
    rewrite <-!(Z.land_ones _ 32) by (cbv; congruence).
    rewrite <-byte.wrap_unsigned at 2. cbv [byte.wrap].
    change (Z.land 255 (Z.ones 32)) with (Z.ones 8).
    rewrite <-Z.land_ones by blia.
    Z.bitwise. Btauto.btauto.
  Qed.

  Lemma lightbulb_handle_ok : program_logic_goal_for_function! lightbulb_handle.
  Proof.
    repeat (eauto || straightline || split_if || eapply interact_nomem || prove_ext_spec || trans_ltu).
    all : subst r; try subst r0; replace (word.unsigned (word.of_Z 42)) with 42 in *.
    2,4: rewrite word.unsigned_of_Z; exact eq_refl.

    2: { eexists; split; [solve[eauto]|].
      split; [solve[eauto]|].
      eexists nil; split; eauto.
      eexists nil; split; cbv [mmio_trace_abstraction_relation]; eauto using List.Forall2_refl.
      right; repeat split; eauto.
      { intros (?&?&?). blia. }
      intros HX; rewrite ?word.unsigned_of_Z in HX; inversion HX. }

    seplog_use_array_load1 H 12.
    seplog_use_array_load1 H 13.
    seplog_use_array_load1 H 23.
    seplog_use_array_load1 H 42.
    unshelve (repeat (eauto || straightline || split_if || eapply interact_nomem || prove_ext_spec)).

    1: letexists; split; [exact eq_refl|]; split; [split; trivial|].
    { subst addr r; cbv [isMMIOAddr];
      rewrite !word.unsigned_of_Z; split; trivial.
      cbv -[Z.le Z.lt]. blia. }
    1: repeat straightline; split; trivial.
    1: repeat straightline; eapply interact_nomem; repeat straightline.
    1: letexists; letexists; split; [exact eq_refl|]; split; [split; trivial|].
    { subst addr r; cbv [isMMIOAddr];
      rewrite !word.unsigned_of_Z; split; trivial.
      cbv -[Z.le Z.lt]. blia. }
    1: repeat straightline; split; trivial.

    1: repeat (eauto || straightline || split_if || eapply interact_nomem || prove_ext_spec || trans_ltu).

    all : eexists; split; [solve[eauto]|].
    all : split; [solve[eauto]|].
    all : eexists; split.
    all: repeat (eapply align_trace_cons || exact (eq_sym (List.app_nil_l _))).
    all : eexists; split.

    all : repeat (eapply List.Forall2_cons || eapply List.Forall2_refl).
    all :
    try match goal with
    |- mmio_event_abstraction_relation _ _ =>
        (left+right); eexists _, _; split; exact eq_refl
    end.

    all : repeat trans_ltu;
    repeat match goal with
    | H : word.unsigned ?v <> 0 |- _ =>
        let v := rdelta.rdelta v in
        let __ := lazymatch v with if word.eqb _ _ then word.of_Z 1 else word.of_Z 0 => I end in
        eapply Properties.word.if_nonzero in H; eapply word.eqb_true in H
    | H : word.unsigned ?v = 0 |- _ =>
        let v := rdelta.rdelta v in
        let __ := lazymatch v with if word.eqb _ _ then word.of_Z 1 else word.of_Z 0 => I end in
        eapply Word.Properties.word.if_zero in H; eapply word.eqb_false in H
    end;
    repeat match goal with x := _ |- _ => subst x end;
    repeat match goal with H : _ |- _ => rewrite !byte_mask_byte in H end.
    all : repeat straightline.

    1: {
      left.
      eexists; repeat split.
      all : rewrite ?word.unsigned_of_Z in H6.
      all : try eassumption.
      1: blia.
      2: eapply word.unsigned_of_Z.
      cbv [gpio_set one existsl concat].
      eexists _, ([_]), ([_]); repeat split; repeat f_equal.
      eapply word.unsigned_inj.
      rewrite ?byte_mask_byte.
      rewrite ?word.unsigned_and_nowrap.
      rewrite word.unsigned_of_Z_1.
      change 1 with (Z.ones 1).
      rewrite Z.land_ones, Z.bit0_mod by blia.
      rewrite !word.unsigned_of_Z.
      cbv [word.wrap].
      rewrite 2(Z.mod_small _ (2^32)); try exact eq_refl.
      1: match goal with |- 0 <= byte.unsigned ?x < _ => pose proof byte.unsigned_range x end; blia.
      clear; Z.div_mod_to_equations; blia. }

    (* parse failures *)
    all : right; repeat split; eauto.
    2,4: rewrite word.unsigned_of_Z; intro X; inversion X.
    all : intros (?&?&?&?&?).
    { rewrite word.unsigned_of_Z in H6; contradiction. }
    { apply H6. rewrite word.unsigned_of_Z. exact H8. }

    Unshelve.
    all : intros; exact True.
  Qed.

  Add Ring wring : (Properties.word.ring_theory (word := word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := word)),
         constants [Properties.word_cst]).

  Require Import bedrock2.ZnWords.
  Require Import bedrock2.SepAutoArray bedrock2.SepCalls.

  Lemma recvEthernet_ok : program_logic_goal_for_function! recvEthernet.
  Proof.
    straightline.
    rename H into Hcall; clear H0 H1. rename H2 into H. rename H3 into H0.
    repeat (straightline || split_if || straightline_call || eauto 99 || prove_ext_spec || ZnWords).

    3: {

    refine (Loops.tailrec_earlyout
      (HList.polymorphic_list.cons (list byte) (HList.polymorphic_list.cons (mem -> Prop) HList.polymorphic_list.nil))
      ["buf";"num_bytes";"i";"read";"err"]
      (fun v scratch R t m buf num_bytes_loop i read err => PrimitivePair.pair.mk (
        word.unsigned err = 0 /\ word.unsigned i <= word.unsigned num_bytes /\
        v = word.unsigned i /\ (bytes (word.add buf i) scratch * R) m /\
        List.length scratch = Z.to_nat (word.unsigned (word.sub num_bytes i)) /\
        word.unsigned i mod 4 = word.unsigned num_bytes mod 4 /\
        num_bytes_loop = num_bytes)
      (fun T M BUF NUM_BYTES I READ ERR =>
         NUM_BYTES = num_bytes_loop /\
         exists RECV, (bytes (word.add buf i) RECV * R) M /\
         List.length RECV = List.length scratch /\
         exists iol, T = iol ++ t /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\
         (word.unsigned ERR = 0 /\ lan9250_readpacket _ RECV ioh \/
          word.unsigned ERR = 2^32-1 /\ TracePredicate.concat TracePredicate.any (spi_timeout _) ioh ) )
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
    { exact (Z.gt_wf (word.unsigned num_bytes)). }

    {
      repeat (split; [trivial||ZnWords|]).
      replace (word.add p_addr i) with p_addr by (subst i; ring).
      progress trans_ltu.

      scancel_asm.
      Tactics.ssplit.
      all : trivial; try listZnWords.
    }

      { straightline_call; repeat straightline.
        { rewrite word.unsigned_of_Z. cbv; clear. intuition congruence. }
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
          { subst br0. rewrite word.unsigned_ltu, Z.ltb_irrefl, word.unsigned_of_Z; exact eq_refl. }
          split; eauto.
          eexists; split; eauto.
          split; eauto.
          eexists; split.
          { subst a; eauto. }
          eexists; split; eauto.
          right; split.
          { subst err. rewrite word.unsigned_of_Z. exact eq_refl. }
          intuition eauto. }

        (* store *)
        do 4 straightline.
        trans_ltu.
        match goal with
          | H: context[word.unsigned (word.sub ?a ?b)] |- _ =>
              pose proof Properties.word.unsigned_range a;
              pose proof Properties.word.unsigned_range b;
              let H := fresh in
              pose proof word.unsigned_sub a b as H;
              unfold word.wrap in H;
              rewrite Z.mod_small in H by blia
        end.
        match goal with H10 : _ ?a0 |- store _ ?a0 _ _ _ => rewrite <- (List.firstn_skipn 4 _) in H10;
          SeparationLogic.seprewrite_in (symmetry! @bytearray_index_merge) H10 end.
        { instantiate (1:= word.of_Z 4).
          rewrite word.unsigned_of_Z.
          rewrite List.length_firstn_inbounds; [exact eq_refl|]. Z.div_mod_to_equations. blia. }
        do 2 straightline.
        match goal with H12:_|-_ => seprewrite_in @scalar32_of_bytes H12 end.
        { eapply List.length_firstn_inbounds; Z.div_mod_to_equations; blia. }
        straightline.
        (* after store *)
        do 3 straightline.
        (* TODO straightline hangs in Loops.enforce *)
        do 5 letexists. split. { repeat straightline. }
        right. do 3 letexists.
        repeat split; repeat straightline; repeat split.
        { intuition idtac. }
        { subst i.
          rewrite word.unsigned_add; cbv [word.wrap]; rewrite Z.mod_small;
          replace (word.unsigned (word.of_Z 4)) with 4.
          2,4: rewrite word.unsigned_of_Z; exact eq_refl.
          1,2: try (Z.div_mod_to_equations; blia). }
        { replace (word.add x9 i)
            with (word.add (word.add x9 x11) (word.of_Z 4)) by (subst i; ring).
          ecancel_assumption. }
        { match goal with x1 := _ |- _ => subst x1; rewrite List.length_skipn end.
          ZnWords. }
        { ZnWords. }
        { ZnWords. }
        { ZnWords. }

        { letexists; repeat split.
          { repeat match goal with x := _ |- _ => is_var x; subst x end; subst.
            cbv [scalar32 truncated_word truncate_word truncate_Z truncated_scalar littleendian ptsto_bytes.ptsto_bytes] in *.
            progress replace (word.add x9 (word.add x11 (word.of_Z 4))) with
                    (word.add (word.add x9 x11) (word.of_Z 4)) in * by ring.
            SeparationLogic.seprewrite_in (@bytearray_index_merge) H25.
            { rewrite word.unsigned_of_Z; exact eq_refl. } { ecancel_assumption. } }
          { subst RECV. rewrite List.app_length.
            rewrite H26. subst x22. rewrite List.length_skipn.
            unshelve erewrite (_ : length (HList.tuple.to_list _) = 4%nat); [exact eq_refl|].
            enough ((4 <= length x7)%nat) by blia.
            Z.div_mod_to_equations; blia. }
          cbv [truncate_word truncate_Z] in *.
          repeat match goal with x := _ |- _ => is_var x; subst x end; subst.
          eexists; split.
          { rewrite List.app_assoc; eauto. }
          eexists; split.
          { eapply List.Forall2_app; eauto.  }
          rewrite HList.tuple.to_list_of_list.
          destruct H29; [left|right]; repeat (straightline || split || eauto using TracePredicate.any_app_more).
          eapply TracePredicate.concat_app; eauto.
          unshelve erewrite (_ : LittleEndianList.le_combine _ = word.unsigned x10); rewrite ?word.of_Z_unsigned; try solve [intuition idtac].
          {
            etransitivity.
            1: eapply (LittleEndianList.le_combine_split 4).
            eapply Properties.word.wrap_unsigned. } } }

      { split; eauto. eexists; split; eauto. split; eauto. exists nil; split; eauto.
        eexists; split; [constructor|].
        left. split; eauto.
        enough (Hlen : length x7 = 0%nat) by (destruct x7; try solve[inversion Hlen]; exact eq_refl).
        PreOmega.zify.
        rewrite H13.
        subst br.
        rewrite word.unsigned_ltu in H11.
        destruct (Z.ltb (word.unsigned x11) (word.unsigned num_bytes)) eqn:HJ.
        { rewrite word.unsigned_of_Z in H11. inversion H11. }
        eapply Z.ltb_nlt in HJ.
        ZnWords. }
      repeat straightline.
      repeat letexists. split. { repeat straightline. }
      eexists _, _. split. { exact eq_refl. }

      repeat straightline.
      subst i.
      match goal with H: _ |- _ =>
        progress repeat (unshelve erewrite (_ : forall x, word.add x (word.of_Z 0) = x) in H; [intros; ring|]);
        progress repeat (unshelve erewrite (_ : forall x, word.sub x (word.of_Z 0) = x) in H; [intros; ring|])
      end.
      eexists; split.
      1: { repeat match goal with |- context [?x] => match type of x with list _ => subst x end end.
        repeat rewrite List.app_assoc. f_equal. }
      eexists; split.
      1:repeat eapply List.Forall2_app; eauto.
      destruct H14; [left|right]; repeat straightline; repeat split; eauto.
      { trans_ltu.
        Import eplace.
        eplace (word.add p_addr _) with (word.add p_addr num_bytes) in * by ZnWords.
        eplace (Z.to_nat (word.unsigned (word.sub p_addr p_addr) / 1)) with O in * by ZnWords.
        cbn [List.firstn array] in *.
        replace (word.unsigned (word.of_Z 1521)) with 1521 in *
          by (rewrite word.unsigned_of_Z; exact eq_refl).
          eexists _, _; repeat split.
        { cbn [seps] in *. SeparationLogic.ecancel_assumption. }
        { revert dependent x2. revert dependent x6. intros.
          destruct H5; repeat straightline; try contradiction.
          destruct H9; repeat straightline; try contradiction.
          eexists _, _; split.
          { rewrite <-!List.app_assoc. eauto using TracePredicate.concat_app. }
          split; [zify_unsigned; eauto|].
        { cbv beta delta [lan9250_decode_length].
          rewrite H11. rewrite List.firstn_length, Znat.Nat2Z.inj_min.
          replace (word.sub num_bytes (word.of_Z 0)) with num_bytes by ring; cbn [List.skipn].
          rewrite ?Znat.Z2Nat.id by eapply word.unsigned_range.
          transitivity (word.unsigned num_bytes); [ZnWords|exact eq_refl]. } }
        { pose proof word.unsigned_range num_bytes.
          rewrite List.length_skipn. blia. }
        rewrite H11, List.length_firstn_inbounds, ?Znat.Z2Nat.id; cbn [List.skipn].
        all: try ZnWords.
        }
      { repeat match goal with H : _ |- _ => rewrite H; intro HX; solve[inversion HX] end. }
      { trans_ltu;
        replace (word.unsigned (word.of_Z 1521)) with 1521 in * by
          (rewrite word.unsigned_of_Z; exact eq_refl).
        replace (Z.to_nat (word.unsigned (word.sub p_addr p_addr) / 1)) with O in * by ZnWords.
        all : cbn [seps array List.firstn List.skipn] in *.
        eexists _; split; eauto; repeat split; try blia.
        { SeparationLogic.seprewrite_in @bytearray_index_merge H10.
          { rewrite H11, List.firstn_length. ZnWords. }
          eassumption. }
        { 1:rewrite List.app_length, List.length_skipn, H11, List.firstn_length.
          replace (word.sub num_bytes (word.of_Z 0)) with num_bytes by ring.
          enough (Z.to_nat (word.unsigned num_bytes) <= length buf)%nat by ZnWords.
          rewrite ?Znat.Z2Nat.id by eapply word.unsigned_range; blia. }
        right. right. split; eauto using TracePredicate.any_app_more. } }

    all: repeat letexists; split; repeat straightline;
      eexists _, _; split; [ exact eq_refl | ].
    all: eexists; split;
      [repeat match goal with |- context [?x] => match type of x with list _ => subst x end end;
      rewrite ?List.app_assoc; eauto|].
    all: eexists; split;
      [repeat eapply List.Forall2_app; eauto|].
    all:
      right; subst err;
      split; [intro HX; rewrite word.unsigned_of_Z in HX; inversion HX|].
    all : repeat ((eexists; split; [solve[eauto]|]) || (split; [solve[eauto]|])).
    all : rewrite !word.unsigned_of_Z.

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
      rewrite word.unsigned_ltu in H6.

      destruct (Z.ltb (word.unsigned num_bytes) (word.unsigned (word.of_Z 1521))) eqn:?.
      all : rewrite word.unsigned_of_Z in Heqb, H6; try inversion H6.
      eapply Z.ltb_nlt in Heqb; revert Heqb.
      repeat match goal with |- context [?x] => match type of x with _ => subst x end end.
      cbv [lan9250_decode_length]. split. 2: cbn in *; blia.
      subst v. rewrite word.unsigned_and_nowrap, word.unsigned_of_Z in H2. eapply H2. }
    { left.
      split; [exact eq_refl|].
      eexists; split; intuition eauto. }
  Defined.

  Import SPI.

  Definition function_impls :=
    [lightbulb_init; lan9250_init; lan9250_wait_for_boot; lan9250_mac_write;
    lightbulb_loop; lightbulb_handle; recvEthernet;  lan9250_writeword; lan9250_readword;
    spi_xchg; spi_write; spi_read].

  Lemma link_lightbulb_loop : spec_of_lightbulb_loop function_impls.
  Proof.
    eapply lightbulb_loop_ok;
    (eapply recvEthernet_ok || eapply lightbulb_handle_ok);
        eapply lan9250_readword_ok; eapply spi_xchg_ok;
        (eapply spi_write_ok || eapply spi_read_ok).
  Qed.
  Lemma link_lightbulb_init : spec_of_lightbulb_init function_impls.
  Proof.
    eapply lightbulb_init_ok; eapply lan9250_init_ok;
    try (eapply lan9250_wait_for_boot_ok || eapply lan9250_mac_write_ok);
    (eapply lan9250_readword_ok || eapply lan9250_writeword_ok);
        eapply spi_xchg_ok;
        (eapply spi_write_ok || eapply spi_read_ok).
  Qed.


  (* Print Assumptions link_lightbulb. *)

  From bedrock2 Require Import ToCString.
  Goal True.
    let c_code := eval cbv in ((* of_string *) (c_module function_impls)) in
    pose c_code.
  Abort.

  (*
  From bedrock2 Require Import ToCString Byte Bytedump.
  Local Open Scope bytedump_scope.
  Set Printing Width 999999.
  Goal True.
    let c_code := eval cbv in (of_string (c_module [lan9250_init; lan9250_wait_for_boot; lightbulb_loop; lightbulb_handle; recvEthernet; lan9250_mac_write; lan9250_writeword; lan9250_readword; SPI.spi_xchg; SPI.spi_read; SPI.spi_write])) in
    idtac c_code.
  Abort.
  *)
End WithParameters.
