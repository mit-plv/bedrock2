Require Import coqutil.Z.Lia.
Require Import bedrock2.Syntax bedrock2.StringNamesSyntax.
Require Import bedrock2.NotationsCustomEntry coqutil.Z.HexNotation.
Require Import bedrock2.FE310CSemantics. (* TODO for andres: [literal] shouldn't need this *)
Require Import coqutil.Macros.symmetry.
Require Import bedrock2.Examples.SPI.
Require Import bedrock2.Examples.LAN9250.
From coqutil Require Import Z.div_mod_to_equations.
From coqutil Require Import Word.Interface Map.Interface.
From coqutil.Tactics Require Import letexists eabstract.
From bedrock2 Require Import FE310CSemantics Semantics WeakestPrecondition ProgramLogic Array Scalars.
From bedrock2.Map Require Import Separation SeparationLogic.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion literal (z : Z) : expr := expr.literal z.
Local Coercion var (x : String.string) : expr := expr.var x.
Local Coercion name_of_func (f : BasicCSyntax.function) := fst f.

(* TODO: refactor *)
Lemma word__unsigned_of_Z_nowrap x : 0 <= x < 2 ^ width -> word.unsigned (word.of_Z x) = x.
Proof.
  intros. rewrite word.unsigned_of_Z. unfold word.wrap. rewrite Z.mod_small; trivial.
Qed.
Local Ltac seplog_use_array_load1 H i :=
  let iNat := eval cbv in (Z.to_nat i) in
  let H0 := fresh in pose proof H as H0;
  unshelve SeparationLogic.seprewrite_in @array_index_nat_inbounds H0;
    [exact iNat|exact (word.of_Z 0)|blia|];
  change ((word.unsigned (word.of_Z 1) * Z.of_nat iNat)%Z) with i in *.
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


Definition main: cmd :=
  let iot : varname := "iot" in
  let r : varname := "r" in
  bedrock_func_body:(
    while (constr:(1)) {
      unpack! r = iot(constr:(1234))
    }
  ).

Definition iot :=
    let p_addr : varname := "p_addr" in
    let bytesWritten : varname := "bytesWritten" in
    let recvEthernet : varname := "recvEthernet" in
    let lightbulb : varname := "lightbulb" in
    let err : varname := "err" in

  ("iot", ((p_addr::nil), (err::nil), bedrock_func_body:(
    unpack! bytesWritten, err = recvEthernet(p_addr);
    if !err { (* success, packet *)
      unpack! err = lightbulb(p_addr, bytesWritten);
      err = (constr:(0)) (* bad packet continue anyway *)
    } else if !(err ^ constr:(1)) { (* success, no packet *)
      err = (constr:(0))
    }
  ))).

Definition recvEthernet :=
    let buf : varname := "buf" in
    let num_bytes : varname := "num_bytes" in
    let i : varname := "i" in
    let err : varname := "err" in
    let read : varname := "read" in

    ("recvEthernet", ((buf::nil), (num_bytes::err::nil), bedrock_func_body:(
        num_bytes = (constr:(0));
        unpack! read, err = lan9250_readword(constr:(Ox"7C")); (* RX_FIFO_INF *)
        require !err else { err = (constr:(-1)) };
        require (read & constr:((2^8-1)*2^16)) else { err = (constr:(1)) }; (* nonempty *)
        unpack! read, err = lan9250_readword(constr:(Ox"40")); (* RX_STATUS_FIFO_PORT *)
        require !err else { err = (constr:(-1)) };

        num_bytes = (read >> constr:(16) & constr:(2^14-1));
        (* round up to next word *)
        num_bytes = ((num_bytes + constr:(4-1)) >> constr:(2));
        num_bytes = (num_bytes + num_bytes);
        num_bytes = (num_bytes + num_bytes);

        require (num_bytes < constr:(1520 + 1)) else { err = (constr:(2)) };

        i = (constr:(0)); while (i < num_bytes) {
            unpack! read, err = lan9250_readword(constr:(0));
            if err { err = (constr:(-1)); i = (num_bytes) }
            else { store4(buf + i, read); i = (i + constr:(4)) }
        }
    ))).

Definition lightbulb :=
    let packet : varname := "packet" in
    let len : varname := "len" in
    let ethertype : varname := "ethertype" in
    let protocol : varname := "protocol" in
    let port : varname := "port" in
    let mmio_val : varname := "mmio_val" in
    let command : varname := "command" in
    let MMIOREAD : varname := "MMIOREAD" in
    let MMIOWRITE : varname := "MMIOWRITE" in
    let r : varname := "r" in

  ("lightbulb", ((packet::len::nil), (r::nil), bedrock_func_body:(
    r = (constr:(42));
    require (r < len) else { r = (constr:(-1)) };

    ethertype = ((load1(packet + constr:(12)) << constr:(8)) | (load1(packet + constr:(13))));
    r = (constr:(1536 - 1));
    require (r < ethertype) else { r = (constr:(-1)) };

    r = (constr:(23));
    r = (packet + r);
    protocol = (load1(r));
    r = (constr:(Ox"11"));
    require (protocol == r) else { r = (constr:(-1)) };

    r = (constr:(42));
    r = (packet + r);
    command = (load1(r));
    command = (command&constr:(1));

    (* pin output enable -- TODO do this in init
    io! mmio_val = MMIOREAD(constr:(Ox"10012008"));
    output! MMIOWRITE(constr:(Ox"10012008"), mmio_val | constr:(2^23));
    *)

    r = (constr:(Ox"1001200c"));
    io! mmio_val = MMIOREAD(r);
    mmio_val = (mmio_val & constr:(Z.clearbit (2^32-1) 23));
    output! MMIOWRITE(r, mmio_val | command << constr:(23));

    r = (constr:(0))
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
          exists recv buf, (bytes p_addr recv * bytes (word.add p_addr bytes_written) buf * R) m' /\ lan9250_recv _ _ recv ioh /\
          word.unsigned bytes_written + Z.of_nat (length buf) = 1520%Z /\
          Z.of_nat (length recv) = word.unsigned bytes_written)
        (word.unsigned err <> 0 /\ exists buf, (array scalar8 (word.of_Z 1) p_addr buf * R) m' /\ length buf = 1520%nat /\ (
           word.unsigned err = 1 /\ lan9250_recv_no_packet _ _ ioh \/
           word.unsigned err = 2 /\ lan9250_recv_packet_too_long _ _ ioh \/
           word.unsigned err = 2^32-1 /\ TracePredicate.concat TracePredicate.any (spi_timeout word) ioh
          ))
      ).

Definition lightbulb_packet_rep cmd (buf : list byte) :=
  let idx i buf := word.of_Z (word.unsigned (List.hd (word.of_Z 0) (List.skipn i buf))) in
  42 < Z.of_nat (length buf) /\
  1535 < word.unsigned ((word.or (word.slu (idx 12%nat buf) (word.of_Z 8)) (idx 13%nat buf))) /\
  idx 23%nat buf = word.of_Z (Ox"11") /\
  cmd = Z.testbit (word.unsigned (List.hd (word.of_Z 0) (List.skipn 42 buf))) 0.

Instance spec_of_lightbulb : spec_of "lightbulb" := fun functions =>
  forall p_addr (buf:list byte) (len:word) R m t,
    (array scalar8 (word.of_Z 1) p_addr buf * R) m ->
    word.unsigned len = Z.of_nat (List.length buf) ->
    WeakestPrecondition.call functions "lightbulb" t m [p_addr; len]
      (fun t' m' rets => exists v, rets = [v] /\ m' = m /\ 
      exists iol, t' = iol ++ t /\
      exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
        (exists cmd, lightbulb_packet_rep cmd buf /\ gpio_set _ 23 cmd ioh /\ word.unsigned v = 0)
        (not (exists cmd, lightbulb_packet_rep cmd buf) /\ ioh = nil /\ word.unsigned v <> 0)
      ).

Instance spec_of_iot : spec_of "iot" := fun functions =>
  forall p_addr buf R m t,
    (bytes p_addr buf * R) m ->
    Z.of_nat (length buf) = 1520 ->
    WeakestPrecondition.call functions "iot" t m [p_addr]
      (fun t' m' rets => exists v, rets = [v] /\
      exists iol, t' = iol ++ t /\
      exists ioh, mmio_trace_abstraction_relation ioh iol /\ (
        (exists packet cmd, (lan9250_recv _ _ packet +++ gpio_set _ 23 cmd) ioh /\ lightbulb_packet_rep cmd packet /\ word.unsigned v = 0) \/
        (exists packet, (lan9250_recv _ _ packet) ioh /\ not (exists cmd, lightbulb_packet_rep cmd packet) /\ word.unsigned v = 0) \/
        (lan9250_recv_no_packet _ _ ioh /\ word.unsigned v = 0) \/
        (lan9250_recv_packet_too_long _ _ ioh /\ word.unsigned v <> 0) \/
        ((TracePredicate.any +++ (spi_timeout word)) ioh /\ word.unsigned v <> 0)
      )).

Require Import bedrock2.AbsintWordToZ.
Import WeakestPreconditionProperties.

Lemma align_trace_cons {T} x xs cont t (H : xs = cont ++ t) : @cons T x xs = (cons x cont) ++ t.
Proof. intros. cbn. congruence. Qed.
Lemma align_trace_app {T} x xs cont t (H : xs = cont ++ t) : @app T x xs = (app x cont) ++ t.
Proof. intros. cbn. subst. rewrite List.app_assoc; trivial. Qed.

Lemma iot_ok : program_logic_goal_for_function! iot.
Proof.
  repeat (match goal with H : or _ _ |- _ => destruct H; intuition idtac end
        || straightline || straightline_call || split_if || ecancel_assumption || eauto || blia).
  all : eexists; split; [solve[eauto]|].
  all : eexists; split.
  all: repeat (eapply align_trace_cons || exact (eq_sym (List.app_nil_l _)) || eapply align_trace_app).
  all : eexists; split.
  all : repeat (eapply List.Forall2_cons || eapply List.Forall2_refl || eapply List.Forall2_app || eauto 15 using concat_app).

  { subst v. rewrite word.unsigned_xor_nowrap, H10 in H4. case (H4 eq_refl). }
  { subst v. rewrite word.unsigned_xor_nowrap, H9 in H4. inversion H4. }
  { subst v. rewrite word.unsigned_xor_nowrap, H9 in H4. inversion H4. }
Qed.

Local Ltac prove_ext_spec :=
  lazymatch goal with
  | |- ext_spec _ _ _ _ _ => split; [cbv; clear; firstorder congruence|]; split; [trivial|]
  end.

Local Ltac zify_unsigned :=
  repeat match goal with
  | |- context[word.unsigned ?e] => let H := unsigned.zify_expr e in rewrite H; pose proof H
  | G : context[word.unsigned ?e] |- _ => let H := unsigned.zify_expr e in rewrite H in G; pose proof H
  end;
  repeat match goal with H:absint_eq ?x ?x |- _ => clear H end;
  repeat match goal with H:?A |- _ => clear H; match goal with G:A |- _ => idtac end end.

Lemma lightbulb_ok : program_logic_goal_for_function! lightbulb.
Proof.
  repeat (eauto || straightline || split_if || eapply interact_nomem || prove_ext_spec || trans_ltu).
  all : subst r; try subst r0; change (word.unsigned (word.of_Z 42)) with 42 in *.

  2: { eexists; split; [solve[eauto]|].
    split; [solve[eauto]|].
    eexists nil; split; eauto.
    eexists nil; split; cbv [mmio_trace_abstraction_relation]; eauto using List.Forall2_refl.
    right; repeat split; eauto. 
    { intros (?&?&?). blia. }
    intros HX; inversion HX. }

  seplog_use_array_load1 H 12.
  seplog_use_array_load1 H 13.
  seplog_use_array_load1 H 23.
  seplog_use_array_load1 H 42.
  repeat (eauto || straightline || split_if || eapply interact_nomem || prove_ext_spec).

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
  repeat match goal with x := word.of_Z _ |- _ => subst x end.

  1: {
    left.
    eexists; repeat split.
    all : try eassumption.
    1: blia.
    cbv [gpio_set one existsl concat].
    eexists _, ([_]), ([_]); repeat split; repeat f_equal.
    subst command.
    eapply word.unsigned_inj.
    rewrite ?word.unsigned_and_nowrap.
    change (word.unsigned (word.of_Z 1)) with (Z.ones 1).
    rewrite Z.land_ones, Z.bit0_mod by blia.
    rewrite !word.unsigned_of_Z.
    cbv [word.wrap]; change width with 32 in *.
    rewrite 2(Z.mod_small _ (2^32)); try exact eq_refl.
    1: match goal with |- 0 <= word.unsigned ?x < _ => pose proof word.unsigned_range x end; blia.
    1: clear; Z.div_mod_to_equations; blia. }

  (* parse failures *)
  all : right; repeat split; eauto; try solve[intros HX; inversion HX]; intros (?&?&?&?&?).
  all : cbn in *; congruence.

  Unshelve.
  all : intros; exact True.
Qed.


Lemma recvEthernet_ok : program_logic_goal_for_function! recvEthernet.
Proof.
  straightline.
  rename H into Hcall; clear H0 H1. rename H2 into H. rename H3 into H0.
  repeat (straightline || split_if || straightline_call || eauto 99 || prove_ext_spec).
  1, 3: cbv - [Z.le Z.lt]; clear; blia.

  3: {

  refine (TailRecursion.tailrec_earlyout
    (HList.polymorphic_list.cons (list byte) (HList.polymorphic_list.cons (mem -> Prop) HList.polymorphic_list.nil))
    ["buf";"num_bytes";"i";"read";"err"]
    (fun v scratch R t m buf num_bytes_loop i read err => PrimitivePair.pair.mk (
      word.unsigned err = 0 /\
      word.unsigned i <= word.unsigned num_bytes /\
      v = word.unsigned i /\
      (bytes (word.add buf i) scratch * R) m /\
      Z.of_nat (List.length scratch) = word.unsigned (word.sub num_bytes i) /\
      word.unsigned i mod 4 = word.unsigned num_bytes mod 4 /\
      num_bytes_loop = num_bytes)
    (fun T M BUF NUM_BYTES I READ ERR =>
       NUM_BYTES = num_bytes_loop /\
       exists RECV,
       (bytes (word.add buf i) RECV * R) M /\
       List.length RECV = List.length scratch /\
       exists iol, T = iol ++ t /\
       exists ioh, mmio_trace_abstraction_relation ioh iol /\
       (word.unsigned ERR = 0 /\ lan9250_readpacket _ _ RECV ioh \/
        word.unsigned ERR = 2^32-1 /\ TracePredicate.concat TracePredicate.any (spi_timeout word) ioh ) )
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
    repeat (straightline || split_if || eapply interact_nomem || eauto 99).
  { exact (Z.gt_wf (word.unsigned num_bytes)). }
  1: repeat (refine (conj _ _)); eauto.
  { eapply Properties.word.unsigned_range. }
  1: zify_unsigned.
  1: replace (word.add p_addr i) with p_addr by (subst i; ring).
  1: rewrite <- (List.firstn_skipn (Z.to_nat (word.unsigned (word.sub num_bytes i) ) )  _) in H.
  1: SeparationLogic.seprewrite_in (symmetry! @bytearray_index_merge) H; [|ecancel_assumption].
    1,2,3:
    repeat match goal with
    | |- ?x = ?x => exact (eq_refl x)
    | _ => progress trans_ltu
    | _ => progress zify_unsigned
    | _ => progress rewrite ?Znat.Z2Nat.id by blia
    | H: _ |- _ => progress (rewrite ?Znat.Z2Nat.id in H by blia)
    | _ => rewrite List.length_firstn_inbounds by (PreOmega.zify; rewrite ?Znat.Z2Nat.id by blia; blia)
    | _ => progress rewrite ?Z.sub_0_r
    end; repeat straightline.
    { repeat match goal with x:= _ |- context[?x]  => subst x end. clear. Z.div_mod_to_equations. blia. }

    { straightline_call; repeat straightline.
      { cbv; clear; intuition congruence. }
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
        { subst br0. rewrite word.unsigned_ltu, Z.ltb_irrefl; exact eq_refl. }
        split; eauto.
        eexists; split; eauto.
        split; eauto.
        eexists; split.
        { subst a; eauto. }
        eexists; split; eauto.
        right; split.
        { exact eq_refl. }
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
      { instantiate (1:= word.of_Z 4). rewrite List.length_firstn_inbounds; [exact eq_refl|]. Z.div_mod_to_equations. blia. }
      eapply store_four_of_sep.
      { match goal with H8:_|-_ => seprewrite_in @scalar32_of_bytes H8; [..|ecancel_assumption]; try exact _; [] end.
        eapply List.length_firstn_inbounds; Z.div_mod_to_equations; blia. }

      (* after store *)
      do 5 straightline.
      (* TODO straightline hangs in TailRecursion.enforce *)
      do 5 letexists. split. { repeat straightline. }
      right. do 3 letexists.
      repeat split; repeat straightline; repeat split.
      { intuition idtac. }
      { subst i.
        rewrite word.unsigned_add; cbv [word.wrap]; rewrite Z.mod_small;
        change (word.unsigned (word.of_Z 4)) with 4; try (Z.div_mod_to_equations; blia). }
      { replace (word.add x9 i)
          with (word.add (word.add x9 x11) (word.of_Z 4)) by (subst i; ring).
        ecancel_assumption. }
      { repeat match goal with x1 := _ |- _ => subst x1; rewrite List.length_skipn; rewrite Znat.Nat2Z.inj_sub end.
        { repeat match goal with H5:_|-_=>rewrite H5 end; subst i.
          progress replace (word.sub num_bytes (word.add x11 (word.of_Z 4)))
            with (word.sub (word.sub num_bytes x11) (word.of_Z 4)) by ring.
          rewrite (word.unsigned_sub _ (word.of_Z 4)).
          unfold word.wrap. rewrite Z.mod_small.
          all: change (word.unsigned (word.of_Z 4)) with 4; change (Z.of_nat 4) with 4.
          all : Z.div_mod_to_equations; blia. }
        Z.div_mod_to_equations; blia. }
      { subst i.
        rewrite word.unsigned_add. unfold word.wrap. rewrite (Z.mod_small _ (2 ^ width)).
        { revert dependent x11. clear. change (word.unsigned (word.of_Z 4)) with 4. intros.
          Z.div_mod_to_equations. blia. }
        change (word.unsigned (word.of_Z 4)) with 4.
        Z.div_mod_to_equations.
        blia. }
      { repeat match goal with |- context [?x] => is_var x; subst x end.
        rewrite word.unsigned_add. unfold word.wrap. rewrite Z.mod_small.
        { change (word.unsigned (word.of_Z 4)) with 4. blia. }
        change (word.unsigned (word.of_Z 4)) with 4. Z.div_mod_to_equations. blia. }
      { subst v'. subst i.
        rewrite word.unsigned_add. change (word.unsigned (word.of_Z 4)) with 4.
        unfold word.wrap. rewrite (Z.mod_small _ (2 ^ width));
          change (2^width) with (2^32) in *; Z.div_mod_to_equations; blia. }

      { letexists; repeat split.
        { repeat match goal with x := _ |- _ => is_var x; subst x end; subst.
          cbv [scalar32 truncated_scalar littleendian ptsto_bytes.ptsto_bytes] in *.
          progress replace (word.add x9 (word.add x11 (word.of_Z 4))) with
                  (word.add (word.add x9 x11) (word.of_Z 4)) in * by ring.
          SeparationLogic.seprewrite_in (@bytearray_index_merge) H25.
          { exact eq_refl. } { ecancel_assumption. } }
        { subst RECV. rewrite List.app_length.
          rewrite H26. subst x22. rewrite List.length_skipn.
          unshelve erewrite (_ : length (HList.tuple.to_list _) = 4%nat); [exact eq_refl|].
          enough ((4 <= length x7)%nat) by blia.
          Z.div_mod_to_equations; blia. }
        repeat match goal with x := _ |- _ => is_var x; subst x end; subst.
        eexists; split.
        { rewrite List.app_assoc; eauto. }
        eexists; split.
        { eapply List.Forall2_app; eauto.  }
        destruct H29; [left|right]; repeat (straightline || split || eauto using TracePredicate__any_app_more).
        eapply TracePredicate.concat_app; eauto.
        unshelve erewrite (_ : LittleEndian.combine _ _ = word.unsigned x10); rewrite !word.of_Z_unsigned; try solve [intuition idtac].
        1: replace (word.unsigned x10) with (word.unsigned x10 mod 2^(Z.of_nat (bytes_per (width:=32) access_size.four)*8)).
        1:rewrite <-LittleEndian.combine_split; f_equal.
        eapply Properties.word.wrap_unsigned. } }

    { split; eauto. eexists; split; eauto. split; eauto. exists nil; split; eauto.
      eexists; split; [constructor|].
      left. split; eauto.
      enough (Hlen : length x7 = 0%nat) by (destruct x7; try solve[inversion Hlen]; exact eq_refl).
      PreOmega.zify.
      rewrite H13.
      subst br.
      rewrite word.unsigned_ltu in H11.
      destruct (word.unsigned x11 <? word.unsigned num_bytes) eqn:HJ; try solve [inversion H11].
      eapply Z.ltb_nlt in HJ.
      revert dependent x7; revert dependent num_bytes; revert dependent x11; clear; intros.
      unshelve erewrite (_:x11 = num_bytes) in *.
      { eapply Properties.word.unsigned_inj. Z.div_mod_to_equations; Lia.lia. }
      rewrite word.unsigned_sub, Z.sub_diag; exact eq_refl. }
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
    { trans_ltu; change (word.unsigned (word.of_Z 1521)) with 1521 in *; eexists _, _; repeat split.
      { SeparationLogic.ecancel_assumption. }
      { revert dependent x2. revert dependent x6. intros.
        destruct H5; repeat straightline; try contradiction.
        destruct H9; repeat straightline; try contradiction.
        eexists _, _; split.
        { rewrite <-!List.app_assoc. eauto using concat_app. }
        split; [zify_unsigned; eauto|].
      { cbv beta delta [lan9250_decode_length].
        rewrite H11. rewrite List.firstn_length, Znat.Nat2Z.inj_min.
        replace (word.sub num_bytes (word.of_Z 0)) with num_bytes by ring.
        rewrite ?Znat.Z2Nat.id by eapply word.unsigned_range.
        transitivity (word.unsigned num_bytes); [blia|exact eq_refl]. } }
      { pose proof word.unsigned_range num_bytes.
        rewrite length_skipn.
        PreOmega.zify. rewrite ?Znat.Z2Nat.id in * by blia; blia. }
      rewrite H11, length_firstn_inbounds, ?Znat.Z2Nat.id.
      all : try (zify_unsigned;
      try Lia.lia;
      eapply Znat.Nat2Z.inj_le;
      rewrite ?Znat.Z2Nat.id; Lia.lia).
      }
    { repeat match goal with H : _ |- _ => rewrite H; intro HX; solve[inversion HX] end. }
    { trans_ltu; change (word.unsigned (word.of_Z 1521)) with 1521 in *.
      eexists _; split; eauto; repeat split; try Lia.lia.
      { SeparationLogic.seprewrite_in @bytearray_index_merge H10.
        { rewrite H11.
          1: replace (word.sub num_bytes (word.of_Z 0)) with num_bytes by ring.
          rewrite List.length_firstn_inbounds, ?Znat.Z2Nat.id.
          1:exact eq_refl.
          1:eapply word.unsigned_range.
          PreOmega.zify.
          rewrite ?Znat.Z2Nat.id by eapply word.unsigned_range.
          blia. }
        eapply H15. }
      { 1:rewrite List.app_length, List.length_skipn, H11, List.firstn_length.
        replace (word.sub num_bytes (word.of_Z 0)) with num_bytes by ring.
        enough (Z.to_nat (word.unsigned num_bytes) <= length buf)%nat by blia.
        PreOmega.zify. rewrite ?Znat.Z2Nat.id by eapply word.unsigned_range; blia. }
      right. right. split; eauto using TracePredicate__any_app_more. } }


  all: repeat letexists; split; repeat straightline;
    eexists _, _; split; [ exact eq_refl | ].
  all: eexists; split;
    [repeat match goal with |- context [?x] => match type of x with list _ => subst x end end;
    rewrite ?List.app_assoc; eauto|].
  all: eexists; split;
    [repeat eapply List.Forall2_app; eauto|].
  all:
    right; subst err;
    split; [intro HX; inversion HX|].
  all : repeat ((eexists; split; [solve[eauto]|]) || (split; [solve[eauto]|])).

  (* two cases of SPI timeout *)
  { left; split; [exact eq_refl|] || right.
    left; split; [exact eq_refl|] || right.
          split; [exact eq_refl|].
      intuition eauto using TracePredicate__any_app_more. }
  { left; split; [exact eq_refl|] || right.
    left; split; [exact eq_refl|] || right.
          split; [exact eq_refl|].
      intuition eauto using TracePredicate__any_app_more. }
  { left; split; [exact eq_refl|] || right.
    left; split; [exact eq_refl|].
    eexists _, _; split.
    1:eapply TracePredicate.concat_app; try intuition eassumption.
    subst v0.
    rewrite word.unsigned_ltu in H6.
    destruct (word.unsigned num_bytes <? word.unsigned (word.of_Z 1521)) eqn:?; try inversion H6.
    eapply Z.ltb_nlt in Heqb; revert Heqb.
    repeat match goal with |- context [?x] => match type of x with _ => subst x end end.
    cbv [lan9250_decode_length]. split. 2: cbn in *; blia.
    subst v. rewrite word.unsigned_and_nowrap in H2. eapply H2. }
  { left.
    split; [exact eq_refl|].
    eexists; split; intuition eauto. }

  Unshelve.
  exact _.
Defined.

(*
Definition x := (iot_ok , lightbulb_ok , recvEthernet_ok , lan9250_readword_ok , spi_read_ok , spi_write_ok).
Print Assumptions x.
Axioms:, SortedListString.string_strict_order, TailRecursion.putmany_gather, parameters_ok FE310CSemantics.parameters, SortedList.TODO
*)

(*
From bedrock2 Require Import ToCString Byte Bytedump.
Local Open Scope bytedump_scope.
Goal True.
(* FIXME: name clashes between this file and lan9250_spec *)
  let c_code := eval cbv in (of_string (@c_module BasicCSyntax.to_c_parameters [iot; lightbulb; recvEthernet; lan9250_readword; spi_read; spi_write])) in
  idtac (* c_code *).
Abort.
*)
