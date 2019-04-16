Require Import coqutil.Z.Lia.
Require Import bedrock2.Syntax bedrock2.StringNamesSyntax.
Require Import bedrock2.NotationsCustomEntry coqutil.Z.HexNotation.
Require Import bedrock2.FE310CSemantics. (* TODO for andres: [literal] shouldn't need this *)

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion literal (z : Z) : expr := expr.literal z.
Local Coercion var (x : String.string) : expr := expr.var x.


Definition iot :=
    let p_addr : varname := "p_addr" in
    let bytesWritten : varname := "bytesWritten" in
    let recvEthernet : varname := "recvEthernet" in
    let lightbulb : varname := "lightbulb" in
    let r : varname := "r" in

  ("iot", ((p_addr::nil), (r::nil), bedrock_func_body:(
    unpack! bytesWritten = recvEthernet(p_addr);
    require (bytesWritten ^ constr:(-1)) else { r = (constr:(-1)) };
    unpack! r = lightbulb(p_addr, bytesWritten);

    r = (constr:(0))
  ))).

Definition recvEthernet :=
    let info : varname := "info" in
    let rxunused : varname := "rx_unused" in
    let rx_status : varname := "rx_status" in
    let rx_packet : varname := "rx_packet" in
    let c : varname := "c" in
    let len_bytes : varname := "len_bytes" in
    let len_words : varname := "len_words" in
    let word : varname := "word" in
    let lan9250_readword : varname := "lan9250_readword" in

    let r : varname := "r" in
    ("recvEthernet", ((rx_packet::nil), (r::nil), bedrock_func_body:(
        (* len rx_packet is [(MAX_ETHERNET+3) / 4] *)

        (* Read RX_FIFO_INF *)
        io! info = lan9250_readword(constr:(Ox"7C"));
        rxunused = ((info >> constr:(16)) & ((constr:(1) << constr:(8)) - constr:(1)));
        require (rxunused - constr:(0)) else { r = (constr:(-1)) };

        (* Read Status FIFO Port *)
        io! rx_status = lan9250_readword(constr:(Ox"40"));
        len_bytes = (rx_status >> constr:(16) & ((constr:(1) << constr:(14)) - constr:(1)));
        len_words = (len_bytes + (constr:(4) - constr:(1)) >> constr:(2));

        (* len_words <= MAX_ETHERNET *)
        require (len_words < constr:(1518 + 1)) else { r = (constr:(-1)) };

        c = (constr:(0));
        word = (constr:(0));
        while (c < len_words) {
            io! word = lan9250_readword(constr:(0));
            store(rx_packet + c * constr:(4), word);
            c = (c + constr:(1))
        };
        r = (len_words)
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
    require (constr:(42) < len) else { r = (constr:(-1)) };

    ethertype = ((load1(packet + constr:(12)) << constr:(8)) | (load1(packet + constr:(13))));
    require (constr:(1536 - 1) < ethertype) else { r = (constr:(-1)) };

    protocol = (load1(packet + constr:(23)));
    require (protocol == constr:(Ox"11")) else { r = (constr:(-1)) };

    command = (load1(packet + constr:(42))); (* TODO: MMIOWRITE one bit only *)

    io! mmio_val = MMIOREAD(constr:(Ox"10012008"));
    output! MMIOWRITE(constr:(Ox"10012008"), mmio_val | constr:(1) << constr:(23));

    io! mmio_val = MMIOREAD(constr:(Ox"1001200c"));
    output! MMIOWRITE(constr:(Ox"1001200c"), mmio_val | command << constr:(23));

    r = (constr:(0))
  ))).

From coqutil Require Import Word.Interface Map.Interface.
From coqutil.Tactics Require Import letexists eabstract.
From bedrock2 Require Import FE310CSemantics Semantics WeakestPrecondition ProgramLogic Array Scalars.
From bedrock2.Map Require Import Separation SeparationLogic.

Local Infix "*" := sep.
Local Infix "*" := sep : type_scope.

Instance spec_of_iot : spec_of "iot" := fun functions =>
  forall p_addr rx_packet R m t,
    (array scalar8 (word.of_Z 1) p_addr rx_packet * R) m ->
    Z.of_nat (List.length rx_packet) = 1518 ->
    WeakestPrecondition.call functions "iot" t m [p_addr]
      (fun t' m' rets => exists v, rets = [v]).

Instance spec_of_recvEthernet : spec_of "recvEthernet" := fun functions =>
  forall p_addr (rx_packet:list byte) R m t,
    (array scalar8 (word.of_Z 1) p_addr rx_packet * R) m ->
    1518 <= Z.of_nat (List.length rx_packet) ->
    (* comment on wormhole mentions < 0x400 for lan9250_readword. TODO check against manual *)
    WeakestPrecondition.call functions "recvEthernet" t m [p_addr]
      (fun t' m' rets => exists bytes_written, rets = [bytes_written] /\
      (
        (exists rx_packet', (array scalar8 (word.of_Z 1) p_addr rx_packet' * 
                          array scalar8 (word.of_Z 1) bytes_written rx_packet *
                          R) m' /\
        word.unsigned bytes_written = Z.of_nat (List.length rx_packet') /\
        word.unsigned bytes_written <> word.unsigned (word.of_Z (-1)))
        \/
        (bytes_written = word.of_Z (-1))
      )).

Instance spec_of_lightbulb : spec_of "lightbulb" := fun functions =>
  forall p_addr (rx_packet:list byte) (len:word) R m t,
    (array scalar8 (word.of_Z 1) p_addr rx_packet * R) m ->
    word.unsigned len = Z.of_nat (List.length rx_packet) ->
    WeakestPrecondition.call functions "lightbulb" t m [p_addr; len]
      (fun t' m' rets => exists v, rets = [v] /\ m' = m).

Ltac seplog_use_array_load1 H i :=
  let iNat := eval cbv in (Z.to_nat i) in
  let H0 := fresh in pose proof H as H0;
  unshelve SeparationLogic.seprewrite_in @array_index_nat_inbounds H0;
    [exact iNat|exact (word.of_Z 0)|blia|];
  change ((word.unsigned (word.of_Z 1) * Z.of_nat iNat)%Z) with i in *.

(* TODO why does typeclass search fail here? *)
Local Instance mapok: map.ok mem := SortedListWord.ok (Naive.word 32 eq_refl) _.
Local Instance wordok: word.ok word := coqutil.Word.Naive.ok _ _.

Lemma iot_ok : program_logic_goal_for_function! iot.
Proof.
  repeat straightline.

  (* from Print Ltac straightline_call. *)
  eapply WeakestPreconditionProperties.Proper_call; cycle -1;
         [ eapply H | try eabstract solve [ Morphisms.solve_proper ].. ];
         [ .. | intros ? ? ? ? ].
  { ecancel_assumption. }
  { Lia.lia. }
  { repeat straightline. letexists. 
    { repeat straightline; split; [|repeat straightline; eauto]. 
      { repeat straightline. }
      { split; repeat straightline. 2:eauto.
        destruct H4.
        2:{ repeat straightline. admit. (* v != and = 0 *) }
        { repeat straightline.
          eapply WeakestPreconditionProperties.Proper_call; cycle -1;
         [ eapply H0 | try eabstract solve [ Morphisms.solve_proper ].. ];
         [ .. | intros ? ? ? ? ].
        { ecancel_assumption. }
        { Lia.lia. }
        { repeat straightline. eauto. } } } }
Admitted.


Lemma recvEthernet_ok : program_logic_goal_for_function! recvEthernet.
Proof.
  repeat straightline.

  seplog_use_array_load1 H 0.
  seplog_use_array_load1 H 64.
  seplog_use_array_load1 H 124.
  repeat straightline.

  cbn [args ext_spec FE310CSemantics.parameters].
  do 2 eexists; split. { eapply Properties.map.split_empty_r. reflexivity. }



  letexists; split; repeat straightline; split; [|repeat straightline; eauto].
  repeat straightline.
  split; [cbv; clear; intuition congruence | intros].
  repeat straightline.
  exists m. split. { eapply Properties.map.split_empty_r. reflexivity. }
  repeat straightline.

  (* if for early out *)
  letexists; split; repeat straightline; split; [|repeat straightline; eauto].
  repeat straightline.


  cbn [args ext_spec FE310CSemantics.parameters].
  do 2 eexists; split. { eapply Properties.map.split_empty_r. reflexivity. }
  split; [cbv; clear; intuition congruence | intros].
  repeat straightline.
  exists m. split. { eapply Properties.map.split_empty_r. reflexivity. }
  repeat straightline.

  letexists; split; repeat straightline; split; [|repeat straightline; eauto].
  repeat straightline.

  (* while loop *)
  refine (TailRecursion.tailrec
    (* types of ghost variables*) HList.polymorphic_list.nil
    (* program variables *) ["info";"rx_unused";"rx_status";"rx_packet";"c";"len_bytes";"len_words";"word"]
    (fun v t m info rx_unused rx_status rx_packet c len_bytes len_words_loop word => 
        PrimitivePair.pair.mk (v = word.unsigned c /\
        exists scratch R, (array scalar8 (word.of_Z 1) (word.add rx_packet (word.mul c (word.of_Z 4)) )  scratch * R) m /\
        Z.of_nat (List.length scratch) = word.unsigned (word.mul (word.sub len_words c) (word.of_Z 4) ) /\
        len_words_loop = len_words)  (* precondition *)
    (fun   T M INFO RX_UNUSED RX_STATUS RX_PACKET C LEN_BYTES LEN_WORDS WORD => (* postcondition *) True))
    (fun n m : Z => m < n <= word.unsigned len_words) (* well_founded relation *)
    _ _ _ _ _);
    (* TODO wrap this into a tactic with the previous refine *)
    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.

  { repeat straightline. }
  { exact (Z.gt_wf _). }
  { repeat straightline. eauto. 1:admit. }
  { repeat straightline.  cbn [args ext_spec FE310CSemantics.parameters].
    do 2 eexists; split. { eapply Properties.map.split_empty_r. reflexivity. }
    split; [cbv; clear; intuition congruence | intros].
    repeat straightline.
    eexists. split. { eapply Properties.map.split_empty_r. eauto. }

  repeat straightline.
  apply Properties.word.if_nonzero in H6.
  rewrite word.unsigned_ltu in H6.
  rewrite Z.ltb_lt in H6.

  rewrite <- (List.firstn_skipn 4 x7) in H7.
Require Import coqutil.Macros.symmetry.
   SeparationLogic.seprewrite_in (symmetry! @bytearray_index_merge) H7.

  { rewrite List.length_firstn_inbounds. { instantiate (1:= word.of_Z 4). eauto. }
  apply Znat.Nat2Z.inj_le.
  rewrite H8. revert H6. admit. }

  eapply store_word_of_sep. { 
    revert H10. unfold scalar. unfold truncated_scalar. unfold littleendian. unfold ptsto_bytes.ptsto_bytes. admit. (* this needs to be proven to fill in H7, scratch *)}
  { 
  
  do 6 straightline.
  (* TODO more than 6 straightlines takes too long *)

    Import Markers.hide.
    do 8 letexists. split. 
    { repeat straightline. }
    { letexists. split.
    { split. { repeat straightline. }
             { letexists. 
               { repeat straightline. letexists. 
                 { split. {
  replace (word.add
             (word.add x2 (word.mul x3 (word.of_Z 4)))
             (word.of_Z 4)) with (word.add x2 (word.mul c (word.of_Z 4))) in H10.
  { ecancel_assumption. }
  { subst c. (* TODO ring. *) admit. }}

  assert (scratch=(List.skipn 4 x7)). { repeat straightline. }
  { repeat straightline. subst scratch. rewrite List.length_skipn. subst c.
  rewrite Znat.Nat2Z.inj_sub.
  { rewrite H8. (* ring *) admit. }
  (* same as apply Znat.Nat2Z.inj_le admitted above  *) admit. }}}}}
  repeat straightline. split.
  { subst v3. subst v'. subst c. admit. }
  repeat straightline. }}}
  do 15 straightline. admit. (* do 16+ straightline is Coq anomaly *)

Admitted.

(* bsearch.v has examples to deal with arrays *)
Lemma lightbulb_ok : program_logic_goal_for_function! lightbulb.
Proof.
  repeat straightline.

  seplog_use_array_load1 H 12.
  seplog_use_array_load1 H 13.
  seplog_use_array_load1 H 23.
  seplog_use_array_load1 H 42.
  repeat straightline.

  (* if for early out *)
  letexists; split; repeat straightline; split; [|repeat straightline; eauto].
  repeat straightline.

  (* if for early out *)
  letexists; split; repeat straightline; split; [|repeat straightline; eauto].
  repeat straightline.

  (* the 1st MMIOREAD *)
  cbn [args ext_spec FE310CSemantics.parameters].
  do 2 eexists; split. { eapply Properties.map.split_empty_r. reflexivity. }
  split; [cbv; clear; intuition congruence | intros].
  repeat straightline.
  exists m. split. { eapply Properties.map.split_empty_r. reflexivity. }
  repeat straightline.
  do 2 eexists; split. { eapply Properties.map.split_empty_r. reflexivity. }

  cbn [args ext_spec FE310CSemantics.parameters].
  split. { cbv; clear; intuition congruence. }
  repeat straightline.
  exists m. split. { eapply Properties.map.split_empty_r. reflexivity. }
  repeat straightline.
  do 2 eexists; split. { eapply Properties.map.split_empty_r. reflexivity. }

  cbn [args ext_spec FE310CSemantics.parameters].
  split. { cbv; clear; intuition congruence. }
  repeat straightline.
  exists m. split. { eapply Properties.map.split_empty_r. reflexivity. }
  repeat straightline.
  do 2 eexists; split. { eapply Properties.map.split_empty_r. reflexivity. }

  cbn [args ext_spec FE310CSemantics.parameters].
  split. { cbv; clear; intuition congruence. }
  repeat straightline.
  exists m. split. { eapply Properties.map.split_empty_r. reflexivity. }
  repeat straightline.
  clear. eauto.
Qed.

Compute BasicCSyntax.c_func (recvEthernet).
Compute BasicCSyntax.c_func (lightbulb).
Compute BasicCSyntax.c_func (iot).