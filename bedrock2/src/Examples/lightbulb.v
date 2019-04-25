Require Import coqutil.Z.Lia.
Require Import bedrock2.Syntax bedrock2.StringNamesSyntax.
Require Import bedrock2.NotationsCustomEntry coqutil.Z.HexNotation.
Require Import bedrock2.FE310CSemantics. (* TODO for andres: [literal] shouldn't need this *)
Require Import coqutil.Macros.symmetry.
From coqutil Require Import Word.Interface Map.Interface.
From coqutil.Tactics Require Import letexists eabstract.
From bedrock2 Require Import FE310CSemantics Semantics WeakestPrecondition ProgramLogic Array Scalars.
From bedrock2.Map Require Import Separation SeparationLogic.
Import Markers.hide.

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
            store4(rx_packet + c * constr:(4), word);
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
      (fun t' m' rets =>
       (* Success, we wrote 0+ bytes to the buffer *)
       (
         exists bytes_written:word, rets = [bytes_written]
         /\
         exists rx_packet', (array scalar8 (word.of_Z 1) p_addr rx_packet' * 
                             array scalar8 (word.of_Z 1) bytes_written rx_packet *
                             R) m'
         /\
         word.unsigned bytes_written = Z.of_nat (List.length rx_packet')
         /\
         word.unsigned bytes_written <> word.unsigned (word.of_Z (-1))
       )
       \/
       (* Fail, we return -1 and don't write anything *)
       (rets = [word.of_Z (-1)] /\ m' = m)
      ).

Instance spec_of_lightbulb : spec_of "lightbulb" := fun functions =>
  forall p_addr (rx_packet:list byte) (len:word) R m t,
    (array scalar8 (word.of_Z 1) p_addr rx_packet * R) m ->
    word.unsigned len = Z.of_nat (List.length rx_packet) ->
    WeakestPrecondition.call functions "lightbulb" t m [p_addr; len]
      (fun t' m' rets => exists v, rets = [v] /\ m' = m).

(* TODO why does typeclass search fail here? *)
Local Instance mapok: map.ok mem := SortedListWord.ok (Naive.word 32 eq_refl) _.
Local Instance wordok: word.ok word := coqutil.Word.Naive.ok _ _.

Lemma word__unsigned_of_Z_nowrap x : 0 <= x < 2 ^ width -> word.unsigned (word.of_Z x) = x.
Proof.
  intros. rewrite word.unsigned_of_Z. unfold word.wrap. rewrite Z.mod_small; trivial.
Qed.

Ltac seplog_use_array_load1 H i :=
  let iNat := eval cbv in (Z.to_nat i) in
  let H0 := fresh in pose proof H as H0;
  unshelve SeparationLogic.seprewrite_in @array_index_nat_inbounds H0;
    [exact iNat|exact (word.of_Z 0)|blia|];
  change ((word.unsigned (word.of_Z 1) * Z.of_nat iNat)%Z) with i in *.

Lemma iot_ok : program_logic_goal_for_function! iot.
Proof.
  repeat straightline.

  (* from Print Ltac straightline_call. *)
  (* recvEthernet call *)
  eapply WeakestPreconditionProperties.Proper_call; cycle -1;
         [ eapply H | try eabstract solve [ Morphisms.solve_proper ].. ];
         [ .. | intros ? ? ? ? ].
  { ecancel_assumption. }
  { Lia.lia. }
  repeat straightline. destruct H3.
    { repeat straightline. letexists. split.
      { repeat straightline. }
      { split.
        { repeat straightline.
          (* lightbulb call *)
          eapply WeakestPreconditionProperties.Proper_call; cycle -1;
           [ eapply H0 | try eabstract solve [ Morphisms.solve_proper ].. ];
           [ .. | intros ? ? ? ? ].
          { repeat straightline. ecancel_assumption. } (* separation logic *)
          { repeat straightline. trivial. }
          { repeat straightline. eauto. }}
          repeat straightline. eauto. }}
          repeat straightline.
          (* cmd is an if statement *)
          letexists; split; repeat straightline; split; [|repeat straightline; eauto].
          repeat straightline.
          eapply WeakestPreconditionProperties.Proper_call; cycle -1;
           [ eapply H0 | try eabstract solve [ Morphisms.solve_proper ].. ];
           [ .. | intros ? ? ? ? ].
          { repeat straightline. ecancel_assumption. }
          { repeat straightline. contradiction. }
          { repeat straightline. eauto. }
Qed.


(* TODO add in. Used for goals involving word arithmetic *)
Add Ring wring : (Properties.word.ring_theory (word := word))
    (preprocess [autorewrite with rew_word_morphism],
     morphism (Properties.word.ring_morph (word := word)),
     constants [Properties.word_cst]).

Lemma recvEthernet_ok : program_logic_goal_for_function! recvEthernet.
Proof.
  repeat straightline.
  cbn [args ext_spec FE310CSemantics.parameters].
  do 2 eexists; split. { eapply Properties.map.split_empty_r. reflexivity. }
  repeat straightline. split.
  { repeat straightline. cbv. split. (* for inequalities like Ox "0" <= word.unsigned (word.of_Z 124) < Ox "400" *)
    { discriminate. } trivial. }
  { repeat straightline. letexists. split.
    { eapply Properties.map.split_empty_r. repeat straightline. }
    { letexists. repeat straightline. split.
      { repeat straightline. }
      { repeat straightline. letexists. split.
        { repeat straightline. }
        { split.
          { repeat straightline. do 2 eexists. split.
            { eapply Properties.map.split_empty_r. reflexivity. }
            { cbn [args ext_spec FE310CSemantics.parameters]. split. 
              { repeat straightline. cbv. split. { discriminate. } trivial. }
              { repeat straightline. letexists. split.
                { eapply Properties.map.split_empty_r. repeat straightline. }
                { repeat straightline. 
                  letexists; split; repeat straightline; split; [|repeat straightline; eauto].
                  repeat straightline.

                  (* while loop *)
                  refine (TailRecursion.tailrec
                    (* types of ghost variables *) (HList.polymorphic_list.cons (list byte) (HList.polymorphic_list.cons (mem -> Prop) HList.polymorphic_list.nil))
                    (* program variables *) ["info";"rx_unused";"rx_status";"rx_packet";"c";"len_bytes";"len_words";"word"]
                    (fun v scratch R t m info rx_unused rx_status rx_packet c len_bytes len_words_loop word => 
                        PrimitivePair.pair.mk (v = word.unsigned c /\
                        (array scalar8 (word.of_Z 1) (word.add rx_packet (word.mul c (word.of_Z 4)) ) scratch * R) m /\
                        Z.of_nat (List.length scratch) = word.unsigned (word.mul (word.sub len_words c) (word.of_Z 4) ) /\
                        len_words_loop = len_words)  (* precondition *)
                                              (fun T M INFO RX_UNUSED RX_STATUS RX_PACKET C LEN_BYTES LEN_WORDS WORD => exists SCRATCH, LEN_WORDS = len_words /\
                                                                                                                                        (array scalar8 (word.of_Z 1) (word.add rx_packet (word.mul c (word.of_Z 4)) ) SCRATCH * R) M /\
                                                                                                                                        List.length SCRATCH = List.length scratch /\
                                                                                                                                        LEN_WORDS = len_words
                    )) (* postcondition *)
                    (fun n m : Z => m < n <= word.unsigned len_words) (* well_founded relation *)
                    _ _ _ _ _ _ _);
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

                  { repeat straightline. split.
                    { eauto. }
                    { split. { replace (word.add p_addr (word.mul c (word.of_Z 4))) with p_addr. {
                                 rewrite <- (List.firstn_skipn (Z.to_nat (word.unsigned (word.mul (word.sub len_words c) (word.of_Z 4)))) _) in H.

                                 SeparationLogic.seprewrite_in (symmetry! @bytearray_index_merge) H.
                                 { (* length of 1st n elem = n, cancel out, of_nat and to_nat cancel *)
                                   rewrite -> List.length_firstn_inbounds.
                                   { rewrite -> Znat.Z2Nat.id.
                                     { eauto. }
                                     { apply Properties.word.unsigned_range. }}
                                   
(*  Z.to_nat (word.unsigned (word.mul (word.sub len_words c) (word.of_Z 4))) <= Datatypes.length rx_packet *)
                                   subst c. Search Z.of_nat. admit. }
                                 ecancel_assumption. }
                               subst c. ring. }


                             split.
                      2:{ reflexivity. }
                      {
                        rewrite -> List.length_firstn_inbounds.
                        { 
                          rewrite -> Znat.Z2Nat.id. { reflexivity. }
                                                    { apply Properties.word.unsigned_range. }}                  
                        {
(* Z.to_nat (word.unsigned (word.mul (word.sub len_words c) (word.of_Z 4))) <= Datatypes.length rx_packet *)
                          admit. }}}}
                  { repeat straightline.
                    { cbn [args ext_spec FE310CSemantics.parameters].
                    do 2 eexists; split. { eapply Properties.map.split_empty_r. reflexivity. }
                    split; [cbv; clear; intuition congruence | intros].
                    repeat straightline.
                    eexists. split. { eapply Properties.map.split_empty_r. eauto. }
                    repeat straightline.

                    (* store *)
                    apply Properties.word.if_nonzero in H3.
                    rewrite word.unsigned_ltu in H3.
                    rewrite Z.ltb_lt in H3.
                    rewrite <- (List.firstn_skipn 4 x) in H4.
                    SeparationLogic.seprewrite_in (symmetry! @bytearray_index_merge) H4.
                    { rewrite List.length_firstn_inbounds. { instantiate (1:= word.of_Z 4). eauto. }
                      apply Znat.Nat2Z.inj_le.
                      repeat straightline.
(* Z.of_nat 4 <= word.unsigned (word.mul (word.sub x7 x5) (word.of_Z 4)) *)
                      admit. } 
                    eapply store_four_of_sep. { (* TODO Andres, reorder lemma hypos. *) seprewrite_in @scalar32_of_bytes H7. { (* word.ok byte *) admit. }
                                                                               { (* word.ok ?word320 *) admit. }
                                                                               2:{ ecancel_assumption. }
                                                                               { repeat straightline.
                                                                                 rewrite -> List.length_firstn_inbounds.
                                                                                 { reflexivity. }
                                                                                 {
(* 4 <= Datatypes.length x *)
                                                                                   admit. }}}
                                              
                                              { do 6 straightline.
                                                (* TODO straightline hangs in TailRecursion.enforce *)
                                                (* TODO more than 6 straightlines takes too long *)
                      
                      do 8 letexists. split. 
                      { repeat straightline. }
                      { letexists. 
                        {  repeat straightline.
                           letexists. 
                                   { repeat straightline. letexists. 
                                     { split. {
                                         replace (word.add
                                                    (word.add x2 (word.mul x3 (word.of_Z 4)))
                                                    (word.of_Z 4)) with (word.add x2 (word.mul c (word.of_Z 4))) in H7.
                                         { split. { repeat straightline. }
                                                  { split.
                                                    {
                                                      repeat straightline.
                                                      subst c.
                                                      replace (word.add x4 (word.mul (word.add x5 (word.of_Z 1)) (word.of_Z 4))) with (word.add (word.add x4 (word.mul x5 (word.of_Z 4))) (word.of_Z 4)) by ring.
                                                      ecancel_assumption. }
                                                    
                                                    split.
                                                    {
(* Z.of_nat (Datatypes.length x17) = word.unsigned (word.mul (word.sub x7 c) (word.of_Z 4)) *)
                                                      admit. }
                                                      { reflexivity. }}}
                                         repeat straightline.
                                         subst c.
(* math, true if x3 = x5 but don't have anything *)
                                         admit. }
                                                split.
                                       { repeat straightline.
                                         subst v'. subst v4. subst c.
(* word.unsigned x5 < word.unsigned (word.add x5 (word.of_Z 1)) <= word.unsigned x7
   arith, with H3 proving the unsigneds dont overflow. prove by converting to Zs *)
                                         admit. }
                                       repeat straightline.
                                       split.
                                       {
                                         subst x9.
                                         unfold scalar32 in H8. unfold truncated_scalar in H8. unfold littleendian in H8. unfold ptsto_bytes.ptsto_bytes in H8.
                                         subst a. subst c.
                                         replace (word.add x4 (word.mul (word.add x5 (word.of_Z 1)) (word.of_Z 4))) with (word.add (word.add x4 (word.mul x5 (word.of_Z 4))) (word.of_Z 4)) in H8 by ring.
                                         SeparationLogic.seprewrite_in (@bytearray_index_merge) H8.
                                         { reflexivity. }
                                         { ecancel_assumption. }}
                                 
Search x16. Search x18.

                                         (* TODO merge scalar into 4 byte array, merge back into array *)
Search x. 
subst SCRATCH. rewrite List.app_length. rewrite H9. subst x17. rewrite List.length_skipn.

change (Datatypes.length
    (HList.tuple.to_list
       (LittleEndian.split (bytes_per access_size.four) (word.unsigned (word.of_Z (word.unsigned v5)))))) with (4%nat).
(* prove len(x) >=4 *)

  admit.
                    }}}}}}
                  (* r = lenwords, TailRecursion postcondition? *)
                    repeat straightline.
                    split.
                    { ecancel_assumption. }
                    { split; reflexivity. }}
                  repeat straightline.
                  
                  left. letexists. split.
                  { repeat straightline. exact eq_refl. }
                  letexists. split.
                  { subst c. replace (word.add p_addr (word.mul (word.of_Z 0) (word.of_Z 4))) with (p_addr) in H4 by ring. admit. }


          split.
                  {
(* (array ptsto (word.of_Z 1) p_addr rx_packet' * array ptsto (word.of_Z 1) bytes_written rx_packet * R) m0 *)
                    admit. }
              
(* word.unsigned bytes_written <> word.unsigned (word.of_Z (-1)) *)
                    admit. }}}}
                  repeat straightline.
(* word.unsigned bytes_written = Z.of_nat (Datatypes.length rx_packet') *) right. split; reflexivity. }}}}
Admitted.

(* TODO into straightline? *)
Ltac trans_ltu :=
          match goal with
          H : word.unsigned ?v <> 0 |- _ =>
          let v := rdelta.rdelta v in
          let __ := lazymatch v with if word.ltu (word.of_Z _) _ then word.of_Z 1 else word.of_Z 0 => I end in
          eapply Properties.word.if_nonzero in H; rewrite word.unsigned_ltu in H; eapply Z.ltb_lt in H end.
        
(* bsearch.v has examples to deal with arrays *)
Lemma lightbulb_ok : program_logic_goal_for_function! lightbulb.
Proof.
  repeat straightline.

  (* if for early out *)
  letexists; split; repeat straightline; split; [|repeat straightline; eauto].
  repeat straightline.

  trans_ltu.
  rewrite word__unsigned_of_Z_nowrap in * by (change (2^width) with (2^32); blia).
  
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
