Require Import coqutil.Z.Lia.
Require Import bedrock2.Syntax bedrock2.StringNamesSyntax.
Require Import bedrock2.NotationsCustomEntry coqutil.Z.HexNotation.
Require Import bedrock2.FE310CSemantics. (* TODO for andres: [literal] shouldn't need this *)
Require Import coqutil.Macros.symmetry.
From coqutil Require Import Z.div_mod_to_equations.
From coqutil Require Import Word.Interface Map.Interface.
From coqutil.Tactics Require Import letexists eabstract.
From bedrock2 Require Import FE310CSemantics Semantics WeakestPrecondition ProgramLogic Array Scalars.
From bedrock2.Map Require Import Separation SeparationLogic.
Import Markers.hide.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion literal (z : Z) : expr := expr.literal z.
Local Coercion var (x : String.string) : expr := expr.var x.

(* TODO: refactor *)
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
Ltac trans_ltu :=
          match goal with
          H : word.unsigned ?v <> 0 |- _ =>
          let v := rdelta.rdelta v in
          let __ := lazymatch v with if word.ltu _ _ then word.of_Z 1 else word.of_Z 0 => I end in
          eapply Properties.word.if_nonzero in H; rewrite word.unsigned_ltu in H; eapply Z.ltb_lt in H end.
Ltac straightline_if :=
  lazymatch goal with
  |- WeakestPrecondition.cmd _ ?c _ _ _ ?post =>
        let c := eval hnf in c in
        lazymatch c with
        | cmd.cond _ _ _ => letexists; split; [|split]
        end
  end.
Lemma interact_nomem call action binds arges t m l post
  args (Hargs : dexprs m l arges args)
  (Hext : ext_spec t map.empty binds args (fun mReceive (rets : list word) =>
    mReceive = map.empty /\
    exists l0 : locals, map.putmany_of_list action rets l = Some l0 /\
    post ((map.empty, binds, args, (map.empty, rets)) :: t) m l0))
  : WeakestPrecondition.cmd call (cmd.interact action binds arges) t m l post.
Proof.
  repeat straightline.
  exists args; split; [exact Hargs|].
  exists m.
  exists map.empty.
  split; [eapply Properties.map.split_empty_r; exact eq_refl|].
  eapply ok; [|eapply Hext]; intros ? ? [? [? []]]; subst.
  eexists; split; [eassumption|].
  Print WeakestPrecondition.cmd_body.
  eexists; split; [eapply Properties.map.split_empty_r; exact eq_refl|].
  assumption.
Qed.



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
    let r : varname := "r" in

  ("iot", ((p_addr::nil), (r::nil), bedrock_func_body:(
    unpack! bytesWritten = recvEthernet(p_addr);
    require (bytesWritten ^ constr:(-1)) else { r = (constr:(-1)) };
    unpack! r = lightbulb(p_addr, bytesWritten);

    r = (constr:(0))
  ))).

Definition recvEthernet :=
    let lan9250_readword : varname := "lan9250_readword" in
    
    let buf : varname := "buf" in
    let num_bytes : varname := "num_bytes" in
    let i : varname := "i" in
    let read : varname := "read" in

    ("recvEthernet", ((buf::nil), (num_bytes::nil), bedrock_func_body:(
        io! read = lan9250_readword(constr:(Ox"7C")); (* RX_FIFO_INF *)
        require (read & constr:((2^8-1)*2^16)) else { num_bytes = (constr:(-1)) }; (* nonempty *)
        io! read = lan9250_readword(constr:(Ox"40")); (* RX_STATUS_FIFO_PORT *)

        num_bytes = (read >> constr:(16) & constr:(2^14-1));
        (* round up to next word *)
        num_bytes = ((num_bytes + constr:(4-1)) >> constr:(2));
        num_bytes = (num_bytes + num_bytes);
        num_bytes = (num_bytes + num_bytes);

        require (num_bytes < constr:(1520 + 1)) else { num_bytes = (constr:(-1)) };

        i = (constr:(0)); while (i < num_bytes) {
            io! read = lan9250_readword(constr:(0));
            store4(buf + i, read);
            i = (i + constr:(4))
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
    command = (load1(r)); (* TODO: MMIOWRITE one bit only *)

    io! mmio_val = MMIOREAD(constr:(Ox"10012008"));
    output! MMIOWRITE(constr:(Ox"10012008"), mmio_val | constr:(2^23));

    r = (constr:(Ox"1001200c"));
    io! mmio_val = MMIOREAD(r);
    output! MMIOWRITE(r, mmio_val | command << constr:(23));

    r = (constr:(0))
  ))).

Local Infix "*" := sep.
Local Infix "*" := sep : type_scope.

Instance spec_of_iot : spec_of "iot" := fun functions =>
  forall p_addr buf R m t,
    (array scalar8 (word.of_Z 1) p_addr buf * R) m ->
    Z.of_nat (List.length buf) = 1520 ->
    WeakestPrecondition.call functions "iot" t m [p_addr]
      (fun t' m' rets => exists v, rets = [v]).

Instance spec_of_recvEthernet : spec_of "recvEthernet" := fun functions =>
  forall p_addr (buf:list byte) R m t,
    (array scalar8 (word.of_Z 1) p_addr buf * R) m ->
    List.length buf = 1520%nat ->
    (* comment on wormhole mentions < 0x400 for lan9250_readword. TODO check against manual *)
    WeakestPrecondition.call functions "recvEthernet" t m [p_addr]
      (fun t' m' rets =>
       (* Success, we wrote 0+ bytes to the buffer *)
       (
         exists bytes_written:word, rets = [bytes_written]
         /\
         exists rx_packet', (array scalar8 (word.of_Z 1) p_addr rx_packet' *
                             array scalar8 (word.of_Z 1) (word.add p_addr bytes_written)
                                                         (List.skipn (Z.to_nat (word.unsigned bytes_written)) buf) *
                             R) m'
         /\
         word.unsigned bytes_written <= Z.of_nat (List.length rx_packet')
       )
       \/
       (* Fail, we return -1 and don't write anything *)
       (rets = [word.of_Z (-1)] /\ m' = m)
      ).

Instance spec_of_lightbulb : spec_of "lightbulb" := fun functions =>
  forall p_addr (buf:list byte) (len:word) R m t,
    (array scalar8 (word.of_Z 1) p_addr buf * R) m ->
    word.unsigned len <= Z.of_nat (List.length buf) ->
    WeakestPrecondition.call functions "lightbulb" t m [p_addr; len]
      (fun t' m' rets => exists v, rets = [v] /\ m' = m).


Lemma iot_ok : program_logic_goal_for_function! iot.
Proof.
  repeat (straightline || straightline_call || ecancel_assumption).
  { blia. }
  match goal with H : or _ _ |- _ => destruct H end;
  repeat (straightline || straightline_call || straightline_if || ecancel_assumption || eauto).
  match goal with H : _ |- _ => case (H eq_refl) end.
Qed.

Ltac prove_ext_spec :=
  lazymatch goal with
  | |- ext_spec _ _ _ _ _ => split; [cbv; clear; firstorder congruence|]; split; [trivial|]
  end.

Lemma recvEthernet_ok : program_logic_goal_for_function! recvEthernet.
Proof.
  repeat (straightline || straightline_if || eapply interact_nomem || eauto 99 || prove_ext_spec).
  refine (TailRecursion.tailrec
    (* types of ghost variables *) (HList.polymorphic_list.cons (list byte) (HList.polymorphic_list.cons (mem -> Prop) HList.polymorphic_list.nil))
    (* program variables *) ["buf";"num_bytes";"i";"read"]
    (fun v scratch R t m buf num_bytes_loop i read =>
      PrimitivePair.pair.mk (v = word.unsigned i /\
      (array scalar8 (word.of_Z 1) (word.add buf i) scratch * R) m /\
      Z.of_nat (List.length scratch) = word.unsigned (word.sub num_bytes i) /\

      word.unsigned i mod 4 = word.unsigned num_bytes mod 4 /\
      num_bytes_loop = num_bytes
      (* (word.unsigned i < word.unsigned num_bytes + 4) *)
      (* /\  word.unsigned i < num_bytes) *) )  (* precondition of every loop *)
      (fun T M BUF NUM_BYTES I READ => exists SCRATCH,
        (array scalar8 (word.of_Z 1) (word.add buf i) SCRATCH * R) M /\
        List.length SCRATCH = List.length scratch /\
        NUM_BYTES = num_bytes)) (* postcondition *)
    (fun n m : Z => m < n <= word.unsigned num_bytes) (* well_founded relation *)
    _ _ _ _ _ _ _);
  (* TODO wrap this into a tactic with the previous refine? *)
  cbn [HList.hlist.foralls HList.tuple.foralls
       HList.hlist.existss HList.tuple.existss
       HList.hlist.apply  HList.tuple.apply
       HList.hlist
       List.repeat Datatypes.length
       HList.polymorphic_list.repeat HList.polymorphic_list.length
       PrimitivePair.pair._1 PrimitivePair.pair._2] in *;
  repeat (straightline || straightline_if || eapply interact_nomem || eauto 99).
  { exact (Z.gt_wf _). }
  { repeat (refine (conj _ _)); eauto.
    { replace (word.add p_addr i) with p_addr by (subst i; ring).
      rewrite <- (List.firstn_skipn (Z.to_nat (word.unsigned (word.sub num_bytes i) ) )  _) in H.
      SeparationLogic.seprewrite_in (symmetry! @bytearray_index_merge) H; [|ecancel_assumption].
      rewrite List.length_firstn_inbounds, Znat.Z2Nat.id; trivial.
      { eapply Properties.word.unsigned_range. }
      trans_ltu. eapply Znat.Nat2Z.inj_le. rewrite -> Znat.Z2Nat.id.
      { rewrite -> H0.
        replace (word.sub num_bytes i) with num_bytes by (subst i; ring).
        rewrite word.unsigned_of_Z in H2. change (word.wrap 1521) with (1521) in H2.
        Lia.lia. }
      replace (word.sub num_bytes i) with num_bytes by (subst i; ring).
      eapply Properties.word.unsigned_range. }
    { replace (word.sub num_bytes i) with num_bytes by (subst i; ring).
      rewrite -> List.length_firstn_inbounds.
      { rewrite Znat.Z2Nat.id; trivial; eapply Properties.word.unsigned_range. }
      rewrite H0. trans_ltu.
      change (word.unsigned (word.of_Z 1521)) with (1521) in H2.
      pose proof Properties.word.unsigned_range num_bytes.
      PreOmega.zify.
      rewrite Znat.Z2Nat.id; Lia.lia. }
    { pose proof Properties.word.unsigned_range num_bytes. PreOmega.zify.
      subst i. subst num_bytes. subst num_bytes2.
      replace (word.add (word.add num_bytes1 num_bytes1) (word.add num_bytes1 num_bytes1)) with (word.mul num_bytes1 (word.of_Z 4)) in * by ring.
      { rewrite word.unsigned_mul. unfold word.wrap.
        rewrite (Z.mod_small _ (2^width)).
        { change (word.unsigned (word.of_Z 0) mod 4) with 0.
          change (word.unsigned (word.of_Z 4)) with 4.
          Z.div_mod_to_equations.
          Lia.lia. }
        change (word.unsigned (word.of_Z 4)) with 4. subst num_bytes1.
        rewrite Properties.word.unsigned_sru_nowrap.
        { rewrite Z.shiftr_div_pow2.
          { change (2 ^ word.unsigned (word.of_Z 2)) with 4.
            pose proof Properties.word.unsigned_range (word.add num_bytes0 (word.of_Z 3)).
            Z.div_mod_to_equations.
            (*  0 <= word.unsigned num_words * word.unsigned (word.of_Z 4)
                < 2 ^ width *)
            Lia.lia. }
          { cbv. congruence. }}
        exact eq_refl. }}}
    (* lan9250_readword *)
    { prove_ext_spec. repeat (straightline || straightline_if).
      (* store *)
      do 2 trans_ltu. rewrite <- (List.firstn_skipn 4 x) in H4.
      SeparationLogic.seprewrite_in (symmetry! @bytearray_index_merge) H4.
      { rewrite List.length_firstn_inbounds.
        { instantiate (1:= word.of_Z 4). eauto. }
        apply Znat.Nat2Z.inj_le. rewrite H5. rewrite word.unsigned_sub.
        unfold word.wrap. rewrite Z.mod_small.
        { revert H6 H3. clear. Z.div_mod_to_equations.
          (* Z.of_nat 4 <= word.unsigned x6 - word.unsigned x5 *)
          Lia.lia. }
        pose proof Properties.word.unsigned_range x2.
        pose proof Properties.word.unsigned_range x3.
        Lia.lia. } 
      eapply store_four_of_sep.
      { seprewrite_in @scalar32_of_bytes H8; [..|ecancel_assumption].
        { exact _. }
        { eapply List.length_firstn_inbounds. apply Znat.Nat2Z.inj_le. rewrite H5.
          rewrite word.unsigned_sub. unfold word.wrap. rewrite Z.mod_small.
          { revert H6 H3. clear. Z.div_mod_to_equations.
            (* Z.of_nat 4 <= word.unsigned x6 - word.unsigned x5 *)
            Lia.lia. }
          pose proof Properties.word.unsigned_range x2.
          pose proof Properties.word.unsigned_range x3.
          (* 0 <= word.unsigned x6 - word.unsigned x5 < 2 ^ width *)
          Lia.lia. }}
      do 5 straightline.
      (* TODO straightline hangs in TailRecursion.enforce *)
      do 4 letexists. split. { repeat straightline. } do 3 letexists.
      repeat split; repeat straightline; repeat split.
      { replace (word.add x1 i)
          with (word.add (word.add x1 x3) (word.of_Z 4)) by (subst i; ring).
        ecancel_assumption. }
      { subst x9. rewrite List.length_skipn. rewrite Znat.Nat2Z.inj_sub.
        { rewrite H5. subst i.
          replace (word.sub x2 (word.add x3 (word.of_Z 4)))
            with (word.sub (word.sub x2 x3) (word.of_Z 4)) by ring.
          rewrite (word.unsigned_sub _ (word.of_Z 4)).
          unfold word.wrap. rewrite Z.mod_small.
          { exact eq_refl. }
          { change (word.unsigned (word.of_Z 4)) with 4.
            pose proof Properties.word.unsigned_range (word.sub x2 x3).
            pose proof Properties.word.unsigned_range x2.
            pose proof Properties.word.unsigned_range x3.
            rewrite word.unsigned_sub. unfold word.wrap. rewrite Z.mod_small.
            { revert H10 H9 H7 H6 H3 H2. clear.
              Z.div_mod_to_equations. Lia.lia. }
            { Z.div_mod_to_equations. Lia.lia. }}}
        apply Znat.Nat2Z.inj_le. rewrite H5. rewrite word.unsigned_sub.
        unfold word.wrap. rewrite Z.mod_small.
        { revert H6 H3. clear. Z.div_mod_to_equations. Lia.lia. }
        pose proof Properties.word.unsigned_range x2.
        pose proof Properties.word.unsigned_range x3.
        Lia.lia. }
      { subst i. rewrite word.unsigned_add. unfold word.wrap. rewrite (Z.mod_small _ (2 ^ width)).
        { revert H6. clear. change (word.unsigned (word.of_Z 4)) with 4.
          Z.div_mod_to_equations. Lia.lia. }
        pose proof Properties.word.unsigned_range x2.
        pose proof Properties.word.unsigned_range x3.
        change (word.unsigned (word.of_Z 4)) with 4.
        change (word.unsigned (word.of_Z 1521)) with 1521 in *.
        revert H9 H7 H6 H3 H2. clear.
        PreOmega.zify. Z.div_mod_to_equations. Lia.lia. }
      { repeat match goal with |- context [?x] => is_var x; subst x end.
        rewrite word.unsigned_add. unfold word.wrap. rewrite Z.mod_small.
        { change (word.unsigned (word.of_Z 4)) with 4. Lia.lia. }
        pose proof Properties.word.unsigned_range x2.
        pose proof Properties.word.unsigned_range x3.
        change (word.unsigned (word.of_Z 4)) with 4.
        change (word.unsigned (word.of_Z 1521)) with 1521 in *.
        revert H9 H7 H6 H3 H2. clear.
        PreOmega.zify. Z.div_mod_to_equations. Lia.lia. }
      { subst v'. subst i.
        rewrite word.unsigned_add. change (word.unsigned (word.of_Z 4)) with 4.
        unfold word.wrap. rewrite (Z.mod_small _ (2 ^ width)).
        { revert H6 H3. clear. Z.div_mod_to_equations. Lia.lia. }
        { pose proof Properties.word.unsigned_range x2.
          pose proof Properties.word.unsigned_range x3.
          change (word.unsigned (word.of_Z 1521)) with 1521 in *.
          PreOmega.zify. Z.div_mod_to_equations. Lia.lia. }}
      { letexists. split.
        { subst x10. subst i.
          repeat match type of H7 with context [?x] => subst x end.
          cbv [scalar32 truncated_scalar littleendian ptsto_bytes.ptsto_bytes] in H7.
          replace (word.add x1 (word.add x3 (word.of_Z 4))) with
                  (word.add (word.add x1 x3) (word.of_Z 4)) in H7 by ring.
          SeparationLogic.seprewrite_in (@bytearray_index_merge) H7.
          { exact eq_refl. } { ecancel_assumption. }}
        split.
        { subst SCRATCH. rewrite List.app_length. rewrite H9. subst x9. rewrite List.length_skipn.
          change (Datatypes.length (HList.tuple.to_list (LittleEndian.split (bytes_per access_size.four) (word.unsigned (word.of_Z (word.unsigned v4)))))) with (4%nat).
          assert (4 <= (Datatypes.length x))%nat. 2:Lia.lia.
          PreOmega.zify.
          rewrite H5. rewrite word.unsigned_sub. unfold word.wrap. rewrite (Z.mod_small _ (2 ^ width)).
          { revert H6 H3. clear. change (word.unsigned (word.of_Z 4)) with 4.
            Z.div_mod_to_equations. Lia.lia. }
          pose proof Properties.word.unsigned_range x12.
          pose proof Properties.word.unsigned_range x3.
          Lia.lia. }
        { reflexivity. }}}
    { left. letexists. split. { repeat straightline. exact eq_refl. }
      letexists. split.
      { subst bytes_written. subst i.
        replace (word.add p_addr (word.of_Z 0)) with (p_addr) in H3 by ring.
        replace (word.add p_addr (word.sub x0 (word.of_Z 0)))
          with (word.add p_addr x0) in H3 by ring.
        replace (word.sub x0 (word.of_Z 0)) with (x0) in H3 by ring.
        ecancel_assumption. }
      subst bytes_written. subst rx_packet'. subst i. rewrite H4.
      replace (word.sub x0 (word.of_Z 0)) with (x0) by ring.
      rewrite List.length_firstn_inbounds, Znat.Z2Nat.id; trivial.
      { reflexivity. }
      { pose proof Properties.word.unsigned_range x0. apply H5. }
      { rewrite H0.
        pose proof Properties.word.unsigned_range x0.
        trans_ltu. eapply Znat.Nat2Z.inj_le. rewrite -> Znat.Z2Nat.id.
        { rewrite word.unsigned_of_Z in H2. change (word.wrap 1521) with (1521) in H2. Lia.lia. }
        { eapply Properties.word.unsigned_range. }
    }}
    Grab Existential Variables. exact _.
Qed.

Lemma lightbulb_ok : program_logic_goal_for_function! lightbulb.
Proof.
  repeat (eauto || straightline || straightline_if || eapply interact_nomem || prove_ext_spec).

  trans_ltu.
  repeat match goal with x := _ |- _ => subst x end.
  rewrite word__unsigned_of_Z_nowrap in * by (change (2^width) with (2^32); blia).

  seplog_use_array_load1 H 12.
  seplog_use_array_load1 H 13.
  seplog_use_array_load1 H 23.
  seplog_use_array_load1 H 42.
  repeat (eauto || straightline || straightline_if || eapply interact_nomem || prove_ext_spec).
Qed.

(*
Compute BasicCSyntax.c_func (recvEthernet).
Compute BasicCSyntax.c_func (lightbulb).
Compute BasicCSyntax.c_func (iot).
*)
