(*
Formalization of a subset of the functionality of Intel's 8254x Network Interface Cards.

PDF Spec:

PCI/PCI-X Family of Gigabit Ethernet Controllers Software Developer's Manual
82540EP/EM, 82541xx, 82544GC/EI, 82545GM/EM, 82546GB/EB, and 82547xx
https://www.intel.com/content/dam/doc/manual/pci-pci-x-family-gbe-controllers-software-dev-manual.pdf

These network cards were launched in the 2000s and discontinued in the 2010s, but continue to be a popular choice for virtualization, where they are often referred to as "e1000".
 *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require coqutil.Map.SortedListZ.
Require Import coqutil.Datatypes.ZList.
Import ZList.List.ZIndexNotations. Local Open Scope zlist_scope.
Require Import coqutil.Datatypes.RecordSetters. Import DoubleBraceUpdate.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.old_dma.StateMachineBasedExtSpec.
Require Import bedrock2.WordNotations. Local Open Scope word_scope.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.SepLib.
Require Import bedrock2.SepBulletPoints.
Require Import bedrock2.RecordPredicates.
Require Import bedrock2.e1000_state.
Require Import bedrock2.old_dma.circular_buffer_slice_based_on_list_of_addrs.

Lemma mod_add_unique: forall [l b x1 x2 m],
    l = (b + x1) mod m ->
    l = (b + x2) mod m ->
    0 <= x1 < m ->
    0 <= x2 < m ->
    x1 = x2.
Proof.
  intros.
  rewrite H in H0. clear H.
  apply (f_equal (fun a => (a - b) mod m)) in H0.
  rewrite 2Zminus_mod_idemp_l in H0.
  replace (b + x1 - b) with x1 in H0 by ring.
  replace (b + x2 - b) with x2 in H0 by ring.
  rewrite 2Z.mod_small in H0 by assumption.
  exact H0.
Qed.

Section WithMem.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Byte.byte}.

  Definition read_RDH(s: e1000_state)(post: word -> e1000_state -> Prop): Prop :=
    False. (* TODO add is mGive and mReceive *)

  Local Open Scope sep_bullets_scope.
  Local Open Scope string_scope.

  Inductive e1000_step: e1000_state -> LogItem -> e1000_state -> Prop :=
  (* ## receive-related: *)

  (* read RDH: new RDH can be anywhere between old RDH (incl) and old RDT (excl),
     we receive the memory chunk for each descriptor between old and new RDH,
     as well as the buffers pointed to by them, which contain newly received packets *)
  | read_RDH_step: forall s mRcv new_RDH rdba (packets: list buf),
      s.(get_e1000_config).(rx_queue_base_addr) = Some rdba ->
      len packets <= len s.(rx_queue) < s.(rx_queue_capacity) ->
      \[new_RDH] = (s.(rx_queue_head) + len packets) mod s.(rx_queue_capacity) ->
      (* we get back a (wrapping) slice of the rx queue as well as the corresponding
         buffers *)
      <{ * circular_buffer_slice rx_desc s.(rx_queue_capacity) s.(rx_queue_head)
                                 s.(rx_queue)[:len packets] /[rdba]
         * scattered_array (array (uint 8) s.(rx_buf_size)) packets
             (List.map (fun d => /[d.(rx_desc_addr)]) s.(rx_queue)[:len packets])
        }> mRcv ->
      e1000_step s ((map.empty, "MMIOREAD", [| /[E1000_RDH] |]), (mRcv, [|new_RDH|]))
        s{{ rx_queue := s.(rx_queue)[:len packets];
            rx_queue_head := (s.(rx_queue_head) + len packets) mod s.(rx_queue_capacity) }}

  (* write RDT: software may set new RDT to anywhere between old RDT (incl) and
     RDH (excl, because otherwise queue considered empty), and by doing so, abandons
     the memory chunks corresponding to these descriptors and the buffers pointed to
     by them, thus providing more space for hardware to store received packets *)
  | write_RDT_step: forall s mGive new_RDT new_descs rdba (fillable: list buf),
      (* Note: strict < because otherwise we had head=tail which would be interpreted
         as an empty circular buffer *)
      len s.(rx_queue) + len fillable < s.(rx_queue_capacity) ->
      s.(get_e1000_config).(rx_queue_base_addr) = Some rdba ->
      \[new_RDT] = (s.(rx_queue_head) + len s.(rx_queue) + len fillable)
                     mod s.(rx_queue_capacity) ->
      len fillable = len new_descs ->
      <{ * circular_buffer_slice rx_desc s.(rx_queue_capacity) s.(rx_queue_head)
                                 new_descs /[rdba]
         * scattered_array (array (uint 8) s.(rx_buf_size)) fillable
             (List.map (fun d => /[d.(rx_desc_addr)]) new_descs)
        }> mGive ->
      e1000_step s ((mGive, "MMIOWRITE", [| /[E1000_RDT]; new_RDT |]), (map.empty, nil))
        s{{ rx_queue := (s.(rx_queue) ++ new_descs)%list }}
        (* no need to update rx_queue_tail because it is inferred from
           rx_queue_head and len rx_queue *)

  (* ## transmit-related *)

  (* read TDH: new TDH can be anywhere between old TDH (incl) and TDT (excl),
     increased TDH means some packets were sent, and we get back the memory chunk
     for each descriptor between old and new TDH, as well as the buffers pointed to
     by them, so we can start reusing these descriptors & buffers for new packets *)
  | read_TDH_step: forall s mRcv new_TDH tdba buf_addrs (packets: list buf),
      s.(get_e1000_config).(tx_queue_base_addr) = Some tdba ->
      len packets <= len s.(tx_queue) < s.(tx_queue_capacity) ->
      buf_addrs = List.map (fun d => d.(tx_desc_addr)) s.(tx_queue)[:len packets] ->
      map.getmany_of_list s.(tx_bufs) buf_addrs = Some packets ->
      \[new_TDH] = (s.(tx_queue_head) + len packets) mod s.(tx_queue_capacity) ->
      (* we get back a (wrapping) slice of the tx queue as well as the corresponding
         buffers *)
      <{ * circular_buffer_slice tx_desc s.(tx_queue_capacity) s.(tx_queue_head)
                                 s.(tx_queue)[:len packets] /[tdba]
         * layout_absolute (List.map (fun pkt => array' (uint 8) pkt) packets)
                           (List.map word.of_Z buf_addrs)
        }> mRcv ->
      e1000_step s ((map.empty, "MMIOREAD", [| /[E1000_TDH] |]), (mRcv, [|new_TDH|]))
        s{{ tx_queue := s.(tx_queue)[:len packets];
            tx_queue_head := (s.(tx_queue_head) + len packets) mod s.(tx_queue_capacity);
            tx_bufs := map.remove_many s.(tx_bufs) buf_addrs }}

  (* write TDT: software may set new TDT to anywhere between old TDT (incl) and
     TDH (excl, because otherwise queue considered empty), and by doing so, indicates
     that between old and new TDT, there are new packets to be sent, and yields
     the descriptor chunks and the buffers pointed to by them to hardware *)
  | write_TDT_step: forall s mGive new_TDT tdba new_descs buf_addrs tx_bufs'
                           (packets: list buf),
      s.(get_e1000_config).(tx_queue_base_addr) = Some tdba ->
      len s.(tx_queue) + len packets < s.(tx_queue_capacity) ->
      buf_addrs = List.map (fun d => d.(tx_desc_addr)) new_descs ->
      map.putmany_of_list_zip buf_addrs packets s.(tx_bufs) = Some tx_bufs' ->
      \[new_TDT] = (s.(tx_queue_head) + len s.(tx_queue) + len packets)
                     mod s.(tx_queue_capacity) ->
      (* we get back a (wrapping) slice of the tx queue as well as the corresponding
         buffers *)
      <{ * circular_buffer_slice tx_desc s.(tx_queue_capacity) s.(tx_queue_head)
                                 new_descs /[tdba]
         * layout_absolute (List.map (fun pkt => array' (uint 8) pkt) packets)
                           (List.map word.of_Z buf_addrs)
        }> mGive ->
      e1000_step s ((mGive, "MMIOWRITE", [| /[E1000_TDT]; new_TDT |]), (map.empty, nil))
        s{{ tx_queue := (s.(tx_queue) ++ new_descs)%list;
            tx_bufs := tx_bufs' }}
  .

  Global Instance ext_spec: ExtSpec :=
    StateMachineBasedExtSpec.ext_spec is_initial_e1000_state e1000_step.

  Axiom TODO: False.

  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma steps_agree_on_unique_state_fields: forall s1 s2 e s1' s2',
      agree_on_unique_state_fields s1 s2 ->
      e1000_step s1 e s1' ->
      e1000_step s2 e s2' ->
      agree_on_unique_state_fields s1' s2'.
  Proof.
    unfold is_initial_e1000_state, agree_on_unique_state_fields.
    intros. destruct s1 as [ [ ] ]; destruct s2 as [ [ ] ]; cbn -[map.empty map.rep] in *.
    inversion H0; clear H0; subst; inversion H1; clear H1; subst; record.simp; fwd.
    all: try lazymatch goal with
      | H: /[_] = /[_] |- _ =>
          eapply word.of_Z_inj_small in H;
          [ discriminate H
          | destruct width_cases as [W | W]; rewrite W; cbv;
            clear; intuition congruence .. ]
      end.
    - lazymatch goal with
      | H1: _ = (_ + _) mod _, H2: _ = (_ + _) mod _ |- _ =>
          rewrite <- (mod_add_unique H1 H2 ltac:(lia) ltac:(lia)) in *
      end.
      auto 10.
    - lazymatch goal with
      | H1: _ = (_ + _) mod _, H2: _ = (_ + _) mod _ |- _ =>
          pose proof (mod_add_unique H1 H2 ltac:(lia) ltac:(lia)) as H_len_fillable
      end.
      rewrite H_len_fillable in *.
      assert (len new_descs = len new_descs0) as H_len_new_descs by lia.
      replace new_descs with new_descs0 in * by case TODO. (* because in same mGive *)
      auto 10.
    - lazymatch goal with
      | H1: _ = (_ + _) mod _, H2: _ = (_ + _) mod _ |- _ =>
          pose proof (mod_add_unique H1 H2 ltac:(lia) ltac:(lia)) as H_len_packets
      end.
      rewrite H_len_packets in *.
      auto 10.
    - lazymatch goal with
      | H1: _ = (_ + _) mod _, H2: _ = (_ + _) mod _ |- _ =>
          pose proof (mod_add_unique H1 H2 ltac:(lia) ltac:(lia)) as H_len_packets
      end.
      rewrite H_len_packets in *.
      do 2 match goal with
      | H: _ |- _ => eapply map.putmany_of_list_zip_sameLength in H
      end.
      rewrite List.map_length in *.
      assert (len new_descs = len new_descs0) as H_len_new_descs by lia.
      replace new_descs with new_descs0 in * by case TODO. (* because in same mGive *)
      auto 10.
  Qed.

  Lemma states_of_same_trace_agree_on_unique_state_fields: forall [t s1 s2],
      trace_can_lead_to is_initial_e1000_state e1000_step t s1 ->
      trace_can_lead_to is_initial_e1000_state e1000_step t s2 ->
      agree_on_unique_state_fields s1 s2.
  Proof.
    induction t; simpl; intros.
    - apply initial_states_agree_on_unique_state_fields; assumption.
    - fwd. eapply steps_agree_on_unique_state_fields. 2-3: eassumption. eauto.
  Qed.

  Global Instance ext_spec_ok: ext_spec.ok ext_spec.
  Proof.
    apply StateMachineBasedExtSpec.ext_spec_ok.
    intros. inversion H3; subst; clear H3; inversion H4; subst; clear H4.
    all: try lazymatch goal with
      | H: /[_] = /[_] |- _ =>
          eapply word.of_Z_inj_small in H;
          [ discriminate H
          | destruct width_cases as [W | W]; rewrite W; cbv;
            clear; intuition congruence .. ]
      end.
    - (* read_RDH_step *)
      reflexivity.
    - (* write_RDT_step *)
      lazymatch goal with
      | H: sep _ _ _ |- _ => destruct H as (mGive2a & mGive2b & D2 & M2a & M2b)
      end.
      lazymatch goal with
      | H: sep _ _ _ |- _ => destruct H as (mGive1a & mGive1b & D1 & M1a & M1b)
      end.
      (* uniqueness stuff: *)
      lazymatch goal with
      | H1: trace_can_lead_to _ _ _ _, H2: trace_can_lead_to _ _ _ _ |- _ =>
          pose proof (states_of_same_trace_agree_on_unique_state_fields H1 H2) as HU
      end.
      unfold agree_on_unique_state_fields in HU.
      fwd.
      replace (rx_queue s2) with (rx_queue s1) in * by congruence.
      replace (rx_queue_base_addr s2) with (rx_queue_base_addr s1) in * by congruence.
      replace (rx_queue_capacity s2) with (rx_queue_capacity s1) in * by congruence.
      replace (rx_buf_size s2) with (rx_buf_size s1) in * by congruence.
      replace (rx_queue_head s2) with (rx_queue_head s1) in * by congruence.
      rename fillable0 into fillable2, fillable into fillable1.
      rename new_descs0 into new_descs2, new_descs into new_descs1.
      lazymatch goal with
      | H1: _ = (_ + _) mod _, H2: _ = (_ + _) mod _ |- _ =>
          pose proof (mod_add_unique H1 H2 ltac:(lia) ltac:(lia)) as H_len_fillable
      end.
      assert (len new_descs1 = len new_descs2) by lia.
      (* In M1a and M2a, we have the same base address, start index, modulus, and
         list length, so: *)
      assert (map.same_domain mGive1a mGive2a) as Hsd by case TODO.
      (* Because of D1, D2, H1, H2: mGive1a and mGive2a are part of the same big m,
         so since they have the same footprint, they must also have the same values: *)
      assert (mGive1a = mGive2a) by case TODO.
      subst mGive2a. clear Hsd.
      (* But now, M1a and M2a imply: *)
      replace new_descs2 with new_descs1 in * by case TODO.
      set (addrs := (List.map (fun d : rx_desc_t => /[rx_desc_addr d]) new_descs1)) in *.
      move M1b at bottom. move M2b at bottom.
      (* same addresses in M1b and M2b and same element size means same footprint: *)
      assert (map.same_domain mGive1b mGive2b) as Hsd by case TODO.
      (* Because of D1, D2, H1, H2: mGive1b and mGive2b are part of the same big m,
         so since they have the same footprint, they must also have the same values: *)
      assert (mGive1b = mGive2b) by case TODO.
      subst mGive2b. clear Hsd.
      (* But now, M1b and M2b imply: *)
      replace fillable2 with fillable1 in * by case TODO.
      unfold map.split in D1, D2.
      destruct D1 as (? & D1). destruct D2 as (? & D2).
      subst mGive1 mGive2.
      reflexivity.
    - reflexivity.
    - case TODO.
  Qed.

  Definition trace_state_satisfies(t: trace)(P: e1000_state -> Prop): Prop :=
    (exists s, trace_can_lead_to is_initial_e1000_state e1000_step t s) /\
    (forall s, trace_can_lead_to is_initial_e1000_state e1000_step t s -> P s).

  Context {locals: map.map String.string word}.

  (* read RDH: new RDH can be anywhere between old RDH (incl) and old RDT (excl),
     we receive the memory chunk for each descriptor between old and new RDH,
     as well as the buffers pointed to by them, which contain newly received packets *)
  Lemma wp_read_RDH: forall e cfg old_RDH old_rx_descs rdba t m l r post,
      cfg.(rx_queue_base_addr) = Some rdba ->
      trace_state_satisfies t (fun s => e1000_ok cfg s /\
         s.(rx_queue_head) = old_RDH /\ s.(rx_queue) = old_rx_descs) ->
      (forall (m' mRcv: mem) (packets: list buf),
          map.split m' mRcv m ->
          len packets <= len old_rx_descs ->
          let new_RDH := /[(old_RDH + len packets) mod cfg.(rx_queue_capacity)] in
          (* we get back a (wrapping) slice of the rx queue as well as the corresponding
             buffers *)
          <{ * circular_buffer_slice rx_desc cfg.(rx_queue_capacity) old_RDH
                                     old_rx_descs[:len packets] /[rdba]
             * scattered_array (array (uint 8) cfg.(rx_buf_size)) packets
                   (List.map (fun d => /[d.(rx_desc_addr)]) (old_rx_descs[:len packets]))
          }> mRcv ->
          post (cons ((map.empty, "MMIOREAD", [| /[E1000_RDH] |]), (mRcv, [|new_RDH|])) t)
               m' (map.put l r new_RDH)) ->
      exec e (cmd.interact [|r|] "MMIOREAD" [|expr.literal E1000_RDH|]) t m l post.
  Proof.
    intros.
    unfold trace_state_satisfies in *. fwd.
    eapply exec.interact_cps.
    3: {
      unfold ext_spec, StateMachineBasedExtSpec.ext_spec.
      split. 1: eauto.
      intros. split.
      - do 3 eexists. eapply read_RDH_step.
        (* TODO the "exists step" part needs to be in the hypotheses *)
  Abort.

End WithMem.
