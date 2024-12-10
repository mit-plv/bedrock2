(*
Formalization of a subset of the functionality of Intel's 8254x Network Interface Cards.

PDF Spec:

PCI/PCI-X Family of Gigabit Ethernet Controllers Software Developer's Manual
82540EP/EM, 82541xx, 82544GC/EI, 82545GM/EM, 82546GB/EB, and 82547xx
https://www.intel.com/content/dam/doc/manual/pci-pci-x-family-gbe-controllers-software-dev-manual.pdf

These network cards were launched in the 2000s and discontinued in the 2010s, but continue to be a popular choice for virtualization, where they are often referred to as "e1000".
 *)

From Coq Require Import String.
From Coq Require Import ZArith.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require coqutil.Map.SortedListZ.
Require Import coqutil.Datatypes.ZList.
Import ZList.List.ZIndexNotations. Local Open Scope zlist_scope.
Require Import coqutil.Datatypes.RecordSetters. Import DoubleBraceUpdate.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.old_dma.StateMachineBasedExtSpec_wp.
Require Import bedrock2.WordNotations. Local Open Scope word_scope.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.SepLib.
Require Import bedrock2.SepBulletPoints.
Require Import bedrock2.RecordPredicates.
Require Import bedrock2.e1000_state.
Require Import bedrock2.old_dma.circular_buffer_slice_based_on_list_of_addrs.

Section WithMem.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Byte.byte}.

(* Operations:

- receive-related:
  + read RDH: new RDH can be anywhere between old RDH (incl) and RDT (excl),
    we receive the memory chunk for each descriptor between old and new RDH,
    as well as the buffers pointed to by them, which contain newly received packets
  + write RDT: software may set new RDT to anywhere between old RDT (incl) and
    RDH (excl, because otherwise queue considered empty), and by doing so, abandons
    the memory chunks corresponding to these descriptors and the buffers pointed to
    by them, thus providing more space for hardware to store received packets
- transmit-related:
  + read TDH: new TDH can be anywhere between old TDH (incl) and TDT (excl),
    increased TDH means some packets were sent, and we get back the memory chunk
    for each descriptor between old and new TDH, as well as the buffers pointed to
    by them, so we can start reusing these descriptors & buffers for new packets
  + write TDT: software may set new TDT to anywhere between old TDT (incl) and
    TDH (excl, because otherwise queue considered empty), and by doing so, indicates
    that between old and new TDT, there are new packets to be sent, and yields
    the descriptor chunks and the buffers pointed to by them to hardware
*)

  Definition read_RDH(s: e1000_state)(post: word -> e1000_state -> Prop): Prop :=
    False. (* TODO add is mGive and mReceive *)

  Local Open Scope sep_bullets_scope.
  Local Open Scope string_scope.

  Inductive e1000_step:
    (* intial state *)
    e1000_state ->
    (* input to external call: memory given away, function name, list of args *)
    mem -> string -> list word ->
    (* output (as a arguments to a postcondition):
       memory received back, return values, new state *)
    (mem -> list word -> e1000_state -> Prop) ->
    Prop :=
  (* read RDH: new RDH can be anywhere between old RDH (incl) and old RDT (excl),
     we receive the memory chunk for each descriptor between old and new RDH,
     as well as the buffers pointed to by them, which contain newly received packets *)
  | read_RDH_step: forall s rdba (post: mem -> list word -> e1000_state -> Prop),
      s.(get_e1000_config).(rx_queue_base_addr) = Some rdba ->
      (forall mRcv new_RDH (packets: list buf),
          len packets <= len s.(rx_queue) ->
          \[new_RDH] = (s.(rx_queue_head) + len packets) mod s.(rx_queue_capacity) ->
          (* we get back a (wrapping) slice of the rx queue as well as the corresponding
             buffers *)
          <{ * circular_buffer_slice rx_desc s.(rx_queue_capacity) s.(rx_queue_head)
                                     s.(rx_queue)[:len packets] /[rdba]
             * scattered_array (array (uint 8) s.(rx_buf_size)) packets
                 (List.map (fun d => /[d.(rx_desc_addr)]) s.(rx_queue)[:len packets])
            }> mRcv ->
          post mRcv [|new_RDH|]
            s{{ rx_queue := s.(rx_queue)[:len packets];
                rx_queue_head := (s.(rx_queue_head) + len packets) mod
                                 s.(rx_queue_capacity) }}) ->
      e1000_step s map.empty "MMIOREAD" [| /[E1000_RDH] |] post
  (* write RDT: software may set new RDT to anywhere between old RDT (incl) and
     RDH (excl, because otherwise queue considered empty), and by doing so, abandons
     the memory chunks corresponding to these descriptors and the buffers pointed to
     by them, thus providing more space for hardware to store received packets *)
  | write_RDT_step: forall s mGive new_RDT new_descs rdba (fillable: list buf) post,
      (* Note: strict < because otherwise we had head=tail which would be interpreted
         as an empty circular buffer *)
      len s.(rx_queue) + len fillable < s.(rx_queue_capacity) ->
      s.(get_e1000_config).(rx_queue_base_addr) = Some rdba ->
      \[new_RDT] = (s.(rx_queue_head) + len s.(rx_queue) + len fillable)
                     mod s.(rx_queue_capacity) ->
      len fillable = len new_descs ->
      <{ * circular_buffer_slice rx_desc s.(rx_queue_capacity) s.(rx_queue_head)
                  (s.(rx_queue) ++ new_descs)%list /[rdba]
         * scattered_array (array (uint 8) s.(rx_buf_size)) fillable
             (List.map (fun d => /[d.(rx_desc_addr)]) (s.(rx_queue) ++ new_descs)%list)
        }> mGive ->
      post map.empty nil s{{ rx_queue := (s.(rx_queue) ++ new_descs)%list }} ->
        (* no need to update rx_queue_tail because it is inferred from
           rx_queue_head and len rx_queue *)
      e1000_step s mGive "MMIOWRITE" [| /[E1000_RDT]; new_RDT |] post
  .


  Lemma weaken_e1000_step: forall s mGive action args post1 post2,
      e1000_step s mGive action args post1 ->
      (forall mReceive rets s', post1 mReceive rets s' -> post2 mReceive rets s') ->
      e1000_step s mGive action args post2.
  Proof.
    intros. inversion H; subst; clear H.
    - eapply read_RDH_step. 1: eassumption. eauto.
    - eapply write_RDT_step; eauto.
  Qed.

  Definition is_unique_field{S F: Type}(R: S -> (S -> Prop) -> Prop)(field: S -> F)
    (s1 s2: S): Prop :=
    forall post1 post2,
      R s1 post1 ->
      R s2 post2 ->
      exists f, R s1 (fun s1' => post1 s1' /\ field s1' = f) /\
                R s2 (fun s2' => post2 s2' /\ field s2' = f).

  Lemma rx_queue_head_unique_initial: forall s1 s2,
      is_initial_e1000_state s1 ->
      is_initial_e1000_state s2 ->
      is_unique_field (fun s post => post s) rx_queue_head s1 s2.
  Proof.
    unfold is_unique_field, is_initial_e1000_state.
    intros. fwd. eexists. eauto.
  Qed.

  Lemma rx_queue_head_unique_step: forall s1 s2 mGive action args,
      s1.(rx_queue_head) = s2.(rx_queue_head) ->
      is_unique_field (fun s post => e1000_step s mGive action args
                                       (fun mRcv rets s' => post s'))
        rx_queue_head s1 s2.
  Proof.
    unfold is_unique_field. intros.
    inversion H0; subst; clear H0; inversion H1; subst; clear H1.
    - eexists. split; econstructor; try eassumption; intros; split; eauto.
      + record.simp.
  Abort.

  Definition trace_state_satisfies: trace -> (e1000_state -> Prop) -> Prop :=
    trace_leads_to_state_satisfying is_initial_e1000_state e1000_step.

  (* Given a trace, some state fields (currently, actually, all, but we don't want to
     rely on it) are uniquely determined: *)
  Lemma unique_state_fields: forall t post,
      trace_state_satisfies t post ->
      exists rdba tdba rxcap txcap rxsz rxq txq rdh tdh,
      trace_state_satisfies t (fun s => post s /\
        s.(rx_queue_base_addr) = rdba /\
        s.(tx_queue_base_addr) = tdba /\
        s.(rx_queue_capacity) = rxcap /\
        s.(tx_queue_capacity) = txcap /\
        s.(rx_buf_size) = rxsz /\
        s.(rx_queue) = rxq /\
        s.(tx_queue) = txq /\
        s.(rx_queue_head) = rdh /\
        s.(tx_queue_head) = tdh).
  Proof.
    unfold trace_state_satisfies, trace_leads_to_state_satisfying.
    intros.
    (* apply_snoc_trace_induction
       exists u, forall s
       vs
       forall s, exists u *)
  Admitted.

  Global Instance ext_spec: ExtSpec :=
    StateMachineBasedExtSpec_wp.ext_spec is_initial_e1000_state e1000_step.

  Global Instance ext_spec_ok: ext_spec.ok ext_spec.
  Proof.
    apply StateMachineBasedExtSpec_wp.ext_spec_ok.
    intros.
  Admitted.

  Context {locals: map.map String.string word}.

  (* read RDH: new RDH can be anywhere between old RDH (incl) and old RDT (excl),
     we receive the memory chunk for each descriptor between old and new RDH,
     as well as the buffers pointed to by them, which contain newly received packets *)
  Lemma wp_read_RDH: forall e cfg rdba old_RDH old_rx_descs t m l r
                            (post: trace -> mem -> locals -> Prop),
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
    unfold trace_state_satisfies in *.
    eapply exec.interact_cps.
    3: {
      unfold ext_spec, StateMachineBasedExtSpec_wp.ext_spec.
  Abort.

End WithMem.
