From Coq Require Import String.
From Coq Require Import ZArith.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import bedrock2.Semantics.

Section WithMem.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Byte.byte}.

  Context {state: Type}.
  Context (is_initial_state: state -> Prop).
  Context (step:
            (* intial state *)
            state ->
            (* input to external call: memory given away, function name, list of args *)
            mem -> string -> list word ->
            (* output (as a arguments to a postcondition):
               memory received back, return values, new state *)
            (mem -> list word -> state -> Prop) ->
            Prop).

  Fixpoint apply_trace(s0: state)(t: trace)(post: state -> Prop): Prop :=
    match t with
    | nil => post s0
    | cons ((mGive, action, args), (mReceive, rets)) t' =>
        apply_trace s0 t' (fun s1 =>
          step s1 mGive action args (fun mReceive' rets' s2 =>
            mReceive' = mReceive ->
            rets' = rets ->
            post s2))
    end.

  Definition trace_leads_to_state_satisfying(t: trace)(post: state -> Prop): Prop :=
    forall s, is_initial_state s -> apply_trace s t post.

  Lemma apply_trace_app: forall t1 t2 s post,
      (* note the reversed order: elements at the head of the trace happened last! *)
      apply_trace s t2 (fun s' => apply_trace s' t1 post) ->
      apply_trace s (List.app t1 t2) post.
  Proof.
    induction t1; simpl; intros.
    - assumption.
    - destruct a as (((mGive & action) & args) & (mReceive & rets)).
      eapply IHt1. exact H.
  Qed.

  Lemma invert_apply_trace_app: forall t1 t2 s post,
      apply_trace s (List.app t1 t2) post ->
      apply_trace s t2 (fun s' => apply_trace s' t1 post).
  Proof.
    induction t1; simpl; intros.
    - assumption.
    - destruct a as (((mGive & action) & args) & (mReceive & rets)).
      eapply IHt1. exact H.
  Qed.

  Lemma apply_trace_snoc: forall t mGive action args mReceive rets s post,
      step s mGive action args (fun mReceive' rets' s' =>
        mReceive' = mReceive -> rets' = rets -> apply_trace s' t post) ->
      apply_trace s (List.app t (cons ((mGive, action, args), (mReceive, rets)) nil)) post.
  Proof. intros. eapply apply_trace_app. simpl. assumption. Qed.

  Lemma invert_apply_trace_snoc: forall t mGive action args mRcv rets s post,
      apply_trace s (List.app t (cons ((mGive, action, args), (mRcv, rets)) nil)) post ->
      step s mGive action args (fun mRcv' rets' s' =>
        mRcv' = mRcv -> rets' = rets -> apply_trace s' t post).
  Proof. intros. eapply invert_apply_trace_app in H. simpl in H. assumption. Qed.

  Hypothesis weaken_step: forall s mGive action args
                                 (post1 post2: mem -> list word -> state -> Prop),
      step s mGive action args post1 ->
      (forall mReceive rets s', post1 mReceive rets s' -> post2 mReceive rets s') ->
      step s mGive action args post2.

  Lemma weaken_apply_trace: forall t s (post1 post2: state -> Prop),
      apply_trace s t post1 ->
      (forall s, post1 s -> post2 s) ->
      apply_trace s t post2.
  Proof.
    induction t; simpl; intros.
    - eauto.
    - destruct a as (((mGive & action) & args) & (mReceive & rets)).
      eapply IHt. 1: exact H. cbv beta.
      intros. eapply weaken_step. 1: eassumption. cbv beta. eauto.
  Qed.

  Lemma apply_trace_induction: forall s0 inv,
      inv s0 ->
      (forall s, inv s -> forall mGive action args,
            step s mGive action args (fun _ _ s' => inv s')) ->
      forall t, apply_trace s0 t inv.
  Proof.
    induction t; simpl; intros.
    - assumption.
    - destruct a as (((mGive & action) & args) & (mReceive & rets)).
      eapply weaken_apply_trace. 1: exact IHt. eauto.
  Qed.

  Lemma apply_snoc_trace_induction: forall P: state -> trace -> (state -> Prop) -> Prop,
      (forall s (post: state -> Prop), post s -> P s nil post) ->
      (forall t s mGive action args mReceive rets mid post,
          step s mGive action args mid ->
          (forall s', mid mReceive rets s' -> apply_trace s' t post /\ P s' t post) ->
          P s (List.app t (cons ((mGive, action, args), (mReceive, rets)) nil)) post) ->
      forall t s post, apply_trace s t post -> P s t post.
  Proof.
    intros until t.
    set (n := List.length t).
    pose proof (eq_refl: n = List.length t) as HL. clearbody n.
    revert t HL. induction n; intros.
    - destruct t. 2: discriminate HL. simpl in H. eauto.
    - pose proof (List.firstn_skipn n t) as Hsplit.
      pose proof (List.length_skipn n t) as HL2.
      rewrite <- HL in HL2. rewrite Nat.sub_succ_l in HL2 by reflexivity.
      rewrite Nat.sub_diag in HL2.
      destruct (List.skipn n t) as [ |h' t']. 1: discriminate HL2.
      destruct t'. 2: discriminate HL2.
      clear HL2. set (tl := List.firstn n t) in *. clearbody tl. subst t.
      rewrite List.app_length in HL. simpl in HL. rewrite Nat.add_comm in HL.
      eapply Nat.succ_inj in HL. specialize IHn with (1 := HL).
      destruct h' as (((mGive & action) & args) & (mReceive & rets)).
      eapply invert_apply_trace_snoc in H1.
      eapply H0. 1: exact H1. cbv beta.
      intros * HA. clear -HA IHn. eauto.
  Qed.

  Lemma weaken_trace_leads_to_state_satisfying: forall t (post1 post2: state -> Prop),
      trace_leads_to_state_satisfying t post1 ->
      (forall s, post1 s -> post2 s) ->
      trace_leads_to_state_satisfying t post2.
  Proof. unfold trace_leads_to_state_satisfying. eauto using weaken_apply_trace. Qed.

  Definition ext_spec: ExtSpec :=
    fun (t: trace)(mGive: mem)(action: String.string)(args: list word)
        (post: mem -> list word -> Prop) =>
      trace_leads_to_state_satisfying t (fun s =>
        step s mGive action args (fun mReceive rets s' => post mReceive rets)).

  Lemma ext_spec_ok: ext_spec.ok ext_spec.
  Proof.
    unfold ext_spec. constructor.
    - unfold trace_leads_to_state_satisfying. intros. (* ?? *) admit.
    - unfold Morphisms.Proper, Morphisms.respectful, Morphisms.pointwise_relation,
        Basics.impl.
      intros. eapply weaken_trace_leads_to_state_satisfying. 1: eassumption.
      cbv beta. intros. eapply weaken_step. 1: eassumption. cbv beta. clear -H. eauto.
    - intros. admit.
  Admitted.

End WithMem.
