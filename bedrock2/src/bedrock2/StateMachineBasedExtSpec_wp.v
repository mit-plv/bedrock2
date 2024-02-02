Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
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

  Fixpoint trace_leads_to_state_satisfying(t: trace)(post: state -> Prop): Prop :=
    match t with
    | nil => forall s, is_initial_state s -> post s
    | cons ((mGive, action, args), (mReceive, rets)) t' =>
        trace_leads_to_state_satisfying t' (fun s =>
          step s mGive action args (fun mReceive' rets' s' =>
            mReceive' = mReceive ->
            rets' = rets ->
            post s'))
    end.

  Hypothesis weaken_step: forall s mGive action args
                                 (post1 post2: mem -> list word -> state -> Prop),
      step s mGive action args post1 ->
      (forall mReceive rets s', post1 mReceive rets s' -> post2 mReceive rets s') ->
      step s mGive action args post2.

  Lemma weaken_trace_leads_to_state_satisfying: forall t (post1 post2: state -> Prop),
      trace_leads_to_state_satisfying t post1 ->
      (forall s, post1 s -> post2 s) ->
      trace_leads_to_state_satisfying t post2.
  Proof.
    induction t; simpl; intros.
    - eauto.
    - destruct a as (((mGive & action) & args) & (mReceive & rets)).
      eapply IHt. 1: exact H. cbv beta.
      intros. eapply weaken_step. 1: eassumption. cbv beta. eauto.
  Qed.

  Definition ext_spec: ExtSpec :=
    fun (t: trace)(mGive: mem)(action: String.string)(args: list word)
        (post: mem -> list word -> Prop) =>
      trace_leads_to_state_satisfying t (fun s =>
        step s mGive action args (fun mReceive rets s' => post mReceive rets)).

  Lemma ext_spec_ok: ext_spec.ok ext_spec.
  Proof.
    unfold ext_spec. constructor.
    - intros. (* ?? *) admit.
    - unfold Morphisms.Proper, Morphisms.respectful, Morphisms.pointwise_relation,
        Basics.impl.
      intros. eapply weaken_trace_leads_to_state_satisfying. 1: eassumption.
      cbv beta. intros. eapply weaken_step. 1: eassumption. cbv beta. clear -H. eauto.
    - intros. admit.
  Admitted.

End WithMem.
