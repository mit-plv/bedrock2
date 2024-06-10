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
            (* start state *)
            state ->
            (* label on transition: pair of input & output
              input: memory given away, function name, list of arguments
              output: memory received back, return values *)
            ((mem * String.string * list word) * (mem * list word)) ->
            (* end state *)
            state ->
            Prop).

  Fixpoint trace_can_lead_to(t: trace)(s: state): Prop :=
    match t with
    | nil => is_initial_state s
    | cons e t' => exists s_prev, trace_can_lead_to t' s_prev /\ step s_prev e s
    end.

  Definition ext_spec: ExtSpec :=
    fun (t: trace)(mGive: mem)(action: String.string)(args: list word)
        (post: mem -> list word -> Prop) =>
      (exists s, trace_can_lead_to t s) /\
      (* ^ required for unique_mGive_footprint and maybe in other places too *)
      (forall s, trace_can_lead_to t s ->
         (exists rets mReceive s', step s ((mGive, action, args), (mReceive, rets)) s') /\
         (forall rets mReceive s', step s ((mGive, action, args), (mReceive, rets)) s' ->
                                  post mReceive rets)).

  Hypothesis action_and_args_determine_mGive:
    forall t m action args
           s1 mGive1 mKeep1 mReceive1 rets1 s1'
           s2 mGive2 mKeep2 mReceive2 rets2 s2',
      trace_can_lead_to t s1 ->
      trace_can_lead_to t s2 ->
      map.split m mKeep1 mGive1 ->
      map.split m mKeep2 mGive2 ->
      step s1 (mGive1, action, args, (mReceive1, rets1)) s1' ->
      step s2 (mGive2, action, args, (mReceive2, rets2)) s2' ->
      mGive1 = mGive2.

  Lemma ext_spec_ok: ext_spec.ok ext_spec.
  Proof.
    unfold ext_spec. constructor.
    - intros *. intros Hs1 Hs2. intros ((s1 & L1) & H1) ((s2 & L2) & H2).
      specialize H1 with (1 := L1). destruct H1 as (A1 & B1).
      specialize H2 with (1 := L2). destruct H2 as (A2 & B2).
      destruct A1 as (rets1 & mReceive1 & s1' & A1).
      destruct A2 as (rets2 & mReceive2 & s2' & A2).
      eapply action_and_args_determine_mGive; cycle -2; eassumption.
    - unfold Morphisms.Proper, Morphisms.respectful, Morphisms.pointwise_relation,
        Basics.impl.
      intros. destruct H0 as (HE & H0). split. 1: exact HE.
      intros. specialize H0 with (1 := H1). destruct H0 as (A & B).
      split. 1: exact A. eauto.
    - intros. destruct H as (HE & H). destruct H0 as (_ & H0). split. 1: exact HE.
      intros. specialize H with (1 := H1). specialize H0 with (1 := H1).
      destruct H as (A & B). destruct H0 as (C & D). split. 1: exact A. eauto.
  Qed.

End WithMem.
