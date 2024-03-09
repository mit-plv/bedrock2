Require Import Coq.Strings.String. Local Open Scope string_scope.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations. Local Open Scope list_scope.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import bedrock2.Semantics.

Section WithMem.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Byte.byte}.

  Class MMIOExtCalls := {
    read_step: trace -> (* trace of events that happened so far *)
               word -> (* address to be read *)
               (word -> mem -> Prop) -> (* postcondition on returned value and memory *)
               Prop;
    write_step: trace -> (* trace of events that happened so far *)
                word -> (* address to be written *)
                word -> (* value to be written *)
                mem -> (* memory whose ownership is passed to the external world *)
               Prop;
  }.

  Global Instance ext_spec{mmio_ext_calls: MMIOExtCalls}: ExtSpec :=
    fun (t: trace)(mGive: mem)(action: String.string)(args: list word)
        (post: mem -> list word -> Prop) =>
      (action = "MMIOREAD" /\
       mGive = map.empty /\
       exists addr, args = [addr] /\
                    read_step t addr (fun v mRcv => post mRcv [v])) \/
      (action = "MMIOWRITE" /\
       exists addr val, args = [addr; val] /\
                        write_step t addr val mGive).

  Class MMIOExtCallsOk(mmio_ext_calls: MMIOExtCalls): Prop := {
    weaken_read_step: forall t addr post1 post2,
      read_step t addr post1 ->
      (forall v mRcv, post1 v mRcv -> post2 v mRcv) ->
      read_step t addr post2;
    intersect_read_step: forall t addr post1 post2,
      read_step t addr post1 ->
      read_step t addr post2 ->
      read_step t addr (fun v mRcv => post1 v mRcv /\ post2 v mRcv);
    write_step_unique_mGive: forall m t mKeep1 mKeep2 mGive1 mGive2 addr val,
      map.split m mKeep1 mGive1 ->
      map.split m mKeep2 mGive2 ->
      write_step t addr val mGive1 ->
      write_step t addr val mGive2 ->
      mGive1 = mGive2;
  }.

  Global Instance ext_spec_ok(mmio_ext_calls: MMIOExtCalls)
    {mmio_ext_calls_ok: MMIOExtCallsOk mmio_ext_calls}: ext_spec.ok ext_spec.
  Proof.
    constructor.
    - (* mGive unique *)
      unfold ext_spec. intros.
      destruct H1; destruct H2; fwd; try congruence.
      eauto using write_step_unique_mGive.
    - (* weaken *)
      unfold Morphisms.Proper, Morphisms.respectful, Morphisms.pointwise_relation,
        Basics.impl.
      unfold ext_spec. intros.
      destruct H0; [left|right]; fwd; eauto 10 using weaken_read_step.
    - (* intersect *)
      unfold ext_spec. intros.
      destruct H; destruct H0; fwd; try (exfalso; congruence); [left | right];
        eauto 10 using intersect_read_step.
  Qed.

End WithMem.
