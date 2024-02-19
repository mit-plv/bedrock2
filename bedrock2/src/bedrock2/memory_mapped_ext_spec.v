Require Import Coq.Strings.String. Local Open Scope string_scope.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations. Local Open Scope list_scope.
Require Import coqutil.Tactics.fwd coqutil.Tactics.autoforward.
Require coqutil.Datatypes.String.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import bedrock2.Semantics.
Local Open Scope string_scope.

#[local] Instance string_of_nbytes_inj: forall nbytes1 nbytes2,
    autoforward (String.of_nat (nbytes1 * 8) = String.of_nat (nbytes2 * 8))
                (nbytes1 = nbytes2).
Proof.
  intros * H.
  eapply String.of_nat_inj in H.
  eapply PeanoNat.Nat.mul_cancel_r. 2: eassumption.
  discriminate.
Qed.

Class MemoryMappedExtCalls{width: Z}{BW: Bitwidth width}
                          {word: word.word width} {mem: map.map word Byte.byte} := {
  mmio_read_step:
    nat -> (* how many bytes to read *)
    trace -> (* trace of events that happened so far *)
    word -> (* address to be read *)
    (word -> mem -> Prop) -> (* postcondition on returned value and memory *)
    Prop;
  mmio_write_step:
    nat -> (* how many bytes to write *)
    trace -> (* trace of events that happened so far *)
    word -> (* address to be written *)
    word -> (* value to be written *)
    mem -> (* memory whose ownership is passed to the external world *)
    Prop;
  (* same signatures for accessing shared memory, i.e. memory that has been passed
     to the external world, but might still be accessible under some conditions,
     and can change each time it is looked at *)
  shared_mem_read_step:
    nat -> (* how many bytes to read *)
    trace -> (* trace of events that happened so far *)
    word -> (* address to be read *)
    (word -> mem -> Prop) -> (* postcondition on returned value and memory *)
    Prop;
  shared_mem_write_step:
    nat -> (* how many bytes to write *)
    trace -> (* trace of events that happened so far *)
    word -> (* address to be written *)
    word -> (* value to be written *)
    mem -> (* memory whose ownership is passed to the external world *)
    Prop;
}.

Section WithMem.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word}.

  Inductive ext_spec{mmio_ext_calls: MemoryMappedExtCalls}: ExtSpec :=
  | ext_spec_mmio_read: forall t addr n post,
      mmio_read_step n t addr (fun v mRcv => post mRcv [v]) ->
      ext_spec t map.empty ("MMIO_READ" ++ String.of_nat (n * 8)) [addr] post
  | ext_spec_mmio_write: forall t addr n mGive v post,
      mmio_write_step n t addr v mGive ->
      post map.empty nil ->
      ext_spec t mGive ("MMIO_WRITE" ++ String.of_nat (n * 8)) [addr; v] post
  | ext_spec_shared_mem_read: forall t addr n post,
      shared_mem_read_step n t addr (fun v mRcv => post mRcv [v]) ->
      ext_spec t map.empty ("SHARED_MEM_READ" ++ String.of_nat (n * 8)) [addr] post
  | ext_spec_shared_mem_write: forall t addr n mGive v post,
      shared_mem_write_step n t addr v mGive ->
      post map.empty nil ->
      ext_spec t mGive ("SHARED_MEM_WRITE" ++ String.of_nat (n * 8)) [addr; v] post.

  Class MemoryMappedExtCallsOk(mmio_ext_calls: MemoryMappedExtCalls): Prop := {
    weaken_mmio_read_step: forall t addr n post1 post2,
      mmio_read_step n t addr post1 ->
      (forall v mRcv, post1 v mRcv -> post2 v mRcv) ->
      mmio_read_step n t addr post2;
    intersect_mmio_read_step: forall t addr n post1 post2,
      mmio_read_step n t addr post1 ->
      mmio_read_step n t addr post2 ->
      mmio_read_step n t addr (fun v mRcv => post1 v mRcv /\ post2 v mRcv);
    mmio_write_step_unique_mGive: forall m t n mKeep1 mKeep2 mGive1 mGive2 addr val,
      map.split m mKeep1 mGive1 ->
      map.split m mKeep2 mGive2 ->
      mmio_write_step n t addr val mGive1 ->
      mmio_write_step n t addr val mGive2 ->
      mGive1 = mGive2;
    weaken_shared_mem_read_step: forall t addr n post1 post2,
      shared_mem_read_step n t addr post1 ->
      (forall v mRcv, post1 v mRcv -> post2 v mRcv) ->
      shared_mem_read_step n t addr post2;
    intersect_shared_mem_read_step: forall t addr n post1 post2,
      shared_mem_read_step n t addr post1 ->
      shared_mem_read_step n t addr post2 ->
      shared_mem_read_step n t addr (fun v mRcv => post1 v mRcv /\ post2 v mRcv);
    shared_mem_write_step_unique_mGive: forall m t n mKeep1 mKeep2 mGive1 mGive2 addr val,
      map.split m mKeep1 mGive1 ->
      map.split m mKeep2 mGive2 ->
      shared_mem_write_step n t addr val mGive1 ->
      shared_mem_write_step n t addr val mGive2 ->
      mGive1 = mGive2;
  }.

  Lemma weaken_ext_spec{mmio_ext_calls: MemoryMappedExtCalls}
    {mmio_ext_calls_ok: MemoryMappedExtCallsOk mmio_ext_calls}:
    forall t mGive a args post1 post2,
      (forall mRcv rets, post1 mRcv rets -> post2 mRcv rets) ->
      ext_spec t mGive a args post1 ->
      ext_spec t mGive a args post2.
  Proof.
    intros; inversion H0; subst; clear H0;
      constructor; eauto using weaken_mmio_read_step, weaken_shared_mem_read_step.
  Qed.

  Instance ext_spec_ok(mmio_ext_calls: MemoryMappedExtCalls)
    {mmio_ext_calls_ok: MemoryMappedExtCallsOk mmio_ext_calls}: ext_spec.ok ext_spec.
  Proof.
    constructor.
    - (* mGive unique *)
      intros. inversion H1; subst; clear H1; inversion H2; subst; clear H2;
        fwd; eauto using mmio_write_step_unique_mGive, shared_mem_write_step_unique_mGive.
    - (* weaken *)
      unfold Morphisms.Proper, Morphisms.respectful, Morphisms.pointwise_relation,
        Basics.impl. eapply weaken_ext_spec.
    - (* intersect *)
      intros. inversion H; subst; clear H; inversion H0; subst; clear H0; fwd;
        constructor;
        eauto using intersect_mmio_read_step, intersect_shared_mem_read_step.
  Qed.

End WithMem.

#[export] Existing Instance ext_spec.
#[export] Existing Instance ext_spec_ok.
