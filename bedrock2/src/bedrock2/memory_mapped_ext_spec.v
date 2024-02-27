Require Import Coq.Strings.String. Local Open Scope string_scope.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List. Import ListNotations. Local Open Scope list_scope.
Require Import coqutil.Datatypes.HList.
Require coqutil.Word.LittleEndian.
Require Import coqutil.Byte.
Require Import coqutil.Tactics.fwd coqutil.Tactics.autoforward.
Require coqutil.Datatypes.String.
Require Import coqutil.Map.Interface coqutil.Map.Domain.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Word.Properties.
Require Import bedrock2.Semantics.
Require Import bedrock2.TraceInspection.
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
                          {word: word.word width}{mem: map.map word Byte.byte} := {
  read_step: forall (sz: nat),
    trace -> (* trace of events that happened so far *)
    word -> (* address to be read *)
    (tuple byte sz -> mem -> Prop) -> (* postcondition on returned value and memory *)
    Prop;
  write_step: forall (sz: nat),
    trace -> (* trace of events that happened so far *)
    word -> (* address to be written *)
    tuple byte sz -> (* value to be written *)
    mem -> (* memory whose ownership is passed to the external world *)
    Prop;
  mmio_addrs: word -> Prop;
}.

Section WithMem.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word}.

  (* Note: This ext_spec is crafted in such a way that no matter how liberal
     read_step and write_step are, all ext calls allowed by this ext_spec can
     be compiled to a RISC-V load or store instruction *)
  Definition ext_spec{mmio_ext_calls: MemoryMappedExtCalls}: ExtSpec :=
    fun (t: trace) (mGive: mem) (action: string) (args: list word)
        (post: mem -> list word -> Prop) =>
      exists n, (n = 1 \/ n = 2 \/ n = 4 \/ (n = 8 /\ width = 64%Z))%nat /\
      ((action = "memory_mapped_extcall_read" ++ String.of_nat (n * 8) /\
        exists addr, args = [addr] /\ mGive = map.empty /\
                     read_step n t addr (fun v mRcv =>
                         post mRcv [word.of_Z (LittleEndian.combine n v)])) \/
       (action = "memory_mapped_extcall_write" ++ String.of_nat (n * 8) /\
        exists addr v, args = [addr; word.of_Z (LittleEndian.combine n v)] /\
                       write_step n t addr v mGive /\
                       post map.empty nil)).

  Definition footprint_list(addr: word)(n: nat): list word :=
    List.unfoldn (word.add (word.of_Z 1)) n addr.

  Class MemoryMappedExtCallsOk(ext_calls: MemoryMappedExtCalls): Prop := {
    weaken_read_step: forall t addr n post1 post2,
      read_step n t addr post1 ->
      (forall v mRcv, post1 v mRcv -> post2 v mRcv) ->
      read_step n t addr post2;
    intersect_read_step: forall t addr n post1 post2,
      read_step n t addr post1 ->
      read_step n t addr post2 ->
      read_step n t addr (fun v mRcv => post1 v mRcv /\ post2 v mRcv);
    read_step_nonempty: forall n t a post,
      read_step n t a post -> exists v mRcv, post v mRcv;
    read_step_returns_owned_mem: forall n t a post mExt,
      externally_owned_mem t mExt ->
      read_step n t a post ->
      read_step n t a (fun v mRcv => post v mRcv /\ exists mExt', map.split mExt mExt' mRcv);
    write_step_unique_mGive: forall m t n mKeep1 mKeep2 mGive1 mGive2 addr val,
      map.split m mKeep1 mGive1 ->
      map.split m mKeep2 mGive2 ->
      write_step n t addr val mGive1 ->
      write_step n t addr val mGive2 ->
      mGive1 = mGive2;
    read_step_addrs_ok: forall n t addr post mExt,
      read_step n t addr post ->
      externally_owned_mem t mExt ->
      PropSet.subset (PropSet.of_list (footprint_list addr n)) mmio_addrs \/
      PropSet.subset (PropSet.of_list (footprint_list addr n)) (map.domain mExt);
    write_step_addrs_ok: forall n t addr val mGive mExt,
      write_step n t addr val mGive ->
      externally_owned_mem t mExt ->
      PropSet.subset (PropSet.of_list (footprint_list addr n)) mmio_addrs \/
      PropSet.subset (PropSet.of_list (footprint_list addr n)) (map.domain mExt);
  }.

  Lemma weaken_ext_spec{mmio_ext_calls: MemoryMappedExtCalls}
    {mmio_ext_calls_ok: MemoryMappedExtCallsOk mmio_ext_calls}:
    forall t mGive a args post1 post2,
      (forall mRcv rets, post1 mRcv rets -> post2 mRcv rets) ->
      ext_spec t mGive a args post1 ->
      ext_spec t mGive a args post2.
  Proof.
    unfold ext_spec; intros; fwd; destruct H0p1; fwd; eauto 10 using weaken_read_step.
  Qed.

  Instance ext_spec_ok(mmio_ext_calls: MemoryMappedExtCalls)
    {mmio_ext_calls_ok: MemoryMappedExtCallsOk mmio_ext_calls}: ext_spec.ok ext_spec.
  Proof.
    constructor.
    - (* mGive unique *)
      unfold ext_spec. intros. fwd. destruct H1p1; destruct H2p1; fwd; try congruence.
      inversion H1p1. fwd. subst n0.
      eapply (f_equal word.unsigned) in H2.
      pose proof (LittleEndian.combine_bound v).
      pose proof (LittleEndian.combine_bound v0).
      assert (2 ^ (8 * Z.of_nat n) <= 2 ^ width). {
        destruct width_cases as [W | W]; rewrite W;
        match goal with
        | H: _ |- _ => destruct H as [? | [? | [? | [? ?] ] ] ]; subst n
        end;
        cbv; congruence.
      }
      rewrite 2word.unsigned_of_Z_nowrap in H2 by lia.
      apply LittleEndian.combine_inj in H2. subst v0.
      eauto using write_step_unique_mGive.
    - (* weaken *)
      unfold Morphisms.Proper, Morphisms.respectful, Morphisms.pointwise_relation,
        Basics.impl. eapply weaken_ext_spec.
    - (* intersect *)
      unfold ext_spec. intros. fwd. destruct Hp1; destruct H0p1; fwd;
        match goal with
        | H: _ ++ _ = _ ++ _ |- _ => inversion H; clear H
        end;
        fwd; eauto 10 using intersect_read_step.
  Qed.

End WithMem.

#[export] Existing Instance ext_spec.
#[export] Existing Instance ext_spec_ok.
