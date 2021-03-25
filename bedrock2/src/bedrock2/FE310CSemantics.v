Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList coqutil.Map.SortedListString.
Require Import coqutil.Word.Interface.
Require coqutil.Word.Naive.
Require Import coqutil.Z.HexNotation.

Import String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

(** This file defines MMIO-only semantics. There is nothing FE310-specific here. *)

Definition MMIOREAD : string := "MMIOREAD".
Definition MMIOWRITE : string := "MMIOWRITE".

Module parameters.
  Class parameters := {
    word :> Word.Interface.word 32;
    word_ok :> word.ok word; (* for impl of mem below *)
    mem :> Interface.map.map word Byte.byte;
    mem_ok :> Interface.map.ok mem; (* for impl of mem below *)
  }.
End parameters. Notation parameters := parameters.parameters.

Section WithParameters.
  Context {p : parameters}.
  Import Interface.map.

  Local Notation bedrock2_trace := (list (parameters.mem * String.string * list parameters.word * (parameters.mem * list parameters.word))).

  (* FIXME: this is a copypaste from [riscv.Platform.FE310ExtSpec.FE310_mmio] *)
  Definition isMMIOAddr (addr:parameters.word) :=
    Ox "00020000" <= word.unsigned addr < Ox "00022000" \/
    Ox "10008000" <= word.unsigned addr < Ox "10010000" \/
    Ox "10012000" <= word.unsigned addr < Ox "10013000" \/
    Ox "10013000" <= word.unsigned addr < Ox "10014000" \/
    Ox "10024000" <= word.unsigned addr < Ox"10025000".
  (* FIXME: this is a copypaste from [riscv.Platform.FE310ExtSpec.FE310_mmio] *)
  Definition isMMIOAligned (n : nat) (addr : parameters.word) :=
    n = 4%nat /\ word.unsigned addr mod 4 = 0.

  Definition ext_spec (t : bedrock2_trace) (mGive : parameters.mem) a (args: list parameters.word) (post:parameters.mem -> list parameters.word -> Prop) :=
    if String.eqb "MMIOWRITE" a then
      exists addr val,
        args = [addr; val] /\
        (mGive = Interface.map.empty /\ isMMIOAddr addr /\ word.unsigned addr mod 4 = 0) /\
        post Interface.map.empty nil
    else if String.eqb "MMIOREAD" a then
      exists addr,
        args = [addr] /\
        (mGive = Interface.map.empty /\ isMMIOAddr addr /\ word.unsigned addr mod 4 = 0) /\
        forall val, post Interface.map.empty [val]
    else False.

  Global Instance semantics_parameters  : Semantics.parameters :=
    {|
    Semantics.word := parameters.word;
    mem := parameters.mem;
    locals := SortedListString.map _;
    env := SortedListString.map _;
    Semantics.ext_spec := ext_spec;
  |}.

  Global Instance ext_spec_ok : ext_spec.ok _.
  Proof.
    split;
    cbv [ext_spec Semantics.ext_spec semantics_parameters
    Morphisms.Proper Morphisms.respectful Morphisms.pointwise_relation Basics.impl
    ];
    intros.
    all :
    repeat match goal with
      | H : context[(?x =? ?y)%string] |- _ =>
          destruct (x =? y)%string in *
      | H: exists _, _ |- _ => destruct H
      | H: _ /\ _ |- _ => destruct H
      | H: False |- _ => destruct H
    end; subst; eauto 8 using Properties.map.same_domain_refl.
  Qed.

  Global Instance ok : Semantics.parameters_ok semantics_parameters.
  Proof.
    split; cbv [env locals mem semantics_parameters]; try exact _.
    { cbv; auto. }
    { exact (SortedListString.ok _). }
    { exact (SortedListString.ok _). }
  Qed.

  (* COPY-PASTE this *)
  Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).
End WithParameters.
