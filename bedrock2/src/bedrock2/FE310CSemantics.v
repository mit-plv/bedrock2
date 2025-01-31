Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Semantics bedrock2.LeakageSemantics.
Require Import bedrock2.SemanticsRelations.
Require coqutil.Datatypes.String coqutil.Map.SortedList coqutil.Map.SortedListString.
Require Import coqutil.Word.Interface.
Require Export coqutil.Word.Bitwidth32.

Import String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

(** This file defines MMIO-only semantics. There is nothing FE310-specific here. *)

Definition MMIOREAD : string := "MMIOREAD".
Definition MMIOWRITE : string := "MMIOWRITE".

Section WithParameters.
  Context {word: word.word 32} {mem: Interface.map.map word Byte.byte}.
  Import Interface.map.

  (* FIXME: this is a copypaste from [riscv.Platform.FE310ExtSpec.FE310_mmio] *)
  Definition isMMIOAddr (addr : word) :=
    0x00020000 <= word.unsigned addr < 0x00022000 \/
    0x10008000 <= word.unsigned addr < 0x10010000 \/
    0x10012000 <= word.unsigned addr < 0x10013000 \/
    0x10013000 <= word.unsigned addr < 0x10014000 \/
    0x10024000 <= word.unsigned addr < 0x10025000.
  (* FIXME: this is a copypaste from [riscv.Platform.FE310ExtSpec.FE310_mmio] *)
  Definition isMMIOAligned (n : nat) (addr : word) :=
    n = 4%nat /\ word.unsigned addr mod 4 = 0.

(* FE310 is a simple enough processor that our leakage assumptions are likely to hold.  There is no official documentation of whether multiply always takes the maximum time or not, but both https://eprint.iacr.org/2019/794.pdf and https://pure.tue.nl/ws/portalfiles/portal/169647601/Berg_S._ES_CSE.pdf quote a fixed number of cycles for FE310 multiplication in the context of cryptography. *)
  Global Instance leakage_ext_spec: LeakageSemantics.ExtSpec :=
    fun (t : trace) (mGive : mem) a (args: list word) (post: mem -> list word -> list word -> Prop) =>
    if String.eqb "MMIOWRITE" a then
      exists addr val,
        args = [addr; val] /\
        (mGive = Interface.map.empty /\ isMMIOAddr addr /\ word.unsigned addr mod 4 = 0) /\
        post Interface.map.empty nil [addr]
    else if String.eqb "MMIOREAD" a then
      exists addr,
        args = [addr] /\
        (mGive = Interface.map.empty /\ isMMIOAddr addr /\ word.unsigned addr mod 4 = 0) /\
        forall val, post Interface.map.empty [val] [addr]
    else False.

  Global Instance leakage_ext_spec_ok : ext_spec.ok leakage_ext_spec.
  Proof.
    split;
    cbv [leakage_ext_spec Morphisms.Proper Morphisms.respectful Morphisms.pointwise_relation Basics.impl];
    intros.
    all :
    repeat match goal with
      | H : context[(?x =? ?y)%string] |- _ =>
          destruct (x =? y)%string in *
      | H: exists _, _ |- _ => destruct H
      | H: _ /\ _ |- _ => destruct H
      | H: False |- _ => destruct H
    end; subst;
    repeat match goal with
      | H: _ :: _ = _ :: _ |- _ => injection H; intros; subst; clear H
    end;
    eauto 8 using Properties.map.same_domain_refl.
  Qed.

  Global Instance ext_spec : Semantics.ExtSpec := deleakaged_ext_spec.
  Global Instance ext_spec_ok : Semantics.ext_spec.ok ext_spec := deleakaged_ext_spec_ok.

  Global Instance locals: Interface.map.map String.string word := SortedListString.map _.
  Global Instance env: Interface.map.map String.string (list String.string * list String.string * cmd) :=
    SortedListString.map _.

  Global Instance locals_ok: Interface.map.ok locals := SortedListString.ok _.
  Global Instance env_ok: Interface.map.ok env := SortedListString.ok _.

  Context {word_ok: word.ok word}.
  (* COPY-PASTE this at the beginning of any section in which you need `ring` for words *)
  Add Ring wring : (Properties.word.ring_theory (word := word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := word)),
         constants [Properties.word_cst]).
End WithParameters.

Arguments locals: simpl never.
Arguments env: simpl never.
