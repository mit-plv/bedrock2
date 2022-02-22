(* Separation logic predicates where the address goes last (just before the memory),
   allowing for uniform treatment of the concept of "the address" of a clause, and
   allowing to use notation like `a |-> predicate args` *)
Require Export Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import coqutil.Z.Lia.
Require Export coqutil.Byte.
Require Import coqutil.Datatypes.HList.
Require Import coqutil.Datatypes.PropSet.
Require Export coqutil.Datatypes.Inhabited.
Require Import coqutil.Tactics.rewr coqutil.Tactics.rdelta.
Require Import Coq.Program.Tactics.
Require Export coqutil.Tactics.Tactics.
Require Export coqutil.Tactics.autoforward.
Require Export coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.OfListWord.
Require Export coqutil.Word.Interface coqutil.Word.Properties.
Require Export coqutil.Tactics.fwd.
Require Export bedrock2.Lift1Prop.
Require Export bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.Array.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Import List.ListNotations. Open Scope list_scope.

Module Export SepLogPredsWithAddrLast. Section __.
  Context {width : Z} {word : Word.Interface.word width} {mem : map.map word byte}.

  Definition at_addr(addr: word)(clause: word -> mem -> Prop): mem -> Prop := clause addr.

  (* Redefinitions to change order of arguments to put address last *)

  Definition ptsto_bytes (n : nat) (value : tuple byte n) (addr : word) : mem -> Prop :=
    ptsto_bytes n addr value.

  Definition littleendian (n : nat) (value : Z) (addr : word) : mem -> Prop :=
    littleendian n addr value.

  Definition truncated_scalar sz (value : Z) addr : mem -> Prop :=
    truncated_scalar sz addr value.

  Definition truncated_word sz (value: word) addr : mem -> Prop :=
    truncated_word sz addr value.

  Definition scalar16 := truncated_word Syntax.access_size.two.
  Definition scalar32 := truncated_word Syntax.access_size.four.
  Definition scalar := truncated_word Syntax.access_size.word.
End __. End SepLogPredsWithAddrLast.

(* `*` is at level 40, and we want to bind stronger than `*`, and moreover,
   `^` is at level 30, and for consistency, we also want to bind stronger than `^`,
   so we choose 25 *)
Notation "addr |-> clause" := (at_addr addr clause)
  (at level 25,
   format "addr  |->  '[' clause ']'").

Inductive get_option{A: Type}: option A -> (A -> Prop) -> Prop :=
| mk_get_option: forall (a: A) (post: A -> Prop), post a -> get_option (Some a) post.

Section SepLog.
  Context {width: Z} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma load_of_sep_cps: forall sz addr value R m (post: word -> Prop),
      sep (addr |-> truncated_word sz value) R m /\ post (truncate_word sz value) ->
      get_option (Memory.load sz m addr) post.
  Proof.
    intros. destruct H. eapply load_of_sep in H. rewrite H.
    constructor. assumption.
  Qed.

  Lemma load_word_of_sep_cps: forall addr value R m (post: word -> Prop),
      sep (addr |-> scalar value) R m /\ post value ->
      get_option (Memory.load Syntax.access_size.word m addr) post.
  Proof.
    intros. destruct H. eapply load_word_of_sep in H. rewrite H.
    constructor. assumption.
  Qed.

  Lemma store_word_of_sep_cps_two_subgoals: forall addr oldvalue newvalue R m (post: mem -> Prop),
      seps [addr |-> scalar oldvalue; R] m ->
      (forall m', seps [addr |-> scalar newvalue; R] m' -> post m') ->
      get_option (Memory.store Syntax.access_size.word m addr newvalue) post.
  Proof.
    intros. eapply Scalars.store_word_of_sep in H. 2: eassumption.
    destruct H as (m1 & E & P). rewrite E. constructor. exact P.
  Qed.

  Lemma store_word_of_sep_cps: forall addr oldvalue newvalue R m (post: mem -> Prop),
      seps [addr |-> scalar oldvalue; R;
            emp (forall m', seps [addr |-> scalar newvalue; R] m' -> post m')] m ->
      get_option (Memory.store Syntax.access_size.word m addr newvalue) post.
  Proof.
    intros. unfold seps in H. apply sep_assoc in H. apply sep_emp_r in H. destruct H.
    eapply store_word_of_sep_cps_two_subgoals. 1: unfold seps. 1: eassumption. eassumption.
  Qed.
End SepLog.
