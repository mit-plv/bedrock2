Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import coqutil.Datatypes.ZList. Import ZList.List.ZIndexNotations.
Require Import bedrock2.Lift1Prop bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.SepLib.
Require Import bedrock2.sepapp.

Section WithMem.
  Context {width} {BW: Bitwidth width} {word: word width} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Definition contiguous(P: word -> mem -> Prop)(n: Z): Prop :=
    forall addr, impl1 (P addr) (array (uint 8) n ? addr).

  Lemma cast_to_anybytes: forall (P: word -> mem -> Prop) a n m,
      contiguous P n -> P a m -> (array (uint 8) n ? a) m.
  Proof. unfold contiguous, impl1. intros. eauto. Qed.

  (* the direction we care about is anybytes -> P, but it is very likely to
     also imply the converse direction, and probably also easy to prove,
     so we make it an iff1 *)
  Definition fillable{V: Type}(P: V -> word -> mem -> Prop)(n: Z): Prop :=
    forall addr, iff1 (array (uint 8) n ? addr) (ex1 (fun v => P v addr)).

  Lemma fillable_to_contiguous{V: Type} P (v: V) n: fillable P n -> contiguous (P v) n.
  Proof.
    unfold fillable, contiguous. intros. specialize (H addr).
    unfold ex1, impl1 in *.
    intros m Hm.
    eapply proj2 in H.
    eapply H.
    eauto.
  Qed.

  Lemma anybytes_contiguous: forall n, contiguous (anyval (array (uint 8) n)) n.
  Proof. unfold contiguous. intros. reflexivity. Qed.

  Lemma sepapps_nil_contiguous: contiguous (sepapps nil) 0.
  Proof.
    unfold contiguous, sepapps, anyval, Memory.anybytes, impl1.
    simpl. intros *. intros [? _]. subst.
    exists nil. unfold array.
    eapply sep_emp_l. split; [reflexivity| ].
    simpl. unfold emp. auto.
  Qed.

  Lemma sepapps_cons_contiguous: forall p tail n1 n2,
      contiguous p n1 ->
      contiguous (sepapps tail) n2 ->
      contiguous (sepapps (cons (mk_sized_predicate p n1) tail)) (n1 + n2).
  Proof.
    unfold contiguous. intros.
    rewrite sepapps_cons.
    simpl.
    intros m Hm.
    eapply merge_anyval_array.
    destruct Hm as (m1 & m2 & D & Hm1 & Hm2).
    unfold impl1 in *.
    exists m1, m2. rewrite Z.mul_1_l. eauto.
  Qed.

  Lemma uintptr_contiguous: forall v, contiguous (uintptr v) (Memory.bytes_per_word width).
  Proof.
    unfold contiguous, impl1, uintptr. intros.
    eapply Scalars.scalar_to_anybytes in H.
    eapply anybytes_from_alt.
    1: destruct width_cases as [E|E]; rewrite E; cbv; discriminate.
    assumption.
  Qed.
End WithMem.

Section WithMem32.
  Context {word: word 32} {BW: Bitwidth 32} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma uintptr32_contiguous: forall v, contiguous (uintptr v) 4.
  Proof. eapply (uintptr_contiguous (width := 32)). Qed.
End WithMem32.

Section WithMem64.
  Context {word: word 64} {BW: Bitwidth 64} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma uintptr64_contiguous: forall v, contiguous (uintptr v) 8.
  Proof. eapply (uintptr_contiguous (width := 64)). Qed.
End WithMem64.

Create HintDb contiguous.
#[export] Hint Resolve
  sepapps_cons_contiguous
  sepapps_nil_contiguous
  uintptr32_contiguous
  uintptr64_contiguous
  anybytes_contiguous
: contiguous.
