Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.omega.Omega.

Section ListFacts.

  Variable T: Type.

  Lemma skipn_all: forall (l: list T), skipn (length l) l = [].
  Proof. induction l; simpl; auto. Qed.

  Lemma skipn_length: forall n (l: list T), length (skipn n l) = length l - n.
  Proof.
    induction n; intros.
    - simpl. omega.
    - simpl.
      destruct l; simpl in IHn.
      * reflexivity.
      * simpl. apply IHn.
  Qed.

End ListFacts.


(* b0 :: b1 :: b2 :: ... bn :: nil === b0 * 2^0 + b1 * 2^1 + ... bn * 2^n *)
Definition word := list bool.

Fixpoint bitwp(f: bool -> bool -> bool)(w1 w2: word){struct w1}: word :=
  match w1, w2 with
  | h1 :: t1, h2 :: t2 => (f h1 h2) :: (bitwp f t1 t2)
  | _, _ => []
  end.

Definition wxor := bitwp xorb.

Fixpoint wmsb(w: word)(default: bool): bool :=
  match w with
  | h :: t => wmsb t h
  | nil => default
  end.

Definition wrepeat(b: bool): nat -> word :=
  fix rec(sz: nat): word :=
  match sz with
  | S sz' => b :: rec sz'
  | O => nil
  end.

Lemma wrepeat_length: forall b n, length (wrepeat b n) = n.
Proof. induction n; simpl; congruence. Qed.

Definition wzero := wrepeat false.

Definition wones := wrepeat true.

Definition sext(w: word)(sz: nat): word :=
  if wmsb w false then w ++ (wones sz) else w ++ (wzero sz).

Definition lossless_shl(w: word)(shamt: nat): word :=
  (wzero shamt) ++ w.

Definition split_upper(n: nat)(w: word): word := skipn (length w - n) w.

Definition split_lower(n: nat)(w: word): word := firstn n w.

Lemma length_split_upper: forall v n,
  n <= length v ->
  length (split_upper n v) = n.
Proof.
  intros. unfold split_upper. rewrite skipn_length. omega.
Qed.

Lemma bitwp_app: forall f u1 u2 v1 v2,
  length u1 = length v1 ->
  length u2 = length v2 ->
  bitwp f (u1 ++ u2) (v1 ++ v2) = bitwp f u1 v1 ++ bitwp f u2 v2.
Admitted.

Lemma wxor_wzero_l: forall sz v,
  wxor (wzero sz) v = v.
Admitted.

Lemma wxor_wzero_r: forall sz v,
  wxor v (wzero sz) = v.
Admitted.

Lemma split_reassemble: forall v wlower wupper,
  length v = wlower + wupper ->
  split_lower wlower v ++ split_upper wupper v = v.
Admitted.

Lemma reassemble_literal_ext0: forall wupper wimm v,
  length v = wimm + wupper ->
  wmsb (split_lower wimm v) false = false ->
  wxor (lossless_shl (split_upper wupper v) wimm) (sext (split_lower wimm v) wupper) = v.
Proof.
  intros.
  unfold lossless_shl, sext, wxor.
  rewrite H0.
  rewrite bitwp_app.
  - fold wxor. rewrite wxor_wzero_l. rewrite wxor_wzero_r.
    apply split_reassemble.
    assumption.
  - unfold split_lower.
    rewrite firstn_length.
    rewrite Nat.min_l by omega.
    unfold wzero. apply wrepeat_length.
  - rewrite length_split_upper by omega. symmetry. apply wrepeat_length.
Qed.
