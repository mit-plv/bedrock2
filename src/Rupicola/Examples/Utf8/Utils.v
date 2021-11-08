Require Import Rupicola.Lib.Api.
Require Import bedrock2.BasicC32Semantics.

Definition F {n} p : if lt_dec p n then Fin.t n else unit :=
  match lt_dec p n as cmp return (if cmp then Fin.t n else unit) with
  | left pr => Fin.of_nat_lt pr
  | _ => tt
  end.

Declare Scope word.
Notation "~w w" := (word.not w) (at level 40, no associativity): word.
Infix "+w" := word.add (at level 50, left associativity): word.
Infix "-w" := word.sub (at level 50, left associativity): word.
Infix ">>w" := word.sru (at level 60, no associativity): word.
Infix ">>>w" := word.srs (at level 60, no associativity): word.
Infix "<<w" := word.slu (at level 60, no associativity): word.
Notation "w1 <?w w2" := (word.b2w (word.ltu w1 w2)) (at level 70, no associativity): word.
Notation "w1 >?w w2" := (word.b2w (word.gtu w1 w2)) (at level 70, no associativity): word.
Notation "w1 <?sw w2" := (word.b2w (word.lts w1 w2)) (at level 70, no associativity): word.
Notation "w1 >?sw w2" := (word.b2w (word.gts w1 w2)) (at level 70, no associativity): word.
Notation "w1 ==w w2" := (word.b2w (word.eqb w1 w2)) (at level 80, no associativity): word.
Infix "&w" := word.and (at level 90, left associativity): word.
Infix "^w" := word.xor (at level 92, left associativity): word.
Infix "|w" := word.or (at level 94, left associativity): word.
Coercion co_word_of_Z := word.of_Z (word := word).
Coercion co_word_of_byte (b: byte) : word := word_of_byte b.
Coercion co_word_of_Fin {n} (f: Fin.t n) : word :=
  word.of_Z (Z.of_nat (proj1_sig (Fin.to_nat f))).
Open Scope word.

Definition byte_of_fin_lt {n} (Hle: (n <= 256)%nat) (f: Fin.t n) : byte :=
  let (n, Hlt) := Fin.to_nat f in
  match Byte.of_nat n as b return Byte.of_nat n = b -> byte with
  | Some b => fun _ => b
  | None => fun HNone =>
             ltac:(apply Byte.of_nat_None_iff in HNone;
                   exfalso; eapply Nat.lt_irrefl;
                   eauto using Nat.lt_irrefl, Nat.le_lt_trans, Nat.lt_le_trans)
  end eq_refl.

Lemma Fin_to_nat_lt {n} (f: Fin.t n) m:
  (n <= m)%nat -> (proj1_sig (Fin.to_nat f) < m)%nat.
Proof. intros; pose proof proj2_sig (Fin.to_nat f); simpl in *; lia. Qed.

Instance Convertible_Fin_byte {n} (Hle: (n <= 256)%nat) : Convertible (Fin.t n) byte :=
  byte_of_fin_lt Hle.
Instance Convertible_Fin_byte_5: Convertible (Fin.t 5) byte :=
  Convertible_Fin_byte (n := 5) ltac:(lia).

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.

  Lemma word_of_byte_of_fin {n} H (f: Fin.t n):
    word_of_byte (byte_of_fin_lt H f) =
      word.of_Z (word := word) (Z.of_nat (proj1_sig (Fin.to_nat f))).
  Proof.
    unfold byte_of_fin_lt.
    destruct Fin.to_nat as (bn & Hf).
    generalize (eq_refl (Byte.of_nat bn)).
    destruct (Byte.of_nat bn) as [b|] at 2 3;
      cbn -[word.of_Z]; intros Hb.
    - apply Byte.to_of_nat in Hb; subst bn.
      rewrite Byte.to_nat_via_N, N_nat_Z; reflexivity.
    - destruct Nat.lt_irrefl.
  Qed.

  Lemma word_of_byte_sru_lt b:
    (Z.to_nat (word.unsigned (word.sru (word := word) (word_of_byte b) (word.of_Z 3))) < 32)%nat .
  Proof.
    pose proof width_at_least_32 as H32.
    pose proof Z.pow_le_mono_r 2 _ _ ltac:(lia) H32.
    pose proof word.unsigned_range (word.sru (word_of_byte b) (word.of_Z 3)).
    apply (Z2Nat.inj_lt _ (Z.of_nat 32)); [lia..|].
    rewrite word.unsigned_sru_shamtZ, Z.shiftr_div_pow2 by lia.
    pose proof word.word_of_byte_range b; apply Z.div_lt_upper_bound; lia.
  Qed.
End __.
