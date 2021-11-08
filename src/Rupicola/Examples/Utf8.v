(*! Branchless utf-8 decoder, from https://github.com/skeeto/branchless-utf8 !*)
Require Import
        Rupicola.Lib.Api
        Rupicola.Lib.Arrays
        Rupicola.Lib.InlineTables.

Require Import bedrock2.BasicC32Semantics.

Definition masks :=
  Eval cbv in List.map byte.of_Z [0x00; 0x7f; 0x1f; 0x0f; 0x07].
Definition mins :=
  Eval cbv in List.map byte.of_Z [4194304; 0; 128; 2048; 65536].
Definition shiftc :=
  Eval cbv in List.map byte.of_Z [0; 18; 12; 6; 0].
Definition shifte :=
  Eval cbv in List.map byte.of_Z [0; 6; 4; 2; 0].

Definition F {n} p : if lt_dec p n then Fin.t n else unit :=
  match lt_dec p n as cmp return (if cmp then Fin.t n else unit) with
  | left pr => Fin.of_nat_lt pr
  | _ => tt
  end.

Notation f x := (@F 5 x).
Definition lengths : list (Fin.t 5) :=
  Eval cbv in
    [f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1;
     f 0; f 0; f 0; f 0; f 0; f 0; f 0; f 0; f 2; f 2; f 2; f 2; f 3; f 3; f 4; f 0].

(* Definition lengths : list byte := *)
(*   Eval cbv in *)
(*     List.map byte.of_Z *)
(*              [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; *)
(*               0; 0; 0; 0; 0; 0; 0; 0; 2; 2; 2; 2; 3; 3; 4; 0]. *)

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

Global Instance Convertible_byte_nat : Convertible byte nat :=
  fun b => Z.to_nat (byte.unsigned b).
Global Instance HasDefault_Fin {n} : HasDefault (Fin.t (S n)) :=
  Fin.F1.
Global Instance Convertible_Fin_nat {n} : Convertible (Fin.t n) nat :=
  fun f => proj1_sig (Fin.to_nat f).

Definition utf8_decode (bs: list byte) : word * word * word :=
  let/n b0 := ListArray.get bs 0 in
  let/n len := InlineTable.get lengths (b0 >>w 3) in

  let/n offset := len +w (((len ==w 0) &w 1) ^w -1) in

  let/n b1 := ListArray.get bs 1 in
  let/n b2 := ListArray.get bs 2 in
  let/n b3 := ListArray.get bs 3 in

  let/n mask := InlineTable.get masks len in
  let/n c := (b0 &w mask) <<w 18 in
  let/n c := c |w (b1 &w 0x3f) <<w 12 in
  let/n c := c |w (b2 &w 0x3f) <<w 6 in
  let/n c := c |w (b3 &w 0x3f) <<w 0 in

  let/n shiftc := InlineTable.get shiftc len in
  let/n c := c >>w shiftc in

  let/n min := InlineTable.get mins len in
  let/n e := (c <?w min) <<w 6 in
  let/n e := e |w ((c >>w 11) ==w 0x1b) <<w 7 in
  let/n e := e |w (0x10FFFF <?w c) <<w 8 in
  let/n e := e |w (b1 &w 0xc0) >>w 2 in
  let/n e := e |w (b2 &w 0xc0) >>w 4 in
  let/n e := e |w (b3       ) >>w 6 in
  let/n e := e ^w 0x2a in

  let/n shifte := InlineTable.get shifte len in
  let/n e := e >>w shifte in

  (c, e, offset).

Instance spec_of_utf8_decode : spec_of "utf8_decode" :=
  fnspec! "utf8_decode" data_ptr len / (data : list byte) R ~> c e offset,
    { requires tr mem :=
        word.unsigned len >= 4 /\
        word.unsigned len = Z.of_nat (length data) /\
        (listarray_value AccessByte data_ptr data * R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        (c, e, offset) = utf8_decode data /\
        (listarray_value AccessByte data_ptr data * R)%sep mem' }.

Definition byte_of_fin_lt {n} (Hle: (n <= 256)%nat) (f: Fin.t n) : byte :=
  let (n, Hlt) := Fin.to_nat f in
  match Byte.of_nat n as b return Byte.of_nat n = b -> byte with
  | Some b => fun _ => b
  | None => fun HNone =>
             ltac:(apply Byte.of_nat_None_iff in HNone;
                   exfalso; eapply Nat.lt_irrefl;
                   eauto using Nat.lt_irrefl, Nat.le_lt_trans, Nat.lt_le_trans)
  end eq_refl.

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

Lemma Fin_to_nat_lt {n} (f: Fin.t n) m:
  (n <= m)%nat -> (proj1_sig (Fin.to_nat f) < m)%nat.
Proof. intros; pose proof proj2_sig (Fin.to_nat f); simpl in *; lia. Qed.

Lemma word_of_byte_sru_lt b:
  (Z.to_nat (word.unsigned (word.sru (word := word) (word_of_byte b) (word.of_Z 3))) < 32)%nat .
Proof.
  pose proof word.unsigned_range (word.sru (word_of_byte b) (word.of_Z 3)).
  apply (Z2Nat.inj_lt _ (Z.of_nat 32)); [lia..|].
  rewrite word.unsigned_sru_shamtZ, Z.shiftr_div_pow2 by lia.
  pose proof word.word_of_byte_range b; apply Z.div_lt_upper_bound; lia.
Qed.

Instance Convertible_Fin_byte {n} (Hle: (n <= 256)%nat) : Convertible (Fin.t n) byte :=
  byte_of_fin_lt Hle.
Instance Convertible_Fin_byte_5: Convertible (Fin.t 5) byte :=
  Convertible_Fin_byte (n := 5) ltac:(lia).

Import UnsizedListArrayCompiler.
Hint Unfold Convertible_byte_nat : compiler_cleanup.
Hint Unfold Convertible_Z_nat : compiler_cleanup.
Hint Unfold Convertible_Fin_nat : compiler_cleanup.
Hint Unfold Convertible_Fin_byte : compiler_cleanup.
Hint Unfold Convertible_Fin_byte_5 : compiler_cleanup.

Hint Unfold co_word_of_Z co_word_of_byte co_word_of_Fin : compiler_cleanup.

Hint Rewrite Nat2Z.id : compiler_side_conditions.
Hint Rewrite @word_of_byte_of_fin : compiler_side_conditions.
#[local] Hint Extern 1 (proj1_sig _ < _)%nat => apply Fin_to_nat_lt; shelve : compiler_side_conditions.

#[local] Hint Resolve word_of_byte_sru_lt : compiler_side_conditions.
#[local] Hint Extern 10 (_ < _)%nat => (cbn; lia) : compiler_side_conditions.
#[local] Hint Extern 10 (_ < _)%Z => (cbn; lia) : compiler_side_conditions.
#[local] Hint Extern 10 (_ <= _)%nat => (cbn; lia) : compiler_side_conditions.
#[local] Hint Extern 10 (_ <= _)%Z => (cbn; lia) : compiler_side_conditions.

Opaque InlineTable.get.
Derive utf8_decode_body SuchThat
       (defn! "utf8_decode" ("data", "len") ~> "c", "e", "offset"
         { utf8_decode_body },
         implements utf8_decode)
       As body_correct.
Proof.
  Time compile.
Qed.

Require Import bedrock2.ToCString.
Compute c_func ("utf8_decode", (["data"; "len"], ["c"; "e"; "offset"], utf8_decode_body)).
