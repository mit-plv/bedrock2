(* Rewritten versions of poly1305 and chacha20 that you can compile with Rupicola *)
Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Crypto.Spec.
Require Import bedrock2.BasicC32Semantics.

(* TODO array_split should record a special fact in the context to make it trivial to re-split. *)
Open Scope Z_scope.

(** * Types and operations **)

Definition array_t := List.list.
Definition array_len {T} (a: array_t T) := List.length a.
Definition array_split_at {T} (n: nat) (a: array_t T) :=
  (List.firstn n a, List.skipn n a).
Definition array_unsplit {T} (a1 a2: array_t T) := a1 ++ a2.
Definition array_slice_at {T} (start len: nat) (a: array_t T) :=
  let (before, rest) := array_split_at start a in
  let (middle, after) := array_split_at len rest in
  (before, middle, after).
Definition array_unslice {T} (a1 a2 a3: array_t T) := a1 ++ a2 ++ a3.

Definition array_get {T} (a: array_t T) (n: nat) (d: T) := List.nth n a d.
Definition array_put {T} (a: array_t T) (n: nat) (t: T) := upd a n t.

Definition buffer_t := List.list.
Definition buf_make T (n: nat) : buffer_t T := [].
Definition buf_push {T} (buf: buffer_t T) (t: T) := buf ++ [t].
Definition buf_append {T} (buf: buffer_t T) (arr: array_t T) := buf ++ arr.
Definition buf_split {T} (buf: buffer_t T) : array_t T * buffer_t T := (buf, []).
Definition buf_unsplit {T} (arr: array_t T) (buf: buffer_t T) : buffer_t T := arr.
Definition buf_as_array {T} (buf: buffer_t T) : buffer_t T := buf.

Definition p : Z := 2^130 - 5.
Definition felem_init_zero := 0.
Definition felem_add (z1 z2: Z) : Z := z1 + z2 mod p.
Definition felem_mul (z1 z2: Z) : Z := z1 * z2 mod p.
Definition bytes_as_felem_inplace (bs: list byte) : Z :=
  le_combine bs.
Definition felem_as_uint128 z : Z := z mod 2 ^ 128.

Definition uint128_add z1 z2 : Z :=
  (z1 + z2) mod 2 ^ 128.
Definition uint128_as_bytes (z: Z) :=
  le_split 16 z.
Definition bytes_as_uint128 (bs: list byte) :=
  le_combine bs.

Definition w32s_of_bytes (bs: list byte) : list word :=
  List.map word.of_Z (List.map le_combine (chunk 4 bs)).

Definition bytes_of_w32s (w32s: list word) : list byte :=
  List.flat_map (le_split 4) (List.map word.unsigned w32s).

Definition array_fold_chunked {A T}
           (a: array_t T) (size: nat)
           (f: A -> list T -> A)
           a0 :=
  List.fold_left (fun acc c => f acc c) (chunk size a) a0.

Axiom felem_size : nat.

(* FIXME isn't this defined somewhere already? *)
Definition byte_land (b1 b2: byte) :=
  byte.of_Z (Z.land (byte.unsigned b1) (byte.unsigned b2)).

#[local] Hint Unfold buf_make : poly.
#[local] Hint Unfold buf_push buf_append : poly.
#[local] Hint Unfold buf_split buf_unsplit buf_as_array : poly.
#[local] Hint Unfold array_split_at array_unsplit : poly.
#[local] Hint Unfold array_fold_chunked : poly.
#[local] Hint Unfold array_get array_put : poly.
#[local] Hint Unfold bytes_as_felem_inplace : poly.
#[local] Hint Unfold felem_init_zero felem_add felem_mul felem_as_uint128 : poly.
#[local] Hint Unfold uint128_add bytes_as_uint128 uint128_as_bytes : poly.
#[local] Hint Unfold bytes_of_w32s w32s_of_bytes : poly.

(** * Poly1305 **)

Definition poly1305 (k : list byte) (m : list byte) (output: Z): list byte :=
  let/n (f16, l16) := array_split_at 16 k in
  let/n scratch := buf_make byte felem_size in
  let/n scratch := buf_append scratch f16 in
  let/n (scratch, lone_byte_and_felem_spare_space) := buf_split scratch in
  let/n scratch := List.map (fun '(w1, w2) => let/n w := byte_land w1 w2 in w)
                           (combine scratch (le_split 16 0x0ffffffc0ffffffc0ffffffc0fffffff)) in
  let/n scratch := buf_unsplit scratch lone_byte_and_felem_spare_space in
  let/n scratch := buf_push scratch x00 in
  let/n scratch := bytes_as_felem_inplace scratch in (* B2 primitive reads first 17 bytes of longer array *)
  let output := felem_init_zero in
  let/n output :=
      array_fold_chunked
        m 16
        (fun output ck =>
           let/n nscratch := buf_make byte felem_size in
           let/n nscratch := buf_append nscratch ck in (* len = 16 *)
           let/n nscratch := buf_push nscratch x01 in (* len = 17 *)
           let/n nscratch := bytes_as_felem_inplace nscratch in
           let/n output := felem_add output nscratch in
           let/n output := felem_mul output scratch in
           output)
        output in
  let/n output := felem_as_uint128 output in
  let/n l16 := bytes_as_uint128 l16 in
  let/n output := uint128_add output l16 in
  let/n l16 := uint128_as_bytes l16 in
  let/n k := array_unsplit f16 l16 in
  let/n output := uint128_as_bytes output in
  output.

(** ** Lemmas **)

Arguments le_combine: simpl nomatch.
Arguments Z.mul: simpl nomatch.

Lemma testbit_byte_unsigned_ge b n:
  8 <= n ->
  Z.testbit (byte.unsigned b) n = false.
Proof.
  intros;
    erewrite prove_Zeq_bitwise.testbit_above;
    eauto using byte.unsigned_range;
    lia.
Qed.

(* FIXME this doesn't do anything *)
Hint Rewrite testbit_byte_unsigned_ge using solve [auto with zarith] : z_bitwise_with_hyps.

Lemma byte_unsigned_land (b1 b2: byte) :
  byte.unsigned (byte_land b1 b2) =
  Z.land (byte.unsigned b1) (byte.unsigned b2).
Proof.
  unfold byte_land; rewrite byte.unsigned_of_Z.
  unfold byte.wrap; rewrite <- Z.land_ones.
  bitblast.Z.bitblast.
  rewrite testbit_byte_unsigned_ge.
  all: lia.
Qed.

Lemma le_combine_app bs1 bs2:
  le_combine (bs1 ++ bs2) =
  Z.lor (le_combine bs1) (Z.shiftl (le_combine bs2) (Z.of_nat (List.length bs1) * 8)).
Proof.
  induction bs1; cbn -[Z.shiftl Z.of_nat Z.mul]; intros.
  - rewrite Z.mul_0_l, Z.shiftl_0_r; reflexivity.
  - rewrite IHbs1, Z.shiftl_lor, Z.shiftl_shiftl, !Z.lor_assoc by lia.
    f_equal; f_equal; lia.
Qed.

Lemma le_combine_app_0 bs:
  le_combine (bs ++ [x00]) = le_combine bs.
Proof.
  rewrite le_combine_app; simpl; rewrite Z.shiftl_0_l, Z.lor_0_r.
  reflexivity.
Qed.

Lemma le_split_mod z n:
  le_split n z = le_split n (z mod 2 ^ (Z.of_nat n * 8)).
Proof.
  apply le_combine_inj.
  - rewrite !length_le_split; reflexivity.
  - rewrite !le_combine_split.
    Z.push_pull_mod; reflexivity.
Qed.

Lemma split_le_combine' bs n:
  List.length bs = n ->
  le_split n (le_combine bs) = bs.
Proof. intros <-; apply split_le_combine. Qed.

Lemma Z_land_le_combine bs1 : forall bs2,
    Z.land (le_combine bs1) (le_combine bs2) =
    le_combine (List.map (fun '(x, y) => byte_land x y) (combine bs1 bs2)).
Proof.
  induction bs1.
  - reflexivity.
  - destruct bs2; [ apply Z.land_0_r | ]; cbn -[Z.shiftl] in *.
    rewrite <- IHbs1, !byte_unsigned_land, !Z.shiftl_land.
    bitblast.Z.bitblast.
    assert (l < 0 \/ 8 <= i) as [Hlt | Hge] by lia.
    + rewrite !(Z.testbit_neg_r _ l) by assumption.
      rewrite !Bool.orb_false_r; reflexivity.
    + rewrite !testbit_byte_unsigned_ge by lia.
      simpl; reflexivity.
Qed.

(** ** Equivalence proof **)

(* change (nlet _ ?v ?k) with (k v) at 1; cbv beta iota. *)

Lemma poly1305_ok k m output:
  Spec.poly1305 k m = poly1305 k m output.
Proof.
  intros; unfold Spec.poly1305, poly1305, nlet.
  autounfold with poly.
  Z.push_pull_mod.
  rewrite <- le_split_mod.
  repeat f_equal.
  repeat (apply FunctionalExtensionality.functional_extensionality; intros).
  Z.push_pull_mod.
  rewrite !app_nil_l.
  repeat f_equal.
  rewrite le_combine_app_0.
  rewrite <- Z_land_le_combine.
  reflexivity.
Qed.

Hint Rewrite <- le_split_mod Z_land_le_combine : poly.
Hint Rewrite le_combine_app_0 : poly.
Hint Rewrite app_nil_r : poly.

Ltac t :=
  intros
  || (autounfold with poly)
  || Z.push_pull_mod
  || (autorewrite with poly)
  || f_equal
  || apply FunctionalExtensionality.functional_extensionality.

Lemma poly1305_ok' k m output:
  Spec.poly1305 k m = poly1305 k m output.
Proof.
  unfold Spec.poly1305, poly1305, nlet; repeat t.
Qed.

(** * ChaCha20 **)

Print Grammar constr.

Local Notation "a + b" := (Z.land (a+b) (Z.ones 32)).
Local Notation "a ^ b" := (Z.lxor a b).
Local Notation "a <<< b" := (Z.shiftl a b + Z.shiftr a (32-b))
  (at level 30).

Definition sq '(a, b, c, d) :=
  let a := a + b in  let d := d ^ a in  let d := d <<< 16 in
  let c := c + d in  let b := b ^ c in  let b := b <<< 12 in
  let a := a + b in  let d := d ^ a in  let d := d <<< 8 in
  (a, b, c, d).

Definition spec_quarter_letd_cast '(a, b, c, d) : \<< word, word, word, word \>> :=
  let/d a := a + b in  let/d d := d ^ a in  let/d d := d <<< 16 in
  let/d c := c + d in  let/d b := b ^ c in  let/d b := b <<< 12 in
  let/d a := a + b in  let/d d := d ^ a in  let/d d := d <<< 8 in
  let/d c := c + d in  let/d b := b ^ c in  let/d b := b <<< 7 in
  \< word.of_Z a, word.of_Z b, word.of_Z c, word.of_Z d \>.

Local Notation "a + b" := (word.add (word := word) a b).
Local Notation "a ^ b" := (word.xor (word := word) a b).
Local Notation "a <<< b" := (word.slu a b + word.sru a (word.sub (word.of_Z 32) b)) (at level 30).

Definition quarter a b c d : \<< word, word, word, word \>> :=
  let/n a := a + b in  let/n d := d ^ a in  let/n d := d <<< word.of_Z 16 in
  let/n c := c + d in  let/n b := b ^ c in  let/n b := b <<< word.of_Z 12 in
  let/n a := a + b in  let/n d := d ^ a in  let/n d := d <<< word.of_Z 8 in
  let/n c := c + d in  let/n b := b ^ c in  let/n b := b <<< word.of_Z 7 in
  \< a, b, c, d \>.

Section words.
  Context {width} {word : Interface.word width} {word_ok: word.ok word}.

  Lemma of_Z_land_ones z :
    word.of_Z (Z.land z (Z.ones width)) = word.of_Z (word := word) z.
  Proof.
    rewrite Z.land_ones by apply word.width_nonneg.
    apply word.unsigned_inj; rewrite !word.unsigned_of_Z; unfold word.wrap.
    Z.push_pull_mod; reflexivity.
  Qed.

  Lemma Z_land_ones_word_add (a b: word) :
    Z.land (word.unsigned a + word.unsigned b) (Z.ones width) =
    word.unsigned (word.add a b).
  Proof. rewrite Z.land_ones, word.unsigned_add; reflexivity || apply word.width_nonneg. Qed.

  Lemma Z_land_ones_rotate (a: word) b (Hrange: 0 < b < width) :
    Z.land (Z.shiftl (word.unsigned a) b + Z.shiftr (word.unsigned a) (width - b)) (Z.ones width) =
    word.unsigned (word.add (word.slu a (word.of_Z b)) (word.sru a (word.sub (word.of_Z width) (word.of_Z b)))).
  Proof.
    rewrite Z.land_ones, word.unsigned_add by lia.
    rewrite word.unsigned_slu, word.unsigned_sru, !word.unsigned_of_Z_nowrap.
    unfold word.wrap; Z.push_pull_mod.
    rewrite word.unsigned_sub, !word.unsigned_of_Z, !word.wrap_small.
    reflexivity.
    all: pose proof Zpow_facts.Zpower2_lt_lin width word.width_nonneg.
    all: rewrite ?word.unsigned_sub, ?word.unsigned_of_Z_nowrap, ?word.wrap_small; lia.
  Qed.

  Lemma of_Z_land_ones_rotate a b (Ha: 0 <= a < 2 ^ width) (Hb: 0 < b < width) :
    word.of_Z (Z.land (Z.shiftl a b + Z.shiftr a (width - b)) (Z.ones width)) =
    word.add (word := word)
      (word.slu (word.of_Z a) (word.of_Z b))
      (word.sru (word.of_Z a) (word.sub (word.of_Z width) (word.of_Z b))).
  Proof.
    apply word.unsigned_inj.
    rewrite word.unsigned_add, word.unsigned_slu, word.unsigned_sru_nowrap;
      rewrite ?word.unsigned_sub, ?word.unsigned_of_Z_nowrap.
    all: rewrite ?(word.wrap_small b), ?(word.wrap_small (width - b)).
    unfold word.wrap; rewrite Z.land_ones by apply word.width_nonneg;
      Z.push_pull_mod; reflexivity.
    all: pose proof Zpow_facts.Zpower2_lt_lin width word.width_nonneg; try lia.
    rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia.
  Qed.
End words.

Hint Rewrite Z_land_ones_rotate using (split; reflexivity) : quarter.
Hint Rewrite <- word.unsigned_xor_nowrap : quarter.
Hint Rewrite Z_land_ones_word_add : quarter.

(*
Lemma q_ok a b c d:
  q (word.of_Z a) (word.of_Z b) (word.of_Z c) (word.of_Z d) =
  let '(a', b', c', d') := sq (a, b, c, d) in
  \< word.of_Z a', word.of_Z b', word.of_Z c', word.of_Z d' \>.
Proof.
  unfold sq, q, nlet.
  repeat (rewrite of_Z_land_ones_rotate ||
          rewrite word.morph_xor ||
          rewrite word.ring_morph_add ||
          rewrite of_Z_land_ones).
  reflexivity.
Admitted.
 *)

Lemma quarter_ok0 a b c d:
  Spec.quarter (word.unsigned a, word.unsigned b, word.unsigned c, word.unsigned d) =
  let '\<a', b', c', d'\> := quarter a b c d in
  (word.unsigned a', word.unsigned b', word.unsigned c', word.unsigned d').
Proof.
  unfold Spec.quarter, quarter, nlet;
    autorewrite with quarter;
    reflexivity.
Qed.

Ltac set_first :=
  lazymatch goal with
  | [  |- nlet _ (word.of_Z ?z) _ = dlet ?z _ ] =>
    set z;
    unfold nlet at 1; unfold dlet at 1
  end.

Lemma quarter_ok' a b c d:
  quarter (word.of_Z a) (word.of_Z b) (word.of_Z c) (word.of_Z d) =
  spec_quarter_letd_cast (a, b, c, d).
Proof.
  unfold spec_quarter_letd_cast, quarter.
  repeat
    (((rewrite <- of_Z_land_ones_rotate) ||
      (rewrite <- word.morph_xor) ||
      (rewrite <- word.ring_morph_add, <- of_Z_land_ones));
     [ set_first | .. ]).
  reflexivity.
Admitted.

(* FIXME these proofs about word/Z are a pain *)

Lemma quarter_ok a b c d:
  0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> 0 <= c < 2 ^ 32 -> 0 <= d < 2 ^ 32 ->
  quarter (word.of_Z a) (word.of_Z b) (word.of_Z c) (word.of_Z d) =
  let '(a', b', c', d') := Spec.quarter (a, b, c, d) in
  \< word.of_Z a', word.of_Z b', word.of_Z c', word.of_Z d' \>.
Proof.
  intros;
  set (wa := word.of_Z a); set (wb := word.of_Z b); set (wc := word.of_Z c); set (wd := word.of_Z d).
  rewrite <- (word.unsigned_of_Z_nowrap a), <- (word.unsigned_of_Z_nowrap b) by assumption.
  rewrite <- (word.unsigned_of_Z_nowrap c), <- (word.unsigned_of_Z_nowrap d) by assumption.
  rewrite quarter_ok0; subst wa wb wc wd; destruct (quarter _ _ _ _) as (?&?&?&?); cbn -[word.of_Z].
  rewrite !word.of_Z_unsigned; reflexivity.
Qed.

Lemma quarter_stable a b c d:
  0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> 0 <= c < 2 ^ 32 -> 0 <= d < 2 ^ 32 ->
  let '(a', b', c', d') := Spec.quarter (a, b, c, d) in
  0 <= a' < 2 ^ 32 /\ 0 <= b' < 2 ^ 32 /\ 0 <= c' < 2 ^ 32 /\ 0 <= d' < 2 ^ 32.
Proof.
  intros.
  rewrite <- (word.unsigned_of_Z_nowrap a), <- (word.unsigned_of_Z_nowrap b) by assumption.
  rewrite <- (word.unsigned_of_Z_nowrap c), <- (word.unsigned_of_Z_nowrap d) by assumption.
  rewrite quarter_ok0; destruct (quarter _ _ _ _) as (?&?&?&?); cbn -[word.of_Z Z.pow].
  repeat (split; try apply word.unsigned_range).
Qed.

Definition quarterround x y z t (st : list word) : list word :=
  let/n stx := array_get st x (word.of_Z 0) in
  let/n sty := array_get st y (word.of_Z 0) in
  let/n stz := array_get st z (word.of_Z 0) in
  let/n stt := array_get st t (word.of_Z 0) in
  let/n (stx, sty, stz, stt) := quarter stx sty stz stt in
  let/n st := array_put st x stx in
  let/n st := array_put st y sty in
  let/n st := array_put st z stz in
  let/n st := array_put st t stt in
  st.

(* FIXME move to coqutil *)
Lemma skipn_map{A B: Type}: forall (f: A -> B) (n: nat) (l: list A),
    skipn n (map f l) = map f (skipn n l).
Proof.
  induction n; intros.
  - reflexivity.
  - simpl. destruct l; simpl; congruence.
Qed.

Lemma map_upds {A B} (f: A -> B) : forall l d n,
    upds (map f l) n (map f d) = map f (upds l n d).
Proof.
  unfold upds; intros;
    rewrite !firstn_map, !skipn_map, !map_app, !map_length; reflexivity.
Qed.

Lemma map_upd {A B} (f: A -> B) : forall l d n,
    upd (map f l) n (f d) = map f (upd l n d).
Proof. intros; apply @map_upds with (d := [d]). Qed.

Lemma quarterround_ok x y z t st :
  (forall i, 0 <= nth i st 0 < 2 ^ 32) ->
  List.map word.of_Z (Spec.quarterround x y z t st) =
  quarterround x y z t (List.map word.of_Z st).
Proof.
  unfold Spec.quarterround, quarterround, nlet; autounfold with poly; intros.
  rewrite !map_nth, !quarter_ok by auto.
  destruct (Spec.quarter _) as (((?&?)&?)&?).
  rewrite !map_upd; reflexivity.
Qed.

Lemma upd_overflow {A} (l: list A) d n:
  (n >= length l)%nat ->
  upd l n d = l.
Proof.
  intros.
  unfold upd, upds.
  rewrite firstn_all2 by lia.
  rewrite skipn_all2 by lia.
  replace (Datatypes.length l - n)%nat with 0%nat by lia.
  simpl; rewrite app_nil_r; reflexivity.
Qed.

Lemma nth_upd_same {A} (l: list A) (a d: A) (k: nat):
  (k < length l)%nat ->
  nth k (upd l k a) d = a.
Proof.
  unfold upd, upds; intros.
  rewrite app_nth2; rewrite firstn_length_le; auto with arith.
  rewrite Nat.sub_diag.
  replace ((Datatypes.length l - k)%nat) with (S (Datatypes.length l - k - 1)%nat) by lia.
  reflexivity.
Qed.

Lemma nth_firstn {A} i:
  forall (l : list A) (d : A) (k : nat),
    (i < k)%nat -> nth i (firstn k l) d = nth i l d.
Proof.
  induction i; destruct k; destruct l; intros;
    try lia; try reflexivity; simpl.
  rewrite IHi; reflexivity || lia.
Qed.

Lemma nth_skipn {A}:
  forall (l : list A) (d : A) (i k : nat),
    nth i (skipn k l) d = nth (i + k) l d.
Proof.
  intros; destruct (Nat.lt_ge_cases (i + k) (length l)); cycle 1.
  - rewrite !nth_overflow; rewrite ?skipn_length; reflexivity || lia.
  - assert ([nth i (skipn k l) d] = [nth (i + k) l d]) as [=->]; try reflexivity.
    rewrite <- !firstn_skipn_nth; rewrite ?skipn_length; try lia.
    rewrite skipn_skipn; reflexivity.
Qed.

Lemma nth_upd_diff {A} (l: list A) (a d: A) (i k: nat):
  (i <> k) ->
  nth i (upd l k a) d = nth i l d.
Proof.
  intros; destruct (Nat.lt_ge_cases i (length l)); cycle 1.
  - rewrite !nth_overflow; rewrite ?upd_length; reflexivity || lia.
  - intros; destruct (Nat.lt_ge_cases k (length l)); cycle 1.
    + rewrite upd_overflow by lia. reflexivity.
    +  rewrite upd_firstn_skipn by lia.
       assert (i < k \/ i > k)%nat as [Hlt | Hgt] by lia.
       * rewrite app_nth1; rewrite ?firstn_length; try lia.
         rewrite nth_firstn by lia; reflexivity.
       * rewrite app_nth2; rewrite ?firstn_length; try lia.
         replace (Nat.min k (length l)) with k by lia.
         replace (i - k)%nat with (S (i - k - 1))%nat by lia.
         cbn [nth app].
         rewrite nth_skipn; f_equal; lia.
Qed.

Lemma nth_upd {A} (l: list A) (a d: A) (i k: nat):
  ((i >= length l)%nat /\ nth i (upd l k a) d = d) \/
  (i = k /\ nth i (upd l k a) d = a) \/
  (i <> k /\ nth i (upd l k a) d = nth i l d).
Proof.
  destruct (Nat.lt_ge_cases i (length l)); cycle 1; [ left | right ].
  - unfold upd; rewrite nth_overflow; rewrite ?upds_length; eauto.
  - destruct (Nat.eq_dec i k) as [-> | Heq]; [ left | right ].
    + rewrite nth_upd_same; auto.
    + rewrite nth_upd_diff; auto.
Qed.

Lemma default_stable {A} (P: A -> Prop) (l: list A) (d: A):
  (forall i : nat, P (nth i l d)) -> P d.
Proof.
  intros H; specialize (H (length l)); rewrite nth_overflow in H;
    assumption || reflexivity.
Qed.


Lemma Forall_nth' {A} (P : A -> Prop) (l : list A) d:
  (P d /\ Forall P l) <-> (forall i, P (nth i l d)).
Proof.
  split; intros H *.
  - destruct H; rewrite <- nth_default_eq; apply Forall_nth_default; eassumption.
  - split; [eapply default_stable; eassumption|].
    apply Forall_nth; intros.
    erewrite nth_indep; eauto.
Qed.

Lemma cons_stable {A} (P: A -> Prop) (l1 l2: list A) (d: A):
  (forall i : nat, P (nth i l1 d)) ->
  (forall i : nat, P (nth i l2 d)) ->
  (forall i : nat, P (nth i (l1 ++ l2) d)).
Proof.
  rewrite <- !Forall_nth', Forall_app; intuition eauto.
Qed.

Lemma app_stable {A} (P: A -> Prop) (l1 l2: list A) (d: A):
  (forall i : nat, P (nth i l1 d)) ->
  (forall i : nat, P (nth i l2 d)) ->
  (forall i : nat, P (nth i (l1 ++ l2) d)).
Proof.
  rewrite <- !Forall_nth', Forall_app; intuition eauto.
Qed.

Lemma upd_stable {A} (P: A -> Prop) (l: list A) (a d: A) k:
  P a ->
  (forall i : nat, P (nth i l d)) ->
  (forall i : nat, P (nth i (upd l k a) d)).
Proof.
  intros;
    destruct (nth_upd l a d i k) as [(? & ->) | [ (? & ->) | (? & ->) ] ];
    subst; eauto; (eapply default_stable; eauto).
Qed.

Lemma quarterround_stable x y z t a:
  (forall i : nat, 0 <= nth i a 0 < 2 ^ 32) ->
  (forall i : nat, 0 <= nth i (Spec.quarterround x y z t a) 0 < 2 ^ 32).
Proof.
  unfold Spec.quarterround, nlet; autounfold with poly; intros.
  pose proof quarter_stable (nth x a 0) (nth y a 0) (nth z a 0) (nth t a 0)
       ltac:(eauto) ltac:(eauto) ltac:(eauto) ltac:(eauto) as Hb.
  destruct (Spec.quarter _) as (((?&?)&?)&?).
  destruct Hb as (?&?&?&?).
  repeat (apply upd_stable; lia || auto; intros).
Qed.

Definition chacha20_block_init : \<< word, word, word, word \>> :=
  Eval cbn -[word.of_Z] in
  match w32s_of_bytes (list_byte_of_string"expand 32-byte k") as l
        return match l with | [w1; w2; w3; w4] => _ | _ => True end with
  | [w1; w2; w3; w4] => \<w1, w2, w3, w4\>
  | _ => I
  end.

Require Import Rupicola.Lib.ControlFlow.DownTo.

(* FIXME word/Z conversion *)
Definition chacha20_block (*256bit*)key (*32bit+96bit*)nonce (*512 bits*)st :=
  let '\< i1, i2, i3, i4 \> := chacha20_block_init in
  let/n st := buf_push st i1 in
  let/n st := buf_push st i2 in
  let/n st := buf_push st i3 in
  let/n st := buf_push st i4 in (* the inits are the chunks of "expand …" *)

  let/n key := w32s_of_bytes key in
  let/n st := buf_append st key in
  let/n key := bytes_of_w32s key in

  let/n nonce := w32s_of_bytes nonce in
  let/n st := buf_append st nonce in
  let/n nonce := bytes_of_w32s nonce in

  let/n st := buf_as_array st in
  let/n ss := buf_make word 16 in
  let/n ss := buf_append ss st in
  let/n ss := buf_as_array ss in
  let/n ss := Nat.iter 10 (fun ss =>
    let/n ss := quarterround  0  4  8 12  ss in
    let/n ss := quarterround  1  5  9 13  ss in
    let/n ss := quarterround  2  6 10 14  ss in
    let/n ss := quarterround  3  7 11 15  ss in
    let/n ss := quarterround  0  5 10 15  ss in
    let/n ss := quarterround  1  6 11 12  ss in
    let/n ss := quarterround  2  7  8 13  ss in
    let/n ss := quarterround  3  4  9 14  ss in
    ss) ss in

  let/n st := List.map (fun '(st_i, ss_i) =>
                         let/n st_i := st_i + ss_i in
                         st_i) (combine st ss) in

  let/n st := bytes_of_w32s st in
  st.

Lemma map_combine_separated {A B A' B'} (fA: A -> A') (fB: B -> B') :
  forall (lA : list A) (lB: list B),
    List.map (fun p => (fA (fst p), fB (snd p))) (combine lA lB) =
    combine (List.map fA lA) (List.map fB lB).
Proof.
  induction lA; destruct lB; simpl; congruence.
Qed.

Lemma map_combine_comm {A B} (f: A * A -> B) :
  (forall a1 a2, f (a1, a2) = f (a2, a1)) ->
  forall (l1 l2 : list A),
    List.map f (combine l1 l2) =
    List.map f (combine l2 l1).
Proof.
  induction l1; destruct l2; simpl; congruence.
Qed.

Lemma map_id {A} (f: A -> A) :
  (forall x, f x = x) ->
  forall l, map f l = l.
Proof. induction l; simpl; congruence. Qed.

Lemma Nat_iter_rew {A B} (fA: A -> A) (fB: B -> B) (g: A -> B):
  (forall a, g (fA a) = fB (g a)) ->
  forall n a b,
    b = g a ->
    g (Nat.iter n fA a) = Nat.iter n fB b.
Proof.
  intros Heq; induction n; simpl; intros; subst.
  - reflexivity.
  - erewrite Heq, IHn; reflexivity.
Qed.

Lemma Nat_iter_rew_inv {A B} (P: A -> Prop) (fA: A -> A) (fB: B -> B) (g: A -> B):
  (forall a, P a -> P (fA a)) ->
  (forall a, P a -> g (fA a) = fB (g a)) ->
  forall n a b,
    P a ->
    b = g a ->
    P (Nat.iter n fA a) /\
    g (Nat.iter n fA a) = Nat.iter n fB b.
Proof.
  intros Hind Heq; induction n; simpl; intros * Ha ->.
  - eauto.
  - specialize (IHn _ _ Ha eq_refl) as [HPa Hg].
    split; eauto. erewrite Heq, Hg; eauto.
Qed.

Lemma word_add_pair_eqn st:
  (let '(s, t) := st in Z.land (s + t) (Z.ones 32)) =
  word.unsigned (word.of_Z (fst st) + word.of_Z (snd st)).
Proof.
  destruct st.
  rewrite Z.land_ones, <- word.ring_morph_add, word.unsigned_of_Z by lia.
  reflexivity.
Qed.

Lemma chacha20_block_ok key nonce :
  Spec.chacha20_block key nonce =
  chacha20_block key nonce [].
Proof.
  unfold Spec.chacha20_block, chacha20_block, chacha20_block_init, nlet.
  autounfold with poly.

  simpl (map le_combine (chunk 4 (list_byte_of_string _))); cbn [List.app].
  erewrite (map_ext _ _ word_add_pair_eqn).
  rewrite <- List.map_map.
  rewrite <- List.map_map with (f := fun st => (_, _)) (g := fun '(s, t) => s + t).
  rewrite map_combine_separated, map_combine_comm by (cbn; intros; ring).
  cbn [List.map]; rewrite List.map_app.
  repeat f_equal.

  eapply Nat_iter_rew_inv with (P := fun a => (forall i : nat, 0 <= nth i a 0 < 2 ^ 32)); intros.
  - eauto 10 using quarterround_stable.
  - rewrite !quarterround_ok; try reflexivity.
    all: eauto 10 using quarterround_stable.
  - do 4 try destruct i as [ | i]; cbn [nth]; try lia.
    apply app_stable.
  - cbn [List.map]; rewrite List.map_app; reflexivity.
Qed.
