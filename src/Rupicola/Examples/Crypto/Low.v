(* Rewritten versions of poly1305 and chacha20 that you can compile with Rupicola *)
Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Crypto.Spec.
Require Import bedrock2.BasicC32Semantics.
Import Datatypes.

(* TODO array_split should record a special fact in the context to make it trivial to re-split. *)
Open Scope Z_scope.

(** * Properties missing from coqutil, bedrock2, or Coq's stdlib *)

(** ** Nat.iter **)

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

(** ** Forall **)

Lemma forall_nth_default {A} (P: A -> Prop) (l: list A) (d: A):
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
  - split; [eapply forall_nth_default; eassumption|].
    apply Forall_nth; intros.
    erewrite nth_indep; eauto.
Qed.

Lemma Forall_nth_default' {A} (P : A -> Prop) (l : list A) d:
  P d -> (Forall P l <-> (forall i, P (nth i l d))).
Proof. intros; rewrite <- Forall_nth'; tauto. Qed.

Lemma Forall_map {A B} (P: B -> Prop) (f: A -> B) (l: list A):
  Forall (fun x => P (f x)) l ->
  Forall P (map f l).
Proof.
  induction l; simpl; intros H.
  - apply Forall_nil.
  - apply invert_Forall_cons in H. apply Forall_cons; tauto.
Qed.

(** map **)

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

Lemma map_id {A} (f: A -> A) l:
  (forall x, List.In x l -> f x = x) ->
  map f l = l.
Proof.
  induction l; simpl.
  - reflexivity.
  - intros H; rewrite (H a), IHl by auto; reflexivity.
Qed.

Lemma skipn_map{A B: Type}: forall (f: A -> B) (n: nat) (l: list A),
    skipn n (map f l) = map f (skipn n l).
Proof.
  induction n; intros.
  - reflexivity.
  - simpl. destruct l; simpl; congruence.
Qed.

Lemma fold_left_combine_fst {A B C} (f: A -> B -> A) : forall (l1: list C) l2 a0,
    (List.length l1 >= List.length l2)%nat ->
    fold_left f l2 a0 = fold_left (fun a '(_, b) => f a b) (combine l1 l2) a0.
Proof.
  induction l1; destruct l2; simpl; intros; try rewrite IHl1; reflexivity || lia.
Qed.

(** ** nth **)

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

(** * upd **)

Lemma upd_overflow {A} (l: list A) d n:
  (n >= length l)%nat ->
  upd l n d = l.
Proof.
  intros.
  unfold upd, upds.
  rewrite firstn_all2 by lia.
  rewrite skipn_all2 by lia.
  replace (length l - n)%nat with 0%nat by lia.
  simpl; rewrite app_nil_r; reflexivity.
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

Lemma nth_upd_same {A} (l: list A) (a d: A) (k: nat):
  (k < length l)%nat ->
  nth k (upd l k a) d = a.
Proof.
  unfold upd, upds; intros.
  rewrite app_nth2; rewrite firstn_length_le; auto with arith.
  rewrite Nat.sub_diag.
  replace ((length l - k)%nat) with (S (length l - k - 1)%nat) by lia.
  reflexivity.
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

Lemma Forall_upd {A} (P: A -> Prop) (l: list A) (a: A) k:
  P a ->
  Forall P l ->
  Forall P (upd l k a).
Proof.
  intros Ha Hl.
  rewrite @Forall_nth_default' with (d := a) in Hl |- *; eauto.
  intros; destruct (nth_upd l a a i k) as [(? & ->) | [ (? & ->) | (? & ->) ] ];
    subst; eauto; eauto.
Qed.

(** ** chunks **)

Lemma Forall_chunk'_length_mod {A} (l: list A) n:
  forall acc, (length acc < n)%nat ->
         ((length l + length acc) mod n = length l mod n)%nat ->
         Forall (fun c => length c = n \/ length c = length l mod n)%nat
                (chunk' n l acc).
Proof.
  set (length l) as ll at 2 3; clearbody ll.
  induction l; simpl; intros.
  - destruct acc; eauto; [].
    apply Forall_cons; eauto.
    right. rewrite <- (Nat.mod_small _ n); assumption.
  - destruct (_ <? _)%nat eqn:Hlt.
    + rewrite Nat.ltb_lt in Hlt.
      eapply IHl; try lia; [].
      rewrite app_length; cbn [List.length].
      replace (ll mod n)%nat; f_equal; lia.
    + rewrite Nat.ltb_ge in Hlt.
      apply Forall_cons;
        rewrite app_length in *; cbn [List.length] in *;
          replace (S (length l + length acc)) with (length l + n)%nat in * by lia.
      * left; lia.
      * apply IHl; simpl; try lia.
        replace (ll mod n)%nat.
        symmetry; rewrite <- Nat.add_mod_idemp_r at 1 by lia. (* FIXME why does ‘at 2’ not work? *)
        rewrite Nat.mod_same by lia.
        reflexivity.
Qed.

Lemma Forall_chunk'_length_pos {A} (l: list A) n:
  forall acc, Forall (fun c => length c > 0)%nat (chunk' n l acc).
Proof.
  induction l; simpl; intros.
  - destruct acc; eauto; [].
    apply Forall_cons; simpl; eauto || lia.
  - destruct (_ <? _)%nat; eauto; [].
    apply Forall_cons; rewrite ?app_length; cbn [length];
      eauto || lia.
Qed.

Lemma Forall_chunk_length_mod {A} (l: list A) n:
  (0 < n)%nat ->
  Forall (fun c => length c = n \/ length c = length l mod n)%nat (chunk n l).
Proof.
  intros; apply Forall_chunk'_length_mod; simpl; eauto.
Qed.

Lemma Forall_chunk_length_le {A} (l: list A) n:
  (0 < n)%nat -> Forall (fun c => 0 < length c <= n)%nat (chunk n l).
Proof.
  intros; eapply Forall_impl; cycle 1.
  - apply Forall_and;
      [ apply Forall_chunk_length_mod | apply Forall_chunk'_length_pos ];
      eauto.
  - cbv beta.
    pose proof Nat.mod_upper_bound (length l) n ltac:(lia).
    intros ? ([-> | ->] & ?); lia.
Qed.

(** * byte **)

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

(* FIXME isn't this defined somewhere already? *)
Definition byte_land (b1 b2: byte) :=
  byte.of_Z (Z.land (byte.unsigned b1) (byte.unsigned b2)).

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

Lemma byte_xor_comm b1 b2:
  byte.xor b1 b2 = byte.xor b2 b1.
Proof. unfold byte.xor; rewrite Z.lxor_comm; reflexivity. Qed.

(** ** le_combine / le_split **)

Arguments le_combine: simpl nomatch.
Arguments le_split : simpl nomatch.
Arguments Z.mul: simpl nomatch.

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

Definition in_bounds x :=
  0 <= x < 2 ^ 32.

Definition forall_in_bounds l:
  (Forall in_bounds l) <-> (forall i, in_bounds (nth i l 0)).
Proof.
  rewrite Forall_nth_default' with (d := 0);
    unfold in_bounds; reflexivity || lia.
Qed.

Lemma le_combine_in_bounds bs:
  (length bs <= 4)%nat ->
  in_bounds (le_combine bs).
Proof.
  unfold in_bounds; intros.
  pose proof le_combine_bound bs.
  pose proof Zpow_facts.Zpower_le_monotone 2 (8 * Z.of_nat (length bs)) 32
       ltac:(lia) ltac:(lia); lia.
Qed.

Lemma Forall_le_combine_in_bounds zs:
  Forall in_bounds (map le_combine (chunk 4 zs)).
Proof.
  eapply Forall_map, Forall_impl.
  - intros a; apply le_combine_in_bounds.
  - eapply Forall_impl; [ | apply Forall_chunk_length_le ];
      simpl; intros; lia.
Qed.

(** ** words **)

Section words.
  (* FIXME these proofs about word/Z are a pain *)
  Context {width} {word : Interface.word width} {word_ok: word.ok word}.

  Lemma _of_Z_land_ones z :
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

  Lemma _of_Z_land_ones_rotate a b (Ha: 0 <= a < 2 ^ width) (Hb: 0 < b < width) :
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

Definition w32s_of_bytes (bs: array_t byte) : array_t word :=
  List.map word.of_Z (List.map le_combine (chunk 4 bs)).

Definition bytes_of_w32s (w32s: array_t word) : array_t byte :=
  List.flat_map (le_split 4) (List.map word.unsigned w32s).

Definition array_fold_chunked {A T}
           (a: array_t T) (size: nat)
           (f: nat -> A -> list T -> A)
           a0 :=
  List.fold_left (fun acc '(i, c) => f i acc c) (enumerate 0 (chunk size a)) a0.

Definition array_map_chunked {T}
           (a: array_t T) (size: nat)
           (f: nat -> list T -> list T) :=
  List.flat_map (fun '(i, c) => f i c) (enumerate 0 (chunk size a)).

Axiom felem_size : nat.

#[local] Hint Unfold buf_make : poly.
#[local] Hint Unfold buf_push buf_append : poly.
#[local] Hint Unfold buf_split buf_unsplit buf_as_array : poly.
#[local] Hint Unfold array_split_at array_unsplit : poly.
#[local] Hint Unfold array_fold_chunked array_map_chunked : poly.
#[local] Hint Unfold array_get array_put : poly.
#[local] Hint Unfold bytes_as_felem_inplace : poly.
#[local] Hint Unfold felem_init_zero felem_add felem_mul felem_as_uint128 : poly.
#[local] Hint Unfold uint128_add bytes_as_uint128 uint128_as_bytes : poly.
#[local] Hint Unfold bytes_of_w32s w32s_of_bytes : poly.

(** * Poly1305 **)

Definition poly1305_loop scratch output msg :=
  let/n output :=
     array_fold_chunked
       msg 16
       (fun idx output ck =>
          let/n nscratch := buf_make byte felem_size in
          let/n nscratch := buf_append nscratch ck in (* len = 16 *)
          let/n nscratch := buf_push nscratch x01 in (* len = 17 *)
          let/n nscratch := bytes_as_felem_inplace nscratch in
          let/n output := felem_add output nscratch in
          let/n output := felem_mul output scratch in
          output)
       output in
  output.

Definition poly1305 (k : array_t byte) (header msg footer : array_t byte) (output: Z): array_t byte :=
  let/n (f16, l16) := array_split_at 16 k in
  let/n scratch := buf_make byte felem_size in
  let/n scratch := buf_append scratch f16 in
  let/n (scratch, lone_byte_and_felem_spare_space) := buf_split scratch in
  let/n scratch := List.map (fun '(w1, w2) => let/n w1 := byte_land w1 w2 in w1)
                           (combine scratch (le_split 16 0x0ffffffc0ffffffc0ffffffc0fffffff)) in
  let/n scratch := buf_unsplit scratch lone_byte_and_felem_spare_space in
  let/n scratch := buf_push scratch x00 in
  let/n scratch := bytes_as_felem_inplace scratch in (* B2 primitive reads first 17 bytes of longer array *)
  let/n output := felem_init_zero in
  let/n output := poly1305_loop scratch output header in
  let/n output := poly1305_loop scratch output msg in
  let/n output := poly1305_loop scratch output footer in
  let/n output := felem_as_uint128 output in
  let/n l16 := bytes_as_uint128 l16 in
  let/n output := uint128_add output l16 in
  let/n l16 := uint128_as_bytes l16 in
  let/n k := array_unsplit f16 l16 in
  let/n output := uint128_as_bytes output in
  output.

(** ** Equivalence proof **)

(* change (nlet _ ?v ?k) with (k v) at 1; cbv beta iota. *)

Lemma combine_app {A B} : forall (lA lA': list A) (lB lB': list B),
    length lA = length lB ->
    combine (lA ++ lA') (lB ++ lB') = combine lA lB ++ combine lA' lB'.
Proof.
  induction lA; destruct lB; simpl; inversion 1; try rewrite IHlA; eauto.
Qed.

Lemma enumerate_app {A} (l l': list A) start :
  enumerate start (l ++ l') =
  enumerate start l ++ enumerate (start + length l) l'.
Proof.
  unfold enumerate.
  rewrite app_length, seq_app, combine_app;
    eauto using seq_length.
Qed.

Lemma chunk_app {A} : forall (l l': list A) n,
    (length l mod n = 0)%nat ->
    chunk n (l ++ l') = chunk n l ++ chunk n l'.
Proof.
  induction l; simpl; intros.
  - reflexivity.
Admitted.

#[local] Hint Unfold poly1305_loop : poly.

Lemma poly1305_ok' k header msg footer output:
  (length header mod 16 = 0)%nat ->
  (length msg mod 16 = 0)%nat ->
  Spec.poly1305 k (header ++ msg ++ footer) = poly1305 k header msg footer output.
Proof.
  intros; unfold Spec.poly1305, poly1305.
  autounfold with poly; unfold nlet.
  Z.push_pull_mod.
  rewrite <- le_split_mod.
  unfold enumerate.
  rewrite <- !fold_left_combine_fst by (rewrite seq_length; lia).
  rewrite <- !fold_left_app, <- !chunk_app by assumption.
  repeat f_equal.
  repeat (apply FunctionalExtensionality.functional_extensionality; intros).
  Z.push_pull_mod.
  rewrite !app_nil_l.
  repeat f_equal.
  rewrite le_combine_app_0.
  rewrite <- Z_land_le_combine.
  reflexivity.
Qed.

Lemma poly1305_ok k msg output:
  Spec.poly1305 k msg = poly1305 k [] msg [] output.
Proof.
  intros; pose proof (poly1305_ok' k [] [] msg output) as H.
  simpl in H. erewrite H; reflexivity.
Qed.

(* Hint Rewrite <- le_split_mod Z_land_le_combine : poly. *)
(* Hint Rewrite le_combine_app_0 : poly. *)
(* Hint Rewrite app_nil_r : poly. *)
(* Hint Rewrite seq_length: poly. *)

(* Ltac t := *)
(*   intros *)
(*   || (autounfold with poly) *)
(*   || Z.push_pull_mod *)
(*   || (autorewrite with poly) *)
(*   || (unfold enumerate; rewrite <- fold_left_combine_fst) *)
(*   || f_equal *)
(*   || apply FunctionalExtensionality.functional_extensionality *)
(*   || lia. *)

(* Lemma poly1305_ok' k m output: *)
(*   Spec.poly1305 k m = poly1305 k m output. *)
(* Proof. *)
(*   unfold Spec.poly1305, poly1305, nlet; repeat t. *)
(* Qed. *)

(** * ChaCha20 **)

Local Notation "a + b" := (word.add (word := word) a b).
Local Notation "a ^ b" := (word.xor (word := word) a b).
Local Notation "a <<< b" := (word.slu a b + word.sru a (word.sub (word.of_Z 32) b)) (at level 30).

Definition quarter a b c d : \<< word, word, word, word \>> :=
  let/n a := a + b in  let/n d := d ^ a in  let/n d := d <<< word.of_Z 16 in
  let/n c := c + d in  let/n b := b ^ c in  let/n b := b <<< word.of_Z 12 in
  let/n a := a + b in  let/n d := d ^ a in  let/n d := d <<< word.of_Z 8 in
  let/n c := c + d in  let/n b := b ^ c in  let/n b := b <<< word.of_Z 7 in
  \< a, b, c, d \>.

Hint Rewrite Z_land_ones_rotate using (split; reflexivity) : quarter.
Hint Rewrite <- word.unsigned_xor_nowrap : quarter.
Hint Rewrite Z_land_ones_word_add : quarter.

Lemma quarter_ok0 a b c d:
  Spec.quarter (word.unsigned a, word.unsigned b, word.unsigned c, word.unsigned d) =
  let '\<a', b', c', d'\> := quarter a b c d in
  (word.unsigned a', word.unsigned b', word.unsigned c', word.unsigned d').
Proof.
  unfold Spec.quarter, quarter, nlet;
    autorewrite with quarter;
    reflexivity.
Qed.

Lemma quarter_ok a b c d:
  in_bounds a -> in_bounds b -> in_bounds c -> in_bounds d ->
  quarter (word.of_Z a) (word.of_Z b) (word.of_Z c) (word.of_Z d) =
  let '(a', b', c', d') := Spec.quarter (a, b, c, d) in
  \< word.of_Z a', word.of_Z b', word.of_Z c', word.of_Z d' \>.
Proof.
  unfold in_bounds; intros.
  set (wa := word.of_Z a); set (wb := word.of_Z b); set (wc := word.of_Z c); set (wd := word.of_Z d).
  rewrite <- (word.unsigned_of_Z_nowrap a), <- (word.unsigned_of_Z_nowrap b) by assumption.
  rewrite <- (word.unsigned_of_Z_nowrap c), <- (word.unsigned_of_Z_nowrap d) by assumption.
  rewrite quarter_ok0; subst wa wb wc wd; destruct (quarter _ _ _ _) as (?&?&?&?); cbn -[word.of_Z].
  rewrite !word.of_Z_unsigned; reflexivity.
Qed.

Lemma quarter_in_bounds a b c d:
  in_bounds a -> in_bounds b -> in_bounds c -> in_bounds d ->
  let '(a', b', c', d') := Spec.quarter (a, b, c, d) in
  in_bounds a' /\ in_bounds b' /\ in_bounds c' /\ in_bounds d'.
Proof.
  unfold in_bounds; intros.
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

Lemma quarterround_ok x y z t st :
  Forall in_bounds st ->
  List.map word.of_Z (Spec.quarterround x y z t st) =
  quarterround x y z t (List.map word.of_Z st).
Proof.
  unfold Spec.quarterround, quarterround, nlet; autounfold with poly; intros H.
  rewrite forall_in_bounds in H.
  rewrite !map_nth, !quarter_ok by auto.
  destruct (Spec.quarter _) as (((?&?)&?)&?).
  rewrite !map_upd; reflexivity.
Qed.

Lemma quarterround_in_bounds x y z t a:
  Forall in_bounds a ->
  Forall in_bounds (Spec.quarterround x y z t a).
Proof.
  unfold Spec.quarterround, nlet; autounfold with poly; intros Ha.
  pose proof Ha as Ha'; rewrite forall_in_bounds in Ha.
  pose proof quarter_in_bounds (nth x a 0) (nth y a 0) (nth z a 0) (nth t a 0)
       ltac:(eauto) ltac:(eauto) ltac:(eauto) ltac:(eauto) as Hb.
  destruct (Spec.quarter _) as (((?&?)&?)&?).
  destruct Hb as (?&?&?&?).
  repeat (apply Forall_upd; auto).
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

  eapply Nat_iter_rew_inv with (P := Forall in_bounds); intros.
  - eauto 10 using quarterround_in_bounds.
  - rewrite !quarterround_ok; try reflexivity;
      eauto 10 using quarterround_in_bounds.
  - repeat (apply Forall_cons; [ red; lia | ]).
    apply Forall_app; split;
      apply Forall_le_combine_in_bounds.
  - cbn [List.map]; rewrite List.map_app; reflexivity.
Qed.

Definition chacha20_encrypt key start nonce plaintext :=
  let plaintext := array_map_chunked plaintext 64 (fun idx chunk => (* FIXME nplaintext *)
    let counter := word.add (word.of_Z (Z.of_nat start)) (word.of_Z (Z.of_nat idx)) in
    let scratch := buf_make word 4 in
    let scratch := buf_push scratch counter in
    let nonce := w32s_of_bytes nonce in
    let scratch := buf_append scratch nonce in (* FIXME? You can save a scratch buffer by doing the nonce concatenation of chacha20 here instead *)
    let nonce := bytes_of_w32s nonce in
    let scratch := buf_as_array scratch in
    let scratch := bytes_of_w32s scratch in
    let st := buf_make word 16 in
    let st := chacha20_block key scratch st in
    let chunk := List.map (fun '(st_i, ss_i) =>
                            let st_i := byte.xor st_i ss_i in
                            st_i)
                         (combine chunk st) in
    chunk) in
  plaintext.


Lemma enumerate_offset {A} (l: list A) : forall (start: nat),
    enumerate start l = map (fun p => (fst p + start, snd p)%nat) (enumerate 0 l).
Proof.
  unfold enumerate; induction l; simpl; intros.
  - reflexivity.
  - rewrite (IHl (S start)), (IHl 1%nat), List.map_map.
    f_equal. simpl. apply map_ext.
    intros; f_equal; lia.
Qed.

Lemma Forall_In {A} {P : A -> Prop} {l : list A}:
  Forall P l -> forall {x}, In x l -> P x.
Proof.
  intros HF; rewrite Forall_forall in HF; intuition.
Qed.

Lemma flat_map_split_combine_chunk:
  forall bs n,
    (0 < n)%nat ->
    (length bs mod n)%nat = 0%nat ->
    flat_map (le_split n) (map le_combine (chunk n bs)) = bs.
Proof.
  intros; rewrite flat_map_concat_map, map_map, map_id, concat_chunk; [reflexivity|].
  intros * Hin;
    pose proof (Forall_In (Forall_chunk_length_mod _ n ltac:(lia)) Hin);
    pose proof (Forall_In (Forall_chunk_length_le _ n ltac:(lia)) Hin);
    cbv beta in *.
  rewrite split_le_combine'; reflexivity || lia.
Qed.

Lemma map_unsigned_of_Z_combine_4 bs :
  map (fun z : Z => word.unsigned (word := word) (word.of_Z z))
      (map le_combine (chunk 4 bs)) =
  map le_combine (chunk 4 bs).
Proof.
  rewrite map_id; [ reflexivity | ].
  intros * Hin%(Forall_In (Forall_le_combine_in_bounds bs)).
  apply word.unsigned_of_Z_nowrap; assumption.
Qed.

Lemma chacha20_encrypt_ok key start nonce plaintext :
  (length nonce mod 4 = 0)%nat ->
  Spec.chacha20_encrypt key start nonce plaintext =
  chacha20_encrypt key start nonce plaintext.
Proof.
  unfold Spec.chacha20_encrypt, chacha20_encrypt, nlet;
    autounfold with poly; intros.
  rewrite enumerate_offset.
  rewrite flat_map_concat_map, map_map, <- flat_map_concat_map.
  f_equal.
  apply FunctionalExtensionality.functional_extensionality; intros (?&?).
  unfold zip; rewrite map_combine_comm by apply byte_xor_comm; f_equal.
  f_equal.
  rewrite chacha20_block_ok.
  f_equal.
  cbn [List.app List.map].
  rewrite word.unsigned_add, !word.unsigned_of_Z, map_map.
  rewrite map_unsigned_of_Z_combine_4.
  cbn [List.flat_map]. f_equal.
  + unfold word.wrap; Z.push_pull_mod; rewrite <- le_split_mod.
    f_equal; simpl; lia.
  + rewrite flat_map_split_combine_chunk; eauto || reflexivity.
Qed.

(* let pad16 xs := repeat x00 (Nat.div_up (length xs) 16 * 16 - length xs) in *)

Definition padded_len {A} (l: array_t A) :=
  (Nat.div_up (length l) 16 * 16)%nat. (* FIXME 16 - (length l) mod 16 *)

Definition padding_len {A} (l: array_t A) :=
  (padded_len l - length l)%nat.

Definition buf_pad {T} (b: buffer_t T) (len: nat) (t: T) :=
  b ++ repeat t (len - length b).

Definition chacha20poly1305_aead_encrypt aad key iv constant plaintext tag :=
  let/n nonce := buf_make word 2 in
  let/n otk_nonce := buf_make word 4 in

  let/n otk_nonce := buf_push otk_nonce (word.of_Z 0) in

  let/n constant := w32s_of_bytes constant in
  let/n nonce := buf_append nonce constant in
  let/n otk_nonce := buf_append otk_nonce constant in
  let/n constant := bytes_of_w32s constant in

  let/n iv := w32s_of_bytes iv in
  let/n nonce := buf_append nonce iv in
  let/n otk_nonce := buf_append otk_nonce iv in
  let/n iv := bytes_of_w32s iv in

  let/n nonce := buf_as_array nonce in
  let/n nonce := bytes_of_w32s nonce in

  let/n otk_nonce := buf_as_array otk_nonce in
  let/n otk_nonce := bytes_of_w32s otk_nonce in

  let/n otk := buf_make word 16 in
  let/n otk := chacha20_block key otk_nonce otk in
  let/n (otk, rest) := array_split_at 32 otk in

  let/n plaintext := chacha20_encrypt key 1 nonce plaintext in

  (* let/n mac_len := padded_len aad in *)
  (* let/n mac_data := buf_make byte mac_len in *)
  (* let/n mac_data := buf_append mac_data aad in *)
  (* let/n mac_data := buf_pad mac_data mac_len x00 in *)
  (* let/n mac_data := buf_as_array mac_data in *)

  let/n footer := buf_make word 4 in
  let/n footer := buf_push footer (word.of_Z (Z.of_nat (length aad))) in
  let/n footer := buf_push footer (word.of_Z 0) in
  let/n footer := buf_push footer (word.of_Z (Z.of_nat (length plaintext))) in
  let/n footer := buf_push footer (word.of_Z 0) in
  let/n footer := buf_as_array footer in
  let/n footer := bytes_of_w32s footer in

  let mac_data := aad in
  let/n tag := poly1305 otk mac_data plaintext footer tag in
  let/n otk := array_unsplit otk rest in
  (plaintext, tag).

#[local] Hint Unfold buf_pad : poly.

Lemma le_split_0_l z:
  le_split 0 z = [].
Proof. reflexivity. Qed.

Lemma le_split_0_r n:
  le_split n 0 = repeat x00 n.
Proof.
  induction n.
  - reflexivity.
  - unfold le_split; fold le_split.
    rewrite Z.shiftr_0_l, IHn; reflexivity.
Qed.

Lemma le_split_zeroes : forall m n z,
  0 <= z < 2 ^ (8 * Z.of_nat n) ->
  le_split (n + m) z = le_split n z ++ le_split m 0.
Proof.
  induction n; cbn -[Z.pow Z.of_nat Z.shiftr]; intros * (Hle & Hlt).
  - replace z with 0 by lia; reflexivity.
  - rewrite IHn, !le_split_0_r; try reflexivity; [].
    rewrite Z.shiftr_div_pow2 by lia; split.
    + apply Z.div_pos; lia.
    + replace (8 * Z.of_nat (S n)) with (8 + 8 * Z.of_nat n)%Z in Hlt by lia.
      rewrite Z.pow_add_r in Hlt by lia.
      apply Z.div_lt_upper_bound; lia.
Qed.

Lemma chacha20poly1305_aead_encrypt_ok aad key iv constant plaintext tag:
  (length iv mod 4 = 0)%nat ->
  (length constant mod 4 = 0)%nat ->
  0 <= Z.of_nat (length aad) < 2 ^ 32 ->
  0 <= Z.of_nat (length plaintext) < 2 ^ 32 ->
  Spec.chacha20poly1305_aead_encrypt aad key iv constant plaintext =
  chacha20poly1305_aead_encrypt aad key iv constant plaintext tag.
Proof.
  unfold Spec.chacha20poly1305_aead_encrypt, chacha20poly1305_aead_encrypt, nlet;
    autounfold with poly; intros.

  assert (length (constant ++ iv) mod 4 = 0)%nat. {
    rewrite ?app_length, Nat.add_mod by lia.
    replace (length iv mod 4)%nat.
    replace (length constant mod 4)%nat.
    reflexivity.
  }

  cbn [List.app List.map List.flat_map].

  rewrite !map_app, !map_map with (f := word.of_Z), !map_unsigned_of_Z_combine_4.
  rewrite <- !map_app, <- !chunk_app, flat_map_split_combine_chunk;
    [ | eauto || lia ..].
  rewrite chacha20_encrypt_ok by eauto.
  rewrite chacha20_block_ok.

  apply f_equal2. reflexivity.

  rewrite !(le_split_zeroes 4 4).
  rewrite <- !app_assoc.
  eassert (?[aad] ++ ?[aad_pad] ++ ?[ciphertext] ++ ?[ciphertext_pad] ++ ?[rest] =
           (?aad ++ ?aad_pad) ++ (?ciphertext ++ ?ciphertext_pad) ++ ?rest) as ->
      by (rewrite <- !app_assoc; reflexivity).
  rewrite poly1305_ok' with (output := tag). (* FIXME no need for msg to have length multiple of 16: real thm is that padding message is same as without padding *)

  rewrite !word.unsigned_of_Z_0.
  rewrite !word.unsigned_of_Z_nowrap.

  apply f_equal4.
  admit. (* FIXME this isn't right: we need a more powerful lemma that skips the padding *)
  admit.

  Lemma length_padded_mod {A} n (l: list A) a:
    (length (l ++ repeat a (Nat.div_up (length l) n * n - length l)) mod n = 0)%nat.
  Proof.
    destruct (Nat.eq_dec n 0); [ subst; reflexivity | ].
    pose proof Nat.div_up_range (length l) n ltac:(eassumption).
    rewrite app_length, repeat_length, <- le_plus_minus by lia.
    apply Nat.mod_mul; assumption.
  Qed.

  Lemma concat_length {A} (lss: list (list A)) :
    length (List.concat lss) =
    List.fold_left Nat.add (List.map (@length _) lss) 0%nat.
  Proof.
    rewrite fold_symmetric by eauto with arith.
    induction lss; simpl; rewrite ?app_length, ?IHlss; reflexivity.
  Qed.

  Lemma map_combine_fst {A B}: forall lA lB,
      length lA = length lB ->
      map fst (@combine A B lA lB) = lA.
  Proof.
    induction lA; destruct lB; simpl; intros; rewrite ?IHlA; reflexivity || lia.
  Qed.

  Lemma map_combine_snd {A B}: forall lB lA,
      length lA = length lB ->
      map snd (@combine A B lA lB) = lB.
  Proof.
    induction lB; destruct lA; simpl; intros; rewrite ?IHlB; reflexivity || lia.
  Qed.

  Lemma length_spec_chacha20_encrypt key start nonce plaintext :
    length (Spec.chacha20_encrypt key start nonce plaintext) = length plaintext.
  Proof.
    unfold Spec.chacha20_encrypt.
    rewrite flat_map_concat_map, concat_length, map_map.
    erewrite map_ext with (g := fun x => length (snd x)); cycle 1.
    - intros (?&?); unfold zip.
      rewrite map_length, combine_length.
      admit. (* FIXME needs a more powerful lemma than map_ext (needs to know List.In *)
    - rewrite <- map_map with (f := snd) (g := @length _).
      unfold enumerate; rewrite map_combine_snd by apply seq_length.
      rewrite <- concat_length, concat_chunk; reflexivity.
  Admitted.

  Lemma length_chacha20_encrypt key start nonce plaintext :
    (length nonce mod 4 = 0)%nat ->
    length (chacha20_encrypt key start nonce plaintext) = length plaintext.
  Proof.
    intros; rewrite <- chacha20_encrypt_ok by assumption;
      apply length_spec_chacha20_encrypt.
  Qed.

  all: try apply length_padded_mod.
  all: try rewrite length_chacha20_encrypt.
  all: try reflexivity.
  all: try eassumption.
Qed.

(* Print Assumptions poly1305_ok. *)
(* Print Assumptions chacha20_encrypt_ok. *)
