(* Rewritten versions of poly1305 and chacha20 that you can compile with Rupicola *)
Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Crypto.Spec.
Require Import bedrock2.BasicC32Semantics.

(* TODO array_split should record a special fact in the context to make it trivial to re-split. *)
Open Scope Z_scope.

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

Definition buffer_t := List.list.
Definition buf_make T (n: nat) : buffer_t T := [].
Definition buf_push {T} (buf: buffer_t T) (t: T) := buf ++ [t].
Definition buf_append {T} (buf: buffer_t T) (arr: array_t T) := buf ++ arr.
Definition buf_split {T} (buf: buffer_t T) : array_t T * buffer_t T := (buf, []).
Definition buf_unsplit {T} (arr: array_t T) (buf: buffer_t T) : buffer_t T := arr.

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

Definition byte_land (b1 b2: byte) :=
  byte.of_Z (Z.land (byte.unsigned b1) (byte.unsigned b2)).

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

#[local] Hint Unfold buf_make : poly.
#[local] Hint Unfold buf_split : poly.
#[local] Hint Unfold buf_push : poly.
#[local] Hint Unfold buf_append : poly.
#[local] Hint Unfold buf_unsplit : poly.
#[local] Hint Unfold array_split_at array_unsplit : poly.
#[local] Hint Unfold array_fold_chunked : poly.
#[local] Hint Unfold bytes_as_felem_inplace : poly.
#[local] Hint Unfold felem_init_zero felem_add felem_mul felem_as_uint128 : poly.
#[local] Hint Unfold uint128_add bytes_as_uint128 uint128_as_bytes : poly.


Arguments le_combine: simpl nomatch.
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


Lemma poly1305_ok k m output:
  List.length k = 32%nat ->
  poly1305 k m = poly1305_uneven_length k m output.
Proof.
  intros; unfold poly1305_uneven_length, poly1305.
  autounfold with poly.
  change (nlet _ ?v ?k) with (k v) at 1; cbv beta iota.
  change (nlet _ ?v ?k) with (k v) at 1; cbv beta iota.
  change ([] ++ ?x) with x.
  change (nlet _ ?v ?k) with (k v) at 1; cbv beta iota.
  change (nlet _ ?v ?k) with (k v) at 1; cbv beta iota.
  change (nlet _ ?v ?k) with (k v) at 1; cbv beta iota.
  change (nlet _ ?v ?k) with (k v) at 1; cbv beta iota.
  change (nlet _ ?v ?k) with (k v) at 1; cbv beta iota.
  change (nlet _ ?v ?k) with (k v) at 1; cbv beta iota.
  change (nlet _ ?v ?k) with (k v) at 1; cbv beta iota.

  change (nlet _ ?v ?k) with (k v) at 1; cbv beta iota.
  change (nlet _ ?v ?k) with (k v) at 2; cbv beta iota.
  change ([] ++ ?x) with x.
  change (nlet _ ?v ?k) with (k v) at 2; cbv beta iota.
  change (nlet _ ?v ?k) with (k v) at 2; cbv beta iota.
  change (nlet _ ?v ?k) with (k v) at 2; cbv beta iota.
  change (nlet _ ?v ?k) with (k v) at 2; cbv beta iota.
  change (nlet _ ?v ?k) with (k v) at 2; cbv beta iota.

  change (nlet _ ?v ?k) with (k v) at 1; cbv beta iota.
  change (nlet _ ?v ?k) with (k v) at 2; cbv beta iota.
  change (nlet _ ?v ?k) with (k v) at 2; cbv beta iota.

  rewrite split_le_combine' by (rewrite skipn_length; lia).

  change (nlet _ ?v ?k) with (k v) at 3; cbv beta iota.
  change (nlet _ ?v ?k) with (k v) at 3; cbv beta iota.
  change (nlet _ ?v ?k) with (k v) at 3; cbv beta iota.

  change (nlet _ ?v ?k) with (k v) at 2; cbv beta iota.
  change (nlet _ ?v ?k) with (k v) at 1; cbv beta iota.

  Z.push_pull_mod.
  rewrite <- le_split_mod.

  f_equal.
  f_equal.

  (* Lemma fold_left_Proper : *)
  (*   forall [A B : Type] (f f': A -> B -> A) (l l': list B) (i i': A), *)
  (*     l = l' -> i = i' -> *)
  (*     (forall a b, f a b = f' a b) -> *)
  (*     fold_left f l i = fold_left f' l' i'. *)
  (* Proof. induction l; intros; subst; simpl; eauto. Qed. *)
  f_equal. (* meh *)
  apply FunctionalExtensionality.functional_extensionality; intros.
  apply FunctionalExtensionality.functional_extensionality; intros.

  Z.push_pull_mod.
  f_equal.
  f_equal.

  rewrite le_combine_app_0.
Admitted.
