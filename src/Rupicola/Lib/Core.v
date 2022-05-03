From Coq Require Export
     Classes.Morphisms Numbers.DecimalString
     String List ZArith Lia.
From bedrock2 Require Export
     Array ArrayCasts Map.Separation ProgramLogic
     Map.SeparationLogic Scalars Syntax WeakestPreconditionProperties
     ZnWords.
From coqutil Require Export
     dlet Byte List
     Z.PushPullMod Tactics.Tactics Tactics.letexists
     Word.Interface Word.Properties Word.Bitwidth
     Map.Interface Map.Properties Map.SortedList.
From coqutil Require Import
     Decidable.
From coqutil Require
     Map.SortedListString.

Export Syntax.Coercions.

Open Scope string_scope.
Export ListNotations.

Declare Scope sep_scope.
Delimit Scope sep_scope with sep.
Infix "*" := (sep) : sep_scope.

Global Set Nested Proofs Allowed.
Global Set Default Goal Selector "1".

Module P2.
  (* Note: Unlike ``coqutil.Datatypes.PrimitivePair.pair``, these are
     non-dependent and the notation for them associates to the left. *)
  Section Primitive.
    Set Primitive Projections.
    Record prod {A B} := pair { car: A; cdr: B }.
  End Primitive.
  Arguments prod: clear implicits.
  Arguments pair {A B} car cdr.
End P2.

Declare Scope p2_scope.
Delimit Scope p2_scope with p2.
Notation "\<<  x ,  .. ,  y ,  z  \>>" :=
  (P2.prod x%type .. (P2.prod y%type z%type) ..) : p2_scope.
Notation "\<  x ,  .. ,  y ,  z  \>" :=
  (P2.pair x .. (P2.pair y z) ..) : p2_scope.
Open Scope p2_scope.

(* ⚠ These pairs associate to the *left*: \< 1, 2, 3 \> is \< 1, \< 2, 3 \> \> *)
Definition __p2_assoc_test:
  (\< 1, 2, 3 \>       <: \<< nat, nat, nat \>>) =
  (\< 1, \< 2, 3 \> \> <: \<< nat, \<< nat, nat \>> \>>)
  := eq_refl.

Create HintDb lia.
#[export] Hint Extern 1 => lia : lia.

Create HintDb nia.
#[export] Hint Extern 1 => nia : nia.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Module map.
  Section __.
    Context {key value value'}
            {map : map.map key value}
            {map' : map.map key value'}
            {map_ok : map.ok map}
            {map'_ok : map.ok map'}
            {key_eqb : key -> key -> bool}
            {key_eq_dec : EqDecider key_eqb}.

    Implicit Types (m : map).

    Lemma get_mapped m k (f: value -> value'):
      map.get (map.fold (fun (m' : map') k v => map.put m' k (f v)) map.empty m) k =
      match map.get m k with
      | Some v => Some (f v)
      | None => None
      end.
    Proof.
      apply map.fold_spec.
      - rewrite !map.get_empty; reflexivity.
      - intros; rewrite !map.get_put_dec; destruct key_eqb; eauto.
    Qed.
  End __.

  Definition map_of_list' {K V} {map: map.map K V} (rev_bindings: list (K * V)) (acc: map) :=
    List.fold_right (fun '(k, v) m => map.put m k v) acc rev_bindings.

  Lemma of_list_is_fold_right' {K V} {map: map.map K V}:
    forall bs acc,
      (fix of_list (l : list (K * V)) : map :=
         match l with
         | [] => acc
         | (k, v) :: l => map.put (of_list l) k v
         end) bs =
      map_of_list' bs acc.
  Proof.
    induction bs as [ | [k v] ]; cbn; intros.
    - reflexivity.
    - rewrite IHbs; reflexivity.
  Qed.

  Lemma of_list_is_fold_right {K V} {map: map.map K V}:
    forall bs, map.of_list bs = map_of_list' bs map.empty :> map.
  Proof. intros; apply of_list_is_fold_right'. Qed.

  Definition map_domains_diff {K V} {map: map.map K V} (m0 m1: map) :=
    map.keys (map.fold (fun (m0: map) k _ => map.remove m0 k) m0 m1).

  Section MapCompat.
    Context {K V0 V1}
            {map0: map.map K V0}
            {map1: map.map K V1}
            {map_ok0: map.ok map0}
            {map_ok1: map.ok map1}
            {K_eqb : K -> K -> bool}
            {K_eq_dec : EqDecider K_eqb}
            (fV: V0 -> V1).

    Definition mapped_compat (m0 : map0) (m1 : map1) :=
      forall k v, map.get m0 k = Some v ->
             map.get m1 k = Some (fV v).

    Lemma mapped_compat_of_list bs1 bs2:
      bs2 = List.map (fun pr => (fst pr, fV (snd pr))) bs1 ->
      mapped_compat (map.of_list (map := map0) bs1)
                    (map.of_list (map := map1) bs2).
    Proof.
      induction bs1 as [| (k1 & v1) bs1] in bs2 |- *;
        (destruct bs2 as [| (k2 & v2) bs2];
         cbn - [map.get map.put];
         intros H k v; inversion H; subst; clear H;
         try congruence).
      - rewrite map.get_empty; inversion 1.
      - rewrite !map.get_put_dec.
        destruct (K_eq_dec k1 k).
        + inversion 1; subst; reflexivity.
        + intros. apply (IHbs1 _ eq_refl). eassumption.
    Qed.
  End MapCompat.

  Definition map_eq {K V} {map0 map1: map.map K V}
             {map_ok0: map.ok map0} {map_ok1: map.ok map1}
             m0 m1 :=
    (forall k, map.get (map := map0) m0 k = map.get (map := map1) m1 k).

  Instance eq_refl {K V} {map: map.map K V} {map_ok: map.ok map} :
    RelationClasses.Reflexive (@map_eq K V map map map_ok map_ok).
  Proof. unfold map_eq; constructor; congruence. Qed.

  Lemma eq_trans {K V}
        {map0 map1 map2: map.map K V}
        {map_ok0: map.ok map0} {map_ok1: map.ok map1} {map_ok2: map.ok map2} :
    forall m0 m1 m2,
      map_eq (map0 := map0) (map1 := map1) m0 m1 ->
      map_eq (map0 := map1) (map1 := map2) m1 m2 ->
      map_eq m0 m2.
  Proof. unfold map_eq; congruence. Qed.

  Lemma eq_sym {K V}
        {map0 map1: map.map K V}
        {map_ok0: map.ok map0} {map_ok1: map.ok map1} :
    forall m0 m1,
      map_eq (map0 := map0) (map1 := map1) m0 m1 ->
      map_eq (map0 := map1) (map1 := map0) m1 m0.
  Proof. unfold map_eq; congruence. Qed.

  Lemma put_proper {K V}
        {map0 map1: map.map K V}
        {map_ok0: map.ok map0} {map_ok1: map.ok map1}
        {key_eqb: K -> K -> bool}
        {key_eq_dec : EqDecider key_eqb} :
    forall k v (m0: map.rep (map := map0)) (m1: map.rep (map := map1)),
      map_eq m0 m1 ->
      map_eq (map.put m0 k v) (map.put m1 k v).
  Proof.
    intros * Heq k.
    destruct (key_eqb k0 k) eqn:Hk;
      [ eapply (Decidable.BoolSpec_true _ _ _ (key_eq_dec _ _)) in Hk |
        eapply (Decidable.BoolSpec_false _ _ _ (key_eq_dec _ _)) in Hk ];
      subst; rewrite ?map.get_put_same, ?map.get_put_diff; auto.
  Qed.

  Lemma remove_proper {K V}
        {map0 map1: map.map K V}
        {map_ok0: map.ok map0} {map_ok1: map.ok map1}
        {key_eqb: K -> K -> bool}
        {key_eq_dec : EqDecider key_eqb} :
    forall k (m0: map.rep (map := map0)) (m1: map.rep (map := map1)),
      map_eq m0 m1 ->
      map_eq (map.remove m0 k) (map.remove m1 k).
  Proof.
    intros * Heq k.
    destruct (key_eqb k0 k) eqn:Hk;
      [ eapply (Decidable.BoolSpec_true _ _ _ (key_eq_dec _ _)) in Hk |
        eapply (Decidable.BoolSpec_false _ _ _ (key_eq_dec _ _)) in Hk ];
      subst; rewrite ?map.get_remove_same, ?map.get_remove_diff; auto.
  Qed.

  Definition remove_many {K V} {M: map.map K V} (m : M) (ks: list K) :=
    List.fold_left map.remove ks m.

  Lemma remove_many_proper {K V}
        {map0 map1: map.map K V}
        {map_ok0: map.ok map0} {map_ok1: map.ok map1}
        {key_eqb: K -> K -> bool}
        {key_eq_dec : EqDecider key_eqb} :
    forall ks (m0: map.rep (map := map0)) (m1: map.rep (map := map1)),
      map_eq m0 m1 ->
      map_eq (remove_many m0 ks) (remove_many m1 ks).
  Proof.
    unfold remove_many; induction ks; simpl; intros.
    - assumption.
    - apply IHks, remove_proper; assumption.
  Qed.

  Lemma ext_eq {K V} {map: map.map K V} {map_ok: map.ok map} :
    forall m0 m1, map_eq m0 m1 -> m0 = m1.
  Proof. apply map.map_ext. Qed.

  Lemma ext_rev {K V} {map: map.map K V} {map_ok: map.ok map} :
    forall m0 m1, m0 = m1 -> map_eq m0 m1.
  Proof. intros; subst; reflexivity. Qed.

  Lemma of_list_proper' {K V}
        {map0 map1: map.map K V}
        {map_ok0: map.ok map0} {map_ok1: map.ok map1}
        {key_eqb: K -> K -> bool}
        {key_eq_dec : EqDecider key_eqb} :
    forall bs m0 m1,
      map_eq (map0 := map0) (map1 := map1) m0 m1 ->
      map_eq (map_of_list' bs m0)
             (map_of_list' bs m1).
  Proof.
    induction bs as [ | (k & v) bs ]; simpl; intros.
    - assumption.
    - apply put_proper, IHbs; assumption.
  Qed.

  Lemma eq_empty {K V}:
    forall {map0 map1: map.map K V}
      {map_ok0: map.ok map0} {map_ok1: map.ok map1},
      map_eq (map.empty (map := map0)) (map.empty (map := map1)).
  Proof.
    red; intros; rewrite !map.get_empty; reflexivity.
  Qed.

  Lemma of_list_proper {K V}
        {map0 map1: map.map K V}
        {map_ok0: map.ok map0} {map_ok1: map.ok map1}
        {key_eqb: K -> K -> bool}
        {key_eq_dec : EqDecider key_eqb} :
    forall bs,
      map_eq (map.of_list (map := map0) bs)
             (map.of_list (map := map1) bs).
  Proof.
    intros; rewrite !of_list_is_fold_right;
      apply of_list_proper', eq_empty.
  Qed.

  Lemma eq_of_list {K V}
        {map0 map1: map.map K V}
        {map_ok0: map.ok map0} {map_ok1: map.ok map1}
        {key_eqb: K -> K -> bool}
        {key_eq_dec : EqDecider key_eqb} :
    forall b1 b2,
      map_eq (map.of_list (map := map0) b1) (map.of_list (map := map0) b2) ->
      map_eq (map.of_list (map := map1) b1) (map.of_list (map := map1) b2).
  Proof.
    intros.
    eapply (eq_trans (map1 := map0));
      [ eapply (eq_trans (map1 := map0)) | ].
    all: eauto using @of_list_proper.
  Qed.

  Lemma remove_many_diff_of_str_list {V} {map: map.map string V} {map_ok: map.ok map}:
    let SM := SortedListString.map V in
    let SM_ok := SortedListString.ok V in
    forall (b0 b1: list (string * V)) ks,
      let sb0 := map.of_list (map := SM) b0 in
      let sb1 := map.of_list (map := SM) b1 in
      ks = map_domains_diff sb0 sb1 -> (* Used for unification *)
      remove_many sb0 ks = sb1 ->
      remove_many (map.of_list (map := map) b0) ks = map.of_list b1.
  Proof.
    intros ?? * Hks Hm%ext_rev; apply ext_eq.
    eapply (eq_trans (map1 := SM)); [ eapply remove_many_proper, of_list_proper | ].
    eapply (eq_trans (map1 := SM)); [ | eapply of_list_proper ].
    exact Hm.
  Qed.

  Lemma get_of_str_list {V} {map: map.map string V} {map_ok: map.ok map}:
    let SM := SortedListString.map V in
    let SM_ok := SortedListString.ok V in
    forall (b: list (string * V)) k v,
      let sb := map.of_list (map := SM) b in
      map.get sb k = v ->
      map.get (map.of_list (map := map) b) k = v.
  Proof.
    intros; rewrite of_list_proper; eassumption.
  Qed.

  Lemma eq_of_str_list {V} {map: map.map string V} {map_ok: map.ok map}:
    let SM := SortedListString.map V in
    let SM_ok := SortedListString.ok V in
    forall (b1 b2: list (string * V)),
      map.of_list (map := SM) b1 = map.of_list (map := SM) b2 ->
      map.of_list (map := map) b1 = map.of_list (map := map) b2.
  Proof.
    intros SM SM_ok b1 b2 H%ext_rev; apply ext_eq.
    apply eq_of_list; assumption.
  Qed.

  Fixpoint list_assoc_str {V} (k: string) (l: list (string * V)) :=
    match l with
    | [] => None
    | (k', v) :: l => if String.eqb k' k then Some v else list_assoc_str k l
    end.

  Lemma get_of_str_list_assoc {V} {map: map.map string V} {map_ok: map.ok map}:
    forall k bs,
      map.get (map.of_list (map := map) bs) k =
      list_assoc_str k bs.
  Proof.
    induction bs as [|(k', v) bs IHbs]; simpl; intros.
    - rewrite map.get_empty; reflexivity.
    - rewrite map.get_put_dec, IHbs; reflexivity.
  Qed.

  Lemma get_of_str_list_assoc_impl {V} {map: map.map string V} {map_ok: map.ok map}:
    forall k bs v,
      list_assoc_str k bs = v ->
      map.get (map.of_list (map := map) bs) k = v.
  Proof. intros; rewrite get_of_str_list_assoc; eassumption. Qed.
End map.

Hint Rewrite @map.get_put_diff @map.get_put_same @map.put_put_same
     @map.remove_put_diff @map.remove_put_same
     @map.remove_empty @map.get_empty
     using (typeclasses eauto || congruence) : mapsimpl.

Section Vectors.
  Lemma Vector_to_list_length {T n}:
    forall (v: Vector.t T n),
      List.length (Vector.to_list v) = n.
  Proof.
    induction v; cbn.
    - reflexivity.
    - f_equal; assumption.
  Qed.

  Lemma Vector_nth_hd_skipn {T n}:
    forall (f: Fin.t n) idx (v : Vector.t T n) (t0 : T),
      idx = proj1_sig (Fin.to_nat f) ->
      Vector.nth v f = List.hd t0 (List.skipn idx (Vector.to_list v)).
  Proof.
    induction f; cbn; intros; rewrite (Vector.eta v).
    - subst; reflexivity.
    - subst; destruct (Fin.to_nat f); cbn.
      erewrite IHf; reflexivity.
  Qed.

  Lemma Vector_to_list_app {A n1 n2} :
    forall v1 v2,
      Vector.to_list (@Vector.append A n1 n2 v1 v2) =
      List.app (Vector.to_list v1) (Vector.to_list v2).
  Proof.
    induction v1; cbn; intros.
    - reflexivity.
    - f_equal. apply IHv1.
  Qed.

  Lemma Vector_to_list_replace {A n}:
    forall (a: Vector.t A n) (idx: nat) (f: Fin.t n) v,
      idx = proj1_sig (Fin.to_nat f) ->
      Vector.to_list (Vector.replace a f v) =
      replace_nth idx (Vector.to_list a) v.
  Proof.
    intros; subst; induction f; cbn; intros; rewrite (Vector.eta a).
    - reflexivity.
    - destruct (Fin.to_nat f); cbn in *.
      f_equal; apply IHf.
  Qed.

  Lemma Vector_nth_replace {T n}:
    forall (idx: Fin.t n) (v: Vector.t T n) (val: T),
      Vector.nth (Vector.replace v idx val) idx = val.
  Proof.
    induction idx; intros; rewrite (Vector.eta v); cbn; try rewrite IHidx; reflexivity.
  Qed.
End Vectors.

Global Open Scope Z_scope.

Section Arith.
  Lemma Z_land_leq_right a b
    : 0 <= a -> 0 <= b ->
      0 <= Z.land a b <= b.
  Proof.
    destruct a as [|pa|], b as [|pb|];
      rewrite ?Z.land_0_l, ?Z.land_0_r;
      try lia; intros _ _.
    revert pb; induction pa; destruct pb; simpl in *; try lia.
    all: specialize (IHpa pb); destruct Pos.land in *; simpl; lia.
  Qed.

  Lemma Nat_mod_eq' a n:
    n <> 0%nat ->
    a = (n * (a / n) + (a mod n))%nat.
  Proof.
    intros; pose proof Nat.mul_div_le a n.
    rewrite Nat.mod_eq; lia.
  Qed.

  Lemma Nat_mod_eq'' a n:
    n <> 0%nat ->
    (n * (a / n) = a - (a mod n))%nat.
  Proof.
    intros; pose proof Nat.mul_div_le a n.
    rewrite Nat.mod_eq; lia.
  Qed.

  Lemma Z_mod_eq' a b:
    b <> 0 ->
    a = b * (a / b) + a mod b.
  Proof. pose proof Z.mod_eq a b; lia. Qed.

  Lemma Z_mod_eq'' a b:
    b <> 0 ->
    b * (a / b) = a - a mod b.
  Proof. pose proof Z.mod_eq a b; lia. Qed.
End Arith.

(** ** Nat.iter **)

Lemma Nat_iter_inv {A} (P: A -> Prop) (fA: A -> A):
  (forall a, P a -> P (fA a)) ->
  forall n a,
    P a ->
    P (Nat.iter n fA a).
Proof. intros Hind; induction n; simpl; auto. Qed.

Lemma Nat_iter_const_length {A : Type} f : forall (n : nat) (l0 : list A),
    (forall l, length (f l) = length l) ->
    length (Nat.iter n f l0) = length l0.
Proof. intros; apply Nat_iter_inv; congruence. Qed.

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

Import List.

(* TODO: should be upstreamed to coqutil *)
Module word.
  Section __.
    Context {width} {word : Interface.word width} {ok : word.ok word}.

    Lemma wrap_small x :
      0 <= x < 2 ^ width ->
      word.wrap x = x.
    Proof. apply Z.mod_small. Qed.

    Lemma wrap_le z:
      0 <= z -> word.wrap z <= z.
    Proof.
      pose proof word.width_pos.
      intros; apply Z.mod_le; [|apply Z.pow_pos_nonneg]; lia.
    Qed.

    Lemma wrap_of_nat_le n:
      word.wrap (Z.of_nat n) <= Z.of_nat n.
    Proof. apply wrap_le; lia. Qed.

    Lemma wrap_range z:
      0 <= word.wrap z < 2 ^ width.
    Proof. apply Z.mod_pos_bound, word.modulus_pos. Qed.

    Lemma swrap_range z:
      - 2 ^ (width - 1) <= word.swrap (word := word) z < 2 ^ (width - 1).
    Proof.
      unfold word.swrap; set (z + _) as z0.
      pose proof Z.mod_pos_bound z0 (2 ^ width) word.modulus_pos as h.
      rewrite word.pow2_width_minus1 in h at 3; lia.
    Qed.

    Lemma wrap_idempotent z:
      word.wrap (word.wrap z) = word.wrap z.
    Proof. apply wrap_small, wrap_range. Qed.

    Lemma swrap_idempotent z:
      word.swrap (word := word) (word.swrap (word := word) z) = word.swrap (word := word) z.
    Proof. apply word.swrap_inrange, swrap_range. Qed.

    Lemma of_Z_wrap z:
      word.of_Z (word := word) z = word.of_Z (word.wrap z).
    Proof. apply word.unsigned_inj; rewrite !word.unsigned_of_Z, wrap_idempotent; reflexivity. Qed.

    Lemma of_Z_swrap z:
      word.of_Z (word := word) z = word.of_Z (word.swrap (word := word) z).
    Proof. apply word.signed_inj; rewrite !word.signed_of_Z, swrap_idempotent; reflexivity. Qed.

    Lemma of_Z_mod z:
      word.of_Z (word := word) z = word.of_Z (z mod 2 ^ width).
    Proof. apply of_Z_wrap. Qed.

    Lemma unsigned_of_Z_b2z b :
      @word.unsigned _ word (word.of_Z (Z.b2z b)) = Z.b2z b.
    Proof.
      destruct b; cbn [Z.b2z];
        auto using word.unsigned_of_Z_0, word.unsigned_of_Z_1.
    Qed.

    Lemma unsigned_of_Z_le (z: Z):
      0 <= z ->
      word.unsigned (word := word) (word.of_Z z) <= z.
    Proof.
      rewrite word.unsigned_of_Z; apply wrap_le.
    Qed.

    Lemma and_leq_right (a b : word)
      : (word.unsigned (word.and a b)) <= (word.unsigned b).
    Proof.
      rewrite word.unsigned_and_nowrap.
      apply Z_land_leq_right.
      all: apply word.unsigned_range.
    Qed.

    Lemma word_to_nat_to_word (w : word) :
      w = word.of_Z (Z.of_nat (Z.to_nat (word.unsigned w))).
    Proof.
      rewrite Z2Nat.id by apply word.unsigned_range.
      rewrite word.of_Z_unsigned; reflexivity.
    Qed.

    Lemma swrap_eq z :
      @word.swrap width _ z = z ->
      - 2 ^ (width - 1) <= z < 2 ^ (width - 1).
    Proof.
      unfold word.swrap; intros H.
      pose proof word.half_modulus_pos.
      apply (Z.add_cancel_r _ _ (2 ^ (width - 1))) in H.
      ring_simplify in H.
      apply Z.mod_small_iff in H.
      + destruct H as [ H | H ]; rewrite (word.pow2_width_minus1 (word := word)) in H; lia.
      + rewrite word.pow2_width_minus1; lia.
    Qed.

    Implicit Types w : word.

    Lemma signed_unsigned_dec w :
      word.signed w =
      if Z_lt_le_dec (word.unsigned w) (2 ^ (width - 1))
      then word.unsigned w
      else word.unsigned w - 2 ^ width.
    Proof.
      rewrite word.signed_eq_swrap_unsigned.
      pose proof word.unsigned_range w.
      destruct Z_lt_le_dec.
      - apply word.swrap_inrange; lia.
      - unfold word.swrap.
        rewrite (word.pow2_width_minus1 (word := word)) in *.
        pose proof word.half_modulus_pos.
        rewrite <- Z_mod_plus_full with (b := -1).
        rewrite Z.mod_small; [ | split ]; lia.
    Qed.

    Lemma signed_gz_unsigned_bounds w :
      0 <= word.signed w <->
      word.unsigned w < 2 ^ (width - 1).
    Proof.
      split; intro H; pose proof word.unsigned_range w.
      - rewrite signed_unsigned_dec in H.
        destruct Z_lt_le_dec in H.
        + assumption.
        + exfalso; lia.
      - rewrite word.signed_eq_swrap_unsigned, word.swrap_inrange; lia.
    Qed.

    Lemma signed_lt_unsigned (w : word):
      word.signed w <= word.unsigned w.
    Proof.
      pose proof word.unsigned_range w.
      rewrite signed_unsigned_dec.
      destruct Z_lt_le_dec; lia.
    Qed.

    Lemma signed_gz_eq_unsigned w :
      0 <= word.signed w ->
      word.unsigned w = word.signed w.
    Proof.
      intros Hgz.
      rewrite word.signed_eq_swrap_unsigned, word.swrap_inrange.
      - reflexivity.
      - pose proof word.unsigned_range w.
        apply signed_gz_unsigned_bounds in Hgz.
        lia.
    Qed.

    Lemma of_nat_to_nat_unsigned w:
      Z.of_nat (Z.to_nat (word.unsigned w)) = (word.unsigned w).
    Proof.
      pose proof word.unsigned_range w.
      rewrite Z2Nat.id; intuition.
    Qed.

    Lemma of_Z_of_nat_to_nat_unsigned w:
      word.of_Z (Z.of_nat (Z.to_nat (word.unsigned w))) = w.
    Proof.
      pose proof word.unsigned_range w.
      rewrite Z2Nat.id, word.of_Z_unsigned; intuition.
    Qed.

    (* FIXME make this a definition *)
    Notation word_of_byte b :=
      (word.of_Z (Byte.byte.unsigned b)).

    Notation byte_of_word w :=
      (byte.of_Z (word.unsigned w)).

    Lemma byte_of_Z_unsigned b:
      byte.of_Z (byte.unsigned b) = b.
    Proof. destruct b; reflexivity. Qed.

    Lemma word_of_byte_range b:
      0 <= @word.unsigned _ word (word_of_byte b) < 256.
    Proof.
      pose proof Byte.to_N_bounded b as H256%N2Z.inj_le.
      pose proof word.unsigned_range (word_of_byte b).
      unfold Byte.byte.unsigned.
      rewrite word.unsigned_of_Z; unfold word.wrap.
      destruct (Z_lt_le_dec 256 (2 ^ width)).
      - rewrite Z.mod_small; lia.
      - pose proof Z.mod_pos_bound (Z.of_N (Byte.to_N b)) (2 ^ width) ltac:(lia).
        lia.
    Qed.

    Definition b2w (b: bool) :=
      (@word.of_Z _ word (Z.b2z b)).

    Lemma b2w_if (b: bool) :
      b2w b = if b then word.of_Z 1 else word.of_Z 0.
    Proof. destruct b; reflexivity. Qed.

    Lemma b2w_inj:
      forall b1 b2, b2w b1 = b2w b2 -> b1 = b2.
    Proof.
      unfold b2w; intros [|] [|]; simpl;
        intros H%(f_equal word.unsigned);
        rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1 in H;
        cbn; congruence.
    Qed.

    Lemma unsigned_b2w b:
      word.unsigned (b2w b) = Z.b2z b.
    Proof. apply unsigned_of_Z_b2z. Qed.

    Section MinMax.
      Definition minu w1 w2 := if word.gtu w1 w2 then w2 else w1.
      Definition mins w1 w2 := if word.gts w1 w2 then w2 else w1.
      Definition maxu w1 w2 := if word.ltu w1 w2 then w2 else w1.
      Definition maxs w1 w2 := if word.lts w1 w2 then w2 else w1.

      Ltac t :=
        unfold minu, maxu, mins, maxs, word.gtu, word.gts, Z.min, Z.max;
        intros; rewrite ?word.unsigned_ltu, ?word.signed_lts;
        rewrite ?word.unsigned_of_Z_nowrap, ?word.signed_of_Z_nowrap by assumption;
        (rewrite Z.compare_antisym + idtac);
        rewrite Z.ltb_compare; destruct (_ ?= _);
        simpl; rewrite ?word.of_Z_unsigned, ?word.of_Z_signed;
        reflexivity.

      Lemma unsigned_minu w1 w2 :
        minu w1 w2 = word.of_Z (Z.min (word.unsigned w1) (word.unsigned w2)).
      Proof. t. Qed.

      Lemma unsigned_maxu w1 w2 :
        maxu w1 w2 = word.of_Z (Z.max (word.unsigned w1) (word.unsigned w2)).
      Proof. t. Qed.

      Lemma signed_mins w1 w2 :
        mins w1 w2 = word.of_Z (Z.min (word.signed w1) (word.signed w2)).
      Proof. t. Qed.

      Lemma signed_maxs w1 w2 :
        maxs w1 w2 = word.of_Z (Z.max (word.signed w1) (word.signed w2)).
      Proof. t. Qed.

      Lemma minu_unsigned w1 w2 :
        word.unsigned (minu w1 w2) = Z.min (word.unsigned w1) (word.unsigned w2).
      Proof. t. Qed.

      Lemma maxu_unsigned w1 w2 :
        word.unsigned (maxu w1 w2) = Z.max (word.unsigned w1) (word.unsigned w2).
      Proof. t. Qed.

      Lemma mins_signed w1 w2 :
        word.signed (mins w1 w2) = Z.min (word.signed w1) (word.signed w2).
      Proof. t. Qed.

      Lemma maxs_signed w1 w2 :
        word.signed (maxs w1 w2) = Z.max (word.signed w1) (word.signed w2).
      Proof. t. Qed.

      Lemma minu_of_Z z1 z2 :
        0 <= z1 < 2 ^ width -> 0 <= z2 < 2 ^ width ->
        minu (word.of_Z z1) (word.of_Z z2) = word.of_Z (Z.min z1 z2).
      Proof. t. Qed.

      Lemma maxu_of_Z z1 z2 :
        0 <= z1 < 2 ^ width -> 0 <= z2 < 2 ^ width ->
        maxu (word.of_Z z1) (word.of_Z z2) = word.of_Z (Z.max z1 z2).
      Proof. t. Qed.

      Lemma mins_of_Z z1 z2 :
        - 2 ^ (width - 1) <= z1 < 2 ^ (width - 1) ->
        - 2 ^ (width - 1) <= z2 < 2 ^ (width - 1) ->
        mins (word.of_Z z1) (word.of_Z z2) = word.of_Z (Z.min z1 z2).
      Proof. t. Qed.

      Lemma maxs_of_Z z1 z2 :
        - 2 ^ (width - 1) <= z1 < 2 ^ (width - 1) ->
        - 2 ^ (width - 1) <= z2 < 2 ^ (width - 1) ->
        maxs (word.of_Z z1) (word.of_Z z2) = word.of_Z (Z.max z1 z2).
      Proof. t. Qed.
    End MinMax.

    Ltac compile_binop_zzw_bitwise lemma :=
      intros; cbn; apply word.unsigned_inj;
      rewrite lemma, !word.unsigned_of_Z by lia;
      unfold word.wrap; rewrite <- ?Z.land_ones by eauto using word.width_nonneg;
      bitblast.Z.bitblast.

    Lemma morph_not x :
      word.of_Z (Z.lnot x) = word.not (word.of_Z x) :> word.
    Proof. compile_binop_zzw_bitwise word.unsigned_not. Qed.

    Lemma morph_and x y:
      word.of_Z (Z.land x y) = word.and (word.of_Z x) (word.of_Z y) :> word.
    Proof. compile_binop_zzw_bitwise word.unsigned_and_nowrap. Qed.

    Lemma morph_or x y:
      word.of_Z (Z.lor x y) = word.or (word.of_Z x) (word.of_Z y) :> word.
    Proof. compile_binop_zzw_bitwise word.unsigned_or_nowrap. Qed.

    Lemma morph_xor x y:
      word.of_Z (Z.lxor x y) = word.xor (word.of_Z x) (word.of_Z y) :> word.
    Proof. compile_binop_zzw_bitwise word.unsigned_xor_nowrap. Qed.

    Lemma morph_shiftl z n:
      0 <= n < width ->
      word.of_Z (Z.shiftl z n) = word.slu (word := word) (word.of_Z z) (word.of_Z n).
    Proof.
      compile_binop_zzw_bitwise word.unsigned_slu_shamtZ.
      rewrite ?Z.testbit_neg_r by assumption; reflexivity.
    Qed.

    Lemma morph_shiftr z n:
      0 <= n < width ->
      0 <= z < 2 ^ width ->
      word.of_Z (Z.shiftr z n) = word.sru (word := word) (word.of_Z z) (word.of_Z n).
    Proof.
      intros; apply word.unsigned_inj.
      rewrite word.unsigned_sru_shamtZ, !Z.shiftr_div_pow2 by lia.
      rewrite !word.unsigned_of_Z_nowrap; try lia; try reflexivity.
      pose proof Z.pow_pos_nonneg 2 n.
      nia.
    Qed.

    Lemma morph_divu z1 z2:
      0 <= z1 < 2 ^ width ->
      0 < z2 < 2 ^ width ->
      word.of_Z (Z.div z1 z2) = word.divu (word := word) (word.of_Z z1) (word.of_Z z2).
    Proof.
      intros; apply word.unsigned_inj.
      rewrite word.unsigned_divu_nowrap.
      all: rewrite !word.unsigned_of_Z_nowrap; try nia; try reflexivity.
    Qed.

    Lemma morph_lts x y:
      - 2 ^ (width - 1) <= x < 2 ^ (width - 1) ->
      - 2 ^ (width - 1) <= y < 2 ^ (width - 1) ->
      (x <? y) = @word.lts _ word (word.of_Z x) (word.of_Z y).
    Proof.
      intros; rewrite word.signed_lts, !word.signed_of_Z, !word.swrap_inrange; eauto.
    Qed.

    Lemma morph_ltu x y:
      0 <= x < 2 ^ width ->
      0 <= y < 2 ^ width ->
      (x <? y) = @word.ltu _ word (word.of_Z x) (word.of_Z y).
    Proof.
      intros; rewrite word.unsigned_ltu, !word.unsigned_of_Z, !wrap_small; eauto.
    Qed.

    Lemma Z_land_wrap_l z1 z2:
      0 <= z2 < 2 ^ width ->
      Z.land (word.wrap z1) z2 = Z.land z1 z2.
    Proof.
      pose proof word.width_pos.
      intros; unfold word.wrap.
      rewrite <- Z.land_ones, <- Z.land_assoc by lia.
      rewrite (Z.land_comm _ z2), Z.land_ones by lia.
      rewrite Z.mod_small by lia.
      reflexivity.
    Qed.

    Lemma Z_land_wrap_r z1 z2:
      0 <= z1 < 2 ^ width ->
      Z.land z1 (word.wrap z2) = Z.land z1 z2.
    Proof.
      intros; rewrite Z.land_comm at 1;
        rewrite Z_land_wrap_l by lia; apply Z.land_comm.
    Qed.

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
      rewrite word.unsigned_sub, !word.unsigned_of_Z, !wrap_small.
      reflexivity.
      all: pose proof Zpow_facts.Zpower2_lt_lin width word.width_nonneg.
      all: rewrite ?word.unsigned_sub, ?word.unsigned_of_Z_nowrap, ?wrap_small; lia.
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
      all: rewrite ?(wrap_small b), ?(wrap_small (width - b)).
      unfold word.wrap; rewrite Z.land_ones by apply word.width_nonneg;
        Z.push_pull_mod; reflexivity.
      all: pose proof Zpow_facts.Zpower2_lt_lin width word.width_nonneg; try lia.
      rewrite Z.land_ones by lia; apply Z.mod_pos_bound; lia.
    Qed.
  End __.
End word.

Notation word_of_byte b :=
  (word.of_Z (Byte.byte.unsigned b)).
Notation byte_of_word w :=
  (byte.of_Z (word.unsigned w)).

Module SeparationLogic. (* FIXME move to bedrock2? *)
  Import Lift1Prop.
  Section SeparationLogic. (* FIXME move to bedrock2? *)
    Context {key value : Type} {map : map.map key value}.

    Definition pure (P: Prop) := (fun m: map => P).

    (* FIXME replace by `and1` *)
    Definition unsep (p q: map -> Prop) : map -> Prop :=
      fun m => p m /\ q m.

    Fixpoint unseps (props: list (map -> Prop)) : map -> Prop :=
      match props with
      | [] => pure True
      | [prop] => prop
      | prop :: props => unsep prop (unseps props)
      end.

    Global Instance Proper_iff1_unsep :
      Proper (iff1 ==> iff1 ==> iff1) unsep.
    Proof. firstorder idtac. Qed.

    Global Instance Proper_impl1_unsep :
      Proper (impl1 ==> impl1 ==> impl1) unsep.
    Proof. firstorder idtac. Qed.

    Lemma unsep_assoc (p q r: map -> Prop) :
      iff1 (unsep (unsep p q) r) (unsep p (unsep q r)).
    Proof. firstorder idtac. Qed.

    Lemma unsep_pure_True_l P :
      iff1 (unsep (pure True) P) P.
    Proof. firstorder idtac. Qed.

    Lemma unsep_pure_True_r P :
      iff1 (unsep P (pure True)) P.
    Proof. firstorder idtac. Qed.

    Lemma unsep_pure_False_l P :
      iff1 (unsep (pure False) P) (pure False).
    Proof. firstorder idtac. Qed.

    Lemma unsep_pure_False_r P :
      iff1 (unsep P (pure False)) (pure False).
    Proof. firstorder idtac. Qed.

    Lemma sep_pure_False_l P :
      iff1 (sep (pure False) P) (pure False).
    Proof. firstorder idtac. Qed.

    Lemma sep_pure_False_r P :
      iff1 (sep P (pure False)) (pure False).
    Proof. firstorder idtac. Qed.

    Lemma impl1_pure_False_l P :
      impl1 (pure False) P.
    Proof. firstorder idtac. Qed.

    Lemma impl1_pure_True_r P :
      impl1 P (pure True).
    Proof. firstorder idtac. Qed.

    Lemma unsep_distr_sep_l: (* FIXME: this is sep_and_r_fwd *)
      forall p1 p2 p3 : map -> Prop,
        impl1 (sep p1 (unsep p2 p3)) (unsep (sep p1 p2) (sep p1 p3)).
    Proof. firstorder idtac. Qed.

    Lemma unsep_distr_sep_r: (* FIXME: this is sep_and_l_fwd *)
      forall p1 p2 p3 : map -> Prop,
        impl1 (sep (unsep p1 p2) p3) (unsep (sep p1 p3) (sep p2 p3)).
    Proof. firstorder idtac. Qed.

    Lemma unseps_distr_sep_l :
      forall p1 ps2,
        impl1 (sep p1 (unseps ps2))
              (unseps (List.map (sep p1) ps2)).
    Proof.
      induction ps2 as [| p2 [|] IHps2]; simpl in *; intros.
      - apply impl1_pure_True_r.
      - reflexivity.
      - rewrite <- IHps2, unsep_distr_sep_l; reflexivity.
    Qed.

    Lemma unseps_distr_sep_r :
      forall ps1 p2,
        impl1 (sep (unseps ps1) p2) (unseps (List.map (fun p1 => sep p1 p2) ps1)).
    Proof.
      induction ps1 as [| p1 [|] IHps1]; simpl in *; intros.
      - apply impl1_pure_True_r.
      - reflexivity.
      - rewrite <- IHps1, unsep_distr_sep_r; reflexivity.
    Qed.

    Lemma unseps_map_impl1_ext (f g: (map -> Prop) -> (map -> Prop))
          (H: forall p, impl1 (f p) (g p)) :
      forall ps, impl1 (unseps (List.map f ps)) (unseps (List.map g ps)).
    Proof.
      induction ps as [| p [|] IHps]; simpl in *; intros.
      - reflexivity.
      - eauto.
      - rewrite IHps, H; reflexivity.
    Qed.

    Lemma unseps_app :
      forall es1 es2,
        iff1 (unseps (es1 ++ es2))
             (unsep (unseps es1) (unseps es2)).
    Proof.
      induction es1 as [| e1 [|] IHes1]; simpl in *; intros.
      - rewrite unsep_pure_True_l; reflexivity.
      - destruct es2; simpl.
        + rewrite unsep_pure_True_r; reflexivity.
        + reflexivity.
      - rewrite IHes1, unsep_assoc.
        reflexivity.
    Qed.

    Lemma unseps_distr_sep:
      forall ps1 ps2,
        impl1 (sep (unseps ps1) (unseps ps2))
              (unseps (map2 sep (product ps1 ps2))).
    Proof.
      intros; rewrite map2_product; revert ps2.
      induction ps1 as [| p1 [|] IHps1]; simpl in *; intros.
      - apply impl1_pure_True_r.
      - rewrite app_nil_r.
        apply unseps_distr_sep_l.
      - rewrite unsep_distr_sep_r, unseps_app.
        rewrite <- IHps1.
        rewrite <- unseps_distr_sep_l.
        reflexivity.
    Qed.
  End SeparationLogic.
End SeparationLogic.

Export SeparationLogic.

Section Byte.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context {word_ok : word.ok word}.

  Lemma byte_morph_and b1 b2:
    word_of_byte (byte.and b1 b2) =
    word.and (word := word) (word_of_byte b1) (word_of_byte b2).
  Proof.
    apply word.unsigned_inj.
    rewrite word.unsigned_and_nowrap, !word.unsigned_of_Z, !wrap_byte_unsigned.
    rewrite byte_unsigned_land; reflexivity.
  Qed.

  Lemma byte_morph_xor b1 b2:
    word_of_byte (byte.xor b1 b2) =
    word.xor (word := word) (word_of_byte b1) (word_of_byte b2).
  Proof.
    apply word.unsigned_inj.
    rewrite word.unsigned_xor_nowrap, !word.unsigned_of_Z, !wrap_byte_unsigned.
    rewrite byte_unsigned_xor; reflexivity.
  Qed.
End Byte.

Require Import coqutil.Word.LittleEndianList.
Arguments le_combine: simpl nomatch.
Arguments le_split : simpl nomatch.
Arguments Z.mul: simpl nomatch.

Section combine_split.
End combine_split.

Section Array.
  Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.
  Context {value} {Mem : map.map word value} {Mem_ok : map.ok Mem}.
  Context {T} (element : word -> T -> Mem -> Prop) (size : word).

  Open Scope Z_scope.

  Definition no_aliasing {A} (repr: word -> A -> Mem -> Prop) :=
    (forall a b p delta m R,
        0 <= delta < word.unsigned size ->
        ~ (repr p a * repr (word.add p (word.of_Z delta)) b * R)%sep m).

  Lemma array_max_length': forall addr xs (R: Mem -> Prop) m,
      (array element size addr xs * R)%sep m ->
      no_aliasing element ->
      0 <= word.unsigned size < 2 ^ width ->
      ~ word.unsigned size * Z.of_nat (length xs) > 2 ^ width.
  Proof.
    unfold not; intros * H He **.
    pose (max_len := Z.to_nat (2 ^ width / word.unsigned size)).
    assert (max_len <= Datatypes.length xs)%nat as B. {
      apply Nat2Z.inj_le; subst max_len; rewrite Z2Nat.id;
        [ apply Z.div_le_upper_bound | ]; ZnWords.
    }
    pose proof (List.firstn_skipn max_len xs) as E.
    pose proof @List.firstn_length_le _ xs max_len B as A.
    destruct (List.firstn max_len xs) as [|h1 t1] eqn:E1; [ ZnWordsL | ].
    destruct (List.skipn max_len xs) as [|h2 t2] eqn:E2; [ ZnWordsL | ].
    rewrite <- E in H.
    SeparationLogic.seprewrite_in @array_append H.
    SeparationLogic.seprewrite_in @array_cons H.
    SeparationLogic.seprewrite_in @array_cons H.
    (* FIXME: Find a way to shorten this proof *)
    rewrite A in H.
    set (word.unsigned size * Z.of_nat max_len) as max_len_bytes in H.
    set (word.add addr (word.of_Z max_len_bytes)) as base in H.
    replace (element addr) with
        (element (word.add base (word.of_Z (word.unsigned (word.sub addr base))))) in H;
      cycle 1.
    - f_equal.
      apply word.unsigned_inj.
      rewrite word.unsigned_add, word.of_Z_unsigned, word.unsigned_sub.
      unfold word.wrap; Z.push_pull_mod.
      erewrite <- (Z.mod_small (word.unsigned addr)) at 2 by apply word.unsigned_range.
      f_equal; lia.
    - eapply He; [ | ecancel_assumption ].
      subst base max_len_bytes max_len; rewrite Z2Nat.id by ZnWords.
      rewrite word.unsigned_sub, word.unsigned_add, word.unsigned_of_Z.
      unfold word.wrap; Z.push_pull_mod.
      rewrite Z_mod_eq''.
      match goal with
      | [  |- _ <= ?t < _ ] => replace t with (2 ^ width mod word.unsigned size mod 2 ^ width)
      end.
      + rewrite Z.mod_small; ZnWords.
      + etransitivity; [ | rewrite <- Z.mod_add with (b := 1) by ZnWords; reflexivity ].
        f_equal; rewrite Z.mul_1_l; lia.
      + lia.
  Qed.

  Lemma array_max_length: forall addr xs (R: Mem -> Prop) m,
      no_aliasing element ->
      0 < word.unsigned size ->
      (array element size addr xs * R)%sep m ->
      word.unsigned size * Z.of_nat (length xs) <= 2 ^ width.
  Proof.
    intros; eapply Znot_gt_le, array_max_length'; eauto using word.unsigned_range.
  Qed.
End Array.

Section Aliasing.
  Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.
  Context {Mem : map.map word byte} {Mem_ok : map.ok Mem}.

  Open Scope Z_scope.

  Lemma bytes_per_word_range :
    0 < Memory.bytes_per_word width < 2 ^ width.
  Proof. (* FIXME: seriously?! *)
    unfold Memory.bytes_per_word; pose proof word.width_pos.
    split; [apply Z.div_str_pos; lia | ].
    apply Z.div_lt_upper_bound; try lia.
    apply Z.lt_add_lt_sub_r.
    replace (2 ^ width) with (2 ^ (Z.succ (width - 1))) by (f_equal; lia).
    rewrite Z.pow_succ_r by lia.
    replace (8 * (2 * 2 ^ (width - 1))) with (8 * 2 ^ (width - 1) + 8 * 2 ^ (width - 1)) by lia.
    assert (0 < 2 ^ (width - 1)) by (apply Z.pow_pos_nonneg; lia).
    transitivity (8 * 2 ^ (width - 1)); try lia.
    etransitivity; [ apply Zpow_facts.Zpower2_lt_lin; lia | ].
    replace (8 * 2 ^ (width - 1)) with (2 ^ (Z.succ (Z.succ (Z.succ (width - 1))))).
    apply Z.pow_lt_mono_r; lia.
    rewrite !Z.pow_succ_r by lia.
    lia.
  Qed.

  Context {BW: Bitwidth width}.

  (* From insertionsort.v in Bedrock2 *)
  Lemma ptsto_no_aliasing': forall addr b1 b2 m (R: Mem -> Prop),
      (ptsto addr b1 * ptsto addr b2 * R)%sep m ->
      False.
  Proof.
    intros. unfold ptsto, sep, map.split, map.disjoint in *.
    repeat match goal with
           | H: exists _, _ |- _ => destruct H
           | H: _ /\ _ |- _ => destruct H
           end.
    subst.
    specialize (H4 addr b1 b2). rewrite ?map.get_put_same in H4. auto.
  Qed.

  Lemma scalar8_no_aliasing :
    no_aliasing (word := word) (Mem := Mem) (word.of_Z 1) ptsto.
  Proof.
    red; intros * h Hmem.
    rewrite word.unsigned_of_Z_1 in h.
    replace delta with 0 in * by lia.
    replace (word.add p (word.of_Z 0)) with p in *; cycle 1.
    - apply word.unsigned_inj;
        rewrite word.unsigned_add, word.unsigned_of_Z_0, Z.add_0_r.
      pose proof word.unsigned_range p; rewrite word.wrap_small by lia;
        reflexivity.
    - eapply ptsto_no_aliasing'; eassumption.
  Qed.

  Lemma scalar_no_aliasing1 sz :
    no_aliasing (word := word) (Mem := Mem)
                (word.of_Z (Z.of_nat (Memory.bytes_per (width := width) sz)))
                (truncated_word sz (mem := Mem)).
  Proof.
    red. intros * h Hmem.
    pose proof bytes_per_range.
    rewrite word.unsigned_of_Z_nowrap in h by lia.
    unfold scalar, truncated_word, truncated_scalar,
    littleendian, ptsto_bytes.ptsto_bytes in *.
    pose proof split_bytes_per_len sz a as Hlena.
    pose proof split_bytes_per_len sz b as Hlenb.
    rewrite 2HList.tuple.to_list_of_list in Hmem.
    set (le_split _ _) as la in Hmem, Hlena.
    set (le_split _ _) as lb in Hmem, Hlenb.
    rewrite <- (firstn_skipn (Z.to_nat delta) la) in Hmem.
    seprewrite_in @array_append Hmem; try lia.
    assert (Z.to_nat delta <= Datatypes.length la)%nat
      by (subst la; rewrite LittleEndianList.length_le_split; lia).
    rewrite word.unsigned_of_Z_1, Z.mul_1_l, firstn_length_le, Z2Nat.id in Hmem by lia.
    destruct lb; cbn -[Z.of_nat] in Hlenb; [ lia | ].
    pose proof List.skipn_length (Z.to_nat delta) la as Hlena'.
    destruct (List.skipn (Z.to_nat delta) la) eqn:Ha; cbn [List.length] in Hlena'; [ lia | ].
    seprewrite_in @array_cons Hmem; try lia.
    seprewrite_in @array_cons Hmem; try lia.
    eapply ptsto_no_aliasing'; ecancel_assumption.
  Qed.

  Lemma scalar_no_aliasing2 :
    no_aliasing (word := word) (Mem := Mem)
                (word.of_Z (Z.of_nat (Memory.bytes_per
                                        (width := width)
                                        access_size.word))) scalar.
  Proof. apply scalar_no_aliasing1. Qed.
End Aliasing.

Section Semantics.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Definition trace_entry :=
    Eval cbv beta in ((fun {A} (_: list A) => A) _ ([]: Semantics.trace)).

  Definition predicate := Semantics.trace -> mem -> locals -> Prop.
  Definition wp_bind_retvars retvars (P: list word -> predicate) :=
    fun tr mem locals =>
      exists ws, map.getmany_of_list locals retvars = Some ws /\
            P ws tr mem locals.

  Definition pure_predicate := mem -> locals -> Prop.
  Definition wp_pure_bind_retvars retvars (P: list word -> pure_predicate) :=
    fun mem locals =>
      exists ws, map.getmany_of_list locals retvars = Some ws /\
            P ws mem locals.

  Lemma WeakestPrecondition_weaken :
    forall cmd {functions} (p1 p2: _ -> _ -> _ -> Prop),
      (forall tr mem locals, p1 tr mem locals -> p2 tr mem locals) ->
      forall tr mem locals,
        WeakestPrecondition.program
          functions cmd tr mem locals p1 ->
        WeakestPrecondition.program
          functions cmd tr mem locals p2.
  Proof. intros; eapply Proper_program; eassumption. Qed.

  Lemma WeakestPrecondition_dexpr_expr :
    forall mem locals (e: expr) w (k: word -> Prop),
      k w ->
      WeakestPrecondition.dexpr mem locals e w ->
      WeakestPrecondition.expr mem locals e k.
  Proof.
    intros; eapply Proper_expr; [ | eassumption ].
    intros ? ->; assumption.
  Qed.

  Lemma getmany_list_map (l : locals) :
    forall a vs (P :_ -> Prop),
      P vs ->
      map.getmany_of_list l a = Some vs ->
      WeakestPrecondition.list_map (WeakestPrecondition.get l) a P.
  Proof.
    unfold map.getmany_of_list;
      induction a; cbn in *; intros.
    all: repeat (destruct_one_match_hyp; [|discriminate]).
    all: match goal with H: Some _ = Some _ |- _ => inversion H; subst end.
    all: try red; eauto.
  Qed.

  (* FIXME generalize *)
  Definition postcondition_func
             (spec : list word -> mem -> Prop)
             R tr :=
    (fun (tr' : Semantics.trace) (mem' : mem) (rets : list word) =>
       tr = tr'
       /\ sep (spec rets) R mem').

  Definition postcondition_func_norets spec R tr :=
    postcondition_func (fun r => sep (emp (r = nil)) (spec r)) R tr.

  (* TODO: Remove locals_post *)
  Definition postcondition_cmd
             locals_post spec retvars R tr :=
    (fun (tr' : Semantics.trace) (mem' : mem)
       (locals : locals) =>
       tr = tr'
       /\ locals_post locals
       /\ exists rets,
           map.getmany_of_list locals retvars = Some rets
           /\ sep (spec rets) R mem').

  Lemma predicate_trivial : forall
        {tr: Semantics.trace}
        {mem: mem}
        {locals: locals} {T} t0,
    (fun (_: T) tr' mem' locals' =>
       tr' = tr /\ mem' = mem /\ locals' = locals)
      t0 tr mem locals.
  Proof. intuition auto with core. Qed.

  Lemma to_byte_of_byte_nowrap b:
    byte_of_word (word_of_byte b : word) = b.
  Proof.
    rewrite word.unsigned_of_Z, word.wrap_small.
    - apply word.byte_of_Z_unsigned.
    - pose proof byte.unsigned_range b.
      destruct width_cases as [-> | ->]; lia.
  Qed.
End Semantics.

Section Misc.
  Lemma eq_impl : forall a b, a = b -> a -> b.
  Proof. intros * -> ?; eassumption. Qed.
End Misc.

Section Nat2Z.
  Lemma Nat2Z_inj_pow a b:
    Z.of_nat (a ^ b) = (Z.of_nat a ^ Z.of_nat b)%Z.
  Proof.
    induction b.
    - reflexivity.
    - cbn -[Z.of_nat Z.pow].
      rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia.
  Qed.

  Lemma Z_div_eucl_unique a b q q' r r':
    0 <= r < b \/ b < r <= 0 ->
    0 <= r' < b \/ b < r' <= 0 ->
    a = b * q + r ->
    a = b * q' + r' ->
    (q = q' /\ r = r').
  Proof.
    intros Hr Hr' Hq Hq';
      erewrite (Z.div_unique a b q r Hr Hq);
      erewrite (Z.div_unique a b q' r' Hr' Hq');
      erewrite (Z.mod_unique a b q r Hr Hq);
      erewrite (Z.mod_unique a b q' r' Hr' Hq');
      split; reflexivity.
  Qed.

  (* FIXME: already exists as div_Zdiv, mod_Zmod *)
  Lemma Nat2Z_inj_div_mod a b:
    Z.of_nat (a / b) = Z.of_nat a / Z.of_nat b /\
    Z.of_nat (a mod b) = Z.of_nat a mod Z.of_nat b.
  Proof.
    destruct (Nat.eq_dec b 0) as [->|].
    - destruct a; split; reflexivity.
    - pose (q := (a / b)%nat).
      pose (r := (a mod b)%nat).
      assert (a = b * q + r)%nat as Hnat by (apply Nat_mod_eq'; lia).
      pose (zq := Z.of_nat a / Z.of_nat b).
      pose (zr := Z.of_nat a mod Z.of_nat b).
      assert (Z.of_nat a = Z.of_nat b * zq + zr) as Hz by (apply Z_mod_eq'; lia).
      apply (f_equal Z.of_nat) in Hnat.
      rewrite Nat2Z.inj_add, Nat2Z.inj_mul in Hnat.
      pose proof Nat.mod_bound_pos a b ltac:(lia) ltac:(lia).
      pose proof Z.mod_bound_or (Z.of_nat a) (Z.of_nat b).
      eapply Z_div_eucl_unique; try eassumption.
      all: try lia.
  Qed.

  Lemma Nat2Z_inj_div a b:
    Z.of_nat (a / b) = Z.of_nat a / Z.of_nat b.
  Proof. apply (Nat2Z_inj_div_mod a b). Qed.

  Lemma Nat2Z_inj_mod a b:
    Z.of_nat (a mod b) = Z.of_nat a mod Z.of_nat b.
  Proof. apply (Nat2Z_inj_div_mod a b). Qed.

  Lemma Nat2Z_inj_odd : forall n,
    Z.odd (Z.of_nat n) = Nat.odd n.
  Proof.
    apply Nat.pair_induction.
    - intros ?? ->; reflexivity.
    - reflexivity.
    - reflexivity.
    - intros; rewrite !Nat2Z.inj_succ, Z.odd_succ_succ. eassumption.
  Qed.

  Lemma Natmod_odd: forall a : nat,
      (a mod 2 = if Nat.odd a then 1 else 0)%nat.
  Proof.
    apply Nat.pair_induction.
    - intros ?? ->; reflexivity.
    - reflexivity.
    - reflexivity.
    - intros.
      replace (S (S n)) with (n + 1 * 2)%nat at 1 by lia.
      rewrite Nat.mod_add by lia.
      eassumption.
  Qed.

  Lemma Natodd_mod : forall a : nat,
      (Nat.odd a = negb (a mod 2 =? 0))%nat.
  Proof.
    intros; rewrite Natmod_odd.
    destruct Nat.odd; reflexivity.
  Qed.
End Nat2Z.

Section Rupicola.
  Definition __rupicola_program_marker {A} (a: A) := True.

  Definition nlet_eq {A} {P: forall a: A, Type}
             (vars: list string) (a0: A)
             (body : forall (a : A) (Heq: a = a0), P a) : P a0 :=
    let x := a0 in body x eq_refl.

  Definition nlet {A T}
             (vars: list string) (a0: A)
             (body : A -> T) : T :=
    let x := a0 in body x.

  Lemma nlet_as_nlet_eq {A T}
        (vars: list string) (val: A)
        (body : A -> T) :
    nlet vars val body =
    nlet_eq (P := fun _ => T) vars val (fun v _ => body v).
  Proof. reflexivity. Qed.

  Inductive RupicolaBindingInfo :=
  | RupicolaBinding (rb_type: Type) (rb_names: list string)
  | NotARupicolaBinding.

  Class IsRupicolaBinding {T} (t: T) := is_rupicola_binding: RupicolaBindingInfo.

  Class HasDefault (T: Type) := default: T.
  Global Instance HasDefault_nat : HasDefault nat := 0%nat.
  Global Instance HasDefault_Z : HasDefault Z := 0%Z.
  Global Instance HasDefault_byte : HasDefault byte := Byte.x00.
  Global Instance HasDefault_Fin {n} : HasDefault (Fin.t (S n)) :=
    Fin.F1.
  Global Instance HasDefault_word {width} {word : Interface.word width} : HasDefault word :=
    word.of_Z 0.

  Class Convertible (T1 T2: Type) := cast: T1 -> T2.
  Global Instance Convertible_self {A}: Convertible A A := id.
  Global Instance Convertible_Z_nat : Convertible Z nat := Z.to_nat.
  Global Instance Convertible_byte_nat : Convertible byte nat :=
    fun b => Z.to_nat (byte.unsigned b).
  Global Instance Convertible_Fin_nat {n} : Convertible (Fin.t n) nat :=
    fun f => proj1_sig (Fin.to_nat f).
  Global Instance Convertible_word_nat {width : Z} {word : word width} : Convertible word nat :=
    fun w => Z.to_nat (word.unsigned w).
End Rupicola.

(* TODO: should be upstreamed to coqutil *)
Module Z.
  Lemma lxor_xorb a b : Z.lxor (Z.b2z a) (Z.b2z b) = Z.b2z (xorb a b).
  Proof. destruct a, b; reflexivity. Qed.
End Z.
