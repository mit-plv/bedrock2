Require Export Coq.Strings.String.
Require Export Coq.Numbers.DecimalString.
Require Export Coq.Lists.List.
Require Export Coq.ZArith.ZArith.
Require Export Coq.micromega.Lia.
Require Export bedrock2.Array.
Require Export bedrock2.Map.Separation.
Require Export bedrock2.ProgramLogic.
Require Export bedrock2.Map.SeparationLogic.
Require Export bedrock2.Scalars.
Require Export bedrock2.Syntax.
Require Export bedrock2.WeakestPreconditionProperties.
Require Export coqutil.dlet.
Require Import coqutil.Decidable.
Require Export coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.SortedList.
Require Export coqutil.Z.PushPullMod.
Require Export coqutil.Tactics.Tactics.
Require Export coqutil.Tactics.letexists.
Require Export coqutil.Word.Interface coqutil.Word.Properties.
Require coqutil.Map.SortedListString.
Require bedrock2.ProgramLogic.

Open Scope string_scope.
Export ListNotations.

Declare Scope sep_scope.
Delimit Scope sep_scope with sep.
Infix "*" := (sep) : sep_scope.

Set Nested Proofs Allowed.
Set Default Goal Selector "1".

Notation word := Semantics.word.

(* FIXME instead of cbn [fst snd], use simpl never hints in the sep case *)
Arguments Semantics.word : simpl never.

Notation address := word (only parsing).

Definition bedrock_func : Type :=
  string * (list string * list string * cmd).
Coercion name_of_func (f : bedrock_func) := fst f.

Definition predicate {parameters: Semantics.parameters} :=
  Semantics.trace -> Semantics.mem -> Semantics.locals -> Prop.

(* TODO: should move upstream to coqutil *)
Module map.
  Section __.
    Context {key value value'}
            {map : map.map key value}
            {map' : map.map key value'}
            {map_ok : map.ok map}
            {map'_ok : map.ok map'}
            {key_eqb : key -> key -> bool}
            {key_eq_dec : EqDecider key_eqb}.

    Lemma put_put_diff_comm k1 k2 v1 v2 m :
      k1 <> k2 ->
      map.put (map.put m k1 v1) k2 v2 = map.put (map.put m k2 v2) k1 v1.
    Proof.
      intros. apply map.map_ext. intros.
      rewrite !map.get_put_dec;
        repeat match goal with |- context [key_eqb ?x ?y] =>
                               destr (key_eqb x y) end;
        congruence.
    Qed.

    Lemma put_noop k v m :
      map.get m k = Some v -> map.put m k v = m.
    Proof.
      intros. apply map.map_ext. intros.
      rewrite !map.get_put_dec;
        repeat match goal with |- context [key_eqb ?x ?y] =>
                               destr (key_eqb x y) end;
        congruence.
    Qed.

    Lemma disjoint_put_r m1 m2 k v :
      map.get m1 k = None ->
      map.disjoint m1 m2 ->
      map.disjoint m1 (map.put m2 k v).
    Proof.
      cbv [map.disjoint]. intros.
      match goal with H : context [map.get (map.put _ ?k _) ?k'] |- _ =>
                      rewrite map.get_put_dec in H
      end.
      destruct_one_match_hyp; subst; eauto; congruence.
    Qed.

    Lemma disjoint_put_l m1 m2 k v :
      map.get m2 k = None ->
      map.disjoint m1 m2 ->
      map.disjoint (map.put m1 k v) m2.
    Proof.
      cbv [map.disjoint]. intros.
      match goal with H : context [map.get (map.put _ ?k _) ?k'] |- _ =>
                      rewrite map.get_put_dec in H
      end.
      destruct_one_match_hyp; subst; eauto; congruence.
    Qed.

    Lemma put_remove_same m k v :
      map.put (map.remove m k)  k v = map.put m k v.
    Proof.
      apply map.map_ext; intro.
      rewrite !map.get_put_dec, !map.get_remove_dec.
      destruct_one_match; congruence.
    Qed.

    Lemma remove_put_same m k v :
      map.remove (map.put m k v) k = map.remove m k.
    Proof.
      intros; apply map.map_ext; intro.
      rewrite !map.get_remove_dec, !map.get_put_dec.
      destruct_one_match; congruence.
    Qed.

    Lemma remove_put_diff m k1 k2 v :
      k1 <> k2 ->
      map.remove (map.put m k1 v) k2 = map.put (map.remove m k2) k1 v.
    Proof.
      intros; apply map.map_ext; intro.
      rewrite !map.get_put_dec, !map.get_remove_dec.
      repeat destruct_one_match; subst;
        rewrite ?map.get_put_diff, ?map.get_put_same by congruence;
        congruence.
    Qed.

    Lemma remove_not_in m k :
      map.get m k = None ->
      map.remove m k = m.
    Proof.
      intros; apply map.map_ext; intros.
      rewrite map.get_remove_dec; destruct_one_match; congruence.
    Qed.

    Lemma getmany_of_list_cons m k ks v vs :
      map.get m k = Some v ->
      map.getmany_of_list m ks = Some vs ->
      map.getmany_of_list m (k :: ks) = Some (v :: vs).
    Proof.
      intros. cbv [map.getmany_of_list] in *.
      cbn [List.map List.option_all].
      destruct_one_match; try congruence; [ ].
      destruct_one_match; congruence.
    Qed.

    Lemma get_mapped m k (f: value -> value'):
      map.get (map.fold (fun m' k v => map.put m' k (f v)) map.empty m) k =
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
    forall bs, map.of_list bs = map_of_list' bs map.empty.
  Proof. intros; apply of_list_is_fold_right'. Qed.

  Definition map_domains_diff {K V} {map: map.map K V} (m0 m1: map) :=
    map.keys (map.fold (fun (m0: map) k _ => map.remove m0 k) m0 m1).

  Definition map_eq {K V} {map0 map1: map.map K V}
             {map_ok0: map.ok map0} {map_ok1: map.ok map1}
             m0 m1 :=
    (forall k, map.get (map := map0) m0 k = map.get (map := map1) m1 k).

  Instance map_eq_refl {K V} {map: map.map K V} {map_ok: map.ok map} :
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

  Definition remove_many {K V} {M: map.map K V} m (ks: list K) :=
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

  Lemma ext_rev  {K V} {map: map.map K V} {map_ok: map.ok map} :
    forall m0 m1, m0 = m1 -> map_eq m0 m1.
  Proof. intros; subst; reflexivity. Qed.

  Lemma remove_many_concretize {K V}
        {map0 map1: map.map K V}
        {map_ok0: map.ok map0} {map_ok1: map.ok map1}
        {key_eqb: K -> K -> bool}
        {key_eq_dec : EqDecider key_eqb} :
    forall (m0 m'0: map.rep (map := map0)) (m1 m'1: map.rep (map := map1)) ks,
      map_eq m0 m1 ->
      map_eq m'0 m'1 ->
      remove_many m1 ks = m'1 ->
      remove_many m0 ks = m'0.
  Proof.
    intros * Heq H'eq H1.
    apply ext_rev in H1.
    apply map.map_ext; change (map_eq (remove_many m0 ks) m'0).
    eauto using @eq_trans, @remove_many_proper, @eq_sym.
  Qed.

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

  Lemma remove_many_diff {V} {map: map.map string V} {map_ok: map.ok map}:
    let SM := SortedListString.map V in
    let SM_ok := SortedListString.ok V in
    forall (b0 b1: list (string * V)) ks,
      let sb0 := map.of_list (map := SM) b0 in
      let sb1 := map.of_list (map := SM) b1 in
      ks = map_domains_diff sb0 sb1 -> (* Used for unification *)
      remove_many sb0 ks = sb1 ->
      remove_many (map.of_list (map := map) b0) ks = map.of_list b1.
  Proof.
    intros; eapply (remove_many_concretize (map0 := map) (map1 := SM)); eauto;
      apply of_list_proper.
  Qed.
End map.

Hint Rewrite @map.get_put_diff @map.get_put_same @map.put_put_same
     @map.remove_put_diff @map.remove_put_same
     @map.remove_empty @map.get_empty
     using (typeclasses eauto || congruence) : mapsimpl.

(* TODO: should move upstream to coqutil *)
Section Lists.
  Context {A : Type}.

  Lemma skipn_seq_step n start len :
    skipn n (seq start len) = seq (start + n) (len - n).
  Proof.
    revert start len.
    induction n; destruct len; cbn; try reflexivity.
    { repeat (f_equal; try lia). }
    { rewrite IHn.
      repeat (f_equal; try lia). }
  Qed.

  Lemma fold_left_skipn_seq i count (step :A -> _) init :
    0 < i <= count ->
    step (fold_left step (rev (skipn i (seq 0 count))) init) (i-1) =
    fold_left step (rev (skipn (i-1) (seq 0 count))) init.
  Proof.
    intros. rewrite !skipn_seq_step, !Nat.add_0_l.
    replace (count - (i - 1)) with (S (count - i)) by lia.
    cbn [seq rev]. rewrite fold_left_app. cbn [fold_left].
    replace (S (i-1)) with i by lia.
    reflexivity.
  Qed.

  Definition fold_left_dependent
             {B C} (stepA : A -> C -> A) (stepB : A -> B -> C -> B)
             cs initA initB :=
    fold_left (fun ab c =>
                 (stepA (fst ab) c, stepB (fst ab) (snd ab) c))
              cs (initA, initB).

  Lemma fold_left_dependent_fst {B C} stepA stepB :
    forall cs initA initB,
      fst (@fold_left_dependent B C stepA stepB cs initA initB) =
      fold_left stepA cs initA.
  Proof.
    induction cs; intros; [ reflexivity | ].
    cbn [fold_left fold_left_dependent fst snd].
    erewrite <-IHcs. reflexivity.
  Qed.
End Lists.

(* TODO: should be upstreamed to coqutil *)
Module word.
  Section __.
    Context {width} {word : Interface.word width} {ok : word.ok word}.

    Open Scope Z_scope.

    Lemma wrap_small x :
      0 <= x < 2 ^ width ->
      word.wrap x = x.
    Proof. apply Z.mod_small. Qed.

    Lemma unsigned_of_Z_b2z b :
      word.unsigned (word.of_Z (Z.b2z b)) = Z.b2z b.
    Proof.
      destruct b; cbn [Z.b2z];
        auto using word.unsigned_of_Z_0, word.unsigned_of_Z_1.
    Qed.

    Lemma swrap_eq z :
      word.swrap z = z ->
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
  End __.
End word.

(* TODO: should be upstreamed to coqutil *)
Module Z.
  Lemma lxor_xorb a b : Z.lxor (Z.b2z a) (Z.b2z b) = Z.b2z (xorb a b).
  Proof. destruct a, b; reflexivity. Qed.
End Z.
