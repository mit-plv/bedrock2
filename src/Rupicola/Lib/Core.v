From Coq Require Export
     Classes.Morphisms Numbers.DecimalString
     String List ZArith Lia.
From bedrock2 Require Export
     Array Map.Separation ProgramLogic
     Map.SeparationLogic Scalars Syntax WeakestPreconditionProperties.
From bedrock2 Require
     ProgramLogic.
From coqutil Require Export
     dlet Byte
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

    Implicit Types (m : map).
    Lemma extends_refl m:
      map.extends m m.
    Proof. firstorder. Qed.

    Lemma extends_eq m1 m2:
      m1 = m2 ->
      map.extends m1 m2.
    Proof. intros * ->; apply extends_refl. Qed.

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
End map.

Hint Rewrite @map.get_put_diff @map.get_put_same @map.put_put_same
     @map.remove_put_diff @map.remove_put_same
     @map.remove_empty @map.get_empty
     using (typeclasses eauto || congruence) : mapsimpl.

(* TODO: should move upstream to coqutil *)
Section Lists.
  Open Scope list_scope.

  Section Single.
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

  Fixpoint replace_nth (n: nat) (l: list A) (a: A) {struct l} :=
    match l, n with
    | [], _ => []
    | _ :: t, 0 => a :: t
    | h :: t, S n => h :: replace_nth n t a
    end.

  Lemma nth_replace_nth:
    forall (xs: list A) idx idx' d v,
      idx' = idx ->
      idx < List.length xs ->
      nth idx' (replace_nth idx xs v) d = v.
  Proof.
    intros; subst; revert dependent idx; revert dependent xs.
    induction xs; cbn; intros idx Hlt.
    - inversion Hlt.
    - destruct idx; simpl.
      + reflexivity.
      + apply IHxs; auto with arith.
  Qed.

  Lemma replace_nth_length:
    forall (l: list A) n a,
      List.length (replace_nth n l a) = List.length l.
  Proof.
    induction l; cbn; intros.
    - reflexivity.
    - destruct n; simpl; rewrite ?IHl; try reflexivity.
  Qed.

  Lemma List_firstn_app_l :
    forall (l1 l2: list A) n,
      n = List.length l1 ->
      List.firstn n (l1 ++ l2) = l1.
  Proof.
    intros; subst.
    rewrite List.firstn_app, List.firstn_all, Nat.sub_diag; simpl.
    rewrite app_nil_r; reflexivity.
  Qed.

  Lemma List_firstn_app_l2 :
    forall (l1 l2: list A) n k,
      n = List.length l1 ->
      (List.firstn (n + k) (l1 ++ l2) = l1 ++ (List.firstn k l2)).
  Proof.
    intros; subst.
    rewrite List.firstn_app, List.firstn_all2, minus_plus; simpl; (reflexivity || lia).
  Qed.

  Lemma List_skipn_app_r :
    forall (l1 l2: list A) n,
      n = List.length l1 ->
      List.skipn n (l1 ++ l2) = l2.
  Proof.
    intros; subst.
    rewrite List.skipn_app, List.skipn_all, Nat.sub_diag; simpl; reflexivity.
  Qed.

  Lemma List_skipn_app_r2 :
    forall (l1 l2: list A) n k,
      n = List.length l1 ->
      List.skipn (n + k) (l1 ++ l2) =
      List.skipn k l2.
  Proof.
    intros; subst.
    rewrite List.skipn_app, List.skipn_all, minus_plus; simpl; (reflexivity || lia).
  Qed.

  Lemma replace_nth_eqn :
    forall (xs: list A) idx x,
      idx < List.length xs ->
      replace_nth idx xs x =
      List.firstn idx xs ++ x :: List.skipn (S idx) xs.
  Proof.
    induction xs; cbn; intros idx x Hlt.
    - inversion Hlt.
    - destruct idx.
      + reflexivity.
      + cbn [List.firstn List.app].
        f_equal; apply IHxs.
        auto with arith.
  Qed.
  End Single.

  Definition product {A B} (As: list A) (Bs: list B) : list (A * B) :=
    flat_map (fun a1 => List.map (pair a1) Bs) As.

  Definition map2 {A B C} (f: A -> B -> C) (ABs: list (A * B)) : list C :=
    List.map (fun ab => f (fst ab) (snd ab)) ABs.

  Lemma map2_map {A B C D} (f: B -> C -> D) (g: A -> B * C) (As: list A) :
    map2 f (List.map g As) =
    List.map (fun a => f (fst (g a)) (snd (g a))) As.
  Proof. unfold map2; rewrite map_map; reflexivity. Qed.

  Lemma map_map2 {A B C D} (f: A -> B -> C) (g: C -> D) (ABs: list (A * B)) :
    List.map g (map2 f ABs) =
    map2 (fun a b => g (f a b)) ABs.
  Proof. unfold map2; rewrite map_map; reflexivity. Qed.

  Lemma map2_map2 {A1 A2 B1 B2 C}
        (f: A1 -> A2 -> (B1 * B2))
        (g: B1 -> B2 -> C) (As: list (A1 * A2)) :
    map2 g (map2 f As) =
    map2 (fun a1 a2 => g (fst (f a1 a2)) (snd (f a1 a2))) As.
  Proof. unfold map2; rewrite map_map; reflexivity. Qed.

  Lemma map2_product {A B C} (f: A -> B -> C) (As: list A) (Bs: list B) :
    map2 f (product As Bs) =
    flat_map (fun a1 => List.map (f a1) Bs) As.
  Proof.
    unfold map2, product.
    rewrite !flat_map_concat_map, !concat_map, !map_map.
    f_equal; apply map_ext; intros; rewrite !map_map; reflexivity.
  Qed.
End Lists.

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
      @word.unsigned _ word (word.of_Z (Z.b2z b)) = Z.b2z b.
    Proof.
      destruct b; cbn [Z.b2z];
        auto using word.unsigned_of_Z_0, word.unsigned_of_Z_1.
    Qed.

    Lemma unsigned_of_Z_le (z: Z):
      0 <= z ->
      word.unsigned (word := word) (word.of_Z z) <= z.
    Proof.
      intros; rewrite word.unsigned_of_Z; unfold word.wrap.
      pose proof word.width_pos.
      pose proof Z.pow_pos_nonneg 2 width.
      apply Z.mod_le; lia.
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
      intros; cbn;
      apply word.unsigned_inj;
      rewrite lemma, !word.unsigned_of_Z;
      bitblast.Z.bitblast;
      rewrite !word.testbit_wrap;
      bitblast.Z.bitblast_core.

    Lemma morph_and x y:
      word.of_Z (Z.land x y) = word.and (word.of_Z x) (word.of_Z y) :> word.
    Proof. compile_binop_zzw_bitwise word.unsigned_and_nowrap. Qed.

    Lemma morph_or x y:
      word.of_Z (Z.lor x y) = word.or (word.of_Z x) (word.of_Z y) :> word.
    Proof. compile_binop_zzw_bitwise word.unsigned_or_nowrap. Qed.

    Lemma morph_xor x y:
      word.of_Z (Z.lxor x y) = word.xor (word.of_Z x) (word.of_Z y) :> word.
    Proof. compile_binop_zzw_bitwise word.unsigned_xor_nowrap. Qed.
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

    (* FIXME shouldn't *this* be the definition of `and1`? *)
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

Section Scalar.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.

  Open Scope Z_scope.

  Lemma bytes_per_width_bytes_per_word : forall width,
      width >= 0 ->
      Z.of_nat (Memory.bytes_per (width := width) access_size.word) = Memory.bytes_per_word width.
  Proof.
    intros; unfold Memory.bytes_per, Memory.bytes_per_word.
    rewrite Z2Nat.id; try apply Z.div_pos; lia.
  Qed.

  Lemma bytes_per_wordwidth_bytes_per_word :
      Z.of_nat (Memory.bytes_per (width := width) access_size.word) = Memory.bytes_per_word width.
  Proof.
    apply bytes_per_width_bytes_per_word.
    pose proof word.width_pos; lia.
  Qed.

  Lemma split_bytes_per_word:
    forall x : word,
      Z.of_nat
        (Datatypes.length
           (HList.tuple.to_list
              (LittleEndian.split (Memory.bytes_per (width := width) access_size.word)
                                  (word.unsigned x)))) = Memory.bytes_per_word width.
  Proof.
    intros x.
    rewrite HList.tuple.length_to_list.
    apply bytes_per_wordwidth_bytes_per_word.
  Qed.

  Lemma scalar_to_anybytes px x:
    Lift1Prop.impl1 (T := mem)
      (scalar px x)
      (Memory.anybytes px (Memory.bytes_per_word width)).
  Proof.
    intros m H; evar (bs: list byte);
      assert (array ptsto (word.of_Z 1) px bs m) by
        (subst bs; simple apply H).
    subst bs; erewrite <- split_bytes_per_word.
    eapply array_1_to_anybytes; eauto.
  Qed.

  Lemma anybytes_to_scalar px:
    Lift1Prop.impl1 (T := mem)
      (Memory.anybytes px (Memory.bytes_per_word width))
      (Lift1Prop.ex1 (scalar px)).
  Proof.
    intros m (bs & Harray & Hlen)%anybytes_to_array_1.
    apply scalar_of_bytes in Harray.
    - eexists; eassumption.
    - destruct width_cases; lia.
    - rewrite Hlen. destruct width_cases; subst; reflexivity || lia.
  Qed.
End Scalar.

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
End Rupicola.

(* TODO: should be upstreamed to coqutil *)
Module Z.
  Lemma lxor_xorb a b : Z.lxor (Z.b2z a) (Z.b2z b) = Z.b2z (xorb a b).
  Proof. destruct a, b; reflexivity. Qed.
End Z.
