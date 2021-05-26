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
Require Export coqutil.Byte.
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

Global Set Nested Proofs Allowed.
Global Set Default Goal Selector "1".

Notation word := Semantics.word.

(* FIXME instead of cbn [fst snd], use simpl never hints in the sep case *)
Arguments Semantics.word : simpl never.

Notation address := word (only parsing).

Definition bedrock_func : Type :=
  string * (list string * list string * cmd).
Coercion name_of_func (f : bedrock_func) := fst f.

Definition predicate {parameters: Semantics.parameters} :=
  Semantics.trace -> Semantics.mem -> Semantics.locals -> Prop.

Module P2.
  Section Primitive.
    Set Primitive Projections.
    Record prod {A B} := pair { fst: A; snd: B }.
  End Primitive.
  Arguments prod: clear implicits.
  Arguments pair {A B} fst snd.
End P2.

Declare Scope p2_scope.
Delimit Scope p2_scope with p2.
Notation "\<  x ,  y ,  .. ,  z  \>" := (P2.pair .. (P2.pair x y) .. z) : p2_scope.
Open Scope p2_scope.

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
  Context {A : Type}.
  Open Scope list_scope.

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

    Local Notation b2w b :=
      (@word.of_Z _ word (Z.b2z b)).

    Lemma b2w_inj:
      forall b1 b2, b2w b1 = b2w b2 -> b1 = b2.
    Proof.
      intros [|] [|]; simpl;
        intros H%(f_equal word.unsigned);
        rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1 in H;
        cbn; congruence.
    Qed.

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


Notation b2w b :=
  (word.of_Z (Z.b2z b)).
Notation word_of_byte b :=
  (word.of_Z (Byte.byte.unsigned b)).
Notation byte_of_word w :=
  (byte.of_Z (word.unsigned w)).

Section Semantics.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok _}.

  Lemma WeakestPrecondition_weaken :
    forall cmd {functions} (p1 p2: _ -> _ -> _ -> Prop),
      (forall tr mem locals, p1 tr mem locals -> p2 tr mem locals) ->
      forall tr mem locals,
        WeakestPrecondition.program
          functions cmd tr mem locals p1 ->
        WeakestPrecondition.program
          functions cmd tr mem locals p2.
  Proof. intros; eapply Proper_program; eassumption. Qed.

  Lemma getmany_list_map l :
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
             {semantics : Semantics.parameters}
             (spec : list word -> Semantics.mem -> Prop)
             R tr :=
    (fun (tr' : Semantics.trace) (mem' : Semantics.mem) (rets : list word) =>
       tr = tr'
       /\ sep (spec rets) R mem').

  Definition postcondition_func_norets
             {semantics : Semantics.parameters} spec R tr :=
    postcondition_func (fun r => sep (emp (r = nil)) (spec r)) R tr.

  (* TODO: Remove locals_post *)
  Definition postcondition_cmd
             {semantics : Semantics.parameters}
             locals_post spec retvars R tr :=
    (fun (tr' : Semantics.trace) (mem' : Semantics.mem)
       (locals : Semantics.locals) =>
       tr = tr'
       /\ locals_post locals
       /\ exists rets,
           map.getmany_of_list locals retvars = Some rets
           /\ sep (spec rets) R mem').

  Lemma predicate_trivial
        {tr: Semantics.trace}
        {mem: Semantics.mem}
        {locals: Semantics.locals} {T} t0:
    (fun (_: T) tr' mem' locals' =>
       tr' = tr /\ mem' = mem /\ locals' = locals)
      t0 tr mem locals.
  Proof. intuition. Qed.

  Lemma to_byte_of_byte_nowrap b:
    byte_of_word (word_of_byte b : word) = b.
  Proof.
    rewrite word.unsigned_of_Z, word.wrap_small.
    - apply word.byte_of_Z_unsigned.
    - pose proof byte.unsigned_range b.
      destruct Semantics.width_cases as [-> | ->]; lia.
  Qed.
End Semantics.

(* TODO: should be upstreamed to coqutil *)
Module Z.
  Lemma lxor_xorb a b : Z.lxor (Z.b2z a) (Z.b2z b) = Z.b2z (xorb a b).
  Proof. destruct a, b; reflexivity. Qed.
End Z.
