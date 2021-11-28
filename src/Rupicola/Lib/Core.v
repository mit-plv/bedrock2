From Coq Require Export
     Classes.Morphisms Numbers.DecimalString
     String List ZArith Lia.
From bedrock2 Require Export
     Array Map.Separation ProgramLogic
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

  Lemma fold_left_push_fn {A' B}
        (f: A -> B -> A)
        (f': A' -> B -> A')
        (g: A -> A')
        (P: A -> Prop):
    forall (l: list B),
      (forall a0 a, List.In a l -> P a0 -> P (f a0 a)) ->
      (forall a0 a, List.In a l -> P a0 -> g (f a0 a) = f' (g a0) a) ->
      forall (a0: A),
        P a0 ->
        g (fold_left f l a0) = fold_left f' l (g a0).
  Proof.
    induction l; simpl; intros HP Hg a0 Pa0.
    - reflexivity.
    - rewrite IHl, Hg; eauto.
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

  Lemma List_assoc_app_cons (l1 l2: list A) (a: A) :
    l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
  Proof. induction l1; simpl; congruence. Qed.

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

  (** ** map **)

  Lemma map_ext_id {A} (f: A -> A) l:
    (forall x, List.In x l -> f x = x) ->
    List.map f l = l.
  Proof.
    induction l; simpl.
    - reflexivity.
    - intros H; rewrite (H a), IHl by auto; reflexivity.
  Qed.

  Lemma skipn_map{A B: Type}: forall (f: A -> B) (n: nat) (l: list A),
      skipn n (List.map f l) = List.map f (skipn n l).
  Proof.
    induction n; intros.
    - reflexivity.
    - simpl. destruct l; simpl; congruence.
  Qed.

  (** ** fold **)

  Lemma fold_left_Proper :
    forall [A B : Type] (f f': A -> B -> A) (l l': list B) (i i': A),
      l = l' -> i = i' ->
      (forall a b, In b l -> f a b = f' a b) ->
      fold_left f l i = fold_left f' l' i'.
  Proof.
    induction l; intros * ? ? Heq; subst; simpl in *;
      try rewrite Heq; eauto.
  Qed.

  Lemma fold_left_inv [A B] (f: A -> B -> A) (P: A -> Prop) :
    forall (l: list B) (a0: A),
      P a0 ->
      (forall a b, In b l -> P a -> P (f a b)) ->
      P (fold_left f l a0).
  Proof. induction l; simpl; firstorder auto. Qed.

  (** ** combine **)

  Lemma fold_left_combine_fst {A B C} (f: A -> B -> A) : forall (l1: list C) l2 a0,
      (List.length l1 >= List.length l2)%nat ->
      fold_left f l2 a0 = fold_left (fun a '(_, b) => f a b) (combine l1 l2) a0.
  Proof.
    induction l1; destruct l2; simpl; intros; try rewrite IHl1; reflexivity || lia.
  Qed.

  Lemma map_combine_fst {A B}: forall lA lB,
      length lA = length lB ->
      List.map fst (@combine A B lA lB) = lA.
  Proof.
    induction lA; destruct lB; simpl; intros; rewrite ?IHlA; reflexivity || lia.
  Qed.

  Lemma map_combine_snd {A B}: forall lB lA,
      length lA = length lB ->
      List.map snd (@combine A B lA lB) = lB.
  Proof.
    induction lB; destruct lA; simpl; intros; rewrite ?IHlB; reflexivity || lia.
  Qed.

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

  Lemma combine_app {A B} : forall (lA lA': list A) (lB lB': list B),
      length lA = length lB ->
      combine (lA ++ lA') (lB ++ lB') = combine lA lB ++ combine lA' lB'.
  Proof.
    induction lA; destruct lB; simpl; inversion 1; try rewrite IHlA; eauto.
  Qed.

  (** ** enumerate **)

  Lemma enumerate_offset {A} (l: list A) : forall (start: nat),
      List.enumerate start l = List.map (fun p => (fst p + start, snd p)%nat) (List.enumerate 0 l).
  Proof.
    unfold List.enumerate; induction l; simpl; intros.
    - reflexivity.
    - rewrite (IHl (S start)), (IHl 1%nat), List.map_map.
      f_equal. simpl. apply map_ext.
      intros; f_equal; lia.
  Qed.

  Lemma enumerate_app {A} (l l': list A) start :
    List.enumerate start (l ++ l') =
      List.enumerate start l ++ List.enumerate (start + length l) l'.
  Proof.
    unfold List.enumerate.
    rewrite app_length, seq_app, combine_app;
      eauto using seq_length.
  Qed.

  (** ** concat **)

  Lemma length_concat_sum {A} (lss: list (list A)) :
    length (List.concat lss) =
      List.fold_left Nat.add (List.map (@length _) lss) 0%nat.
  Proof.
    rewrite fold_symmetric by eauto with arith.
    induction lss; simpl; rewrite ?app_length, ?IHlss; reflexivity.
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


  Lemma nth_seq len: forall i start d,
    (i < len)%nat ->
    nth i (seq start len) d = (i + start)%nat.
  Proof.
    induction len; destruct i; intros; simpl; try lia.
    rewrite IHlen; lia.
  Qed.

  Lemma nth_inj {A} n : forall (l l': list A) d,
    length l = n ->
    length l' = n ->
    (forall i, (i < n)%nat -> nth i l d = nth i l' d) ->
    l = l'.
  Proof.
    induction n; destruct l, l'; cbn [List.length]; intros * ?? Hi; try lia.
    - reflexivity.
    - f_equal.
      + apply (Hi 0%nat ltac:(lia)).
      + eapply IHn; eauto; intros i0 Hi0.
        apply (Hi (S i0)%nat ltac:(lia)).
  Qed.

  Lemma nth_repeat {A} (a d: A): forall n i,
      (i < n)%nat ->
      nth i (repeat a n) d = a.
  Proof.
    induction n; destruct i; simpl; intros; try lia.
    - reflexivity.
    - apply IHn; lia.
  Qed.

  Lemma nth_repeat_default {A} (d: A): forall n i,
      nth i (repeat d n) d = d.
  Proof.
    intros; destruct (Nat.lt_ge_cases i n).
    - rewrite nth_repeat by lia; reflexivity.
    - rewrite nth_overflow by (rewrite repeat_length; lia); reflexivity.
  Qed.

  Lemma map_seq_nth_slice {A} (l: list A) (d: A) :
    forall len start,
      List.map (fun idx => nth idx l d) (seq start len) =
      List.firstn len (List.skipn start l) ++
      repeat d (start + len - Nat.max start (List.length l)).
  Proof.
    intros.
    eapply @nth_inj with (d := d); intros.
    - rewrite map_length, seq_length; reflexivity.
    - rewrite app_length, firstn_length, repeat_length, skipn_length; lia.
    - destruct (Nat.lt_ge_cases i (List.length (List.firstn len (List.skipn start l))));
        [rewrite app_nth1 by lia | rewrite app_nth2 by lia].
      all: rewrite <- nth_nth_nth_map with (dn := List.length l) by lia.
      all: rewrite nth_seq by lia.
      + rewrite nth_firstn, nth_skipn by lia; reflexivity.
      + rewrite firstn_length, skipn_length in *.
        rewrite nth_overflow, nth_repeat_default by lia.
        reflexivity.
  Qed.

  Lemma map_seq_nth_slice_le {A} (l: list A) (d: A) :
    forall len start,
      (start + len <= List.length l)%nat ->
      List.map (fun idx => nth idx l d) (seq start len) =
      List.firstn len (List.skipn start l).
  Proof.
    intros; rewrite map_seq_nth_slice.
    replace (_ + _ - _)%nat with 0%nat by lia; simpl.
    rewrite app_nil_r; reflexivity.
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

(** ** Forall **)

Import List.

Lemma Forall_In {A} {P : A -> Prop} {l : list A}:
  Forall P l -> forall {x}, In x l -> P x.
Proof.
  intros HF; rewrite Forall_forall in HF; intuition.
Qed.

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
  Forall P (List.map f l).
Proof.
  induction l; simpl; intros H.
  - apply Forall_nil.
  - inversion H; subst. apply Forall_cons; tauto.
Qed.

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
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context {word_ok : word.ok word}.

  Lemma width_at_least_32 : 32 <= width.
  Proof. destruct width_cases; lia. Qed.

  Lemma byte_wrap_range z:
    0 <= byte.wrap z < 2 ^ width.
  Proof.
    pose proof Z.mod_pos_bound z 8.
    clear dependent word; unfold byte.wrap; destruct width_cases; subst; lia.
  Qed.

  Lemma byte_range_32 z:
    0 <= byte.wrap z < 2 ^ 32.
  Proof.
    pose proof Z.mod_pos_bound z 8.
    clear dependent word; unfold byte.wrap; lia.
  Qed.

  Lemma byte_range_64 z:
    0 <= byte.wrap z < 2 ^ 64.
  Proof.
    pose proof Z.mod_pos_bound z 8.
    clear dependent word; unfold byte.wrap; lia.
  Qed.

  Lemma width_mod_8 : width mod 8 = 0.
  Proof. destruct width_cases as [-> | ->]; reflexivity. Qed.

  Lemma wrap_byte_unsigned b:
    word.wrap (width := width) (byte.unsigned b) =
    byte.unsigned b.
  Proof.
    pose proof byte.unsigned_range b.
    rewrite word.wrap_small by (destruct width_cases as [-> | ->]; lia).
    reflexivity.
  Qed.

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

  Context {mem: map.map word byte} {mem_ok : map.ok mem}.

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

Module byte.
  (* FIXME isn't this defined somewhere already? *)
  Definition and (b1 b2: byte) :=
    byte.of_Z (Z.land (byte.unsigned b1) (byte.unsigned b2)).

  Lemma wrap_range z:
    0 <= byte.wrap z < 2 ^ 8.
  Proof. apply Z.mod_pos_bound. reflexivity. Qed.
End byte.

Section Byte.
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
    byte.unsigned (byte.and b1 b2) =
    Z.land (byte.unsigned b1) (byte.unsigned b2).
  Proof.
    unfold byte.and; rewrite byte.unsigned_of_Z.
    unfold byte.wrap; rewrite <- Z.land_ones.
    bitblast.Z.bitblast.
    rewrite testbit_byte_unsigned_ge.
    all: lia.
  Qed.

  Lemma byte_unsigned_xor (b1 b2: byte) :
    byte.unsigned (byte.xor b1 b2) =
      Z.lxor (byte.unsigned b1) (byte.unsigned b2).
  Proof.
    unfold byte.xor; rewrite byte.unsigned_of_Z.
    unfold byte.wrap; rewrite <- Z.land_ones.
    bitblast.Z.bitblast.
    rewrite !testbit_byte_unsigned_ge.
    all: reflexivity || lia.
  Qed.

  Lemma byte_xor_comm b1 b2:
    byte.xor b1 b2 = byte.xor b2 b1.
  Proof. unfold byte.xor; rewrite Z.lxor_comm; reflexivity. Qed.

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

Ltac div_up_t :=
  cbv [Nat.div_up]; zify;
  rewrite ?Zdiv.div_Zdiv, ?mod_Zmod in * by Lia.lia;
  nia.

Section DivUp.
  Lemma div_up_eqn a b:
    (b <> 0)%nat ->
    Nat.div_up a b =
    (a / b + if a mod b =? 0 then 0 else 1)%nat.
  Proof. destruct (Nat.eqb_spec (a mod b) 0); div_up_t. Qed.

  Lemma div_up_add_mod a b n:
    (a mod n = 0)%nat ->
    Nat.div_up (a + b) n =
    (Nat.div_up a n + Nat.div_up b n)%nat.
  Proof.
    intros; destruct (Nat.eq_dec n 0); subst; [ reflexivity | ].
    rewrite !div_up_eqn by lia.
    rewrite <- Nat.add_mod_idemp_l by assumption.
    replace (a mod n)%nat; cbn [Nat.add Nat.eqb].
    rewrite (Nat.div_mod a n) by assumption.
    replace (a mod n)%nat; cbn [Nat.add Nat.eqb].
    rewrite !Nat.add_0_r, !(Nat.mul_comm n (a/n)).
    rewrite !Nat.div_add_l, !Nat.div_mul by assumption.
    lia.
  Qed.

  Lemma div_up_exact a b:
    (b <> 0)%nat ->
    (a mod b = 0)%nat <->
    (a = b * (Nat.div_up a b))%nat.
  Proof.
    intros.
    rewrite div_up_eqn by lia.
    split; intros Heq.
    - rewrite Heq; cbn; rewrite Nat.mul_add_distr_l, Nat.mul_0_r, Nat.add_0_r.
      apply Nat.div_exact; assumption.
    - replace a; rewrite Nat.mul_comm; apply Nat.mod_mul; assumption.
  Qed.

  Lemma div_up_exact_mod a b:
    (b <> 0)%nat ->
    (a mod b = 0)%nat ->
    ((Nat.div_up a b) * b = a)%nat.
  Proof. intros * H0 Hmod; eapply div_up_exact in Hmod; lia. Qed.
End DivUp.

Section Chunks.
  Lemma nth_chunk {A} k (Hk: (k <> 0)%nat) (bs: list A) i d
        (Hi : (i < Nat.div_up (length bs) k)%nat) :
    nth i (chunk k bs) d = firstn k (skipn (i*k) bs).
  Proof.
    pose proof nth_error_chunk k Hk bs i Hi as Hn.
    eapply nth_error_nth in Hn; eassumption.
  Qed.

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

  Lemma length_chunk_app {A} (l l' : list A) (n : nat) :
    (n <> 0)%nat ->
    (length l mod n)%nat = 0%nat ->
    length (chunk n (l ++ l')) = length (chunk n l ++ chunk n l').
  Proof.
    intros; repeat rewrite ?app_length, ?length_chunk by assumption.
    rewrite div_up_add_mod by assumption; reflexivity.
  Qed.

  Open Scope list_scope.

  Lemma chunk_app {A} : forall (l l': list A) n,
      (n <> 0)%nat ->
      (length l mod n = 0)%nat ->
      chunk n (l ++ l') = chunk n l ++ chunk n l'.
  Proof.
    intros * Hn Hmod.
    eapply nth_ext with (d := []) (d' := []); [ | intros idx ].
    - apply length_chunk_app; assumption.
    - intros Hidx; eassert (Some _ = Some _) as HS; [ | injection HS; intros Hs; apply Hs ].
      rewrite <- !nth_error_nth' by assumption.
      rewrite <- !nth_error_nth' by (rewrite length_chunk_app in Hidx; eassumption).
      assert (idx < length (chunk n l) \/ length (chunk n l) <= idx)%nat as [Hlt | Hge] by lia;
        [ rewrite nth_error_app1 | rewrite nth_error_app2 ]; try eassumption.
      all: rewrite !nth_error_chunk.
      all: repeat rewrite ?length_chunk, ?app_length, ?div_up_add_mod in Hlt by assumption.
      all: repeat rewrite ?length_chunk, ?app_length, ?div_up_add_mod in Hidx by assumption.
      all: repeat rewrite ?length_chunk, ?app_length, ?div_up_add_mod in Hge by assumption.
      all: rewrite ?length_chunk, ?app_length, ?div_up_add_mod by assumption.
      all: try lia.
      all: pose proof Nat.div_up_range (length l) n ltac:(lia).
      + pose proof div_up_exact_mod (length l) n ltac:(lia) ltac:(lia).
        rewrite !firstn_skipn_comm, !firstn_app.
        replace (idx * n + n - length l)%nat with 0%nat by nia.
        simpl; rewrite app_nil_r; reflexivity.
      + rewrite Nat.mul_sub_distr_r.
        erewrite div_up_exact_mod by lia.
        rewrite skipn_app, skipn_all2; [ reflexivity | nia ].
  Qed.
End Chunks.

Require Import coqutil.Word.LittleEndianList.
Arguments le_combine: simpl nomatch.
Arguments le_split : simpl nomatch.
Arguments Z.mul: simpl nomatch.

Section combine_split.
  Lemma le_combine_app bs1 bs2:
    le_combine (bs1 ++ bs2) =
      Z.lor (le_combine bs1) (Z.shiftl (le_combine bs2) (Z.of_nat (List.length bs1) * 8)).
  Proof.
    induction bs1; cbn -[Z.shiftl Z.of_nat Z.mul]; intros.
    - rewrite Z.mul_0_l, Z.shiftl_0_r; reflexivity.
    - rewrite IHbs1, Z.shiftl_lor, Z.shiftl_shiftl, !Z.lor_assoc by lia.
      f_equal; f_equal; lia.
  Qed.

  Lemma le_combine_0 n:
    le_combine (repeat Byte.x00 n) = 0.
  Proof. induction n; simpl; intros; rewrite ?IHn; reflexivity. Qed.

  Lemma le_combine_app_0 bs n:
    le_combine (bs ++ repeat Byte.x00 n) = le_combine bs.
  Proof.
    rewrite le_combine_app; simpl; rewrite le_combine_0.
    rewrite Z.shiftl_0_l, Z.lor_0_r.
    reflexivity.
  Qed.

  Lemma le_combine_snoc_0 bs:
    le_combine (bs ++ [Byte.x00]) = le_combine bs.
  Proof. apply le_combine_app_0 with (n := 1%nat). Qed.

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
      le_combine (List.map (fun '(x, y) => byte.and x y) (combine bs1 bs2)).
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

  Definition in_bounds n x :=
    0 <= x < 2 ^ n.

  Definition forall_in_bounds l n:
    0 <= n ->
    (Forall (in_bounds n) l) <-> (forall i, in_bounds n (nth i l 0)).
  Proof.
    intros; pose proof Z.pow_pos_nonneg 2 n.
    rewrite Forall_nth_default' with (d := 0);
      unfold in_bounds; reflexivity || lia.
  Qed.

  Lemma le_combine_in_bounds bs n:
    (length bs <= n)%nat ->
    in_bounds (8 * Z.of_nat n) (le_combine bs).
  Proof.
    unfold in_bounds; intros.
    pose proof le_combine_bound bs.
    pose proof Zpow_facts.Zpower_le_monotone 2 (8 * Z.of_nat (length bs)) (8 * Z.of_nat n)
         ltac:(lia) ltac:(lia); lia.
  Qed.

  Lemma Forall_le_combine_in_bounds n zs:
    (0 < n)%nat ->
    Forall (in_bounds (8 * Z.of_nat n)) (List.map le_combine (chunk n zs)).
  Proof.
    intros; eapply Forall_map, Forall_impl.
    - intros a; apply le_combine_in_bounds.
    - eapply Forall_impl; [ | apply Forall_chunk_length_le ];
        simpl; intros; lia.
  Qed.

  Lemma le_split_0_l z:
    le_split 0 z = [].
  Proof. reflexivity. Qed.

  Lemma le_split_0_r n:
    le_split n 0 = repeat Byte.x00 n.
  Proof.
    induction n.
    - reflexivity.
    - unfold le_split; fold le_split.
      rewrite Z.shiftr_0_l, IHn; reflexivity.
  Qed.

  Open Scope list_scope.

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

  Lemma flat_map_le_split_combine_chunk:
    forall bs n,
      (0 < n)%nat ->
      (length bs mod n)%nat = 0%nat ->
      flat_map (le_split n) (List.map le_combine (chunk n bs)) = bs.
  Proof.
    intros; rewrite flat_map_concat_map, map_map, map_ext_id, concat_chunk; [reflexivity|].
    intros * Hin;
      pose proof (Forall_In (Forall_chunk_length_mod _ n ltac:(lia)) Hin);
      pose proof (Forall_In (Forall_chunk_length_le _ n ltac:(lia)) Hin);
      cbv beta in *.
    rewrite split_le_combine'; reflexivity || lia.
  Qed.

  Lemma map_unsigned_of_Z_le_combine_4
        {word : Word.Interface.word 32} {word_ok : word.ok word} bs :
    List.map (fun z : Z => word.unsigned (word := word) (word.of_Z z))
             (List.map le_combine (chunk 4 bs)) =
    List.map le_combine (chunk 4 bs).
  Proof.
    rewrite map_ext_id; [ reflexivity | ].
    intros * Hin%(Forall_In (Forall_le_combine_in_bounds 4 bs ltac:(lia))).
    apply word.unsigned_of_Z_nowrap; assumption.
  Qed.

  Lemma le_combine_nth_chunk n (bs: list byte) idx dd:
    n <> 0%nat ->
    (idx < Nat.div_up (Datatypes.length bs) n)%nat ->
    le_combine (nth idx (chunk n bs) dd) =
    le_combine (List.map (fun idx => nth idx bs Byte.x00) (seq (idx * n) n)).
  Proof.
    intros.
    rewrite nth_chunk by assumption.
    rewrite map_seq_nth_slice, le_combine_app_0.
    reflexivity.
  Qed.

  Lemma In_map_combine_in_bounds n (Hn: n <> 0%nat) bs a:
    In a (List.map le_combine (chunk n bs)) ->
    0 <= a < 2 ^ (8 * Z.of_nat n).
  Proof.
    intros; eapply (Forall_In (Forall_le_combine_in_bounds n bs ltac:(lia)));
      eassumption.
  Qed.
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
    destruct (List.firstn max_len xs) as [|h1 t1] eqn:E1; [ ZnWords | ].
    destruct (List.skipn max_len xs) as [|h2 t2] eqn:E2; [ ZnWords | ].
    rewrite <- E in H.
    SeparationLogic.seprewrite_in @array_append H.
    SeparationLogic.seprewrite_in @array_cons H.
    SeparationLogic.seprewrite_in @array_cons H.
    (* FIXME: Get Sam to make this proof magically shorter *)
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

  Lemma scalar_no_aliasing1 :
    no_aliasing (word := word) (Mem := Mem)
                (word.of_Z (Memory.bytes_per_word width))
                (scalar (mem := Mem)).
  Proof.
    red; intros * h Hmem.
    pose proof bytes_per_word_range.
    rewrite word.unsigned_of_Z_nowrap in h by lia.
    unfold scalar, truncated_word, truncated_scalar,
    littleendian, ptsto_bytes.ptsto_bytes in *.
    pose proof split_bytes_per_word a as Hlena.
    pose proof split_bytes_per_word b as Hlenb.
    set (HList.tuple.to_list _) as la in Hmem, Hlena.
    set (HList.tuple.to_list _) as lb in Hmem, Hlenb.
    rewrite <- (firstn_skipn (Z.to_nat delta) la) in Hmem.
    seprewrite_in @array_append Hmem; try lia.
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
  Proof.
    pose proof bytes_per_word_range.
    simpl; rewrite Z2Nat.id by lia; apply scalar_no_aliasing1.
  Qed.
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
