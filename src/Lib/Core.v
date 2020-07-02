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
Require Export coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.SortedList.
Require Export coqutil.Z.PushPullMod.
Require Export coqutil.Tactics.Tactics.
Require Export coqutil.Tactics.letexists.
Require Export coqutil.Word.Interface coqutil.Word.Properties.
Require bedrock2.ProgramLogic.

Open Scope string_scope.
Export ListNotations.

Declare Scope sep_scope.
Delimit Scope sep_scope with sep.
Infix "*" := (sep) : sep_scope.

Set Nested Proofs Allowed.

Notation word := Semantics.word.

(* FIXME instead of cbn [fst snd], use simpl never hints in the sep case *)
Arguments Semantics.word : simpl never.

Notation address := word (only parsing).

Definition bedrock_func : Type :=
  string * (list string * list string * cmd).
Coercion name_of_func (f : bedrock_func) := fst f.

(* TODO: should move upstream to coqutil *)
Module map.
  Section __.
    Context {key value} {map : map.map key value}
            {map_ok : map.ok map}
            {key_eqb}
            {key_eq_dec :
               forall x y : key, BoolSpec (x = y) (x <> y) (key_eqb x y)}.

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
  End __.
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

    Lemma wrap_small x :
      (0 <= x < 2 ^ width)%Z ->
      word.wrap x = x.
    Proof. apply Z.mod_small. Qed.

    Lemma unsigned_of_Z_b2z b :
      word.unsigned (word.of_Z (Z.b2z b)) = Z.b2z b.
    Proof.
      destruct b; cbn [Z.b2z];
        auto using word.unsigned_of_Z_0, word.unsigned_of_Z_1.
    Qed.
  End __.
End word.

(* TODO: should be upstreamed to coqutil *)
Module Z.
  Lemma lxor_xorb a b : Z.lxor (Z.b2z a) (Z.b2z b) = Z.b2z (xorb a b).
  Proof. destruct a, b; reflexivity. Qed.
End Z.
