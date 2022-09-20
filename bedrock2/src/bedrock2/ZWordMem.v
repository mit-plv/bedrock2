Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import coqutil.Tactics.fwd coqutil.Tactics.Tactics.
Require Import coqutil.Datatypes.ZList.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require Import coqutil.Word.LittleEndianList.
Require Import coqutil.Map.OfListWord.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.PurifySep.

Import ZList.List.ZIndexNotations.
Local Open Scope zlist_scope.

(* TODO move *)
Module List.
  Section WithA.
    Context [A: Type].

    Lemma split_at: forall n (l: list A), l = l[:n] ++ l[n:].
    Proof.
      intros. unfold List.upto, List.from. symmetry. apply List.firstn_skipn.
    Qed.

    Lemma len_nil: len (@nil A) = 0.
    Proof. intros. reflexivity. Qed.

    Lemma len_cons: forall a (l: list A), len (a :: l) = 1 + len l.
    Proof. intros. simpl (List.length (a :: l)). lia. Qed.

    Lemma len_app: forall (l1 l2: list A), len (l1 ++ l2) = len l1 + len l2.
    Proof. intros. rewrite List.app_length. lia. Qed.
  End WithA.
End List.

Undelimit Scope sep_scope.

(* PredTp equals `Z -> mem -> Prop` if the predicate takes any number of values
   and its size depends on these values.
   PredTp equals `V1 -> ... -> Vn -> Z -> mem -> Prop` for some `V1..Vn` if the
   predicate takes one `n` values, but its size does not depend on these values. *)
Definition PredicateSize{PredTp: Type}(pred: PredTp) := Z.
Existing Class PredicateSize.

(* Derives the size of a value-independent predicate applied to a value *)
#[export] Hint Extern 4 (PredicateSize (?pred ?v)) =>
  lazymatch constr:(_: PredicateSize pred) with
  | ?sz => exact sz
  end
: typeclass_instances.

(* Note: Not using a Section here because `Hint Extern` declared inside a Section cannot
   be exported) *)

Definition sepapp{key value}{mem: map.map key value}
  (P1 P2: Z -> mem -> Prop){P1size: PredicateSize P1}: Z -> mem -> Prop :=
  fun addr => sep (P1 addr) (P2 (addr + P1size)).

#[export] Hint Extern 1 (PredicateSize (sepapp ?P1 ?P2)) =>
  lazymatch constr:(_: PredicateSize P1) with
  | ?sz1 => lazymatch constr:(_: PredicateSize P2) with
            | ?sz2 => exact (sz1 + sz2)
            end
  end
: typeclass_instances.

(* Every memory predicate with a given start address and size should satisfy
   this bounds check.
   By wrapping any memory predicate in this range_ok predicate, we can assert
   that it indeed satisfies this bounds check.
   The NULL pointer may not be used as an address, but arrays whose last byte
   is just at 2^width-1 are allowed.
   This guarantees that the size of an array always fits into a word, and in
   particular, that two adjacent arrays whose size fits into a word can be
   combined into an array whose size fits into a word as well, without requiring
   any Z inequalities as preconditions. *)
Definition range_ok{width}{word: word width}{mem: map.map word Byte.byte}
  (pred: Z -> mem -> Prop){size: PredicateSize pred}: Z -> mem -> Prop :=
  fun start => sep (emp (0 < start /\ start + size <= 2 ^ width)) (pred start).

#[export] Hint Extern 1 (PredicateSize (range_ok ?pred)) =>
  lazymatch constr:(_: PredicateSize pred) with
  | ?sz => exact sz
  end
: typeclass_instances.

(* Note: Instead of wrapping a predicate pred inside range_ok, we could also
   assert `checks_range pred`:

    Definition checks_range(pred: Z -> mem -> Prop){size: PredicateSize pred}: Prop :=
      forall start m, pred start m -> 0 < start /\ start + size <= 2 ^ width.

   But in order to create predicates that satisfy checks_range, we'd still need
   range_ok, so we might as well just use only range_ok (or occasianally, assert
   `range_ok pred = pred`). *)

Lemma range_ok_idemp{width}{word: word width}{word_ok: word.ok word}
  {mem: map.map word Byte.byte}{mem_ok: map.ok mem}
  (pred: Z -> mem -> Prop){size: PredicateSize pred}:
  range_ok (range_ok pred) = range_ok pred.
Proof.
  unfold range_ok. extensionality addr. eapply iff1ToEq. split; intros.
  - eapply sep_emp_l in H. eapply proj2 in H. exact H.
  - eapply sep_emp_l. split. 2: exact H. eapply sep_emp_l in H.
    eapply proj1 in H. exact H.
Qed.

Lemma sepapp_range_ok{width}{word: word width}{word_ok: word.ok word}
  {mem: map.map word Byte.byte}{mem_ok: map.ok mem}
  (P1 P2: Z -> mem -> Prop){P1size: PredicateSize P1}{P2size: PredicateSize P2}:
  sepapp (range_ok P1) (range_ok P2) = range_ok (sepapp (range_ok P1) (range_ok P2)).
Proof.
  unfold range_ok, sepapp. extensionality start. eapply iff1ToEq.
  reify_goal.
  cancel_seps_at_indices 1%nat 2%nat. 1: reflexivity.
  cancel_seps_at_indices 2%nat 3%nat. 1: reflexivity.
  cbn [seps]. split; intros.
  - eapply sep_emp_l in H. destruct H. destruct H0. subst x.
    eapply sep_emp_l. split. 1: lia.
    eapply sep_emp_l. split. 1: lia.
    split. 2: lia. reflexivity.
  - eapply sep_emp_l in H. destruct H. eapply sep_emp_l in H0. destruct H0. destruct H1.
    subst x.
    eapply sep_emp_l. split. 1: lia. split. 2: lia. reflexivity.
Qed.

Definition pure_at_raw{key value}{mem: map.map key value}(P: Prop)(addr: Z):
  mem -> Prop := emp P.
#[export] Hint Extern 1 (PredicateSize (pure_at_raw ?P)) => exact 0 : typeclass_instances.
#[export] Hint Opaque pure_at_raw : typeclass_instances. (* to avoid confusion with hole *)

Definition pure_at{width}{word: word width}{mem: map.map word Byte.byte}(P: Prop):
  Z -> mem -> Prop := range_ok (pure_at_raw P).
#[export] Hint Extern 1 (PredicateSize (pure_at _)) => exact 0 : typeclass_instances.
#[export] Hint Opaque pure_at : typeclass_instances.

Definition hole_raw{key value}{mem: map.map key value}(n addr: Z): mem -> Prop := emp True.
#[export] Hint Extern 1 (PredicateSize (hole_raw ?n)) => exact n : typeclass_instances.
#[export] Hint Opaque hole_raw : typeclass_instances.

Definition hole{width}{word: word width}{mem: map.map word Byte.byte}(n: Z):
  Z -> mem -> Prop := range_ok (hole_raw n).
#[export] Hint Extern 1 (PredicateSize (hole ?n)) => exact n : typeclass_instances.
#[export] Hint Opaque hole : typeclass_instances.

Definition array_raw{width}{word: word width}{mem: map.map word Byte.byte}{T: Type}
  (elem: T -> Z -> mem -> Prop){elemSize: PredicateSize elem}:
  list T -> Z -> mem -> Prop :=
  fix rec xs :=
    match xs with
    | nil => pure_at_raw True
    | cons h tl => sepapp (elem h) (rec tl)
    end.

#[export] Hint Extern 1 (PredicateSize (@array_raw ?width ?word ?mem ?T ?elem ?elemSize ?vs)) =>
  exact (len vs * elemSize) : typeclass_instances.

(* Note: 0 <= elemSize is required to ensure that start+elemSize does not become
   negative, and making the inequality strict is convenient because then range_ok
   implies that n fits into a word (which would not be the case if elemSize=0
   because upper-bounding n*0=0 has no effect. *)
Definition array{width}{BW: Bitwidth width}{word: word width}
  {mem: map.map word Byte.byte}{T: Type}
  (elem: T -> Z -> mem -> Prop){elemSize: PredicateSize elem}
  (n: Z)(vs: list T): Z -> mem -> Prop :=
  sepapp (pure_at (len vs = n /\ 0 < elemSize)) (range_ok (array_raw elem vs)).

(* Note: We don't pass a list ?vs to the pattern, because the length is already given by n *)
#[export] Hint Extern 1
  (PredicateSize (@array ?width ?BW ?word ?mem ?T ?elem ?elemSize ?n)) =>
  exact (n * elemSize) : typeclass_instances.

Section WithMem.
  Context {width}{word: word width}{word_ok: word.ok word}.
  Context {mem: map.map word Byte.byte}{mem_ok: map.ok mem}.

  Lemma sep_assoc_eq: forall (p q r: mem -> Prop),
      sep (sep p q) r = sep p (sep q r).
  Proof.
    intros. eapply iff1ToEq. eapply sep_assoc.
  Qed.

  Lemma sepapp_pure_at_raw_True_l: forall (p: Z -> mem -> Prop),
      sepapp (pure_at_raw True) p = p.
  Proof.
    unfold sepapp, pure_at_raw. intros. extensionality addr. eapply iff1ToEq.
    rewrite Z.add_0_r. eapply sep_emp_True_l.
  Qed.

  Lemma sepapp_pure_at_raw_True_r: forall (p: Z -> mem -> Prop) {sz: PredicateSize p},
      sepapp p (pure_at_raw True) = p.
  Proof.
    unfold sepapp, pure_at_raw. intros. extensionality addr. eapply iff1ToEq.
    eapply sep_emp_True_r.
  Qed.

  Lemma sepapp_assoc(P1 P2 P3: Z -> mem -> Prop)
    {sz1: PredicateSize P1}{sz2: PredicateSize P2}:
    sepapp (sepapp P1 P2) P3 = sepapp P1 (sepapp P2 P3).
  Proof.
    unfold sepapp. extensionality addr.
    rewrite sep_assoc_eq. rewrite Z.add_assoc.
    reflexivity.
  Qed.
End WithMem.

Section ArrayLemmas.
  Context {width}{BW: Bitwidth width}{word: word width}{word_ok: word.ok word}.
  Context {mem: map.map word Byte.byte}{mem_ok: map.ok mem}.
  Context {T: Type}(elem: T -> Z -> mem -> Prop){elemSize: PredicateSize elem}.

  Lemma purify_array: forall n vs a,
      purify (array elem n vs a)
        (len vs = n /\
         0 < elemSize /\
         0 < a /\
         a + n * elemSize <= 2 ^ width).
  Proof.
    unfold purify, array, sepapp, pure_at, pure_at_raw, range_ok. intros.
    rewrite ?sep_assoc_eq in H.
    repeat (eapply sep_emp_l in H; destruct H as (? & H)). lia.
  Qed.

  Lemma array_raw_app xs ys:
    array_raw elem (xs ++ ys) = sepapp (array_raw elem xs) (array_raw elem ys).
  Proof.
    induction xs.
    - simpl. symmetry. apply sepapp_pure_at_raw_True_l.
    - change (array_raw elem ((a :: xs) ++ ys)) with
        (sepapp (elem a) (array_raw elem (xs ++ ys))).
      rewrite IHxs.
      change (array_raw elem (a :: xs)) with (sepapp (elem a) (array_raw elem xs)).
      rewrite <- sepapp_assoc. extensionality addr. unfold sepapp. f_equal.
      f_equal. change (len (a :: xs)) with (Z.of_nat (S (length xs))). lia.
  Qed.

  (* given a goal of the form (iff1 LHS RHS), where LHS and RHS only consist
     of sep and emp, turns it into purely propositional goals *)
  Ltac de_emp :=
    intro m'; split; intros Hm;
      rewrite ?sep_assoc_eq in Hm;
      rewrite ?sep_assoc_eq;
      repeat match goal with
        | H: sep (emp _) _ _ |- _ => eapply sep_emp_l in H; destruct H
        | H: emp _ _ |- _ => destruct H
        end;
      subst;
      repeat match goal with
        | |- sep (emp _) _ _ => eapply sep_emp_l
        | |- _ /\ _ => split
        | |- emp _ map.empty => refine (conj eq_refl _)
        end.

  Lemma array_split(i: Z)(n: Z)(vs: list T):
    0 <= i <= n ->
    array elem n vs = sepapp (array elem i vs[:i]) (array elem (n-i) vs[i:]).
  Proof.
    intros.
    extensionality addr. etransitivity.
    { eapply f_equal2. 2: reflexivity. apply (List.split_at i). }
    unfold array. rewrite array_raw_app.
    unfold sepapp, pure_at, pure_at_raw, range_ok.
    rewrite ?Z.add_0_r.
    eapply assume_pure_of_sides_of_sep_eq.
    1,2: purify_rec.
    intros.
    assert (len vs[:i] + len vs[i:] = len vs). {
      rewrite (List.split_at i vs) at 3. rewrite List.len_app. reflexivity.
    }
    rewrite List.len_app in *.
    rewrite List.len_upto by lia.
    eapply iff1ToEq. cancel. cbn [seps].
    de_emp; lia.
  Qed.

  Lemma array_cons(n: Z)(v: T)(vs: list T):
    array elem n (v :: vs) = sepapp (range_ok (elem v)) (array elem (n-1) vs).
  Proof.
    intros.
    change (v :: vs) with ([|v|] ++ vs).
    extensionality addr.
    eapply assume_pure_of_sides_of_sep_eq.
    { eapply purify_array. }
    { unfold sepapp. eapply purify_sep_skip_l. eapply purify_array. }
    intros.
    rewrite List.len_app, List.len_cons, List.len_nil in *.
    rewrite (array_split 1) by lia.
    unfold sepapp. rewrite Z.mul_1_l.
    f_equal.
    unfold array. simpl (len ([|v|] ++ vs)[:1]).
    simpl (array_raw elem ([|v|] ++ vs)[:1]).
    unfold sepapp, pure_at, range_ok, pure_at_raw.
    rewrite Z.add_0_r. eapply iff1ToEq.
    cancel. cbn [seps]. de_emp; lia.
  Qed.

  Lemma array_merge(n1 n2: Z)(vs1 vs2: list T):
    sepapp (array elem n1 vs1) (array elem n2 vs2) =
      sepapp (pure_at (len vs1 = n1 /\ len vs2 = n2))
             (array elem (n1 + n2) (vs1 ++ vs2)).
  Proof.
  Admitted.

End ArrayLemmas.

#[export] Hint Resolve purify_array : purify.

Definition nbits_to_nbytes(nbits: Z): Z := (Z.max 0 nbits + 7) / 8.

Lemma nbits_to_nbytes_nonneg: forall nbits, 0 <= nbits_to_nbytes nbits.
Proof. intros. unfold nbits_to_nbytes. Z.to_euclidean_division_equations. lia. Qed.

Lemma nbits_to_nbytes_8: forall n, 0 <= n -> nbits_to_nbytes (8 * n) = n.
Proof.
  intros. unfold nbits_to_nbytes. Z.to_euclidean_division_equations. lia.
Qed.

(*
Fixpoint le_combine_z(bytes: list Z): Z :=
  match bytes with
  | nil => 0
  | h :: t => Z.lor h (Z.shiftl (le_combine_z t) 8)
  end.
*)
Definition le_combine_z(bytes: list Z): Z :=
  le_combine (List.map Byte.byte.of_Z bytes).

(* Just for internal use, as long as uint is not defined yet.
   Prefer `array (uint 8)`, because it takes a `list Z` instead of a `list byte`,
   so fewer conversions are needed, and generic array lemmas can be reused. *)
Definition bytearray{width}{word: word width}{mem: map.map word Byte.byte}
  (bs: list Byte.byte)(addr: Z)(m: mem): Prop :=
  m = map.of_list_word_at (word.of_Z addr) bs.

#[export] Hint Extern 1 (PredicateSize (bytearray ?bs)) =>
  exact (len bs) : typeclass_instances.

Definition uint{width}{BW: Bitwidth width}{word: word width}{mem: map.map word Byte.byte}
  (nbits: Z)(v: Z): Z -> mem -> Prop :=
  sepapp (pure_at (0 <= v < 2 ^ nbits))
    (range_ok (bytearray (LittleEndianList.le_split (Z.to_nat (nbits_to_nbytes nbits)) v))).

#[export] Hint Extern 1 (PredicateSize (uint ?nbits)) =>
  let sz := lazymatch isZcst nbits with
            | true => eval cbv in (nbits_to_nbytes nbits)
            | false => constr:(nbits_to_nbytes nbits)
            end in
  exact sz
: typeclass_instances.

Lemma purify_uint{width: Z}{BW: Bitwidth width}{word: word width}{word_ok: word.ok word}
  {mem: map.map word Byte.byte}{mem_ok: map.ok mem}: forall a v nbits,
    purify (mem := mem) (uint nbits v a)
      (0 <= v < 2 ^ nbits /\
       0 < a /\
       a + nbits_to_nbytes nbits <= 2 ^ width).
Proof.
  unfold purify, uint, pure_at, pure_at_raw, range_ok, sepapp. intros.
  rewrite !sep_assoc_eq in H.
  repeat (eapply sep_emp_l in H; destruct H as (? & H)).
  rewrite length_le_split in H2.
  pose proof nbits_to_nbytes_nonneg nbits.
  lia.
Qed.

#[export] Hint Resolve purify_uint : purify.

Section ScalarsLemmas.
  Context {width}{BW: Bitwidth width}{word: word width}{word_ok: word.ok word}.
  Context {mem: map.map word Byte.byte}{mem_ok: map.ok mem}.

  Lemma bytes_to_uint: forall L (bs: list Z),
      array (uint 8) L bs =
      sepapp (pure_at (len bs = L /\ List.Forall (fun b => 0 <= b < 256) bs))
             (uint (8 * L) (le_combine_z bs)).
  Proof.
    intros.
    unfold array. unfold uint at 2. extensionality addr. unfold sepapp.
    unfold pure_at, pure_at_raw, range_ok.
    rewrite Z.add_0_r.
    rewrite length_le_split.
    (*
    rewrite nbits_to_nbytes_8 by lia.
    rewrite Nat2Z.id.
    unfold le_combine_z.
    pose proof (split_le_combine (List.map Byte.byte.of_Z bs)) as P.
    rewrite List.map_length in P.
    rewrite P. clear P.

    eapply assume_pure_of_sides_of_sep_eq.
    1,2: purify_rec.
    intros.

    remember (Z.to_nat L) as nbytes eqn: E.
    eapply (f_equal Z.of_nat) in E. rewrite Z2Nat.id in E by lia. subst L.
    revert nbytes bs E.
    induction nbytes; intros;
      extensionality addr; extensionality m;
      apply PropExtensionality.propositional_extensionality.
    - unfold array. unfold uint, byteseq_predicate. simpl in E.
      rewrite <- E.
      destruct bs; try discriminate.
      simpl. change (nbits_to_nbytes 0) with 0 in *.
      split; intros.
      + eapply sep_emp_l in H. fwd.
        case TODO.
      + fwd. eapply sep_emp_l.
        case TODO.
    - destruct bs; try discriminate.
      rewrite array_cons.
      replace (len (u :: bs) - 1) with (len bs) by (rewrite List.length_cons; lia).
      rewrite IHnbytes by (rewrite List.length_cons in *; lia).
*)
  Abort.

End ScalarsLemmas.
Declare Scope sepapp_scope.
Infix "*+" := sepapp (at level 36, left associativity) : sepapp_scope.
