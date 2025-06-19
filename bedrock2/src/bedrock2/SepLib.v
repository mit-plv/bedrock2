Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface coqutil.Map.OfListWord coqutil.Map.Memory coqutil.Word.LittleEndianList.
Require Import coqutil.Datatypes.ZList. Import ZList.List.ZIndexNotations.
Require Import bedrock2.Lift1Prop bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.PurifySep.
Require Import bedrock2.is_emp.
Require Export bedrock2.anyval.
Require Import bedrock2.Array bedrock2.Scalars.

(* PredTp equals `word -> mem -> Prop` if the predicate takes any number of values
   and its size depends on these values.
   PredTp equals `V1 -> ... -> Vn -> word -> mem -> Prop` for some `V1..Vn` if the
   predicate takes `n` values, but its size does not depend on these values. *)
Definition PredicateSize{PredTp: Type}(pred: PredTp) := Z.
Existing Class PredicateSize.

Ltac can_have_PredicateSize PredTp :=
  lazymatch PredTp with
  | @word.rep ?wi ?wo -> @map.rep (@word.rep ?wi ?wo) Coq.Init.Byte.byte _ -> Prop => idtac
  | ?V -> ?P => can_have_PredicateSize P
  end.

(* Derives the size of a value-independent predicate applied to a value *)
#[export] Hint Extern 4 (PredicateSize (?pred ?v)) =>
  let t := type of pred in can_have_PredicateSize t;
  lazymatch constr:(_: PredicateSize pred) with
  | ?sz => exact sz
  end
: typeclass_instances.

Notation invisible_cast T x :=
  match Set return T with
  | _ => x
  end.

Notation sizeof p := (invisible_cast (PredicateSize p) _).

Definition array{width}{BW: Bitwidth width}{word: word width}
  {mem: map.map word Byte.byte}[T: Type]
  (elem: T -> word -> mem -> Prop){elemSize: PredicateSize elem}
  (n: Z)(vs: list T)(addr: word): mem -> Prop :=
  sep (emp (len vs = n))
      (array (fun a v => elem v a) (word.of_Z elemSize) addr vs).

(* Note: We don't pass a list ?vs to the pattern, because the length is already given by n *)
#[export] Hint Extern 1
  (PredicateSize (@array ?width ?BW ?word ?mem ?T ?elem ?elemSize ?n)) =>
  exact (n * elemSize) : typeclass_instances.

Lemma purify_array{width}{BW: Bitwidth width}{word: word width}{word_ok: word.ok word}
  {mem: map.map word Byte.byte}{mem_ok: map.ok mem}[T: Type] elem
  {elemSize: PredicateSize elem}(n: Z)(vs: list T)(addr: word):
  purify (array elem n vs addr) (len vs = n). (* TODO also n <= 2^width or n < 2^width? *)
Proof.
  unfold purify, array. intros. eapply sep_emp_l in H. apply H.
Qed.
#[export] Hint Resolve purify_array | 10 : purify.

(* for concrete lists: *)
Lemma purify_array_and_elems{width}{BW: Bitwidth width}
  {word: word width}{word_ok: word.ok word}
  {mem: map.map word Byte.byte}{mem_ok: map.ok mem}[T: Type] elem
  {elemSize: PredicateSize elem}{P: Prop}
  (n: Z)(vs: list T)(addr: word):
  purify (bedrock2.Array.array (fun a v => elem v a) (word.of_Z elemSize) addr vs) P ->
  purify (array elem n vs addr) (len vs = n /\ P).
Proof.
  unfold purify, array. intros. eapply sep_emp_l in H0. split. 1: apply H0.
  eapply H. apply H0.
Qed.
Ltac is_concrete_list l :=
  lazymatch l with
  | nil => idtac
  | cons _ ?t => is_concrete_list t
  end.
#[export] Hint Extern 5 (purify (array ?elem ?n ?vs ?addr) _) =>
  is_concrete_list vs;
  eapply purify_array_and_elems;
  unfold bedrock2.Array.array;
  purify_rec
: purify.

(* for non-concrete lists.
   Note: not registered as a hint because usually not needed *)
Lemma purify_array_ith_elem{width}{BW: Bitwidth width}
  {word: word width}{word_ok: word.ok word}
  {mem: map.map word Byte.byte}{mem_ok: map.ok mem}[T: Type] elem
  {elemSize: PredicateSize elem}{P: T -> Prop}{inh: Inhabited.inhabited T}
  (n: Z)(vs: list T)(addr: word):
  (forall v a, purify (elem v a) (P v)) ->
  purify (array elem n vs addr) (forall i, 0 <= i < len vs -> P (List.get vs i)).
Proof.
  unfold purify, array. intros. eapply sep_emp_l in H0. apply proj2 in H0.
  eapply array_index_nat_inbounds
    with (n := Z.to_nat i) (default := Inhabited.default) in H0. 2: lia.
  destruct H0 as (_ & m2 & _ & _ & M).
  destruct M as (m3 & _ & _ & M & _).
  eapply H in M.
  Tactics.eqapply M.
  unfold List.get.
  Tactics.destruct_one_match. 1: exfalso; lia.
  rewrite <- List.hd_skipn_nth_default.
  apply List.nth_default_eq.
Qed.

Definition nbits_to_nbytes(nbits: Z): Z := (Z.max 0 nbits + 7) / 8.

Lemma nbits_to_nbytes_nonneg: forall nbits, 0 <= nbits_to_nbytes nbits.
Proof. intros. unfold nbits_to_nbytes. Z.to_euclidean_division_equations. lia. Qed.

Lemma nbits_to_nbytes_8: forall n, 0 <= n -> nbits_to_nbytes (8 * n) = n.
Proof.
  intros. unfold nbits_to_nbytes. Z.to_euclidean_division_equations. lia.
Qed.

Ltac nbits_to_exact_nbytes nbits :=
  let sz := lazymatch isZcst nbits with
            | true => eval cbv in (nbits_to_nbytes nbits)
            | false => constr:(nbits_to_nbytes nbits)
            end in
  exact sz.


Definition uint{width}{BW: Bitwidth width}{word: word width}{mem: map.map word Byte.byte}
  (nbits: Z)(v: Z)(addr: word): mem -> Prop :=
  sep (emp (0 <= v < 2 ^ nbits))
      (le_split (Z.to_nat (nbits_to_nbytes nbits)) v $@ addr ).

#[export] Hint Extern 1 (PredicateSize (uint ?nbits)) =>
  nbits_to_exact_nbytes nbits
: typeclass_instances.

Lemma purify_uint{width}{BW: Bitwidth width}{word: word width}{word_ok: word.ok word}
  {mem: map.map word Byte.byte}{mem_ok: map.ok mem} nbits v a:
  purify (uint nbits v a) (0 <= v < 2 ^ nbits).
Proof.
  unfold purify, uint. intros. eapply sep_emp_l in H. apply proj1 in H. exact H.
Qed.
#[export] Hint Resolve purify_uint : purify.


Definition uintptr{width}{BW: Bitwidth width}{word: word width}{mem: map.map word Byte.byte}
                  (v a: word): mem -> Prop := scalar a v.

#[export] Hint Extern 1 (PredicateSize (@uintptr ?width ?BW ?word ?mem)) =>
  nbits_to_exact_nbytes width
: typeclass_instances.

Lemma purify_uintptr{width}{BW: Bitwidth width}{word: word width}
  {mem: map.map word Byte.byte} v a:
  purify (uintptr v a) True.
Proof. unfold purify. intros. constructor. Qed.
#[export] Hint Resolve purify_uintptr : purify.

#[export] Hint Extern 1 (cannot_purify (uintptr ? _))
=> constructor : suppressed_warnings.

#[export] Hint Extern 1 (cannot_purify (uint _ ? _))
=> constructor : suppressed_warnings.

#[export] Hint Extern 1 (cannot_purify (if _ then _ else _))
=> constructor : suppressed_warnings.


Definition pointer_to{width}{BW: Bitwidth width}
  {word: word width}{mem: map.map word Byte.byte}
  (P: word -> mem -> Prop)(pointerAddr: word): mem -> Prop :=
  ex1 (fun targetAddr => sep (uintptr targetAddr pointerAddr) (P targetAddr)).

#[export] Hint Extern 1 (PredicateSize (@pointer_to ?width ?BW ?word ?mem ?pred)) =>
  nbits_to_exact_nbytes width
: typeclass_instances.


Lemma anyval_is_emp{word: Type}{mem: map.map word Coq.Init.Byte.byte}[T: Type]
  (p: T -> word -> mem -> Prop)(q: T -> Prop)(a: word):
  (forall x: T, is_emp (p x a) (q x)) -> is_emp (anyval p a) (exists x: T, q x).
Proof. unfold anyval, is_emp, impl1, emp, ex1. intros. firstorder idtac. Qed.

#[export] Hint Resolve anyval_is_emp | 5 : is_emp.

#[export] Hint Extern 1 (PredicateSize (anyval ?p)) =>
  lazymatch constr:(_: PredicateSize p) with
  | ?s => exact s
  end
: typeclass_instances.

Section WithMem.
  Context {width} {BW: Bitwidth width} {word: word width} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma purify_anyval_array T (elem: T -> word -> mem -> Prop) {sz: PredicateSize elem} n a:
    purify (array elem n ? a) (0 <= n).
    (* Note:
     - (n <= 2^width) would hold (because of max memory size)
     - (n < 2^width) would be more useful but is not provable currently *)
  Proof.
    unfold purify, anyval, ex1. intros * [vs Hm].
    eapply purify_array in Hm. lia.
  Qed.

  Lemma sep_assoc_eq: forall (p q r: mem -> Prop),
      sep (sep p q) r = sep p (sep q r).
  Proof.
    intros. eapply iff1ToEq. eapply sep_assoc.
  Qed.

  Import ZList.List.ZIndexNotations.
  Local Open Scope zlist_scope.

  Section Array.
    Context [T: Type] (elem: T -> word -> mem -> Prop) {sz: PredicateSize elem}.

    (* The opposite direction does not hold because (len (vs1 ++ vs2) = n1 + n2) does
     not imply (len vs1 = n1 /\ len vs2 = n2), but we can quantify over a vs:=vs1++vs2
     and use vs[:i] ++ vs[i:], resulting in the lemma split_array below *)
    Lemma merge_array: forall n1 n2 vs1 vs2 a m,
        sep (array elem n1 vs1 a)
          (array elem n2 vs2 (word.add a (word.of_Z (sz * n1)))) m ->
        array elem (n1 + n2) (vs1 ++ vs2) a m.
    Proof.
      unfold array. intros.
      pose proof (Array.array_append (fun (a0 : word) (v : T) => elem v a0)
                    (word.of_Z sz) vs1 vs2 a) as A.
      eapply iff1ToEq in A.
      rewrite A. clear A.
      rewrite sep_assoc_eq in H.
      eapply sep_emp_l in H.
      destruct H as [? H]. subst n1.
      eapply sep_comm in H.
      rewrite sep_assoc_eq in H.
      eapply sep_emp_l in H.
      destruct H as [? H]. subst n2.
      eapply sep_emp_l. split.
      1: rewrite List.app_length; lia.
      rewrite word.ring_morph_mul.
      rewrite word.of_Z_unsigned.
      rewrite <- word.ring_morph_mul.
      eapply sep_comm in H.
      exact H.
    Qed.

    Lemma split_array: forall vs n i a m,
        0 <= i <= len vs ->
        array elem n vs a m ->
        sep (array elem i vs[:i] a)
          (array elem (n-i) vs[i:] (word.add a (word.of_Z (sz * i)))) m.
    Proof.
      unfold array. intros.
      eapply sep_emp_l in H0. destruct H0.
      rewrite (List.split_at_index vs i) in H1 by assumption.
      eapply Array.array_append in H1.
      rewrite sep_assoc_eq.
      eapply sep_emp_l.
      split.
      { apply List.len_upto. assumption. }
      apply sep_comm.
      rewrite sep_assoc_eq.
      eapply sep_emp_l.
      split.
      { subst. apply List.len_from. assumption. }
      rewrite word.ring_morph_mul in H1.
      rewrite word.of_Z_unsigned in H1.
      rewrite <- word.ring_morph_mul in H1.
      rewrite List.len_upto in H1 by assumption.
      apply sep_comm.
      exact H1.
    Qed.

    Lemma array_nil_is_emp: forall n a, is_emp (array elem n nil a) (n = 0).
    Proof.
      unfold is_emp, impl1, array. intros. eapply sep_emp_l in H.
      simpl in H. destruct H. unfold emp in *. destruct H0. auto.
    Qed.

    Lemma array_0_is_emp: forall n xs a, n = 0 -> is_emp (array elem n xs a) (xs = nil).
    Proof.
      intros. destruct xs.
      - eapply weaken_is_emp. 2: eapply array_nil_is_emp. intros. reflexivity.
      - unfold is_emp, array, impl1. intros. eapply sep_emp_l in H0. apply proj1 in H0.
        subst n. discriminate.
    Qed.

    Hint Resolve array_0_is_emp : is_emp.

    Lemma anyval_array_0_is_emp: forall n a, n = 0 -> is_emp (array elem n ? a) True.
    Proof.
      intros. eapply weaken_is_emp. 1: intros _; constructor.
      typeclasses eauto with is_emp.
    Qed.

    Lemma merge_anyval_array: forall n1 n2 addr m,
        sep (array elem n1 ? addr)
            (array elem n2 ? (word.add addr (word.of_Z (sz * n1)))) m ->
        (array elem (n1 + n2) ? addr) m.
    Proof.
      unfold anyval. intros * Hm.
      eapply sep_ex1_l in Hm. destruct Hm as [bs1 Hm].
      eapply sep_ex1_r in Hm. destruct Hm as [bs2 Hm].
      exists (bs1 ++ bs2).
      eapply merge_array. exact Hm.
    Qed.

    Lemma split_anyval_array: forall n i addr m,
        0 <= i <= n ->
        (array elem n ? addr) m ->
        sep (array elem i ? addr)
            (array elem (n-i) ? (word.add addr (word.of_Z (sz * i)))) m.
    Proof.
      intros * B Hm.
      destruct Hm as [bs Hm].
      pose proof Hm as HP. eapply purify_array in HP.
      unfold anyval.
      eapply sep_ex1_l. exists bs[:i].
      eapply sep_ex1_r. exists bs[i:].
      subst n.
      eapply split_array in Hm. 2: eassumption.
      exact Hm.
    Qed.

    Lemma array1_to_elem{inh: Inhabited.inhabited T}: forall addr l,
        impl1 (array elem 1 l addr) (elem l[0] addr).
    Proof.
      unfold impl1, array. intros. eapply sep_emp_l in H. destruct H as (? & ?).
      destruct l. 1: discriminate.
      destruct l. 2: { simpl in H. exfalso. lia. }
      simpl in H0. eapply sep_emp_r in H0. apply (proj1 H0).
    Qed.
  End Array.

  Lemma ptsto_to_uint8: forall a b m, ptsto a b m -> uint 8 (Byte.byte.unsigned b) a m.
  Proof.
    intros a b m Hb.
    eapply sep_emp_l. split. 1: eapply Byte.byte.unsigned_range.
    change (Z.to_nat _) with 1%nat.
    cbv [le_split] in *. rewrite Byte.byte.of_Z_unsigned.
    cbv [sepclause_of_map ptsto] in *. rewrite map.of_list_word_singleton. auto.
  Qed.

  Lemma uint8_to_ptsto: forall a b m, uint 8 b a m -> ptsto a (Byte.byte.of_Z b) m.
  Proof.
    intros a b m [Hle Hb]%sep_emp_l; revert Hb.
    change (Z.to_nat _) with 1%nat.
    cbv [le_split]. rewrite map.of_list_word_singleton.
    cbv [sepclause_of_map ptsto]; auto.
  Qed.

  Lemma anybytes_from_alt: forall addr n m,
      0 <= n -> Memory.anybytes addr n m -> (array (uint 8) n ? addr) m.
  Proof.
    unfold anyval. intros * B H.
    eapply anybytes_to_array_1 in H. destruct H as (bs & Hm & Hl).
    exists (List.map Byte.byte.unsigned bs).
    unfold array. eapply sep_emp_l. split.
    { rewrite List.map_length. lia. }
    eapply array_map.
    eapply impl1_array. 2: exact Hm.
    unfold impl1. eapply ptsto_to_uint8.
  Qed.

  Lemma anybytes_to_alt: forall addr n m,
      (array (uint 8) n ? addr) m -> Memory.anybytes addr n m.
  Proof.
    unfold anyval. intros. destruct H as (bs & H).
    unfold array in H. eapply sep_emp_l in H. destruct H as (? & H). subst n.
    eapply impl1_array in H.
    - eapply (array_map ptsto Byte.byte.of_Z addr bs (word.of_Z 1)) in H.
      eapply array_1_to_anybytes in H. rewrite List.map_length in H. exact H.
    - clear m bs addr H. unfold impl1. eapply uint8_to_ptsto.
  Qed.

  Lemma uint_to_uintptr: forall a z,
      impl1 (uint width z a) (uintptr (word.of_Z z) a).
  Proof.
    unfold uint, uintptr. intros.
    eapply impl1_l_sep_emp. intros.
    unfold scalar, truncated_word, truncated_scalar.
    rewrite word.unsigned_of_Z_nowrap by assumption.
    unfold nbits_to_nbytes, Memory.bytes_per, Memory.bytes_per_word.
    rewrite Z.max_r by apply word.width_nonneg.
    reflexivity.
  Qed.

  Lemma uintptr_to_uint: forall a w,
      impl1 (uintptr w a) (uint width (word.unsigned w) a) .
  Proof.
    unfold uint, uintptr. intros.
    eapply impl1_r_sep_emp. split. 1: eapply word.unsigned_range.
    unfold scalar, truncated_word, truncated_scalar.
    unfold nbits_to_nbytes, Memory.bytes_per, Memory.bytes_per_word.
    rewrite Z.max_r by apply word.width_nonneg.
    reflexivity.
  Qed.
End WithMem.

Notation "'EX' x .. y , p" := (ex1 (fun x => .. (ex1 (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'EX'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

#[export] Hint Extern 1
  (PredicateSize (anyval (@array ?width ?BW ?word ?mem ?T ?elem ?elemSize ?n))) =>
  exact (n * elemSize) : typeclass_instances.

#[export] Hint Resolve purify_anyval_array : purify.

Require Import bedrock2.unzify.

#[export] Hint Resolve array_nil_is_emp : is_emp.
#[export] Hint Extern 1 (is_emp (array ?elem ?n ?xs ?a) _) =>
  eapply (array_0_is_emp elem n xs a ltac:(zify_goal; xlia zchecker)) : is_emp.
#[export] Hint Extern 1 (is_emp (array ?elem ?n ? ?a) _) =>
  eapply (anyval_array_0_is_emp elem n a ltac:(zify_goal; xlia zchecker)) : is_emp.
