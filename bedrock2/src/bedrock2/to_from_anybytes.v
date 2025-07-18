Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import coqutil.Datatypes.Inhabited.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Datatypes.ZList. Import ZList.List.ZIndexNotations.
Require Import bedrock2.Lift1Prop bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.SepLib.
Require Import bedrock2.sepapp.

Section WithMem.
  Context {width} {BW: Bitwidth width} {word: word width} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Definition unchecked_load_uint8s(m: mem)(addr: word)(n: Z): list Z :=
    List.map Byte.byte.unsigned
      (Option.force (coqutil.Map.Memory.load_bytes m addr (Z.to_nat n))).

  Lemma array_to_load_bytes: forall n bs addr m,
      array (uint 8) n bs addr m ->
      array (uint 8) n (unchecked_load_uint8s m addr n) addr m.
  Proof.
    unfold array. intros. eapply sep_emp_l in H. destruct H as (L & H).
    eapply sep_emp_l.
    unfold unchecked_load_uint8s.
    rewrite List.map_length.
  Abort.

  Definition contiguous(P: word -> mem -> Prop)(n: Z): Prop :=
    forall addr, impl1 (P addr) (array (uint 8) n ? addr).

  (* Informative version of contiguous that can be used to instantiate evars that
     were created before we know that we need to invoke contiguous.
     BUT this does not work because it the expression (unchecked_load_uint8s m addr n)
     that we'd like to use to instantiate the evar depends on m, which won't be in the
     evar scope. *)
  Definition contiguous_info_bad(P: word -> mem -> Prop)(n: Z): Prop :=
    forall addr m, P addr m -> array (uint 8) n (unchecked_load_uint8s m addr n) addr m.

  (* sometimes, we don't need the actual proof, but only want to know whether it's
     contiguous to determine whether a proof step is safe, so we can save the proof effort *)
  Inductive fake_contiguous(P: word -> mem -> Prop): Prop :=
    mk_fake_contiguous.

  Lemma contiguous_to_fake P n: contiguous P n -> fake_contiguous P.
  Proof. intros. constructor. Qed.

  Lemma cast_to_anybytes: forall (P: word -> mem -> Prop) a n m,
      contiguous P n -> P a m -> (array (uint 8) n ? a) m.
  Proof. unfold contiguous, impl1. intros. eauto. Qed.

  (* Informative version of contiguous that can be used to instantiate evars that
     were created before we know that we need to invoke contiguous. *)
  Definition contiguous_info[V: Type](P: V -> word -> mem -> Prop)(n: Z): Type :=
    { f: V -> list Z | forall v addr m, P v addr m -> array (uint 8) n (f v) addr m }.

  Lemma array_uint8_contiguous_info: forall n, contiguous_info (array (uint 8) n) n.
  Proof. unfold contiguous_info. intros. exists id. intros *. exact id. Qed.

  (* predicate P can be filled with any byte list of length n *)
  Definition fillable[V: Type](P: V -> word -> mem -> Prop)(n: Z): Type :=
    { f: list Z -> V | forall addr bs m, array (uint 8) n bs addr m -> P (f bs) addr m }.

  (* Allows us to obtain a V without introducing a new variable that would not be
     in the scope of a previously created evar *)
  Lemma unfold_fillable[V: Type](P: V -> word -> mem -> Prop)(n: Z)
    (h: fillable P n):
    forall addr bs m, array (uint 8) n bs addr m -> P (proj1_sig h bs) addr m.
  Proof. unfold fillable. intros. destruct h as (f & h). simpl. eapply h. exact H. Qed.

  Section Bad.
    (* just here for illustration of how we'd prove other lemmas if they were actually
     needed *)
    Hypothesis array_to_load_bytes: forall n bs addr m,
        array (uint 8) n bs addr m ->
        array (uint 8) n (unchecked_load_uint8s m addr n) addr m.

    Lemma contiguous_to_info_bad: forall P n, contiguous P n -> contiguous_info_bad P n.
    Proof.
      unfold contiguous, contiguous_info_bad, anyval, impl1, ex1. intros.
      specialize H with (1 := H0). destruct H as (bs & H).
      eapply array_to_load_bytes. eassumption.
    Qed.

    Lemma contiguous_implies_proj1_of_fillable[T: Type]:
      forall (P: word -> mem -> Prop) (F: T -> word -> mem -> Prop) (n: Z) (a: word)
             (HC: contiguous P n) (HF: fillable F n),
      forall m, P a m -> F (proj1_sig HF (unchecked_load_uint8s m(*<--BAD*) a n)) a m.
    Proof.
      unfold  fillable, impl1, anyval, ex1. intros. destruct HF as (f & HF). simpl.
      eapply contiguous_to_info_bad in HC.
      unfold contiguous_info_bad in HC. specialize HC with (1 := H).
      eapply HF. exact HC.
    Qed.
  End Bad.

  Lemma contiguous_info_implies_proj1[T1 T2: Type]:
    forall (P1: T1 -> word -> mem -> Prop) (P2: T2 -> word -> mem -> Prop) (n: Z)
           (HC: contiguous_info P1 n) (HF: fillable P2 n),
      forall v a, impl1 (P1 v a) (P2 (proj1_sig HF (proj1_sig HC v)) a).
  Proof.
    unfold contiguous_info, fillable, impl1, anyval, ex1.
    intros. destruct HF as (f & HF). destruct HC as (c & HC). simpl.
    eapply HF. eapply HC. exact H.
  Qed.

  Lemma contiguous_implies_anyval_of_fillable{T: Type}:
    forall (P: word -> mem -> Prop) (F: T -> word -> mem -> Prop) (n: Z) (a: word),
      contiguous P n ->
      fillable F n ->
      impl1 (P a) (anyval F a).
  Proof.
    unfold contiguous, fillable, impl1, anyval, ex1. intros.
    specialize H with (1 := H0). destruct H as (vs & H).
    eexists. eapply (unfold_fillable _ _ X). eapply H.
  Qed.

  Lemma contiguous_implies_anyval_of_sepapps[T: Type]:
    forall (P: word -> mem -> Prop) (F: T -> word -> mem -> Prop) (n: Z) (a: word) preds,
      contiguous P n ->
      F = (fun v: T => sepapps (preds v)) ->
      (forall bs m, sep (array (uint 8) n bs a) (emp True) m ->
                    sep (EX v, (sepapps (preds v)) a) (emp True) m) ->
      impl1 (P a) (anyval F a).
  Proof.
    unfold contiguous, impl1, anyval, ex1. intros. subst F.
    setoid_rewrite sep_emp_r in H1.
    specialize H with (1 := H2). destruct H as (bs & H).
    specialize H1 with (1 := conj H I).
    apply H1.
  Qed.

  Lemma array_uint8_contiguous: forall v n, contiguous (array (uint 8) n v) n.
  Proof. unfold contiguous. intros. unfold anyval. eapply impl1_ex1_r. reflexivity. Qed.

  Lemma anybytes_contiguous: forall n, contiguous (anyval (array (uint 8) n)) n.
  Proof. unfold contiguous. intros. reflexivity. Qed.

  Lemma sepapps_nil_contiguous: contiguous (sepapps nil) 0.
  Proof.
    unfold contiguous, sepapps, anyval, Memory.anybytes, impl1.
    simpl. intros *. intros [? _]. subst.
    exists nil. unfold array.
    eapply sep_emp_l. split; [reflexivity| ].
    simpl. unfold emp. auto.
  Qed.

  Lemma sepapps_cons_contiguous: forall p tail n1 n2,
      contiguous p n1 ->
      contiguous (sepapps tail) n2 ->
      contiguous (sepapps (cons (mk_sized_predicate p n1) tail)) (n1 + n2).
  Proof.
    unfold contiguous. intros.
    rewrite sepapps_cons.
    simpl.
    intros m Hm.
    eapply merge_anyval_array.
    destruct Hm as (m1 & m2 & D & Hm1 & Hm2).
    unfold impl1 in *.
    exists m1, m2. rewrite Z.mul_1_l. eauto.
  Qed.

  Lemma uintptr_contiguous: forall v, contiguous (uintptr v) (Memory.bytes_per_word width).
  Proof.
    unfold contiguous, impl1, uintptr. intros.
    eapply Scalars.scalar_to_anybytes in H.
    eapply anybytes_from_alt.
    1: destruct width_cases as [E|E]; rewrite E; cbv; discriminate.
    assumption.
  Qed.

  Lemma uint_contiguous: forall (nbits v: Z),
      (nbits_to_nbytes nbits) <= 2^width ->
      contiguous (uint nbits v) (nbits_to_nbytes nbits).
  Proof.
    unfold contiguous, impl1. intros nbits v Hw addr m H. eapply anybytes_from_alt.
    { apply nbits_to_nbytes_nonneg. }
    unfold uint in H. eapply sep_emp_l in H. apply proj2 in H.
    cbv [Memory.anybytes] in *; extract_ex1_and_emp_in_hyps.
    cbv [sepclause_of_map] in *; subst m; eexists; intuition eauto;
       rewrite ?LittleEndianList.length_le_split, ?Z2Nat.id in *; trivial using nbits_to_nbytes_nonneg.
  Qed.

  Lemma fillable_emp_True(T: Type){inh: Inhabited.inhabited T}:
    fillable (fun (_: T) (_: word) => emp True) 0.
  Proof.
    unfold fillable. exists (fun _ => Inhabited.default).
    unfold array. intros. eapply sep_emp_l in H. destruct H as (L & H).
    destruct bs. 2: discriminate L. clear L. simpl in H. exact H.
  Qed.

  Lemma fillable_transform[X Y: Type](t: X -> Y)(p: word -> Y -> mem -> Prop)(n: Z):
    fillable (fun v a => p a (t v)) n -> fillable (fun v a => p a v) n.
  Proof. unfold fillable. intros (f & H). exists (fun bs => t (f bs)). exact H. Qed.

  Lemma fillable_impl[V: Type](P Q: V -> word -> mem -> Prop):
    (forall v a m, P v a m -> Q v a m) ->
    forall n, fillable P n -> fillable Q n.
  Proof.
    unfold fillable. intros. destruct X as (f & F). exists f. intros.
    eapply H. eapply F. assumption.
  Qed.

  Section WithT.
    Context [T: Type] {inh: Inhabited.inhabited T}.

    Fixpoint fixed_size_tuple_of_list(n: nat)(l: list T): HList.tuple T n.
      refine (match n with
              | O => tt
              | S m => _
              end).
      constructor.
      1: exact (List.hd Inhabited.default l).
      eapply fixed_size_tuple_of_list. exact (List.tl l).
    Defined.

    Lemma fixed_size_tuple_of_list_to_list: forall n l,
        List.length l = n ->
        HList.tuple.to_list (fixed_size_tuple_of_list n l) = l.
    Proof.
      induction n; simpl; intros; destruct l; try discriminate.
      - reflexivity.
      - simpl. f_equal. eapply IHn. simpl in H. eapply Nat.succ_inj. exact H.
    Qed.
  End WithT.

  Lemma truncated_scalar_fillable sz:
    fillable (fun (v: Z) (a: word) => Scalars.truncated_scalar sz a v)
      (Z.of_nat (Memory.bytes_per (width := width) sz)).
  Proof.
    unfold Scalars.truncated_scalar, fillable, array.
    exists (fun v => LittleEndianList.le_combine (List.map Byte.byte.of_Z v)); intros.
    extract_ex1_and_emp_in_hyps.
    rewrite LittleEndianList.split_le_combine' by (rewrite List.map_length; lia).
    apply Array.array1_iff_eq_of_list_word_at; try exact _.
    { rewrite List.map_length; case BW as [ [ -> | -> ] ], sz in *; unfold Memory.bytes_per, Memory.bytes_per_word in *; try (Z.div_mod_to_equations; lia). }
    eapply Array.array_map, Array.impl1_array, H; cbv [impl1 uint]; intros; cbv beta.
    extract_ex1_and_emp_in_hyps.
    progress change (Z.to_nat (nbits_to_nbytes 8)) with 1%nat in *.
    unfold LittleEndianList.le_split in *; rewrite OfListWord.map.of_list_word_singleton in *.
    cbv [ptsto sepclause_of_map] in *; subst; reflexivity.
  Qed.

  Lemma truncated_word_fillable:
    fillable (fun v a: word => Scalars.truncated_word Syntax.access_size.word a v)
             (Memory.bytes_per_word width).
  Proof.
    unfold Scalars.truncated_word.
    eapply fillable_transform with (X := Z) (t := word.of_Z).
    pose proof (truncated_scalar_fillable Syntax.access_size.word) as F.
    assert (Z.of_nat (Memory.bytes_per (width := width) Syntax.access_size.word) =
              Memory.bytes_per_word width) as E. {
      destruct width_cases as [W | W]; rewrite W; reflexivity.
    }
    rewrite <- E.
    eapply fillable_impl. 2: eapply (truncated_scalar_fillable Syntax.access_size.word).
    cbv beta. intros *.
    unfold Scalars.truncated_scalar.
    rewrite LittleEndianList.le_split_mod.
    rewrite word.unsigned_of_Z. unfold word.wrap.
    intro H. eqapply H. f_equal. f_equal. f_equal.
    destruct width_cases as [W | W]; rewrite W; reflexivity.
  Qed.

  Lemma scalar_fillable:
    fillable (fun v a : word => Scalars.scalar a v) (Memory.bytes_per_word width).
  Proof. unfold Scalars.scalar. eapply truncated_word_fillable. Qed.

  Lemma uintptr_fillable: fillable uintptr (Memory.bytes_per_word width).
  Proof. unfold uintptr. apply scalar_fillable. Qed.

  Lemma uint_fillable(nbits: Z):
    0 < nbits ->
    nbits mod 8 = 0 ->
    fillable (uint nbits) (nbits_to_nbytes nbits).
  Proof.
    unfold fillable, uint. intros. eexists. intros * Hm.
    unfold array in Hm. eapply sep_emp_l in Hm. destruct Hm as (L & Hm).
    eapply (Array.impl1_array _ (fun (a : word) (v : Z) => uint 8 v a)
              (fun (a : word) (v : Z) => ptsto a (Byte.byte.of_Z v))) in Hm.
    2: { unfold impl1. intros. eapply uint8_to_ptsto. assumption. }
    eapply (Array.array_map _ _ addr bs (word.of_Z 1)) in Hm.
    eapply sep_emp_l.
    split.
    2: {
      rewrite <- L. revert Hm.
      rewrite Nat2Z.id.
      instantiate (1 := (fun bs =>
        LittleEndianList.le_combine (List.map Byte.byte.of_Z bs))).
      cbv beta.
      rewrite <- (List.map_length Byte.byte.of_Z bs).
      rewrite LittleEndianList.split_le_combine.
      intros ?%Array.bytearray_iff_bytes; extract_ex1_and_emp_in_hyps; trivial.
    }
    cbv beta.
    pose proof (LittleEndianList.le_combine_bound (List.map Byte.byte.of_Z bs)) as A.
    rewrite List.map_length in A.
    replace (8 * Z.of_nat (length bs)) with nbits in A.
    1: exact A.
    unfold nbits_to_nbytes in *. Z.div_mod_to_equations. lia.
  Qed.

  Lemma uint8_fillable: fillable (uint 8) 1.
  Proof. apply uint_fillable; reflexivity. Qed.

  Lemma uint16_fillable: fillable (uint 16) 2.
  Proof. apply uint_fillable; reflexivity. Qed.

  Lemma uint32_fillable: fillable (uint 32) 4.
  Proof. apply uint_fillable; reflexivity. Qed.

  Lemma uint64_fillable: fillable (uint 64) 8.
  Proof. apply uint_fillable; reflexivity. Qed.

  Lemma array_fillable: forall T (elem: T -> word -> mem -> Prop) (sz: PredicateSize elem) n,
      0 < sz ->
      fillable elem sz ->
      fillable (array elem n) (sz * n).
  Proof.
    unfold fillable, array. intros. destruct X as (f & F).
    exists (fun bs => List.map f (List.chunk (Z.to_nat sz) bs)).
    intros * Hm.
    eapply sep_emp_l in Hm. destruct Hm as [Hl Hm].
    eapply sep_emp_l. split.
    { rewrite List.map_length. rewrite List.length_chunk by lia.
      unfold List.Nat.div_up. clear -Hl H.
      rewrite Nat2Z.inj_div. Z.div_mod_to_equations. nia. }
    replace n with (Z.of_nat (Z.to_nat n)) in * by lia.
    forget (Z.to_nat n) as N. clear n.
    revert bs addr m Hl Hm. induction N; intros.
    - simpl in Hl. rewrite Z.mul_0_r in Hl. destruct bs; try discriminate Hl; [].
      simpl. simpl in *. exact Hm.
    - rewrite <- (List.firstn_skipn (Z.to_nat sz) bs) in Hm|-*.
      eapply Array.array_append in Hm.
      destruct Hm as (m1 & m2 & D & Hm1 & Hm2).
      specialize IHN with (2 := Hm2).
      rewrite List.skipn_length in IHN.
      specialize (IHN ltac:(lia)).
      specialize (F addr (List.firstn (Z.to_nat sz) bs) m1).
      rewrite List.chunk_app. 2: lia.
      2: {
        rewrite List.firstn_length. clear -Hl H.
        replace (Init.Nat.min (Z.to_nat sz) (length bs)) with (Z.to_nat sz) by lia.
        apply Nat.Div0.mod_same.
      }
      rewrite List.map_app.
      eapply Array.array_append.
      exists m1, m2. ssplit. 1: exact D.
      + rewrite List.chunk_small by (rewrite List.firstn_length; lia).
        simpl. apply sep_emp_r. split. 2: constructor.
        eapply F. eapply sep_emp_l. split.
        { rewrite List.firstn_length. lia. }
        exact Hm1.
      + eqapply IHN. f_equal.
        rewrite List.map_length. rewrite List.length_chunk by lia.
        rewrite List.firstn_length. rewrite Nat.min_l by lia.
        unfold List.Nat.div_up.
        rewrite Nat2Z.inj_div.
        rewrite Z2Nat.id by lia.
        replace (Z.of_nat (Z.to_nat sz + (Z.to_nat sz - 1)) / sz) with 1.
        2: {
          clear -H. Z.div_mod_to_equations. nia.
        }
        rewrite word.unsigned_of_Z_1.
        rewrite Z.mul_1_r, Z.mul_1_l. rewrite word.of_Z_unsigned.
        reflexivity.
  Qed.

  (* TODO make non-fake *)
  Lemma array_fake_contiguous: forall T (elem: T -> word -> mem -> Prop)
                                      {sz: PredicateSize elem} n vs,
      (forall v, fake_contiguous (elem v)) ->
      fake_contiguous (array elem n vs).
  Proof. intros. constructor. Qed.

  Lemma sepapps_nil_fake_contiguous: fake_contiguous (sepapps nil).
  Proof. constructor. Qed.

  Lemma sepapps_cons_fake_contiguous: forall p sz l,
      fake_contiguous p ->
      fake_contiguous (sepapps l) ->
      fake_contiguous (sepapps (cons (mk_sized_predicate p sz) l)).
  Proof. intros. constructor. Qed.

  Lemma anyval_fake_contiguous{T: Type}: forall p: T -> word -> mem -> Prop,
      (forall v, fake_contiguous (p v)) ->
      fake_contiguous (anyval p).
  Proof. intros. constructor. Qed.
End WithMem.

Section WithMem32.
  Context {word: word 32} {BW: Bitwidth 32} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma uintptr32_contiguous: forall v, contiguous (uintptr v) 4.
  Proof. eapply (uintptr_contiguous (width := 32)). Qed.

  Lemma uintptr32_fillable: fillable uintptr 4.
  Proof. eapply (uintptr_fillable (width := 32)). Qed.
End WithMem32.

Section WithMem64.
  Context {word: word 64} {BW: Bitwidth 64} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma uintptr64_contiguous: forall v, contiguous (uintptr v) 8.
  Proof. eapply (uintptr_contiguous (width := 64)). Qed.

  Lemma uintptr64_fillable: fillable uintptr 8.
  Proof. eapply (uintptr_fillable (width := 64)). Qed.
End WithMem64.

Create HintDb contiguous.
#[global] Hint Variables Opaque : contiguous.
#[global] Hint Constants Opaque : contiguous.
#[global] Hint Transparent PredicateSize : contiguous.

#[export] Hint Resolve
  sepapps_cons_contiguous
  sepapps_nil_contiguous
  uintptr32_contiguous
  uintptr64_contiguous
  uint_contiguous
  array_uint8_contiguous
  array_uint8_contiguous_info
  anybytes_contiguous
  contiguous_to_fake
  array_fake_contiguous
  sepapps_nil_fake_contiguous
  sepapps_cons_fake_contiguous
  anyval_fake_contiguous
: contiguous.

Create HintDb fillable.
#[global] Hint Variables Opaque : fillable.
#[global] Hint Constants Opaque : fillable.
#[global] Hint Transparent PredicateSize : fillable.

#[export] Hint Resolve
  uintptr32_fillable
  uintptr64_fillable
  uint8_fillable
  uint16_fillable
  uint32_fillable
  uint64_fillable
: fillable.

#[export] Hint Extern 1 (fillable (array ?elem ?n) _) =>
  eapply array_fillable; [ xlia zchecker | eauto with fillable ]
: fillable.

#[export] Hint Extern 20 (contiguous ?p ?n) =>
  let h := head p in unfold h; typeclasses eauto with contiguous
: contiguous.

#[export] Hint Extern 20 (fake_contiguous ?p) =>
  let h := head p in unfold h; typeclasses eauto with contiguous
: contiguous.

Ltac is_contiguous P :=
  assert_succeeds (eassert (contiguous P _) by typeclasses eauto with contiguous).

Ltac is_fake_contiguous P :=
  assert_succeeds (assert (fake_contiguous P) by typeclasses eauto with contiguous).

Section TestsWithMem64.
  Context {word: word 64} {BW: Bitwidth 64} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Goal forall (foo: word -> mem -> Prop) (v: word), True.
    intros.
    is_contiguous (uintptr v).
    Fail is_contiguous foo.
    Fail is_fake_contiguous foo.
    assert (fake_contiguous foo) as A.
    2: {
      Fail is_contiguous foo.
      is_fake_contiguous foo.
      clear A.
      assert (contiguous foo 42) as A.
      2: {
        is_contiguous foo.
        is_fake_contiguous foo.
  Abort.
End TestsWithMem64.
