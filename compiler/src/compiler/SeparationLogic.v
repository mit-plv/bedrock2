Require Export Coq.Lists.List. Export ListNotations.
Require Export Coq.ZArith.ZArith. Open Scope Z_scope.
Require Export coqutil.Word.Interface coqutil.Word.Properties.
Require Export coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.rdelta coqutil.Tactics.destr coqutil.Decidable.
Require Import coqutil.Tactics.rewr coqutil.Tactics.Tactics.
Require Export coqutil.Z.Lia.
Require Export coqutil.Datatypes.PropSet.
Require Export bedrock2.Lift1Prop.
Require Export bedrock2.Map.Separation.
Require Export bedrock2.Map.SeparationLogic.
Require Export bedrock2.Array.
Require Export bedrock2.Scalars.
Require Export coqutil.Word.SimplWordExpr.
Require Export bedrock2.SepLogAddrArith.
Require Import coqutil.Tactics.Simp.
Require Export riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
Require Import riscv.Spec.Decode.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
From coqutil Require Import Map.Memory LittleEndianList.

Declare Scope sep_scope.

Infix "*" := sep : sep_scope.

Delimit Scope sep_scope with sep.
Arguments impl1 {T} (_)%sep (_)%sep.
Arguments iff1 {T} (_)%sep (_)%sep.

(* TODO does not get rid of %sep in printing as intended *)
Arguments sep {key} {value} {map} (_)%sep (_)%sep.

Definition bytes_per_word{width}{BW: Bitwidth width}: Z := Memory.bytes_per_word width.

Section ptstos.
  Context {width} {BW: Bitwidth width} {word: word.word width} {word_ok: word.ok word}.
  Context {mem : map.map word byte} {mem_ok: map.ok mem}.
  Context (iset: InstructionSet).

  Definition word_array: word -> list word -> mem -> Prop :=
    array ptsto_word (word.of_Z bytes_per_word).

  (* we use InvalidInstruction to put data into the instruction memory, so we have
     to allow them, but make sure that they can be represented with 32 bits *)
  Definition valid_InvalidInstruction(instr: Instruction): Prop :=
    exists n, 0 <= n < 2 ^ 32 /\ instr = InvalidInstruction n.

  (* contains all the conditions needed to successfully execute instr, except
     that addr needs to be in the set of executable addresses, which is dealt with elsewhere *)
  Definition ptsto_instr(addr: word)(instr: Instruction): mem -> Prop :=
     ((le_split 4 (encode instr) $@ addr) *
     emp (verify instr iset \/ valid_InvalidInstruction instr) *
     emp ((word.unsigned addr) mod 4 = 0))%sep.

  Definition program(addr: word)(prog: list Instruction): mem -> Prop :=
    array ptsto_instr (word.of_Z 4) addr prog.

  Lemma invert_ptsto_instr: forall {addr instr R m},
    (ptsto_instr addr instr * R)%sep m ->
     (verify instr iset \/ valid_InvalidInstruction instr) /\
     (word.unsigned addr) mod 4 = 0.
  Proof.
    intros.
    unfold array, ptsto_instr in *.
    lazymatch goal with
    | H: (?T * ?P1 * ?P2 * R)%sep ?m |- _ =>
      assert ((T * R * P1 * P2)%sep m) as A by ecancel_assumption; clear H
    end.
    do 2 (apply sep_emp_r in A; destruct A as [A ?]).
    auto.
  Qed.

  Lemma invert_ptsto_program1: forall {addr instr R m},
    (program addr [instr] * R)%sep m ->
     (verify instr iset \/ valid_InvalidInstruction instr) /\
     (word.unsigned addr) mod 4 = 0.
  Proof.
    unfold program. intros. simpl in *. eapply invert_ptsto_instr.
    ecancel_assumption.
  Qed.

  Lemma cast_word_array_to_bytes bs (addr : word) : iff1
    (array ptsto_word (word.of_Z bytes_per_word) addr bs)
    (array ptsto (word.of_Z 1) addr (flat_map (fun x =>
       (LittleEndianList.le_split (Z.to_nat bytes_per_word) (word.unsigned x)))
          bs)).
  Proof.
    clear iset.
    revert addr; induction bs; intros; [reflexivity|].
    cbn [array flat_map].
    etransitivity. 1:eapply Proper_sep_iff1; [reflexivity|]. 1:eapply IHbs.
    etransitivity. 2:symmetry; eapply bytearray_append.
    eapply Proper_sep_iff1.
    { unfold scalar, truncated_word, truncated_scalar.
      rewrite array1_iff_eq_of_list_word_at; try exact _; Morphisms.f_equiv.
      rewrite length_le_split.
      clear -BW; case BW as [ [ -> | -> ] ]; cbv; discriminate. }
    assert (0 < bytes_per_word). { (* TODO: deduplicate *)
      unfold bytes_per_word; simpl; destruct width_cases as [EE | EE]; rewrite EE; cbv; trivial.
    }
    Morphisms.f_equiv.
    Morphisms.f_equiv.
    Morphisms.f_equiv.
    simpl.
    rewrite LittleEndianList.length_le_split.
    rewrite Z2Nat.id; blia.
  Qed.

  Lemma byte_list_to_word_list_array: forall bytes,
    Z.of_nat (length bytes) mod bytes_per_word = 0 ->
    exists word_list : list word,
      Z.of_nat (Datatypes.length word_list) =
      Z.of_nat (Datatypes.length bytes) / bytes_per_word /\
    forall p,
      iff1 (array ptsto (word.of_Z 1) p bytes)
           (array ptsto_word (word.of_Z bytes_per_word) p word_list).
  Proof.
    clear iset.
    assert (AA: 0 < bytes_per_word). {
      unfold bytes_per_word.
      simpl.
      destruct width_cases as [E | E]; rewrite E; cbv; reflexivity.
    }
    intros.
    Z.div_mod_to_equations.
    subst r.
    specialize (H0 ltac:(blia)); clear H1.
    ring_simplify in H0.
    assert (0 <= q) by Lia.nia.
    generalize dependent bytes.
    pattern q.
    refine (natlike_ind _ _ _ q H); clear -BW word_ok mem_ok; intros.
    { case bytes in *; cbn in *; ring_simplify in H0; try discriminate.
      exists nil; split; reflexivity. }
    rewrite Z.mul_succ_r in *.
    specialize (H0 (List.skipn (Z.to_nat bytes_per_word) bytes)).
    rewrite List.length_skipn in H0.
    specialize (H0 ltac:(Lia.nia)).
    case H0 as [words' [Hlen Hsep] ].
    eexists (cons _ words').
    split; [cbn; blia|].
    intros p0; specialize (Hsep (word.add p0 (word.of_Z bytes_per_word))).
    rewrite array_cons.
    etransitivity.
    2:eapply Proper_sep_iff1; [reflexivity|].
    2:eapply Hsep.
    clear Hsep.

    rewrite <-(List.firstn_skipn (Z.to_nat bytes_per_word) bytes) at 1.
    unfold ptsto_word, truncated_word, truncated_scalar.

    rewrite <-bytearray_index_merge.
    1: eapply Proper_sep_iff1; [|reflexivity].
    2: rewrite word.unsigned_of_Z; setoid_rewrite Z.mod_small.
    3: {
      unfold bytes_per_word.
      simpl.
      destruct width_cases as [E | E]; rewrite E; cbv; intuition discriminate.
    }
    2: rewrite List.length_firstn_inbounds; Lia.nia.
    Morphisms.f_equiv.
    setoid_rewrite word.unsigned_of_Z.
    setoid_rewrite Z.mod_small.
    1:unshelve erewrite (_:Memory.bytes_per Syntax.access_size.word = length _); shelve_unifiable; cycle 1.
    1:setoid_rewrite LittleEndianList.split_le_combine.
    { rewrite array1_iff_eq_of_list_word_at; try exact _; Morphisms.f_equiv.
      rewrite List.firstn_length, Nat2Z.inj_min, H1.
      etransitivity; [eapply Z.le_min_l|].
      clear -BW; case BW as [ [ -> | -> ] ]; cbv; discriminate. }
    { rewrite List.length_firstn_inbounds; try Lia.nia.
        clear -BW; case BW as [ [ -> | -> ] ]; cbv; trivial. }
    intros.
    pose proof (LittleEndianList.le_combine_bound (List.firstn (Z.to_nat bytes_per_word) bytes)).
    split; [blia|].
    destruct H0.
    eapply Z.lt_le_trans. 1: eassumption.
    eapply Z.pow_le_mono_r. 1: reflexivity.
    rewrite List.length_firstn_inbounds; try Lia.nia.
    unfold bytes_per_word;
    destruct width_cases as [E | E]; rewrite E; cbv; inversion 1.
  Qed.

  Lemma ll_mem_to_hl_mem: forall mH mL (addr: word) bs R,
      (eq mH * array ptsto (word.of_Z 1) addr bs * R)%sep mL ->
      exists mTraded,
        (eq (map.putmany mH mTraded) * R)%sep mL /\
        map.disjoint mH mTraded /\
        Memory.anybytes addr (Z.of_nat (List.length bs)) mTraded.
  Proof.
    unfold sep, map.split.
    intros.
    simp.
    epose proof array_1_to_anybytes.
    eauto 10.
    Unshelve. all : exact _.
  Qed.

  Lemma hl_mem_to_ll_mem: forall mH mHSmall mTraded mL (addr: word) n R,
      map.split mH mHSmall mTraded ->
      Memory.anybytes addr n mTraded ->
      (eq mH * R)%sep mL ->
      exists bs,
        List.length bs = Z.to_nat n /\
        (eq mHSmall * array ptsto (word.of_Z 1) addr bs * R)%sep mL.
  Proof.
    unfold sep, map.split.
    intros.
    apply anybytes_to_array_1 in H0.
    simp. repeat eexists; try eassumption.
  Qed.

  Lemma load_from_word_array: forall p words frame m i v,
      (word_array p words * frame)%sep m ->
      nth_error words (Z.to_nat i) = Some v ->
      0 <= i ->
      Memory.load Syntax.access_size.word m (word.add p (word.of_Z (i * bytes_per_word))) = Some v.
  Proof.
    unfold word_array.
    intros.
    eapply nth_error_split in H0. simp.
    seprewrite_in @array_append H.
    seprewrite_in @array_cons H.
    eapply load_word_of_sep.
    use_sep_assumption.
    cancel.
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. f_equal. f_equal. rewrite Z.mul_comm. f_equal. 1: blia.
      apply word.unsigned_of_Z_nowrap.
      unfold bytes_per_word.
      destruct width_cases as [E | E]; rewrite E; cbv; intuition congruence.
    }
    ecancel_done.
  Qed.

  Lemma store_to_word_array: forall p oldwords frame m i v,
      (word_array p oldwords * frame)%sep m ->
      0 <= i < Z.of_nat (List.length oldwords) ->
      exists newwords m',
        Memory.store Syntax.access_size.word m (word.add p (word.of_Z (i * bytes_per_word))) v = Some m' /\
        (word_array p newwords * frame)%sep m' /\
        nth_error newwords (Z.to_nat i) = Some v /\
        (forall j w, j <> Z.to_nat i -> nth_error oldwords j = Some w -> nth_error newwords j = Some w) /\
        length newwords = length oldwords.
  Proof.
    unfold word_array.
    intros.
    destruct (List.nth_error oldwords (Z.to_nat i)) eqn: E. 2: {
      exfalso. eapply nth_error_Some. 2: eassumption. blia.
    }
    eapply nth_error_split in E. simp.
    seprewrite_in @array_append H.
    seprewrite_in @array_cons H.
    eexists (l1 ++ v :: l2).
    eapply store_word_of_sep. {
      use_sep_assumption. cancel. cancel_seps_at_indices 0%nat 0%nat. {
        f_equal. f_equal. f_equal. rewrite Z.mul_comm. f_equal. 1: blia.
        apply word.unsigned_of_Z_nowrap.
        unfold bytes_per_word.
        destruct width_cases as [E | E]; rewrite E; cbv; intuition congruence.
      }
      ecancel_done.
    }
    clear H.
    intros. ssplit.
    - seprewrite @array_append. seprewrite @array_cons.
      use_sep_assumption.
      cancel.
      cancel_seps_at_indices 0%nat 0%nat. {
        f_equal. f_equal. f_equal. rewrite Z.mul_comm. f_equal. 2: blia.
        symmetry. apply word.unsigned_of_Z_nowrap.
        unfold bytes_per_word.
        destruct width_cases as [E | E]; rewrite E; cbv; intuition congruence.
      }
      ecancel_done.
    - rewrite nth_error_app2 by blia. replace (Z.to_nat i - length l1)%nat with O by blia. reflexivity.
    - intros. assert (j < Z.to_nat i \/ Z.to_nat i < j)%nat as C by blia. destruct C as [C | C].
      + rewrite nth_error_app1 by blia. rewrite nth_error_app1 in H1 by blia. assumption.
      + rewrite nth_error_app2 by blia. rewrite nth_error_app2 in H1 by blia.
        replace (j - length l1)%nat with (S (j - length l1 - 1)) in * by blia.
        assumption.
    - rewrite ?List.app_length. reflexivity.
  Qed.
End ptstos.

(* These lemmas are for any kind of map, so that they can also be used to describe locals *)
Section MoreSepLog.
  Context {key value} {map : map.map key value}.
  Context {ok : map.ok map} {key_eqb: key -> key -> bool} {key_eq_dec : EqDecider key_eqb}.

  Lemma sep_inline_eq: forall (A R: map -> Prop) m1,
    (exists m2, (R * eq m2)%sep m1 /\ A m2) <->
    (R * A)%sep m1.
  Proof.
    unfold iff, Separation.sep.
    repeat match goal with
           | |- _ => intros || simp || eassumption || reflexivity
           | |- _ /\ _ => split
           | |- exists _, _ => eexists
           end.
  Qed.

  Lemma subst_split: forall (m m1 m2 M: map) (R: map -> Prop),
      map.split m m1 m2 ->
      (eq m * R)%sep M ->
      (eq m1 * eq m2 * R)%sep M.
  Proof.
    intros.
    unfold map.split in H. destruct H. subst.
    use_sep_assumption.
    cancel.
    cbn [seps].
    intro m. unfold sep, map.split. split; intros.
    - subst. eauto 10.
    - simp. reflexivity.
  Qed.

  Lemma subst_split_bw: forall (m m1 m2 M : map) (R : map -> Prop),
      map.split m m1 m2 ->
      sep (sep (eq m1) (eq m2)) R M ->
      sep (eq m) R M.
  Proof.
    unfold sep, map.split. intros. simp. eauto 10.
  Qed.

  Lemma eq_sep_to_split: forall (m m1: map) P,
      (eq m1 * P)%sep m ->
      exists m2, map.split m m1 m2 /\ P m2.
  Proof. unfold sep. intros. simp. eauto. Qed.

  Lemma sep_put_iff: forall (m: map) P R k v_old v_new,
      (ptsto k v_old * R)%sep m ->
      iff1 P (ptsto k v_new * R)%sep ->
      P (map.put m k v_new).
  Proof.
    intros.
    eapply sep_put in H.
    seprewrite H0.
    ecancel_assumption.
  Qed.

  Lemma sep_eq_put: forall (m1 m: map) P x v,
      (eq m1 * P)%sep m ->
      (forall m' w, P m' -> map.get m' x = Some w -> False) ->
      (eq (map.put m1 x v) * P)%sep (map.put m x v).
  Proof.
    intros. unfold sep, map.split in *. simp.
    exists (map.put mp x v), mq.
    specialize H0 with (1 := Hp2).
    repeat split; trivial.
    - apply map.map_ext.
      intro y.
      rewrite map.get_put_dec.
      rewrite ?map.get_putmany_dec.
      destr (map.get mq y).
      + destruct_one_match.
        * subst. exfalso. eauto.
        * reflexivity.
      + destruct_one_match.
        * subst. rewrite map.get_put_same. reflexivity.
        * rewrite map.get_put_diff by congruence. reflexivity.
    - unfold map.disjoint in *. intros.
      rewrite map.get_put_dec in H. destruct_one_match_hyp.
      + subst. eauto.
      + eauto.
  Qed.

  Lemma grow_eq_sep: forall (M M' m mAdd: map) (R: map -> Prop),
      (eq m * R)%sep M ->
      map.split M' M mAdd ->
      (eq (map.putmany m mAdd) * R)%sep M'.
  Proof.
    intros. apply sep_comm. apply sep_comm in H.
    unfold sep, map.split in *. simp.
    do 2 eexists. ssplit. 4: reflexivity. 3: eassumption.
    - symmetry. apply map.putmany_assoc.
    - unfold map.disjoint in *. intros. rewrite map.get_putmany_dec in H0.
      destruct_one_match_hyp.
      + simp. eapply H0p1. 2: eassumption. rewrite map.get_putmany_dec.
        rewrite H. instantiate (1 := ltac:(destruct(map.get mq k))).
        destruct (map.get mq k); reflexivity.
      + eauto.
  Qed.

  Lemma join_sep: forall (m m1 m2: map) (P P1 P2: map -> Prop),
      map.split m m1 m2 ->
      P1 m1->
      P2 m2 ->
      iff1 (P1 * P2)%sep P ->
      P m.
  Proof.
    unfold sep, map.split. intros. simp. eapply H2. eauto 10.
  Qed.

  Lemma sep_def: forall {m: map} {P Q: map -> Prop},
      (P * Q)%sep m ->
      exists m1 m2, map.split m m1 m2 /\ P m1 /\ Q m2.
  Proof. unfold sep. intros *. apply id. Qed.

  Lemma sep_eq_empty_l: forall (R: map -> Prop), (eq map.empty * R)%sep = R.
  Proof.
    intros. eapply iff1ToEq.
    unfold iff1, sep, map.split. split; intros.
    - destruct H as (? & ? & (? & ?) & ? & ?). subst. rewrite map.putmany_empty_l. assumption.
    - pose map.putmany_empty_l; pose map.disjoint_empty_l; eauto 10.
  Qed.

  Lemma sep_eq_empty_r: forall (R: map -> Prop), (R * eq map.empty)%sep = R.
  Proof.
    intros. eapply iff1ToEq.
    unfold iff1, sep, map.split. split; intros.
    - destruct H as (? & ? & (? & ?) & ? & ?). subst. rewrite map.putmany_empty_r. assumption.
    - pose map.putmany_empty_r; pose map.disjoint_empty_r; eauto 10.
  Qed.

  Lemma get_in_sep: forall (lSmaller l: map) k v R,
      map.get lSmaller k = Some v ->
      (eq lSmaller * R)%sep l ->
      map.get l k = Some v.
  Proof.
    intros. eapply sep_comm in H0.
    unfold sep, map.split in H0. simp.
    eapply map.get_putmany_right.
    assumption.
  Qed.

  Lemma eq_put_to_sep: forall (m: map) k v,
      map.get m k = None ->
      eq (map.put m k v) = sep (eq m) (ptsto k v).
    intros. eapply iff1ToEq.
    unfold iff1, ptsto, sep, map.split. split; intros.
    - subst. exists m, (map.put map.empty k v). ssplit; try reflexivity.
      + apply map.map_ext. intros.
        rewrite map.get_put_dec, map.get_putmany_dec, map.get_put_dec, map.get_empty.
        destr (key_eqb k k0); reflexivity.
      + unfold map.disjoint. intros. rewrite map.get_put_dec in H1.
        rewrite map.get_empty in H1. destr (key_eqb k k0); congruence.
    - destruct H0 as (? & ? & (? & ?) & ? & ?).  subst.
      apply map.map_ext. intros.
      rewrite map.get_put_dec, map.get_putmany_dec, map.get_put_dec, map.get_empty.
      destr (key_eqb k k0); reflexivity.
  Qed.

  Lemma ptsto_no_aliasing: forall l (Q: map -> Prop) R k v1 v2,
      Q l ->
      iff1 Q (ptsto k v1 * ptsto k v2 * R)%sep ->
      False.
  Proof.
    intros. seprewrite_in H0 H. apply sep_emp_r in H. apply proj1 in H.
    unfold sep, map.split, ptsto, map.disjoint in H.
    decompose [Logic.and ex] H. clear H. subst.
    specialize (H7 k). rewrite ?map.get_put_same in H7. eauto.
  Qed.

  Lemma get_Some_to_ptsto: forall k v (m: map),
      map.get m k = Some v ->
      eq m = (eq (map.remove m k) * ptsto k v)%sep.
  Proof.
    intros. extensionality l. eapply propositional_extensionality.
    unfold sep, map.split.
    split; intros.
    - subst. do 2 eexists. ssplit; try reflexivity.
      + apply map.map_ext. intros.
        rewrite map.get_putmany_dec, map.get_put_dec, map.get_remove_dec, map.get_empty.
        destr (key_eqb k k0); congruence.
      + unfold map.disjoint. intros.
        rewrite map.get_remove_dec in H0. rewrite map.get_put_dec, map.get_empty in H1.
        destr (key_eqb k k0); congruence.
    - unfold ptsto in H0. decompose [Logic.and ex] H0. subst.
      apply map.map_ext. intros.
        rewrite map.get_putmany_dec, map.get_put_dec, map.get_remove_dec, map.get_empty.
        destr (key_eqb k k0); congruence.
  Qed.

  Lemma sep_ptsto_to_get_None: forall k v m (R: map -> Prop) l,
      (eq m * ptsto k v * R)%sep l ->
      map.get m k = None.
  Proof.
    intros. destr (map.get m k); [exfalso|reflexivity].
    erewrite get_Some_to_ptsto in H by eassumption.
    eapply ptsto_no_aliasing. 1: exact H. ecancel.
  Qed.

  Lemma ptsto_unique: forall k v0 v1 (R1 R2: map -> Prop) l,
      (ptsto k v0 * R1)%sep l ->
      (ptsto k v1 * R2)%sep l ->
      v0 = v1.
  Proof.
    intros. apply sep_comm in H. apply sep_comm in H0.
    unfold sep, map.split, ptsto in *.
    decompose [Logic.and ex] H. decompose [Logic.and ex] H0. subst.
    apply (f_equal (fun m => map.get m k)) in H6.
    rewrite ?map.get_putmany_dec, ?map.get_put_same in H6.
    congruence.
  Qed.

  Lemma sep_eq_to_disjoint: forall m1 m2 (R: map -> Prop) l,
      (eq m1 * eq m2 * R)%sep l ->
      map.disjoint m1 m2.
  Proof.
    unfold sep, map.split. intros. decompose [Logic.and ex] H. subst. assumption.
  Qed.
End MoreSepLog.

(* This can be overridden by the user.
   The idea of "addr" is that if the addresses of two sepclauses are the same,
   we're sure that these two clauses should be matched & canceled with each other,
   even if they still contain many evars outside of their address.
   "addr" should return a Gallina term of type "word" *)
Ltac addr P ::=
  let __ := lazymatch type of P with
            | @map.rep _ _ _ -> Prop => idtac
            | _ => fail 10000 P "is not a sep clause"
            end in
  lazymatch P with
  | ptsto ?A _ => A
  | ptsto_word ?A _ => A
  | ptsto_instr _ ?A _ => A
  | array _ _ ?A _ => A
  | word_array ?A _ => A
  | _ => fail "no recognizable address"
  end.

#[export] Hint Unfold program word_array: unf_to_array.

Require Export bedrock2.footpr.
