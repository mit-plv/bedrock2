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
Require Export bedrock2.ptsto_bytes.
Require Export coqutil.Word.SimplWordExpr.
Require Export bedrock2.SepLogAddrArith.
Require Import coqutil.Tactics.Simp.
Require Export riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
Require Import riscv.Spec.Decode.

Declare Scope sep_scope.

Infix "*" := sep : sep_scope.

Delimit Scope sep_scope with sep.
Arguments impl1 {T} (_)%sep (_)%sep.
Arguments iff1 {T} (_)%sep (_)%sep.

(* TODO does not get rid of %sep in printing as intended *)
Arguments sep {key} {value} {map} (_)%sep (_)%sep.

Section ptstos.
  Context {W: Words}.
  Context {mem : map.map word byte} {mem_ok: map.ok mem}.
  Context (iset: InstructionSet).

  Definition bytes_per_word: Z := Memory.bytes_per_word width.

  Definition word_array: word -> list word -> mem -> Prop :=
    array ptsto_word (word.of_Z bytes_per_word).

  (* we use InvalidInstruction to put data into the instruction memory, so we have
     to allow them, but make sure that they can be represented with 32 bits *)
  Definition valid_InvalidInstruction(instr: Instruction): Prop :=
    exists n, 0 <= n < 2 ^ 32 /\ instr = InvalidInstruction n.

  (* contains all the conditions needed to successfully execute instr, except
     that addr needs to be in the set of executable addresses, which is dealt with elsewhere *)
  Definition ptsto_instr(addr: word)(instr: Instruction): mem -> Prop :=
    (truncated_scalar Syntax.access_size.four addr (encode instr) *
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
       HList.tuple.to_list (LittleEndian.split (Z.to_nat bytes_per_word) (word.unsigned x)))
          bs)).
  Proof.
    revert addr; induction bs; intros; [reflexivity|].
    cbn [array flat_map].
    etransitivity. 1:eapply Proper_sep_iff1; [reflexivity|]. 1:eapply IHbs.
    etransitivity. 2:symmetry; eapply bytearray_append.
    eapply Proper_sep_iff1.
    { reflexivity. }
    assert (0 < bytes_per_word). { (* TODO: deduplicate *)
      unfold bytes_per_word; simpl; destruct width_cases as [EE | EE]; rewrite EE; cbv; trivial.
    }
    Morphisms.f_equiv.
    Morphisms.f_equiv.
    Morphisms.f_equiv.
    simpl.
    rewrite HList.tuple.length_to_list.
    rewrite Z2Nat.id; blia.
  Qed.

  Lemma putmany_of_footprint_None: forall n (vs: HList.tuple byte n) (addr: word) (z: Z) (m: mem),
      0 < z ->
      z + Z.of_nat n <= 2 ^ width ->
      map.get m addr = None ->
      map.get (map.putmany_of_tuple (Memory.footprint (word.add addr (word.of_Z z)) n) vs m)
              addr = None.
  Proof.
    induction n; intros.
    - simpl. assumption.
    - destruct vs as [v vs]. simpl.
      assert (2 ^ width > 0) as Gz. {
        destruct width_cases as [E | E]; rewrite E; reflexivity.
      }
      rewrite map.get_put_diff; cycle 1. {
        clear -H H0 Gz. intro C.
        apply (f_equal word.unsigned) in C.
        rewrite word.unsigned_add in C. unfold word.wrap in C.
        rewrite word.unsigned_of_Z in C. unfold word.wrap in C.
        pose proof (word.unsigned_range addr) as R.
        remember (word.unsigned addr) as w.
        rewrite Z.add_mod_idemp_r in C by blia.
        rewrite Z.mod_eq in C by blia.
        assert (z = 2 ^ width * ((w + z) / 2 ^ width)) by blia.
        remember ((w + z) / 2 ^ width) as k.
        assert (k < 0 \/ k = 0 \/ 0 < k) as D by blia. destruct D as [D | [D | D]]; Lia.nia.
      }
      rewrite <- word.add_assoc.
      replace ((word.add (word.of_Z (word := @word W) z) (word.of_Z 1)))
        with (word.of_Z (word := @word W) (z + 1)); cycle 1. {
        apply word.unsigned_inj.
        rewrite word.unsigned_add.
        rewrite! word.unsigned_of_Z.
        apply Z.add_mod.
        destruct width_cases as [E | E]; rewrite E; cbv; discriminate.
      }
      eapply IHn; try blia; assumption.
  Qed.

  Lemma putmany_of_footprint_None'': forall n (vs: HList.tuple byte n) (a1 a2: word) (m: mem),
      0 < word.unsigned (word.sub a1 a2) ->
      word.unsigned (word.sub a1 a2) + Z.of_nat n <= 2 ^ width ->
      map.get m a2 = None ->
      map.get (map.putmany_of_tuple (Memory.footprint a1 n) vs m) a2 = None.
  Proof.
    intros.
    pose proof putmany_of_footprint_None as P.
    specialize P with (1 := H) (2 := H0) (3 := H1).
    specialize (P vs).
    replace (word.add a2 (word.of_Z (word.unsigned (word.sub a1 a2)))) with a1 in P; [exact P|].
    apply word.unsigned_inj.
    rewrite word.unsigned_add. unfold word.wrap.
    rewrite word.of_Z_unsigned.
    rewrite word.unsigned_sub. unfold word.wrap.
    rewrite Z.add_mod_idemp_r by (destruct width_cases as [E | E]; rewrite E; cbv; discriminate).
    rewrite <- (word.of_Z_unsigned a1) at 1.
    rewrite word.unsigned_of_Z. unfold word.wrap.
    f_equal.
    blia.
  Qed.

  Lemma putmany_of_footprint_None': forall n (vs: HList.tuple byte n) (a1 a2: word) (m: mem),
      a1 <> a2 ->
      word.unsigned (word.sub a1 a2) + Z.of_nat n <= 2 ^ width ->
      map.get m a2 = None ->
      map.get (map.putmany_of_tuple (Memory.footprint a1 n) vs m) a2 = None.
  Proof.
    intros.
    apply putmany_of_footprint_None''; try assumption.
    pose proof (word.unsigned_range (word.sub a1 a2)).
    assert (word.unsigned (word.sub a1 a2) = 0 \/ 0 < word.unsigned (word.sub a1 a2)) as C
        by blia. destruct C as [C | C].
    - exfalso. apply H.
      rewrite word.unsigned_sub in C.
      apply word.unsigned_inj.
      apply Z.div_exact in C; [|(destruct width_cases as [E | E]; rewrite E; cbv; discriminate)].
      remember ((word.unsigned a1 - word.unsigned a2) / 2 ^ width) as k.
      pose proof (word.unsigned_range a1).
      pose proof (word.unsigned_range a2).
      assert (k < 0 \/ k = 0 \/ 0 < k) as D by blia. destruct D as [D | [D | D]]; try Lia.nia.
      (* LIABUG if primitive projections are on, we need this:
      rewrite D in C.
      rewrite Z.mul_0_r in C.
      blia.
      *)
    - assumption.
  Qed.

  Lemma byte_list_to_word_list_array {word_ok: word.ok word}: forall bytes,
    Z.of_nat (length bytes) mod bytes_per_word = 0 ->
    exists word_list : list word,
      Z.of_nat (Datatypes.length word_list) =
      Z.of_nat (Datatypes.length bytes) / bytes_per_word /\
    forall p,
      iff1 (array ptsto (word.of_Z 1) p bytes)
           (array ptsto_word (word.of_Z bytes_per_word) p word_list).
  Proof.
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
    revert dependent bytes.
    pattern q.
    refine (natlike_ind _ _ _ q H); clear -word_ok mem_ok; intros.
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
    unfold ptsto_word, truncated_word, truncated_scalar, littleendian.

    rewrite <-bytearray_index_merge.
    1: eapply Proper_sep_iff1; [|reflexivity].
    2: rewrite word.unsigned_of_Z; setoid_rewrite Z.mod_small.
    3: {
      unfold bytes_per_word.
      simpl.
      destruct width_cases as [E | E]; rewrite E; cbv; intuition discriminate.
    }
    2: rewrite List.length_firstn_inbounds; Lia.nia.
    cbv [ptsto_bytes.ptsto_bytes].
    Morphisms.f_equiv.
    setoid_rewrite word.unsigned_of_Z.
    setoid_rewrite Z.mod_small.
    1: unshelve setoid_rewrite LittleEndian.split_combine.
    1: {
      eapply eq_rect; [exact (HList.tuple.of_list (List.firstn (Z.to_nat bytes_per_word) bytes))|].
      abstract (rewrite List.length_firstn_inbounds; try Lia.nia; reflexivity). }
    1:rewrite HList.tuple.to_list_eq_rect.
    1:rewrite HList.tuple.to_list_of_list; trivial.
    match goal with |- context[LittleEndian.combine _ ?xs] => generalize xs end.
    intros.
    pose proof (LittleEndian.combine_bound t).
    split; [blia|].
    destruct H0.
    eapply Z.lt_le_trans. 1: eassumption.
    eapply Z.pow_le_mono_r. 1: reflexivity.
    simpl.
    destruct width_cases as [E | E]; rewrite E; cbv; intuition discriminate.
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

  Lemma sep_inline_eq: forall (A R: mem -> Prop) m1,
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

End ptstos.

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
  | ptsto_bytes _ ?A _ => A
  | ptsto_word ?A _ => A
  | ptsto_instr _ ?A _ => A
  | array _ _ ?A _ => A
  | word_array ?A _ => A
  | _ => fail "no recognizable address"
  end.

Hint Unfold program word_array: unf_to_array.

Require Export bedrock2.footpr.
