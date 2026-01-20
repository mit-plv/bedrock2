Require Import ZArith Psatz List.
Require Import bedrock2.NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Spec only. *)
(*
Definition csel :=
  func! (c, a, b) ~> r {
    if c {
      r = a
    } else {
      r = b
    }
  }.
*)

(* Spec only. *)
(*
Definition ctime_lt :=
  func! (a, b) ~> r {
    r = (a - b - $1) >> $63
  }.
*)

Definition index_bits :=
  func! (p_input, nbits, i, w) ~> r {
    idx = i >> $3; (* index = i/8 *)
    a = load1(p_input + idx);
    b = $0;
    if idx + $1 < (nbits + $7) >> $3 {
      b = load1(p_input + idx + $1)
    };
    s = a + (b << $8);
    t = s >> (i & $7); (* offset = i%8 *)
    r = t & (($1 << w) - $1)
  }.

(* Word size (nonzero). *)
Definition w := 5.

Definition words_unpack :=
  func! (p_input, p_output, nbits) {
    i = $0;
    while i < nbits {
      unpack! r = index_bits(p_input, nbits, i, $w);
      store1(p_output, r); p_output = p_output + $1;
      i = i + $w;
      $(cmd.unset "r")
    }
  }.

Definition recode :=
  func! (words, ci, n) ~> ci {
      while n {
        x = load1(words) + ci;
        unpack! ci = ctime_lt($(2^(w - 1)), x);
        unpack! x = csel(ci, x - $(2^w), x);
        store1(words, x); words = words + $1;
        n = n - $1;
        $(cmd.unset "x")
      }
    }.

Definition recode_wrap :=
  func! (words, n) {
    unpack! _c = recode(words, $0, n)
  }.

From bedrock2 Require Import WeakestPrecondition ProgramLogic.
From bedrock2 Require Import Map.SeparationLogic Array Scalars.
From coqutil Require Import Byte Word.Naive Word.Interface Word.LittleEndianList.

Module byte.
Definition swrap : Z -> Z := word.swrap (word := word8).
Definition signed (b : byte) : Z := swrap (byte.unsigned b).
End byte.

Require Import bedrock2.BasicC64Semantics.

(* TODO: csel should constrain the input to a single bit. *)
Local Instance spec_of_csel : spec_of "csel" :=
  fnspec! "csel" c a b ~> r,
  { requires t m := True;
    ensures T M :=
      M = m /\ T = t /\
      r = if word.unsigned c =? 0 then b else a
  }.

Local Instance spec_of_ctime_lt : spec_of "ctime_lt" :=
  fnspec! "ctime_lt" a b ~> r,
  { requires t m := True;
    ensures T M :=
      M = m /\ T = t /\
      r = if word.unsigned a <? word.unsigned b then word.of_Z 1 else word.of_Z 0
  }.

Import ProgramLogic.Coercions.
Set Printing Coercions.

Definition positional B : list Z -> Z :=
  fold_right (fun a s => a + B*s) 0.

Lemma positional_map_cons {T} (f : T -> Z) B h t :
  positional B ((f h) :: (map f t)) = f h + B*(positional B (map f t)).
Proof. constructor. Qed.

Lemma positional_cons B h t :
  positional B (h :: t) = h + B*(positional B t).
Proof. constructor. Qed.

Lemma positional_nil B :
  positional B nil = 0.
Proof. reflexivity. Qed.

Definition positional_words B (l : list word) : Z :=
  positional B (map word.unsigned l).

Definition positional_signed_words B (l : list word) : Z :=
  positional B (map word.signed l).

Definition positional_bytes B (l : list byte) : Z :=
  positional B (map byte.unsigned l).

Definition positional_signed_bytes B (l : list byte) : Z :=
  positional B (map byte.signed l).

Lemma positional_bytes_cons B (h : byte) (t : list byte) :
  positional_bytes B (h :: t) = byte.unsigned h + B*(positional_bytes B t).
Proof. constructor. Qed.

Local Notation bytearray := (Array.array ptsto (word.of_Z 1)).

Local Instance spec_of_index_bits : spec_of "index_bits" :=
  fnspec! "index_bits" (p_input nbits i w : word) / input ~> r,
    { requires t m :=
        m =*> bytearray p_input input /\
        8 * (length input - 1) < nbits <= 8 * length input /\
        le_combine input < 2^nbits /\
        i < nbits /\
        0 <= w <= 8 /\
        nbits + 7 <= (word.of_Z (-1) : word);
      ensures T M :=
        M = m /\
        T = t /\
        r = le_combine input / 2^i mod 2^w :>Z
    }.

Local Instance spec_of_words_unpack : spec_of "words_unpack" :=
  fnspec! "words_unpack" (p_input p_output nbits : word) / input output R,
    { requires t m :=
        m =* bytearray p_input input * bytearray p_output output * R /\
        8 * (length input - 1) < nbits <= 8 * length input /\
        w * (length output - 1) < nbits <= w * length output /\
        le_combine input < 2^nbits /\
        nbits + 7 <= (word.of_Z (-1) : word);
      ensures T M := exists OUTPUT,
        M =* bytearray p_input input * bytearray p_output OUTPUT * R /\
        length output = length OUTPUT /\
        T = t /\
        Forall (fun b => (0 <= byte.unsigned b < 2^w)) OUTPUT /\
        le_combine input = positional_bytes (2^w) OUTPUT
    }.

Local Instance spec_of_recode : spec_of "recode" :=
  fnspec! "recode" (p_words ci n : word) / words R ~> CO,
    { requires t m :=
        m =* bytearray p_words words * R /\ length words = word.unsigned n :>Z /\
        Forall (fun b => (0 <= byte.unsigned b < 2^w)) words /\ 0 <= ci <= 1;
      ensures T M := exists WORDS,
        M =* bytearray p_words WORDS * R /\ length WORDS = word.unsigned n :>Z /\
        T = t /\ (* We have WORDS, CARRY_OUT = recode(words, carry_in) *)
        positional_signed_bytes (2^w) WORDS + 2^(w*n)*CO = word.unsigned ci + positional_bytes (2^w) words /\
        Forall (fun b => (-2^w + 2 <= 2*(byte.signed b) <= 2^w)) WORDS /\ 0 <= CO <= 1
    }.

Local Instance spec_of_recode_wrap : spec_of "recode_wrap" :=
  fnspec! "recode_wrap" (p_words n : word) / words R,
  { requires t m :=
      m =* bytearray p_words words * R /\ length words = word.unsigned n :>Z /\
      Forall (fun b => (0 <= byte.unsigned b < 2^w)) words /\
      2 * (positional_bytes (2^w) words) < 2^(w*n) /\
      -2^(w*n) <= positional (2^w) (repeat (-2^w + 2) (Z.to_nat n));
    ensures T M := exists WORDS,
      M =* bytearray p_words WORDS * R /\ length WORDS = word.unsigned n :>Z /\
      T = t /\
      positional_signed_bytes (2^w) WORDS = positional_bytes (2^w) words /\
      Forall (fun b => (-2^w + 2 <= 2*(byte.signed b) <= 2^w)) WORDS
  }.

Require Import bedrock2.ZnWords Coq.ZArith.ZArith Lia.
From coqutil Require Import Tactics.Tactics Word.Properties Datatypes.List.

Lemma bytearray_load_of_sep addr (addr' : word) n (values : list byte) R m
  (Hsep : (sep (bytearray addr values) R m))
  (_ : addr' = (word.add addr (word.of_Z (Z.of_nat n))))
  (_ : (n < length values)%nat) :
  Memory.load access_size.one m addr' =
  Some (word.of_Z (byte.unsigned (nth_default Byte.x00 values n))).
Proof.
  rewrite nth_default_eq.
  rewrite <-(firstn_nth_skipn _ _ values Byte.x00 H0) in Hsep.
  do 2 seprewrite_in @bytearray_append Hsep.
  seprewrite_in @array_cons Hsep.
  seprewrite_in @array_nil Hsep.
  rewrite length_firstn, min_l, <-H in Hsep by lia.
  eapply load_one_of_sep.
  ecancel_assumption.
Qed.

Lemma bytearray_load_of_sep' (addr addr': word) (values : list byte) R m :
  (sep (bytearray addr values) R m) ->
  let offset := word.unsigned (word.sub addr' addr) in
    (let n := Z.to_nat offset in (n < length values)%nat ->
    Memory.load access_size.one m addr' =
    Some (word.of_Z (byte.unsigned (nth_default Byte.x00 values n)))).
Proof.
  intros.
  eapply bytearray_load_of_sep; eauto.
  subst offset n.
  rewrite Z2Nat.id by apply word.unsigned_range.
  rewrite word.of_Z_unsigned.
  ring.
Qed.

Ltac bitwise_setup k :=
  apply Z.bits_inj'; intros k **;
  repeat rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.shiftl_spec, ?Z.testbit_mod_pow2, ?bitblast.Z.div_pow2_bits' by ZnWords.

Ltac bitwise_solve solver :=
  repeat match goal with |- context _g[Z.ltb ?a ?b] => progress (
    case (Z.ltb_spec a b) as [];
    repeat rewrite ?Bool.andb_true_l, ?Bool.andb_true_r, ?Bool.andb_false_l, ?Bool.andb_false_r,
                   ?Bool.orb_true_l, ?Bool.orb_true_r, ?Bool.orb_false_l, ?Bool.orb_false_r;
    try solve [solver])
  end.

Lemma index_bits_ok : program_logic_goal_for_function! index_bits.
Proof.
  repeat (straightline || apply WeakestPreconditionProperties.dexpr_expr).
  (* First byte load. *)
  eexists _.
  split.
  {
    eapply bytearray_load_of_sep'; eauto.
    ZnWords.
  }
  repeat straightline.
  (* Second byte load. *)
  eexists _.
  split.
  { repeat straightline. }
  split; intro cond; repeat (straightline || apply WeakestPreconditionProperties.dexpr_expr).
  {
    eexists _.
    split.
    {
      eapply bytearray_load_of_sep'; eauto.
      revert cond.
      case word.ltu_spec; intros; ZnWords.
    }

    repeat straightline.

    subst r t s v b.
    (* Subtraction in address computation. *)
    rewrite <-word.add_assoc, !word.word_sub_add_l_same_l.

    repeat rewrite ?word.unsigned_and_nowrap, ?word.unsigned_sru, ?word.unsigned_add, ?word.unsigned_sub, ?word.unsigned_slu; try ZnWords.
    {
      rewrite !word.unsigned_of_Z.
      cbv [word.wrap].

      rewrite (Z.mod_small 1) by lia.

      change (7 mod 2^64) with (Z.ones 3).
      rewrite Z.land_ones by lia.

      set (nth_default Byte.x00 input (Z.to_nat (word.unsigned idx))) as b1.
      set (nth_default Byte.x00 input (Z.to_nat ((word.unsigned idx + 1) mod 2 ^ 64))) as b2.

      assert (1 <= 2^w0 <= 2^8) by (split; [ZnWords | apply Z.pow_le_mono_r; lia]).

      assert ((Z.shiftl 1 (word.unsigned w0) mod 2 ^ 64 - 1) mod 2 ^ 64 = Z.ones (word.unsigned w0)) as ->.
      {
        rewrite Z.shiftl_1_l.
        (rewrite_strat (bottomup Z.mod_small)); try lia.
        rewrite Z.ones_equiv, Z.sub_1_r.
        reflexivity.
      }

      set (word.unsigned i mod 2 ^ 3).
      set ((le_combine input / 2 ^ word.unsigned i) mod 2 ^ word.unsigned w0).

      pose proof byte.unsigned_range b1.
      pose proof byte.unsigned_range b2.
      (rewrite_strat (bottomup Z.mod_small)); rewrite ?Z.shiftr_div_pow2; try ZnWords.
      {
        rewrite Z.land_ones by ZnWords.

        rewrite Z.shiftl_mul_pow2 by lia.

        epose proof nth_default_le_split
          (Z.to_nat (word.unsigned idx))
          (length input) (le_combine input)
          ltac:(ZnWords) Byte.x00 as Hb1.
        rewrite split_le_combine in Hb1.
        subst b1.
        rewrite Hb1.
        clear Hb1.

        revert cond.
        case word.ltu_spec;
        repeat rewrite ?word.unsigned_add, ?word.unsigned_and, ?word.unsigned_sru, ?word.unsigned_of_Z_1, ?word.unsigned_of_Z_0 by ZnWords;
        intros Hcond **; try lia.
        unfold word.wrap in Hcond.
        repeat rewrite word.unsigned_of_Z_nowrap in Hcond by lia.

        epose proof nth_default_le_split
          (Z.to_nat ((word.unsigned idx + 1) mod 2 ^ 64))
          (length input) (le_combine input)
          ltac:(ZnWords) Byte.x00 as Hb2.
        rewrite split_le_combine in Hb2.
        subst b2.
        rewrite Hb2.
        clear Hb2.
        assert ((word.unsigned idx + 1) mod 2 ^ 64 = word.unsigned idx + 1) as -> by ZnWords.

        rewrite !Z2Nat.id by ZnWords.
        rewrite !byte.unsigned_of_Z.
        rewrite !Z.shiftr_div_pow2 by ZnWords.

        unfold byte.wrap.

        subst z0 z.
        set (le_combine input).

        assert(
          (z / 2 ^ (8 * word.unsigned idx)) mod 2 ^ 8 + (z / 2 ^ (8 * (word.unsigned idx + 1))) mod 2 ^ 8 * 2 ^ 8 =
          z / 2 ^ (8 * word.unsigned idx) mod 2 ^ 16
        ) as ->.
        {
          rewrite <-Z.shiftl_mul_pow2 by lia.
          rewrite <-bitblast.Z.or_to_plus.

          {
            bitwise_setup k.
            bitwise_solve ltac:(
              (reflexivity) ||
              (lia) ||
              (assert (k - 8 + 8 * (word.unsigned idx + 1) = k + 8 * word.unsigned idx) as -> by ZnWords;
              rewrite <-?Z.lor_spec, ?Z.lor_diag;
              reflexivity)
            ).
          }
          bitwise_setup k.
          bitwise_solve ltac:(
            (lia) ||
            (rewrite Z.testbit_0_l; reflexivity)
          ).
        }

        assert (word.unsigned idx = i / 2 ^ 3) as -> by ZnWords.

        assert (z = z mod 2^nbits) as ->.
        {
          rewrite Z.mod_small; trivial.
          pose proof le_combine_bound input.
          ZnWords.
        }

        bitwise_setup k.
        assert (k + i mod 2 ^ 3 + 8 * (i / 2 ^ 3) = k + i) as -> by ZnWords.
        bitwise_solve ltac:(
          (reflexivity) ||
          (Z.to_euclidean_division_equations; nia) ||
          (lia)
        ).
      }
      rewrite Z.shiftl_mul_pow2 by lia.
      Z.to_euclidean_division_equations; nia.
    }
    rewrite word.unsigned_of_Z_nowrap by lia.
    change (7) with (Z.ones 3).
    rewrite Z.land_ones by lia.
    ZnWords.
  }

  subst r t s b.
  (* Subtraction in address computation. *)
  rewrite word.word_sub_add_l_same_l.

  repeat rewrite ?word.unsigned_and_nowrap, ?word.unsigned_sru, ?word.unsigned_add, ?word.unsigned_sub, ?word.unsigned_slu; try ZnWords.
  {
    rewrite !word.unsigned_of_Z.
    cbv [word.wrap].

    rewrite (Z.mod_small 0), (Z.mod_small 1) by lia.
    rewrite Z.add_0_r, Zmod_mod.

    change (7 mod 2^64) with (Z.ones 3).
    rewrite Z.land_ones by lia.

    set (nth_default Byte.x00 input (Z.to_nat (word.unsigned idx))) as b.

    assert (1 <= 2^w0 <= 2^8) by (split; [ZnWords | apply Z.pow_le_mono_r; lia]).

    assert ((Z.shiftl 1 (word.unsigned w0) mod 2 ^ 64 - 1) mod 2 ^ 64 = Z.ones (word.unsigned w0)) as ->.
    {
      rewrite Z.shiftl_1_l.
      (rewrite_strat (bottomup Z.mod_small)); try lia.
      rewrite Z.ones_equiv, Z.sub_1_r.
      reflexivity.
    }

    set (word.unsigned i mod 2 ^ 3).
    set ((le_combine input / 2 ^ word.unsigned i) mod 2 ^ word.unsigned w0).

    pose proof byte.unsigned_range b.
    (rewrite_strat (bottomup Z.mod_small)); rewrite ?Z.shiftr_div_pow2; try ZnWords.
    {
      rewrite Z.land_ones by ZnWords.

      epose proof nth_default_le_split
        (Z.to_nat (word.unsigned idx))
        (length input) (le_combine input)
        ltac:(ZnWords) Byte.x00 as Hb.
      rewrite split_le_combine in Hb.
      subst b.
      rewrite Hb.
      clear Hb.

      rewrite Z2Nat.id by ZnWords.
      rewrite byte.unsigned_of_Z.
      rewrite Z.shiftr_div_pow2 by ZnWords.

      unfold byte.wrap.

      subst z0 z.
      set (le_combine input).

      assert (word.unsigned idx = i / 2 ^ 3) as -> by ZnWords.

      revert cond.
      case word.ltu_spec;
      repeat rewrite ?word.unsigned_add, ?word.unsigned_and, ?word.unsigned_sru, ?word.unsigned_of_Z_1 by ZnWords;
      intros Hcond **; try lia.
      unfold word.wrap in Hcond.
      repeat rewrite word.unsigned_of_Z_nowrap in Hcond by lia.

      assert (z = z mod 2^nbits) as ->.
      {
        rewrite Z.mod_small; trivial.
        pose proof le_combine_bound input.
        ZnWords.
      }

      bitwise_setup k.
      assert (k + i mod 2 ^ 3 + 8 * (i / 2 ^ 3) = k + i) as -> by ZnWords.
      bitwise_solve ltac:(
        (reflexivity) ||
        (Z.to_euclidean_division_equations; nia) ||
        (exfalso; ZnWords)
      ).
    }
    {
      pose proof Z.mod_bound_pos i (2 ^ 3) ltac:(ZnWords) ltac:(lia).
      Z.to_euclidean_division_equations; nia.
    }
  }
  rewrite word.unsigned_of_Z_nowrap by lia.
  change (7) with (Z.ones 3).
  rewrite Z.land_ones by lia.
  ZnWords.
Qed.

Lemma unpack_ok : program_logic_goal_for_function! words_unpack.
Proof.
  repeat straightline.

  refine ((Loops.tailrec
    (* types of ghost variables*) (HList.polymorphic_list.cons _
                                  (HList.polymorphic_list.cons _ HList.polymorphic_list.nil))
    (* program variables *) (["p_input";"p_output";"nbits";"i"] : list String.string))
    (fun v output R t m p_input p_output nbits_ i => PrimitivePair.pair.mk (* precondition *)
      (v = word.unsigned i /\
      nbits_ = nbits /\ (* input = inside loop *)
      m =* bytearray p_input input * bytearray p_output output * R /\
      8 * (length input - 1) < nbits <= 8 * length input /\
      w * (length output - 1) < nbits - i <= w * length output /\
      le_combine input < 2^nbits /\
      nbits + w <= (word.of_Z (-1) : word))
    (fun           T M P_INPUT P_OUTPUT NBITS I => (* postcondition *)
      exists OUTPUT,
      M =* bytearray p_input input * bytearray p_output OUTPUT * R /\
      length output = length OUTPUT /\
      T = t /\
      p_input = P_INPUT /\
      nbits = NBITS /\ (* inside loop = output *)
      Forall (fun b => (0 <= byte.unsigned b < 2^w)) OUTPUT /\
      le_combine input / 2^i = positional_bytes (2^w) OUTPUT
      (* le_combine input = le_combine input mod 2^i + positional_bytes (2^w) OUTPUT *)
      ))
    (fun n m => m < n <= nbits + w) (* well_founded relation *)
    _ _ _ _ _ _ _);
  Loops.loop_simpl.

  { repeat straightline. }
  { eapply Z.gt_wf. }
  {
    repeat straightline.
    cbv [w] in *.
    ssplit; try ecancel_assumption; try ZnWords.
  }
  {
    repeat straightline; subst br; cbv [w] in *.
    {
      revert H7.
      case word.ltu_spec; intros;
      rewrite word.unsigned_of_Z_nowrap in H8 by ZnWords; try lia.

      straightline_call. (* call index_bits *)
      {
        repeat straightline.
        ssplit.
        {
          eexists _.
          ecancel_assumption.
        }
        { assumption. }
        { assumption. }
        { assumption. }
        { assumption. }
        { ZnWords. }
        { ZnWords. }
        { assumption. }
      }
      repeat straightline.

      clear dependent output; rename x into output.
      destruct output as [| out0 output_rest].
      {
        (* Empty list case. *)
        rewrite List.length_nil in *.
        lia.
      }

      cbn [bytearray] in * |-.
      repeat straightline.

      eexists _, _, _.
      repeat straightline.
      {
        cbn [length] in *.
        ssplit; try ecancel_assumption; try ZnWords.
      }

      split.
      {
        (* loop test *)
        ZnWords.
      }

      repeat straightline.
      eexists (_ :: _).
      ssplit.
      {
        cbn [bytearray].
        ecancel_assumption.
      }
      { rewrite !length_cons. ZnWords. }
      { reflexivity. }
      { reflexivity. }
      { reflexivity. }

      {
        (* Forall bound on output. *)
        apply Forall_cons.
        {
          rewrite H19.
          rewrite word.unsigned_of_Z_nowrap by ZnWords.
          rewrite byte.unsigned_of_Z.
          cbv [byte.wrap].
          rewrite Z.mod_small; ZnWords.
        }
        assumption.
      }

      rewrite positional_bytes_cons.
      rewrite <-H21, H19.
      subst i.

      rewrite word.unsigned_of_Z_nowrap by ZnWords.
      rewrite word.unsigned_add_nowrap by ZnWords.
      rewrite word.unsigned_of_Z_nowrap by ZnWords.

      rewrite byte.unsigned_of_Z.
      cbv [byte.wrap].
      rewrite Z.mod_small by ZnWords.

      rewrite Z.pow_add_r by ZnWords.
      rewrite <-Z.div_div by ZnWords.

      rewrite Z.add_comm.
      rewrite <-Z.div_mod by ZnWords.

      reflexivity.
    }
    (* base case *)
    eexists x.
    ssplit; try ecancel_assumption; auto;
    revert H7;
    case word.ltu_spec; intros;
    rewrite word.unsigned_of_Z_nowrap in H8 by ZnWords;
    try discriminate;
    assert (length x = 0%nat) by ZnWords;
    rewrite length_zero_iff_nil in *;
    subst x.
    { apply Forall_nil. }
    cbv [positional_bytes positional map fold_right].
    assert (2 ^ word.unsigned nbits <= 2 ^ word.unsigned x4) by (apply Z.pow_le_mono_r; ZnWords).
    assert (le_combine input < 2 ^ word.unsigned x4) by ZnWords.
    apply Z.div_small.
    split; [apply le_combine_bound | assumption].
  }
  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; auto.
  subst i.
  rewrite word.unsigned_of_Z_0, Z.pow_0_r, Z.div_1_r in H13.
  assumption.
Qed.

Require Import coqutil.Z.PushPullMod.

Lemma byte_swrap_wrap b : byte.swrap (byte.wrap b) = byte.swrap b.
Proof.
  cbv [byte.wrap byte.swrap word.swrap].
  Z.mod_equality.
Qed.

Lemma byte_wrap_word_wrap w : byte.wrap (word.wrap w) = byte.wrap w.
Proof.
  cbv [byte.wrap word.wrap].
  rewrite Z.mod_mod_divide; [|exists (2^56)]; reflexivity.
Qed.

Lemma byte_swrap_word_wrap w : byte.swrap (word.wrap w) = byte.swrap w.
Proof.
  rewrite <-byte_swrap_wrap, byte_wrap_word_wrap, byte_swrap_wrap; reflexivity.
Qed.

Lemma recode_ok : program_logic_goal_for_function! recode.
Proof.
  repeat straightline.

  refine ((Loops.tailrec
    (* types of ghost variables*) (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ HList.polymorphic_list.nil))
    (* program variables *) (["words";"ci";"n"] : list String.string))
    (fun v words R t m p_words ci n => PrimitivePair.pair.mk (* precondition *)
      (v = word.unsigned n /\
      m =* bytearray p_words words * R /\ length words = word.unsigned n :>Z /\
      Forall (fun b => (0 <= byte.unsigned b < 2^w)) words /\ 0 <= ci <= 1)
    (fun           T M P_WORDS (CO : word) N => T = t /\ (* postcondition *)
      exists WORDS,
      M =* bytearray p_words WORDS * R /\ length WORDS = word.unsigned n :>Z /\
      positional_signed_bytes (2^w) WORDS + 2^(w*n)*CO = word.unsigned ci + positional_bytes (2^w) words /\
      Forall (fun b => (-2^w + 2 <= 2*(byte.signed b) <= 2^w)) WORDS /\ 0 <= CO <= 1))
    (fun n m => 0 <= n < m) (* well_founded relation *)
    _ _ _ _ _ _ _);
  Loops.loop_simpl.

  { repeat straightline. }
  { eapply Z.lt_wf. }
  {
    repeat straightline.
    ssplit; try ecancel_assumption; try lia; trivial.
  }
  {
    repeat straightline.
    {
      clear dependent words; rename x into words.
      (* Take the first element from the word list. *)
      destruct words as [| w0 words_rest].
      { rewrite List.length_nil in *; lia. }
      {
        cbn [array] in * |-.
        repeat straightline.
        (* call ctime_lt *)
        straightline_call; trivial.
        repeat straightline.
        (* call csel *)
        straightline_call; trivial.
        repeat straightline.

        exists words_rest; eexists _; exists (v - 1).
        repeat straightline.
        {
          ssplit.
          { ZnWords. }
          { ecancel_assumption. }
          {
            subst n.
            rewrite word.unsigned_sub_nowrap;
            rewrite word.unsigned_of_Z_1;
            rewrite <-H8;
            rewrite List.length_cons;
            lia.
          }
          { inversion H9. assumption. }
          all: subst x; case Z.ltb_spec; ZnWords.
        }
        {
          split.
          { lia. }
          {
            repeat straightline.
            eexists (_ :: _).
            ssplit.
            {
              cbn [array].
              ecancel_assumption.
            }
            { rewrite length_cons; ZnWords. }
            {
              cbn [positional_signed_bytes positional_bytes positional map fold_right].
              cbv [x4 x].
              case Z.ltb_spec; intros; case Z.eqb_spec; intros; try ZnWords;
              revert H13; cbv[x positional_signed_bytes positional_bytes];
              case Z.ltb_spec; intros; try ZnWords;
              [
                rewrite word.unsigned_of_Z_1, (Z.add_comm 1), <-Z.sub_move_r in H17 |
                rewrite word.unsigned_of_Z_0, Z.add_0_l in H17
              ];
              rewrite <-H17; cbv[v0 w] in *;
              rewrite !Z.pow_mul_r by lia; change (Z.pow 2 5) with 32;
              apply Z.sub_move_0_r.

              (* TODO: ring_simplify stalls Qed so we so some manual simplifications. *)

              {
                assert (32 * (positional 32 (map byte.signed x8) + 32 ^ word.unsigned n * word.unsigned x6 - 1) =
                32 * positional 32 (map byte.signed x8) + 32 * 32 ^ word.unsigned n * word.unsigned x6 - 32) as -> by lia.
                set (32 * positional 32 (map byte.signed x8)) as cancel.
                assert (byte.signed (byte.of_Z (word.unsigned (word.sub (word.add (word.of_Z (byte.unsigned w0)) x2) (word.of_Z 32)))) + cancel + 32 ^ word.unsigned x3 * word.unsigned x6 - (word.unsigned x2 + (byte.unsigned w0 + (cancel + 32 * 32 ^ word.unsigned n * word.unsigned x6 - 32))) =
                byte.signed (byte.of_Z (word.unsigned (word.sub (word.add (word.of_Z (byte.unsigned w0)) x2) (word.of_Z 32)))) + 32 ^ word.unsigned x3 * word.unsigned x6 - 32 * word.unsigned x6 * 32 ^ word.unsigned n - word.unsigned x2 - byte.unsigned w0 + 32) as -> by lia.
                shelve.
              }

              {
                assert (32 * (positional 32 (map byte.signed x8) + 32 ^ word.unsigned n * word.unsigned x6) =
                32 * positional 32 (map byte.signed x8) + 32 * 32 ^ word.unsigned n * word.unsigned x6) as -> by lia.
                set (32 * positional 32 (map byte.signed x8)) as cancel.
                assert (byte.signed (byte.of_Z (word.unsigned (word.add (word.of_Z (byte.unsigned w0)) x2))) + cancel + 32 ^ word.unsigned x3 * word.unsigned x6 - (word.unsigned x2 + (byte.unsigned w0 + (cancel + 32 * 32 ^ word.unsigned n * word.unsigned x6))) =
                byte.signed (byte.of_Z (word.unsigned (word.add (word.of_Z (byte.unsigned w0)) x2))) + 32 ^ word.unsigned x3 * word.unsigned x6 - 32 * word.unsigned x6 * 32 ^ word.unsigned n - word.unsigned x2 - byte.unsigned w0) as -> by lia.
                shelve.
              }

              Unshelve.
              {
                set (word.of_Z (byte.unsigned w0)) as b0.
                assert (word.unsigned (word.sub (word.add b0 x2) (word.of_Z 32)) = word.wrap (b0 + x2 - 32)) as -> by ZnWords.

                cbv [byte.signed].
                rewrite byte.unsigned_of_Z, byte_swrap_wrap, byte_swrap_word_wrap.
                cbv [byte.swrap word.swrap].
                subst b0.
                rewrite word.unsigned_of_Z_nowrap by (pose proof byte.unsigned_range w0; lia).
                rewrite Z.mod_small by (inversion H9; ZnWords).

                ring_simplify.
                subst n.
                rewrite word.unsigned_sub_nowrap by ZnWords.
                rewrite <-H8; cbn [length]; rewrite ?Nat2Z.inj_succ, ?Z.pow_succ_r by lia.
                assert ((Z.succ (Z.of_nat (length words_rest)) - word.unsigned (word.of_Z 1)) = (Z.of_nat (length words_rest))) as -> by ZnWords.
                ZnWords.
              }
              {
                cbv [byte.signed].
                rewrite byte.unsigned_of_Z, byte_swrap_wrap.

                rewrite word.unsigned_add_nowrap.
                {
                  cbv [byte.swrap word.swrap].
                  rewrite Z.mod_small by (inversion H9; ZnWords).

                  ring_simplify.
                  subst n.
                  rewrite word.unsigned_sub_nowrap by ZnWords.
                  rewrite <-H8; cbn [length]; rewrite ?Nat2Z.inj_succ, ?Z.pow_succ_r by lia.
                  assert ((Z.succ (Z.of_nat (length words_rest)) - word.unsigned (word.of_Z 1)) = (Z.of_nat (length words_rest))) as -> by ZnWords.

                  rewrite word.unsigned_of_Z.
                  cbv [word.wrap].
                  rewrite Z.mod_small by (inversion H9; ZnWords).
                  ZnWords.
                }
                rewrite word.unsigned_of_Z.
                cbv [word.wrap].
                pose proof byte.unsigned_range w0.
                ZnWords.
              }
            }
            {
              constructor.
              {
                cbv [x4 x].
                case Z.ltb_spec; intros; case Z.eqb_spec; intros; try ZnWords; inversion H9; cbv [v0 w] in *;
                set (word.of_Z (byte.unsigned w0)) as b0;
                [
                  assert (word.unsigned (word.sub (word.add b0 x2) (word.of_Z 32)) = word.wrap (b0 + x2 - 32)) as -> by ZnWords |
                  assert (word.unsigned (word.add b0 x2) = word.wrap (b0 + x2)) as -> by ZnWords
                ];
                cbv [byte.signed];
                rewrite byte.unsigned_of_Z, byte_swrap_wrap, byte_swrap_word_wrap;
                cbv [byte.swrap word.swrap];
                subst b0;
                rewrite word.unsigned_of_Z_nowrap by (pose proof byte.unsigned_range w0; lia);
                rewrite Z.mod_small by lia;
                ZnWords.
              }
              assumption.
            }
            { assumption. }
            { assumption. }
          }
        }
      }
    }
    {
      (*base case*)
      assert (length x = 0%nat) by ZnWords.
      rewrite length_zero_iff_nil in *.
      subst x.
      eexists _.
      ssplit.
      { ecancel_assumption. }
      { assumption. }
      {
        cbn [positional_signed_bytes positional_bytes positional List.map fold_right].
        rewrite H6, Z.mul_0_r. ZnWords.
      }
      { apply Forall_nil. }
      { assumption. }
      { assumption. }
    }
  }
  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; auto.
Qed.
(* TODO: Print Assumptions recode_ok returns subproofs. *)

Lemma positional_bounded (l : list Z) L U :
  let n := length l in
  Forall (fun b => (L <= 2*b <= U)) l ->
  positional (2^w) (List.repeat L n) <= 2 * (positional (2^w) l) <= positional (2^w) (List.repeat U n).
Proof.
  induction 1.
  {
    subst n.
    rewrite length_nil, ?positional_nil.
    lia.
  }
  {
    subst n.
    rewrite length_cons, positional_cons.
    cbn [repeat].
    rewrite ?positional_cons.
    cbv [w] in *.
    lia.
  }
Qed.

Lemma recode_wrap_ok : program_logic_goal_for_function! recode_wrap.
Proof.
  repeat straightline.
  straightline_call.
  {
    ssplit.
    { ecancel_assumption. }
    { assumption. }
    { assumption. }
    { ZnWords. }
    { ZnWords. }
  }
  repeat straightline.
  eexists _.
  ssplit.
  { ecancel_assumption. }
  { assumption. }
  { reflexivity. }
  {
    assert (word.unsigned x <> 1).
    {
      intros Hx.
      rewrite word.unsigned_of_Z_0, Z.add_0_l, Hx, Z.mul_1_r in H9.

      epose proof positional_bounded (map byte.signed x0) (- 2 ^ w + 2) (2 ^ w) ltac:(apply Forall_map; assumption).
      rewrite length_map in H5.
      progress fold (positional_signed_bytes (2 ^ w) x0) in H5.

      assert (2*positional_signed_bytes (2 ^ w) x0 < -2^(w*n)) by lia.
      assert (positional (2 ^ w) (repeat (- 2 ^ w + 2) (length x0)) < -2 ^ (w * n)) by lia.

      rewrite <-H7, Nat2Z.id in H4.
      rewrite <-H7 in H13.
      lia.
    }
    ZnWords.
  }
  { assumption. }
Qed.

Lemma positional_dist_p256 (B := 2^w) h t
  (l := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551) :
  let words := cons h t in
    Forall (fun b => (-2^w + 2 <= 2*b <= 2^w)) words ->
    0 < 2 * positional B words < l ->
    h mod l <> B*(positional B t) mod l.
    (* or both sides zero if scalar = 0 *)
Proof.
  intros.
  rewrite Z.cong_iff_0.
  rewrite Z.mod_divide by lia.
  intros [x].
  inversion H; subst.
  cbv [words] in H0.
  rewrite positional_cons in H0.
  cbv [w] in *.
  lia.
Qed.
