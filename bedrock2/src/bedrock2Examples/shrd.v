Require Import bedrock2.NotationsCustomEntry bedrock2.wsize.

Import Syntax BinInt String.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition shrd :=
  func! (lo, hi, n) ~> (res) {
      res = lo >> n;
      if n {
        res = hi << ($wsize - n) | res
      }
    }.

Import coqutil.Word.Bitwidth coqutil.Map.Interface Coq.Init.Byte Coq.Strings.String.
Import coqutil.Map.SortedListString. Local Existing Instances SortedListString.map SortedListString.ok.
From bedrock2 Require Import Semantics WeakestPrecondition ProgramLogic.
Import ProgramLogic.Coercions.

Section WithSemantics.
Context {width} {BW: Bitwidth width}.
Local Notation word := (bits width).
Context {mem: map.map word byte}.
Context {ext_spec: ExtSpec} {ext_spec_ok : ext_spec.ok ext_spec}.
Context {mem_ok: map.ok mem}.

Definition spec_of_shrd : spec_of "shrd" :=
  fnspec! "shrd" (lo hi n : word) ~> res,
    { requires t m := n < width;
      ensures T M :=
        M = m /\ T = t /\
        Zmod.unsigned res = Z.lor (Z.shiftl hi (width - n)) (Z.shiftr lo n) mod 2^width
    }.

Require Import bedrock2.ZnWords Coq.ZArith.ZArith Lia.

Local Ltac mlia := case BW as [ [ -> | -> ] ]; ZnWords.

Lemma shrd_ok :
  let '_ := spec_of_shrd in
  program_logic_goal_for_function! shrd.
Proof.
  repeat (straightline || apply WeakestPreconditionProperties.dexpr_expr).
  split; intro n_cond; repeat (straightline || unfold cmd_body).
  {
    subst v res. cbn [interp_op1].
    rewrite shamt_of_Z_small by mlia.
    rewrite eval_wsize'.
    assert (2 ^ Z.log2 width = width) as Hl by (case BW as [ [ -> | -> ] ]; reflexivity).
    rewrite !Hl.
    rewrite (Z.mod_small (Zmod.unsigned n) width) by mlia.
    rewrite bits.unsigned_or, Zmod.unsigned_slu, Zmod.unsigned_sub, bits.unsigned_of_Z, Zmod.unsigned_sru by mlia.
    rewrite (Z.mod_small width), (Z.mod_small (_ - _)) by mlia.
    rewrite (Z.mod_small (width - _) width) by mlia.
    rewrite <-!Z.land_ones, !Z.land_lor_distr_l, !Z.land_ones by mlia.
    rewrite (Z.mod_small (Z.shiftr _ _)); trivial.
    rewrite Z.shiftr_div_pow2 by mlia.
    pose proof (bits.unsigned_range lo width_nonneg).
    pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) ltac:(mlia)).
    split. { apply Z.div_pos; lia. }
    eapply Z.le_lt_trans with (m := Zmod.unsigned lo); [ | lia ].
    apply Z.div_le_upper_bound; [ lia | ].
    pose proof (Z.mul_nonneg_nonneg (2 ^ n - 1) (Zmod.unsigned lo) ltac:(lia) ltac:(lia)).
    lia.
  }
  {
    cbv [res].
    assert (2 ^ Z.log2 width = width) as Hl by (case BW as [ [ -> | -> ] ]; reflexivity).
    rewrite !Hl.
    rewrite (Z.mod_small (Zmod.unsigned n) width) by mlia.
    rewrite Zmod.unsigned_sru by lia.
    rewrite n_cond, Z.shiftr_0_r, Z.sub_0_r.
    rewrite <-!Z.land_ones, !Z.land_lor_distr_l, !Z.land_ones by mlia.
    rewrite Z.shiftl_mul_pow2, Z.mod_mul by mlia.
    rewrite Z.lor_0_l.
    rewrite Z.mod_small; trivial.
    apply bits.unsigned_range, width_nonneg.
  }
Qed.

Definition spec_of_shrd_arith : spec_of "shrd" :=
  fnspec! "shrd" (lo hi n : word) ~> res,
    { requires t m := Zmod.unsigned n < width;
      ensures T M :=
        M = m /\ T = t /\
        res = (lo + 2^width * hi) / 2^n mod 2^width :> Z
    }.

Lemma shdr_ok_arith :
  let '_ := spec_of_shrd_arith  in
  program_logic_goal_for_function! shrd.
Proof.
  cbv [program_logic_goal_for spec_of_shrd_arith].
  intros.
  eapply WeakestPreconditionProperties.Proper_call; [|apply shrd_ok]; trivial.
  intros ? ? ? spec.
  destruct spec as (res & ? & ? & ? & spec).
  exists res.
  repeat split; trivial.
  rewrite spec.
  rewrite <-BitOps.or_to_plus.
  {
    rewrite Z.mul_comm.
    rewrite <-Z.shiftl_mul_pow2 by mlia.
    rewrite <-Z.shiftr_div_pow2, Z.shiftr_lor, Z.shiftr_shiftl_l by mlia.
    rewrite Z.lor_comm.
    trivial.
  }
  {
    rewrite <-bits.mod_to_Z.
    rewrite <-Z.land_ones by mlia.
    rewrite <-Z.land_assoc, (Z.land_comm (Z.ones width) _).
    rewrite Z.land_ones, Z.mul_comm, Z.mod_mul by mlia.
    rewrite Z.land_0_r.
    trivial.
  }
Qed.
End WithSemantics.
