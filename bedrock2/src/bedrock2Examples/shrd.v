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

Import coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface Coq.Init.Byte Coq.Strings.String.
Import coqutil.Map.SortedListString. Local Existing Instances SortedListString.map SortedListString.ok.
From bedrock2 Require Import Semantics WeakestPrecondition ProgramLogic.
Import ProgramLogic.Coercions.

Section WithSemantics.
Context {width} {BW: Bitwidth width}.
Context {word: word.word width} {mem: map.map word byte}.
Context {ext_spec: ExtSpec} {ext_spec_ok : ext_spec.ok ext_spec}.
Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

Definition spec_of_shrd : spec_of "shrd" :=
  fnspec! "shrd" (lo hi n : word) ~> res,
    { requires t m := n < width;
      ensures T M :=
        M = m /\ T = t /\
        word.unsigned res = Z.lor (Z.shiftl hi (width - n)) (Z.shiftr lo n) mod 2^width
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
    subst v res. cbn [interp_op1]; rewrite eval_wsize'.
    rewrite word.unsigned_or, word.unsigned_slu, word.unsigned_sub, word.unsigned_of_Z, word.unsigned_sru by mlia.
    cbv [word.wrap].
    
    rewrite (Z.mod_small width), (Z.mod_small (_ - _)) by mlia.
    rewrite <-!Z.land_ones, !Z.land_lor_distr_l, !Z.land_ones by mlia.
    rewrite !Zmod_mod.
    trivial.
  }
  {
    cbv [res].
    rewrite word.unsigned_sru by lia.
    cbv [word.wrap].
    rewrite n_cond, Z.shiftr_0_r, Z.sub_0_r.
    rewrite <-!Z.land_ones, !Z.land_lor_distr_l, !Z.land_ones by lia.
    rewrite Z.shiftl_mul_pow2, Z.mod_mul by lia.
    rewrite Z.lor_0_l.
    trivial.
  }
Qed.

Definition spec_of_shrd_arith : spec_of "shrd" :=
  fnspec! "shrd" (lo hi n : word) ~> res,
    { requires t m := word.unsigned n < width;
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
    rewrite <-Z.shiftr_div_pow2, Z.shiftr_lor, Z.shiftr_shiftl_l by ZnWords.
    rewrite Z.lor_comm.
    trivial.
  }
  {
    rewrite <-Properties.word.wrap_unsigned.
    rewrite <-Z.land_ones by mlia.
    rewrite <-Z.land_assoc, (Z.land_comm (Z.ones width) _).
    rewrite Z.land_ones, Z.mul_comm, Z.mod_mul by mlia.
    rewrite Z.land_0_r.
    trivial.
  }
Qed.
End WithSemantics.
