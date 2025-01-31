Require Import bedrock2.NotationsCustomEntry.

Import Syntax BinInt String.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition shrd :=
  func! (lo, hi, n) ~> (res) {
      res = lo >> n;
      if n {
        res = hi << ($64 - n) | res
      }
    }.

From bedrock2 Require Import WeakestPrecondition ProgramLogic BasicC64Semantics.
Import ProgramLogic.Coercions.

Local Instance spec_of_shrd : spec_of "shrd" :=
  fnspec! "shrd" (lo hi n : word) ~> res,
    { requires t m := n < 64;
      ensures T M :=
        M = m /\ T = t /\
        word.unsigned res = Z.lor (Z.shiftl hi (64 - n)) (Z.shiftr lo n) mod 2^64
    }.

Require Import bedrock2.ZnWords Coq.ZArith.ZArith Lia.

Lemma shrd_ok : program_logic_goal_for_function! shrd.
Proof.
  repeat (straightline || apply WeakestPreconditionProperties.dexpr_expr).
  split; intro n_cond; repeat (straightline || unfold cmd_body).
  {
    cbv [v res].
    rewrite word.unsigned_or, word.unsigned_slu, word.unsigned_sub, word.unsigned_of_Z, word.unsigned_sru by ZnWords.
    cbv [word.wrap].
    change (64 mod 2^64) with 64.
    rewrite (Z.mod_small (64 - _)) by ZnWords.
    rewrite <-!Z.land_ones, !Z.land_lor_distr_l, !Z.land_ones by lia.
    rewrite !Zmod_mod.
    trivial.
  }
  {
    cbv [res].
    rewrite word.unsigned_sru by lia.
    cbv [word.wrap].
    rewrite n_cond, Z.shiftr_0_r.
    change (64 - 0) with 64.
    rewrite <-!Z.land_ones, !Z.land_lor_distr_l, !Z.land_ones by lia.
    rewrite Z.shiftl_mul_pow2, Z.mod_mul by lia.
    rewrite Z.lor_0_l.
    trivial.
  }
Qed.

Section ArithmeticSpec.
  Local Instance spec_of_shrd_arith : spec_of "shrd" :=
    fnspec! "shrd" (lo hi n : word) ~> res,
      { requires t m := word.unsigned n < 64;
        ensures T M :=
          M = m /\ T = t /\
          res = (lo + 2^64 * hi) / 2^n mod 2^64 :> Z
      }.

  Lemma shdr_ok_arith : program_logic_goal_for_function! shrd.
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
      rewrite <-Z.shiftl_mul_pow2 by lia.
      rewrite <-Z.shiftr_div_pow2, Z.shiftr_lor, Z.shiftr_shiftl_l by ZnWords.
      rewrite Z.lor_comm.
      trivial.
    }
    {
      rewrite <-Properties.word.wrap_unsigned.
      rewrite <-Z.land_ones by lia.
      rewrite <-Z.land_assoc, (Z.land_comm (Z.ones 64) _).
      rewrite Z.land_ones, Z.mul_comm, Z.mod_mul by lia.
      rewrite Z.land_0_r.
      trivial.
    }
  Qed.
End ArithmeticSpec.
