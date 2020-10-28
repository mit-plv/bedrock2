Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Word.Interface.
Require Import bedrock2.Semantics. (* for the semantics parameters record *)
Local Open Scope Z_scope.

Lemma computable_bounds{lo v hi: Z}(H: andb (Z.leb lo v) (Z.ltb v hi) = true): lo <= v < hi.
Proof.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply Z.leb_le in H1.
  apply Z.ltb_lt in H2.
  auto.
Qed.

Lemma computable_le{lo v: Z}(H: Z.leb lo v = true): lo <= v.
Proof. apply Z.leb_le. assumption. Qed.

Lemma computable_lt{lo v: Z}(H: Z.ltb lo v = true): lo < v.
Proof. apply Z.ltb_lt. assumption. Qed.

Ltac cleanup_for_ZModArith :=
  repeat match goal with
         | a := _ |- _ => subst a
         | H: ?T |- _ => tryif is_lia T then fail else clear H
         end.

(* TODO improve *)
Ltac simpl_list_length_exprs :=
  rewrite ?List.length_skipn, ?List.firstn_length.

(* word laws for shifts where the shift amount is a Z instead of a word *)
Module word.
  Section WithWord.
    Context {width} {word : word.word width} {word_ok : word.ok word}.

    Lemma unsigned_slu_shamtZ: forall (x: word) (a: Z),
        0 <= a < width ->
        word.unsigned (word.slu x (word.of_Z a)) = word.wrap (Z.shiftl (word.unsigned x) a).
    Proof.
      intros. assert (width <= 2 ^ width) by (apply Zpow_facts.Zpower2_le_lin; blia).
      rewrite word.unsigned_slu; rewrite word.unsigned_of_Z; unfold word.wrap; rewrite (Z.mod_small a); blia.
    Qed.

    Lemma unsigned_sru_shamtZ: forall (x: word) (a: Z),
        0 <= a < width ->
        word.unsigned (word.sru x (word.of_Z a)) = word.wrap (Z.shiftr (word.unsigned x) a).
    Proof.
      intros. assert (width <= 2 ^ width) by (apply Zpow_facts.Zpower2_le_lin; blia).
      rewrite word.unsigned_sru; rewrite word.unsigned_of_Z; unfold word.wrap; rewrite (Z.mod_small a); blia.
    Qed.

    Lemma signed_srs_shamtZ: forall (x: word) (a: Z),
        0 <= a < width ->
        word.signed (word.srs x (word.of_Z a)) = word.swrap (Z.shiftr (word.signed x) a).
    Proof.
      intros. assert (width <= 2 ^ width) by (apply Zpow_facts.Zpower2_le_lin; blia).
      rewrite word.signed_srs; rewrite word.unsigned_of_Z; unfold word.wrap; rewrite (Z.mod_small a); blia.
    Qed.

    Lemma unsigned_if: forall (b: bool) thn els,
        word.unsigned (if b then thn else els) = if b then word.unsigned thn else word.unsigned els.
    Proof. intros. destruct b; reflexivity. Qed.
  End WithWord.
End word.

Ltac wordOps_to_ZModArith_step :=
  rewrite ?word.unsigned_of_Z, ?word.signed_of_Z, ?word.of_Z_unsigned,
          ?word.unsigned_add, ?word.unsigned_sub, ?word.unsigned_opp,
          ?word.unsigned_or, ?word.unsigned_and, ?word.unsigned_xor,
          ?word.unsigned_not, ?word.unsigned_ndn,
          ?word.unsigned_mul, ?word.signed_mulhss, ?word.signed_mulhsu, ?word.unsigned_mulhuu,
          ?word.unsigned_divu, ?word.signed_divs, ?word.unsigned_modu, ?word.signed_mods,
          ?word.unsigned_slu_shamtZ, ?word.unsigned_sru_shamtZ, ?word.signed_srs_shamtZ,
          ?word.unsigned_eqb, ?word.unsigned_ltu, ?word.signed_lts,
          ?word.unsigned_if,
          ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2
  in * by solve [ reflexivity
                | trivial
                | apply computable_bounds; reflexivity
                | apply computable_le; reflexivity];
  cbv [word.wrap] in *.

Ltac clear_unused_nonProps :=
        repeat match goal with
               | x: ?T |- _ => lazymatch type of T with
                               | Prop => fail
                               | _ => clear x
                               end
               end.

Require Import coqutil.Tactics.Tactics.
Require Import Cdcl.Itauto.

Ltac make_bitwidth_concrete :=
  so fun hyporgoal => match hyporgoal with
  | context [@width ?p] =>
    first [ change (@width p) with 32 in *
          | change (@width p) with 64 in *
          | let wc := fresh in pose proof (@width_cases _ _) as wc;
            let W := fresh "Width" in forget (@width p) as W;
            destruct wc; subst W ]
  end.

Ltac dewordify_step :=
  so fun hyporgoal =>
       match hyporgoal with
       | context [@word.unsigned ?w ?i ?x] =>
         let a := fresh "w0" in forget (@word.unsigned w i x) as a
       | context [@List.length ?T ?l] =>
         let a := fresh "len0" in forget (@List.length T l) as a
       end.

Ltac dewordify :=
  repeat dewordify_step;
  make_bitwidth_concrete;
  so fun hyporgoal => match hyporgoal with
  | context [@word.rep ?w ?inst] => let n := fresh "word" in forget (@word.rep w inst) as n
  end.

Ltac ZnWords_pre :=
  lazymatch goal with
  | |- ?G => tryif is_lia G then idtac else fail "this tactic does not solve this kind of goal"
  end;
  cleanup_for_ZModArith;
  simpl_list_length_exprs;
  repeat wordOps_to_ZModArith_step;
  dewordify;
  clear_unused_nonProps.

Require Import Lia.

Ltac log_goal :=
  try (repeat match goal with
              | x: _ |- _ => revert x
              end;
       match goal with
       | |- ?G => idtac "--- goal ---"; idtac G
       end;
       fail).

(* Note: zify is called to expose propositional structure to itauto, and leaf-lia
   will call it again (deliberately) to do more preprocessing enabled by the
   assumptions added by itauto *)
Ltac better_lia :=
(*log_goal;*)
  Z.div_mod_to_equations;
  Zify.zify;
  itauto lia.

Ltac ZnWords := ZnWords_pre; better_lia.
