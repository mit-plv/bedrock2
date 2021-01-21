Require Import Coq.ZArith.ZArith.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Z.Lia.
Require Import coqutil.Z.HexNotation.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
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
  subst; (* <-- substituting `@eq word _ _` might create opportunities for wordOps_to_ZModArith_step *)
  repeat match goal with
         | a := _ |- _ => subst a
         | H: ?T |- _ => tryif is_lia T then fail else clear H
         end.

(* TODO improve *)
Ltac simpl_list_length_exprs :=
  rewrite ?List.length_skipn, ?List.firstn_length, ?List.app_length, ?List.length_cons, ?List.length_nil in *.

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
        word.unsigned (word.sru x (word.of_Z a)) = Z.shiftr (word.unsigned x) a.
    Proof.
      intros. assert (width <= 2 ^ width) by (apply Zpow_facts.Zpower2_le_lin; blia).
      rewrite word.unsigned_sru_nowrap; rewrite word.unsigned_of_Z;
        unfold word.wrap; rewrite (Z.mod_small a); blia.
    Qed.

    Lemma signed_srs_shamtZ: forall (x: word) (a: Z),
        0 <= a < width ->
        word.signed (word.srs x (word.of_Z a)) = Z.shiftr (word.signed x) a.
    Proof.
      intros. assert (width <= 2 ^ width) by (apply Zpow_facts.Zpower2_le_lin; blia).
      rewrite word.signed_srs_nowrap; rewrite word.unsigned_of_Z;
        unfold word.wrap; rewrite (Z.mod_small a); blia.
    Qed.

    Lemma unsigned_if: forall (b: bool) thn els,
        word.unsigned (if b then thn else els) = if b then word.unsigned thn else word.unsigned els.
    Proof. intros. destruct b; reflexivity. Qed.
  End WithWord.
End word.

Ltac wordOps_to_ZModArith_step :=
  (* Note: duplication because `rewrite in *` doesn't work as expected,
     COQBUG https://github.com/coq/coq/issues/3051,
     and also because autorewrite doesn't infer the typeclasses either *)
  match goal with
  | H: _ |- _ => progress
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
  in H by solve [ reflexivity
                | trivial
                | apply computable_bounds; reflexivity
                | apply computable_le; reflexivity]
  | |- _ => progress
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
  in |-* by solve [ reflexivity
                | trivial
                | apply computable_bounds; reflexivity
                | apply computable_le; reflexivity]
  end;
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

Ltac dewordify_step :=
  so fun hyporgoal =>
       match hyporgoal with
       | context [@word.unsigned ?w ?i ?x] =>
         pose proof word.unsigned_range x;
         let a := fresh "w0" in forget (@word.unsigned w i x) as a
       | context [@List.length ?T ?l] =>
         let a := fresh "len0" in forget (@List.length T l) as a
       end.

Ltac dewordify :=
  repeat dewordify_step;
  (* "try" because maybe all occurrences of words are already gone *)
  try (so fun hyporgoal => match hyporgoal with
  | context [@word.rep ?w ?inst] => let n := fresh "word" in forget (@word.rep w inst) as n
  end).

Ltac unfold_Z_nat_consts :=
  repeat so fun hyporgoal => match hyporgoal with
         | context[?x] =>
           let r := rdelta_const x in
           lazymatch r with
           | Ox ?s => let r' := eval cbv in r in change x with r' in *
           | _ =>
             lazymatch isZcst r with
             | true => progress change x with r in *
             | false =>
               lazymatch isnatcst r with
               | true => progress change x with r in *
               end
             end
           end
         end.

Ltac is_lia_prop P :=
  lazymatch P with
  | ?A \/ ?B => is_lia_prop A; is_lia_prop B
  | ?A /\ ?B => is_lia_prop A; is_lia_prop B
  | False => idtac
  | True => idtac
  | ?A => is_lia A
  end.

Ltac canonicalize_word_width_and_instance :=
  repeat so fun hyporgoal => match hyporgoal with
     | context [@word.unsigned ?wi ?inst] =>
       let wi' := eval cbn in wi in let inst' := eval cbn in inst in
       progress ( change wi with wi' in *; change inst with inst' in * )
     | context [@word.signed   ?wi ?inst] =>
       let wi' := eval cbn in wi in let inst' := eval cbn in inst in
       progress ( change wi with wi' in *; change inst with inst' in * )
     end.

Ltac ZnWords_pre :=
  try eapply word.unsigned_inj;
  lazymatch goal with
  | |- ?G => is_lia_prop G
  end;
  cleanup_for_ZModArith;
  simpl_list_length_exprs;
  unfold_Z_nat_consts;
  canonicalize_word_width_and_instance;
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
