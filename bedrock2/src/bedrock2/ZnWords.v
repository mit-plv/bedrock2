Require Import Coq.Program.Tactics.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zpow_facts.
Require Import coqutil.Tactics.rdelta coqutil.Tactics.rewr coqutil.Tactics.ParamRecords.
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
  subst*; (* <-- substituting `@eq word _ _` might create opportunities for wordOps_to_ZModArith_step *)
  repeat match goal with
         | a := _ |- _ => subst a
         | H: ?T |- _ => tryif is_lia T then fail else clear H
         end.

(* TODO improve
   @ needed because of COQBUG https://github.com/coq/coq/issues/3051 *)
Ltac simpl_list_length_exprs :=
  rewrite ?@List.length_skipn, ?@List.firstn_length, ?@List.app_length, ?@List.length_cons, ?@List.length_nil in *.


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

    Lemma unsigned_if: forall (b: bool) (thn els : word),
        word.unsigned (if b then thn else els) = if b then word.unsigned thn else word.unsigned els.
    Proof. intros. destruct b; reflexivity. Qed.
  End WithWord.
End word.

Ltac wordOps_to_ZModArith_getEq t :=
  match t with
  | context[@word.unsigned ?wi ?wo (word.of_Z ?z)] => constr:(@word.unsigned_of_Z wi wo _ z)
  | context[@word.signed ?wi ?wo (word.of_Z ?z)] => constr:(@word.signed_of_Z wi wo _ z)
  | context[@word.of_Z ?wi ?wo (word.unsigned ?z)] => constr:(@word.of_Z_unsigned wi wo _ z)
  | context[@word.unsigned ?wi ?wo (word.add ?x ?y)] => constr:(@word.unsigned_add wi wo _ x y)
  | context[@word.unsigned ?wi ?wo (word.sub ?x ?y)] => constr:(@word.unsigned_sub wi wo _ x y)
  | context[@word.unsigned ?wi ?wo (word.opp ?x)] => constr:(@word.unsigned_opp wi wo _ x)
  | context[@word.unsigned ?wi ?wo (word.or ?x ?y)] => constr:(@word.unsigned_or wi wo _ x y)
  | context[@word.unsigned ?wi ?wo (word.and ?x ?y)] => constr:(@word.unsigned_and wi wo _ x y)
  | context[@word.unsigned ?wi ?wo (word.xor ?x ?y)] => constr:(@word.unsigned_xor wi wo _ x y)
  | context[@word.unsigned ?wi ?wo (word.not ?x)] => constr:(@word.unsigned_not wi wo _ x)
  | context[@word.unsigned ?wi ?wo (word.ndn ?x ?y)] => constr:(@word.unsigned_ndn wi wo _ x y)
  | context[@word.unsigned ?wi ?wo (word.mul ?x ?y)] => constr:(@word.unsigned_mul wi wo _ x y)
  | context[@word.signed ?wi ?wo (word.mulhss ?x ?y)] => constr:(@word.signed_mulhss wi wo _ x y)
  | context[@word.signed ?wi ?wo (word.mulhsu ?x ?y)] => constr:(@word.signed_mulhsu wi wo _ x y)
  | context[@word.unsigned ?wi ?wo (word.mulhuu ?x ?y)] => constr:(@word.unsigned_mulhuu wi wo _ x y)
  | context[@word.unsigned ?wi ?wo (word.divu ?x ?y)] => constr:(@word.unsigned_divu wi wo _ x y)
  | context[@word.signed ?wi ?wo (word.divs ?x ?y)] => constr:(@word.signed_divs wi wo _ x y)
  | context[@word.unsigned ?wi ?wo (word.modu ?x ?y)] => constr:(@word.unsigned_modu wi wo _ x y)
  | context[@word.signed ?wi ?wo (word.mods ?x ?y)] => constr:(@word.signed_mods wi wo _ x y)
  | context[@word.unsigned ?wi ?wo (word.slu ?x (word.of_Z ?a))] => constr:(@word.unsigned_slu_shamtZ wi wo _ x a)
  | context[@word.unsigned ?wi ?wo (word.sru ?x (word.of_Z ?a))] => constr:(@word.unsigned_sru_shamtZ wi wo _ x a)
  | context[@word.signed ?wi ?wo (word.srs ?x (word.of_Z ?a))] => constr:(@word.signed_srs_shamtZ wi wo _ x a)
  | context[@word.eqb ?wi ?wo ?x ?y] => constr:(@word.unsigned_eqb wi wo _ x y)
  | context[@word.ltu ?wi ?wo ?x ?y] => constr:(@word.unsigned_ltu wi wo _ x y)
  | context[@word.lts ?wi ?wo ?x ?y] => constr:(@word.signed_lts wi wo _ x y)
  | context[@word.unsigned ?wi ?wo (if ?b then ?thn else ?els)] => constr:(@word.unsigned_if wi wo _ b thn els)
  | context[Z.shiftr ?a ?n] => constr:(Z.shiftr_div_pow2 a n)
  | context[Z.shiftl ?a ?n] => constr:(Z.shiftl_mul_pow2 a n)
  end.

Ltac wordOps_to_ZModArith_step :=
  (* Note: `rewrite in *` doesn't work as expected,
     COQBUG https://github.com/coq/coq/issues/3051,
     and autorewrite doesn't infer the typeclasses either,
     COQBUG https://github.com/coq/coq/issues/10848, and
     we don't want rewrite to replace evars with the LHS
     of the rewrite lemmas, COQBUG https://github.com/coq/coq/issues/10848 *)
  (rewr wordOps_to_ZModArith_getEq in * by
      solve [ reflexivity
            | trivial
            | apply computable_bounds; reflexivity
            | apply computable_le; reflexivity]);
  cbv [word.wrap word.swrap] in *.

Ltac clear_unused_nonProps :=
        repeat match goal with
               | x: ?T |- _ => lazymatch type of T with
                               | Prop => fail
                               | _ => clear x
                               end
               end.

Require Import coqutil.Tactics.Tactics.

Ltac dewordify_step :=
  so fun hyporgoal =>
       match hyporgoal with
       | context [@word.unsigned ?w ?i ?x] =>
         pose proof (word.unsigned_range x : 0 <= @word.unsigned w i x < 2 ^ w);
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
  simpl_param_projections; (* <-- should take care of width (if it's a member of a record called `parameters`) *)
  repeat so fun hyporgoal => match hyporgoal with
     | context [@word.unsigned ?wi ?inst] =>
       let inst' := eval cbn in inst in progress ( change inst with inst' in * )
     | context [@word.signed ?wi ?inst] =>
       let inst' := eval cbn in inst in progress ( change inst with inst' in * )
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
       | |- ?G => idtac "Goal"; idtac G; idtac ". Proof. t. Abort."
       end;
       fail).

Ltac better_lia :=
(*log_goal;*)
  Z.div_mod_to_equations;
  lia.

Ltac ZnWords := ZnWords_pre; better_lia.
