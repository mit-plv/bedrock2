Require Import Coq.micromega.Lia.
(*
This file provides a tactic `ZnWords`, intended to solve goals containing a mix of
`word` and `Z` arithmetic.
It works by reducing all `word` operations to `Z` operations modulo `2^width`, eliminating
the modulo operations using Euclidean equations (`Z.div_mod_to_equations`), and then
calling `lia`.
The `width` has to be concrete, because otherwise the Euclidean equations become non-linear
and thus are not understood by `lia`.
It also simplifies `List.length` expressions (concrete lists, app, cons, skipn, firstn, map,
repeat, unfoldn, upd) when the goal or a hypothesis mentions a list length, and case-splits
boolean variables appearing in `if`s, so that the former `ZnWordsL` and `listZnWords` are
just aliases of `ZnWords`.
*)
Require Import Coq.Program.Tactics.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zpow_facts.
Require Import coqutil.Tactics.rdelta coqutil.Tactics.rewr.
Require Import coqutil.Z.ZLib.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Bitwidth coqutil.Word.Properties.
Require Import bedrock2.groundcbv.
Require Import bedrock2.WordPushDownLemmas.
Require coqutil.Datatypes.List.
Require Import coqutil.Tactics.foreach_hyp.
Require Import bedrock2.unzify.
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
  repeat ( rewrite ?@List.length_skipn, ?@List.firstn_length, ?@List.app_length, ?@List.length_cons, ?@List.length_nil in * ).

(* The following list-length preprocessing used to live in SepAutoArray.v (listZnWords). *)

Ltac destruct_bool_vars :=
  repeat match goal with
         | H: context[if ?b then _ else _] |- _ =>
             is_var b; let t := type of b in constr_eq t bool; destruct b
         | |- context[if ?b then _ else _] =>
             is_var b; let t := type of b in constr_eq t bool; destruct b
         end.

Ltac concrete_list_length l :=
  lazymatch l with
  | cons ?h ?t => let r := concrete_list_length t in constr:(S r)
  | nil => constr:(O)
  | List.app ?l1 ?l2 =>
      let r1 := concrete_list_length l1 in
      let r2 := concrete_list_length l2 in
      let r := eval cbv in (r1 + r2)%nat in constr:(r)
  | List.map _ ?l' => concrete_list_length l'
  | List.unfoldn _ ?n _ =>
      let n' := groundcbv n in
      lazymatch isnatcst n' with
      | true => constr:(n')
      end
  | _ => let l' := eval unfold l in l in concrete_list_length l'
  end.

Ltac rewr_with_eq e :=
  lazymatch type of e with
  | ?LHS = _ => progress (pattern LHS; eapply rew_zoom_bw; [exact e|])
  end.

Ltac list_length_simpl_step_in_goal :=
  match goal with
  | |- context[@List.length ?T ?l] =>
      let n := concrete_list_length l in change (@List.length T l) with n
  | |- context[List.length (List.skipn ?n ?l)] => rewr_with_eq (List.length_skipn n l)
  | |- context[List.length (List.firstn ?n ?l)] => rewr_with_eq (List.firstn_length n l)
  | |- context[List.length (?l1 ++ ?l2)] => rewr_with_eq (List.app_length l1 l2)
  | |- context[List.length (?h :: ?t)] => rewr_with_eq (List.length_cons t h)
  | |- context[List.length (List.map ?f ?l)] => rewr_with_eq (List.map_length f l)
  | |- context[List.length (List.unfoldn ?step ?n ?start)] =>
      rewr_with_eq (List.length_unfoldn step n start)
  | |- context[List.length (List.repeat ?v ?n)] => rewr_with_eq (List.repeat_length v n)
  end.

Goal forall (l1 l2: list Z) (a: Z),
    a + Z.of_nat (List.length (l1 ++ l2)) =
    Z.of_nat (List.length l1) + Z.of_nat (List.length l2) + a.
Proof.
  intros. list_length_simpl_step_in_goal.
Abort.

(* Only rewrites below the line, because rewriting above the line should already
   have been done (or will be done later), but the goal below the line might be the
   sidecondition of another rewrite lemma that's being tried and thus did not yet
   appear anywhere in the context before.
   For example, trying to rewrite with List.firstn_all2 creates a sidecondition
   containing a (List.length l) that did not yet have any chance to get
   simplified.
   For efficiency, we only use rewrite lemmas here that don't have sideconditions
   themselves, and use the simplest possible homemade rewr_with_eq to avoid any
   unexpected performance pitfalls of Coq's existing rewrite tactics. *)
Ltac list_length_rewrites_without_sideconds_in_goal :=
  repeat list_length_simpl_step_in_goal.

(* Cheap syntactic check so that goals without list lengths pay nothing for the
   list preprocessing. Meant to be run after cleanup_for_ZModArith, when only
   arithmetic hypotheses are left. *)
Ltac has_list_length :=
  match goal with
  | |- context[@List.length _ _] => idtac
  | _: context[@List.length _ _] |- _ => idtac
  end.

Ltac ZnWords_list_pre :=
  tryif has_list_length then (
    try (progress unfold List.upd, List.upds in * );
    list_length_rewrites_without_sideconds_in_goal;
    simpl_list_length_exprs
  ) else idtac.

Ltac wordOps_to_ZModArith_getEq t :=
  match t with
  | context[@Zmod.unsigned (2 ^ ?w) (Zmod.of_Z _ ?a) mod 2 ^ Z.log2 ?w] => constr:(@unsigned_of_Z_shamt w a)
  | context[@Zmod.unsigned (2 ^ ?w) (Zmod.of_Z _ ?z)] => constr:(@bits.unsigned_of_Z w z)
  | context[@Zmod.unsigned ?m Zmod.zero] => constr:(Zmod.unsigned_0 m)
  | context[@Zmod.unsigned (2 ^ ?w) Zmod.one] => constr:(@bits.unsigned_1 w)
  | context[@Zmod.signed ?m (Zmod.of_Z _ ?z)] => constr:(@Zmod.signed_of_Z m z)
  | context[@Zmod.of_Z ?m (Zmod.unsigned ?z)] => constr:(@Zmod.of_Z_unsigned m z)
  | context[@Zmod.unsigned ?m (Zmod.add ?x ?y)] => constr:(@Zmod.unsigned_add m x y)
  | context[@Zmod.unsigned ?m (Zmod.sub ?x ?y)] => constr:(@Zmod.unsigned_sub m x y)
  | context[@Zmod.unsigned ?m (Zmod.opp ?x)] => constr:(@Zmod.unsigned_opp m x)
  | context[@Zmod.unsigned ?m (Zmod.or ?x ?y)] => constr:(@unsigned_or_modwrap m x y)
  | context[@Zmod.unsigned ?m (Zmod.and ?x ?y)] => constr:(@Zmod.unsigned_and m x y)
  | context[@Zmod.unsigned ?m (Zmod.xor ?x ?y)] => constr:(@unsigned_xor_modwrap m x y)
  | context[@Zmod.unsigned (2 ^ ?w) (Zmod.not ?x)] => constr:(@bits.unsigned_not' w x)
  | context[@Zmod.unsigned ?m (Zmod.ndn ?x ?y)] => constr:(@Zmod.unsigned_ndn m x y)
  | context[@Zmod.unsigned ?m (Zmod.mul ?x ?y)] => constr:(@Zmod.unsigned_mul m x y)
  | context[@Zmod.unsigned ?m (Zmod.udiv ?x ?y)] => constr:(@Zmod.unsigned_udiv m x y)
  | context[@Zmod.signed ?m (Zmod.squot ?x ?y)] => constr:(@Zmod.signed_squot_nz m x y)
  | context[@Zmod.unsigned ?m (Zmod.umod ?x ?y)] => constr:(@Zmod.unsigned_umod m x y)
  | context[@Zmod.signed ?m (Zmod.srem ?x ?y)] => constr:(@Zmod.signed_srem m x y)
  | context[@Zmod.unsigned ?m (Zmod.slu ?x ?n)] => constr:(@Zmod.unsigned_slu m x n)
  | context[@Zmod.unsigned ?m (Zmod.sru ?x ?n)] => constr:(@Zmod.unsigned_sru m x n)
  | context[@Zmod.unsigned ?m (Zmod.srs ?x ?n)] => constr:(@Zmod.unsigned_srs m x n)
  | context[@Zmod.signed ?m (Zmod.srs ?x ?n)] => constr:(@Zmod.signed_srs m x n)
  | context[@Zmod.eqb ?m ?x ?y] =>
      constr:(eq_refl : @Zmod.eqb m x y = Z.eqb (Zmod.unsigned x) (Zmod.unsigned y))
  | context[Z.smodulo ?z (2 ^ ?w)] => constr:(@Z.smodulo_pow2 w z)
  | context[Z.ones ?n] => constr:(Z.ones_equiv n)
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
  rewr wordOps_to_ZModArith_getEq in * by
      solve [ reflexivity
            | trivial
            | apply computable_bounds; reflexivity
            | apply computable_le; reflexivity].

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
       | context [@Zmod.unsigned (2 ^ ?w) ?x] =>
         pose proof (bits.unsigned_range x
                       ltac:(first [ exact (proj1 (Z.leb_le 0 w) eq_refl)
                                   | exact width_nonneg
                                   | lia ])
                     : 0 <= @Zmod.unsigned (2 ^ w) x < 2 ^ w);
         let a := fresh "w0" in forget (@Zmod.unsigned (2 ^ w) x) as a
       end.

Ltac dewordify :=
  repeat dewordify_step;
  (* "try" because maybe all occurrences of words are already gone *)
  try (so fun hyporgoal => match hyporgoal with
  | context [Zmod (2 ^ ?w)] => let n := fresh "word" in forget (Zmod (2 ^ w)) as n
  end).

Ltac slow_unfold_Z_nat_consts_step :=
  so fun hyporgoal => match hyporgoal with
         | context[?x] =>
             let r := progress_rdelta_const x in
             lazymatch isZcst r with
             | true => progress change x with r in *
             | false =>
               lazymatch isnatcst r with
               | true => progress change x with r in *
               end
             end
         end.

Create HintDb ZnWords_unfold.

Ltac unfold_Z_nat_consts := autounfold with ZnWords_unfold in *.

Ltac word_eqs_to_Z_eqs :=
  repeat  match goal with
          | H: @eq (Zmod ?m) _ _ |- _ => apply (f_equal (@Zmod.unsigned m)) in H
          | H: not (@eq (Zmod ?m) ?x ?y) |- _ =>
              let H' := fresh H in
              pose proof ((fun E => H (Zmod.unsigned_inj m x y E))
                          : Zmod.unsigned x <> Zmod.unsigned y) as H';
              clear H; rename H' into H
          end.

Ltac ZnWords_pre :=
  fold_pow2_moduli;
  try eapply Zmod.unsigned_inj;
  lazymatch goal with
  | |- ?G => is_lia G;
             (* if there are evars in the goal, the preprocessing might affect the
                evars or their evarcontexts in tricky ways that no one wants to
                debug, so we should fail here, except if the goal is contradictory,
                so we do exfalso *)
             tryif has_evar G then exfalso else idtac

  end;
  destruct_bool_vars;
  word_eqs_to_Z_eqs;
  cleanup_for_ZModArith;
  ZnWords_list_pre;
  repeat wordOps_to_ZModArith_step;
  dewordify;
  clear_unused_nonProps;
  unfold_Z_nat_consts.

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

(* Ltac ZnWords := time "ZnWords" (ZnWords_pre; better_lia). *)
Ltac ZnWords := ZnWords_pre; better_lia.

(* Deprecated alias: ZnWords now does the list-length rewriting itself
   (only when a list length occurs, so plain word goals do not pay for it). *)
Ltac ZnWordsL := ZnWords.

(* zlia: the unzify preprocessing (proof-term zification of let-bound vars, hyps and
   goal, see unzify.v) as a closing tactic, finished by `Z.div_mod_to_equations; lia`
   like ZnWords. Differences to ZnWords: the word arithmetic is not rewritten but
   derived as proof terms, so an abstract width works (a Bitwidth instance is needed),
   and a hypothesis that cannot be zified is skipped instead of aborting.
   Before calling lia, the zified equations `unsigned (op ..) = ..` are rewritten back
   into the terms they describe and `a - m * (a / m)` is folded into `a mod m`;
   without this, lia was 10-50x slower than after the ZnWords preprocessing, because
   the proof-term engine leaves word terms under Z.to_nat/Nat.sub untouched (it only
   poses disjunctive case facts about them) and its inlined expansions grow
   exponentially with the nesting depth of the word operations. *)

Require Import coqutil.Tactics.ident_ops.

Lemma mod_eq_all: forall a b, a mod b = a - b * (a / b).
Proof.
  intros. destruct (Z.eq_dec b 0).
  - subst. rewrite Z.mod_0_r, Z.div_0_r. lia.
  - apply Z.mod_eq. assumption.
Qed.

(* For a let-bound list, connect (length x) to (length body), so that the list-length
   facts zify_len poses about the body reach the occurrences of x. (Not done by
   zify_letbound_var itself: it would make LiveVerif's `steps` prove more goals than
   the existing proof scripts expect.) *)
Ltac zlia_letbound_var bw x body tp :=
  try (lazymatch tp with
       | list _ =>
           let pf := zify_len bw body in
           let n := fresh "__Zdef_" x in
           let __ := unique_pose_proof_name n (pf : Z.of_nat (List.length x) = _) in
           idtac
       | _ => zify_letbound_var bw x body tp
       end).
Ltac zlia_hyp bw h tp := try (zify_hyp bw h tp).

(* Like apply_range_bounding_lemma_in_hyp, but keeps the equation, because zlia
   rewrites with it afterwards. *)
Ltac zlia_pose_range_bound bw h tp :=
  tryif ident_starts_with __Zrange_ h then
    lazymatch tp with
    | Zmod.unsigned _ = _ =>
        let r := fresh "__Zbound_0" in
        pose proof (@word.unsigned_range_eq _ bw _ _ h) as r
    | Zmod.signed _ = _ =>
        let r := fresh "__Zbound_0" in
        pose proof (@word.signed_range_eq_for_lia _ bw _ _ h) as r
    | Z.of_nat _ = _ =>
        let r := fresh "__Zbound_0" in
        pose proof (Z_of_nat_range_eq h) as r
    | _ => idtac
    end
  else idtac.

Ltac zlia_zify :=
  fold_pow2_moduli;
  let bw := get_bitwidth_or_dummy in
  foreach_var (zlia_letbound_var bw);
  foreach_hyp (zlia_hyp bw);
  try (let g := lazymatch goal with |- ?g => g end in
       let pf := zify_prop bw g in
       eapply (iff_to_bw_impl _ _ pf));
  foreach_hyp_upwards (zlia_pose_range_bound bw).

Ltac zlia_fold_mods := repeat rewrite <- mod_eq_all in *.

(* Rewrite with each zified equation whose lhs is `unsigned t`, `signed t` or
   `Z.of_nat t` for a compound t (for a variable t, the equation is a definition
   that lia can use as is), then drop the equation: after the rewrite, its lhs
   occurs nowhere else. *)
Ltac zlia_rewrite_defs :=
  repeat match goal with
         | H: @eq Z ?a ?b |- _ =>
             tryif constr_eq a b then clear H
             else (lazymatch a with
                   | Zmod.unsigned ?t => assert_fails (is_var t)
                   | Zmod.signed ?t => assert_fails (is_var t)
                   | Z.of_nat ?t => assert_fails (is_var t)
                   end;
                   try rewrite H in *;
                   clear H)
         end.

(* lia's own zify handles Z.to_nat and Nat.sub, and the case facts that
   zify_of_nat poses for them only make lia case-split more. *)
Ltac zlia_clear_native_cases :=
  repeat match goal with
         | H: _ /\ Z.of_nat (Z.to_nat _) = _ \/ _ |- _ => clear H
         | H: _ /\ Z.of_nat (Nat.sub _ _) = _ \/ _ |- _ => clear H
         end.

Ltac zlia_pre :=
  fold_pow2_moduli;
  try eapply Zmod.unsigned_inj;
  lazymatch goal with
  | |- ?G => is_lia G; tryif has_evar G then exfalso else idtac
  end;
  subst;
  destruct_bool_vars;
  zlia_zify;
  repeat match goal with
         | H: ?T |- _ => tryif is_lia T then fail else clear H
         end;
  clear_unused_nonProps;
  ZnWords_list_pre;
  zlia_fold_mods;
  zlia_rewrite_defs;
  zlia_clear_native_cases.

Ltac zlia := zlia_pre; Z.div_mod_to_equations; lia.
