Require Import Coq.micromega.Lia.
(*
This file provides a tactic `ZnWords`, intended to solve goals containing a mix of
`word` and `Z` arithmetic.
It works by reducing all `word` operations to `Z` operations modulo `2^width`, eliminating
the modulo operations using Euclidean equations (`Z.div_mod_to_equations`), and then
calling `lia`.
The `width` has to be concrete, because otherwise the Euclidean equations become non-linear
and thus are not understood by `lia`.
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
  word_eqs_to_Z_eqs;
  cleanup_for_ZModArith;
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

(* A ZnWords that does also some list rewriting, which is often too expensive,
   and can be done more efficiently if it's only done occasionally rather
   than before each ZnWords invocation *)
Ltac ZnWordsL :=
  (* will subst vars bound by :=, which enables rewrites in their bodies *)
  cleanup_for_ZModArith;
  simpl_list_length_exprs;
  ZnWords.

(* ===== zify-based variant (mit-plv/coqutil#56 prototype) =====
   [coqutil.Word.ZifyBitsAll] registers zify instances for [bits 8/16/32/64] and
   hooks them into every [lia]; [bits_lia] is its closing tactic.  [ZnWords_zify]
   is the drop-in candidate for [ZnWords]: the same goal guard and context
   pruning, then [bits_lia] instead of the rewrite table + dewordify. *)
Require Import coqutil.Word.ZifyBitsAll.

(* [is_lia] extended with what zify translates: word (dis)equalities, [Zmod.eqb]. *)
Ltac is_lia_word P :=
  lazymatch P with
  | @eq (Zmod _) _ _ => idtac
  | not (@eq (Zmod _) _ _) => idtac
  | @eq bool (Zmod.eqb _ _) _ => idtac
  | @eq bool _ (Zmod.eqb _ _) => idtac
  | ?A /\ ?B => is_lia_word A; is_lia_word B
  | ?A \/ ?B => is_lia_word A; is_lia_word B
  | ?A -> ?B => is_lia_word A; is_lia_word B
  | not ?A => is_lia_word A
  | _ => is_lia P
  end.

(* No goal-shape guard: zify handles the propositional structure of a goal
   itself, and a goal without arithmetic can still be closed by a contradiction
   in the hypotheses (second attempt), as unzify's zify_goal does.  A goal with
   evars is taken only when it is arithmetic, and then by contradiction, as the
   rewrite-based tactic did: proving a non-arithmetic evar goal by exfalso would
   leave the evar for the caller (LiveVerif's canceling) to trip over. *)
Ltac ZnWords_zify_pre :=
  lazymatch goal with
  | |- ?G => tryif has_evar G then (is_lia_word G; exfalso) else idtac
  end;
  subst*;
  repeat match goal with
         | a := _ |- _ => subst a
         | H: ?T |- _ => tryif is_lia_word T then fail else clear H
         end;
  unfold_Z_nat_consts.

(* Facts that unzify poses and zify cannot derive: lengths of ZList operations
   (as case disjunctions, which lia splits) and word-valued [if]. *)
Require Import coqutil.Datatypes.ZList.
Section ZListFacts.
  Context {A : Type}.
  Lemma len_upto_eq (l : list A) i :
    Z.of_nat (List.length (List.upto i l)) = Z.min (Z.max i 0) (Z.of_nat (List.length l)).
  Proof. cbv [List.upto]. rewrite List.firstn_length. lia. Qed.
  Lemma len_from_eq (l : list A) i :
    Z.of_nat (List.length (List.from i l)) = Z.of_nat (List.length l) - Z.min (Z.max i 0) (Z.of_nat (List.length l)).
  Proof. cbv [List.from]. rewrite List.length_skipn. lia. Qed.
  Lemma len_repeatz_eq (x : A) n : Z.of_nat (List.length (List.repeatz x n)) = Z.max n 0.
  Proof. cbv [List.repeatz]. rewrite List.repeat_length. lia. Qed.
  Lemma len_set_cases (l : list A) i x :
    (0 <= i < Z.of_nat (List.length l) /\ Z.of_nat (List.length (List.set l i x)) = Z.of_nat (List.length l)) \/ ~ (0 <= i < Z.of_nat (List.length l)).
  Proof. destruct (Z_le_dec 0 i), (Z_lt_dec i (Z.of_nat (List.length l))); auto using List.len_set; tauto. Qed.
End ZListFacts.

Lemma if_cases {T} (c : bool) (a b : T) :
  (c = true /\ (if c then a else b) = a) \/ (c = false /\ (if c then a else b) = b).
Proof. destruct c; auto. Qed.

Ltac ZnWords_zify_pose pf :=
  let t := type of pf in
  lazymatch goal with
  | H : t |- _ => fail
  | _ => pose proof pf
  end.

Ltac ZnWords_zify_if_cases c a b :=
  lazymatch type of a with
  | Z => ZnWords_zify_pose (if_cases c a b)
  | Zmod _ => ZnWords_zify_pose (if_cases c a b)
  end.

Ltac ZnWords_zify_facts :=
  repeat match goal with
         | |- context [Z.of_nat (List.length (List.upto ?i ?l))] => ZnWords_zify_pose (len_upto_eq l i)
         | H : context [Z.of_nat (List.length (List.upto ?i ?l))] |- _ => ZnWords_zify_pose (len_upto_eq l i)
         | |- context [Z.of_nat (List.length (List.from ?i ?l))] => ZnWords_zify_pose (len_from_eq l i)
         | H : context [Z.of_nat (List.length (List.from ?i ?l))] |- _ => ZnWords_zify_pose (len_from_eq l i)
         | |- context [Z.of_nat (List.length (List.set ?l ?i ?x))] => ZnWords_zify_pose (len_set_cases l i x)
         | H : context [Z.of_nat (List.length (List.set ?l ?i ?x))] |- _ => ZnWords_zify_pose (len_set_cases l i x)
         | |- context [Z.of_nat (List.length (List.repeatz ?x ?n))] => ZnWords_zify_pose (len_repeatz_eq x n)
         | H : context [Z.of_nat (List.length (List.repeatz ?x ?n))] |- _ => ZnWords_zify_pose (len_repeatz_eq x n)
         | |- context [Z.of_nat (List.length (?l1 ++ ?l2))] => ZnWords_zify_pose (List.len_app l1 l2)
         | H : context [Z.of_nat (List.length (?l1 ++ ?l2))] |- _ => ZnWords_zify_pose (List.len_app l1 l2)
         | |- context [Z.of_nat (List.length (?a :: ?l))] => ZnWords_zify_pose (List.len_cons a l)
         | H : context [Z.of_nat (List.length (?a :: ?l))] |- _ => ZnWords_zify_pose (List.len_cons a l)
         | |- context [Z.of_nat (List.length (@nil ?A))] => ZnWords_zify_pose (@List.len_nil A)
         | H : context [Z.of_nat (List.length (@nil ?A))] |- _ => ZnWords_zify_pose (@List.len_nil A)
         | |- context [if ?c then ?a else ?b] => ZnWords_zify_if_cases c a b
         | H : context [if ?c then ?a else ?b] |- _ => ZnWords_zify_if_cases c a b
         end.

Ltac ZnWords_zify :=
  ZnWords_zify_pre; ZnWords_zify_facts; first [ bits_lia | exfalso; bits_lia ].

(* The rewrite-based tactic stays available as [ZnWords_legacy] for the few
   goals the zify path does not prove (nonlinear word products, an abstract
   width without a Bitwidth instance): see the call sites that name it. *)
Ltac ZnWords_legacy := ZnWords_pre; better_lia.
Ltac ZnWords ::= ZnWords_zify.
