Require Export Coq.Lists.List. Export ListNotations.
Require Export Coq.ZArith.BinInt. Open Scope Z_scope.
Require Export coqutil.Word.Interface coqutil.Word.Properties.
Require Export coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.rdelta coqutil.Tactics.destr.
Require Export coqutil.Z.Lia.
Require Export bedrock2.Lift1Prop.
Require Export bedrock2.Map.Separation.
Require Export bedrock2.Map.SeparationLogic.
Require Export bedrock2.Array.
Require Export compiler.SimplWordExpr.

Infix "*" := sep : sep_scope.

Delimit Scope sep_scope with sep.
Arguments impl1 {T} (_)%sep (_)%sep.
Arguments iff1 {T} (_)%sep (_)%sep.

(* TODO does not get rid of %sep in printing as intended *)
Arguments sep {key} {value} {map} (_)%sep (_)%sep.


Lemma f_equal2: forall {A B: Type} {f1 f2: A -> B} {a1 a2: A},
    f1 = f2 -> a1 = a2 -> f1 a1 = f2 a2.
Proof. intros. congruence. Qed.

(* unifies two separation logic clauses syntactically, instantiating as many evars
   as it wants, but for subterms of type word, applies word solver instead of syntatic unify,
   and for subterms of type Z, applies lia instead of syntactic unify *)
Ltac wclause_unify OK :=
  lazymatch type of OK with
  | word.ok ?WORD =>
    lazymatch goal with
    | |- @eq ?T ?x ?y =>
      tryif first [is_evar x | is_evar y | constr_eq x y] then (
        reflexivity
      ) else (
        tryif (unify T (@word.rep _ WORD)) then (
          solve [solve_word_eq OK]
        ) else (
          tryif (unify T Z) then (
            solve [bomega]
          ) else (
            lazymatch x with
            | ?x1 ?x2 => lazymatch y with
                         | ?y1 ?y2 => refine (f_equal2 _ _); wclause_unify OK
                         | _ => fail "" x "is an application while" y "is not"
                         end
            | _ => lazymatch y with
                   | ?y1 ?y2 => fail "" x "is not an application while" y "is"
                   | _ => tryif constr_eq x y then reflexivity else fail "" x "does not match" y
                   end
            end
          )
        )
      )
    end
  | _ => fail 1000 "OK does not have the right type"
  end.

(* This can be overridden by the user.
   The idea of a "tag" is that it's a subterm of a sepclause which is so unique that if
   the same tag appears both on the left and on the right of an iff1, we're sure that
   these two clauses should be matched & canceled with each other.
   "tag" should return any Gallina term. *)
Ltac tag P :=
  let __ := lazymatch type of P with
            | @map.rep _ _ _ -> Prop => idtac
            | _ => fail 10000 P "is not a sep clause"
            end in
  lazymatch P with
  | _ => fail "no recognizable tag"
  end.

(* This can be overridden by the user.
   The idea of "addr" is that if the addresses of two sepclauses are the same,
   we're sure that these two clauses should be matched & canceled with each other,
   even if they still contain many evars outside of their address.
   "addr" should return a Gallina term of type "word" *)
Ltac addr P :=
  let __ := lazymatch type of P with
            | @map.rep _ _ _ -> Prop => idtac
            | _ => fail 10000 P "is not a sep clause"
            end in
  lazymatch P with
  | ptsto ?A _ => A
  | array _ _ ?A _ => A
  | _ => fail "no recognizable address"
  end.

(* completely solves a sepclause equality or fails *)
Ltac sepclause_eq OK :=
  match goal with
  | |- ?G => assert_fails (has_evar G);
             wclause_unify OK
  | |- ?lhs = ?rhs => let tagL := tag lhs in
                      let tagR := tag rhs in
                      constr_eq tagL tagR;
                      wclause_unify OK
  | |- ?lhs = ?rhs => let addrL := addr lhs in
                      let addrR := addr rhs in
                      assert_fails (has_evar addrL);
                      assert_fails (has_evar addrR);
                      replace addrL with addrR by solve_word_eq OK;
                      (reflexivity || fail 10000 lhs "and" rhs "have the same address"
                      "according to addr, but can't be matched")
  end.

Ltac pick_nat n :=
  multimatch n with
  | S ?m => constr:(m)
  | S ?m => pick_nat m
  end.

Ltac wcancel_step OK := once (
  let RHS := lazymatch goal with |- Lift1Prop.iff1 _ (seps ?RHS) => RHS end in
  let jy := index_and_element_of RHS in (* <-- multi-success! *)
  let j := lazymatch jy with (?i, _) => i end in
  let y := lazymatch jy with (_, ?y) => y end in
  assert_fails (idtac; let y := rdelta_var y in is_evar y);
  let LHS := lazymatch goal with |- Lift1Prop.iff1 (seps ?LHS) _ => LHS end in
  let l := eval cbv [List.length] in (List.length LHS) in
  let i := pick_nat l in (* <-- multi-success! *)
  cancel_seps_at_indices i j; [sepclause_eq OK|]).

Ltac wcancel OK :=
  cancel;
  repeat wcancel_step OK;
  try solve [ecancel_done'].

(* mostly useful for debugging, once everything works, wcancel should do all the work *)
Ltac cancel_by_tag :=
  let RHS := lazymatch goal with |- Lift1Prop.iff1 _ (seps ?RHS) => RHS end in
  let jy := index_and_element_of RHS in
  let j := lazymatch jy with (?i, _) => i end in
  let y := lazymatch jy with (_, ?y) => y end in
  let tagR := tag y in
  assert_fails (idtac; let y := rdelta_var y in is_evar y);
  let LHS := lazymatch goal with |- Lift1Prop.iff1 (seps ?LHS) _ => LHS end in
  let l := eval cbv [List.length] in (List.length LHS) in
  let i := pick_nat l in
  let x := eval cbv [List.nth] in (List.nth i LHS (emp True)) in
  let tagL := tag x in
  constr_eq tagL tagR;
  cancel_seps_at_indices i j.

Section Unique.
  Context {key value} {map : map.map key value} {ok : map.ok map}.

  Definition unique_footprint(P: map -> Prop): Prop :=
    forall m1 m2, P m1 -> P m2 -> map.same_domain m1 m2.

  Lemma same_domain_split: forall m1 m2 m1l m1r m2l m2r,
      map.same_domain m1l m2l ->
      map.same_domain m1r m2r ->
      map.split m1 m1l m1r ->
      map.split m2 m2l m2r ->
      map.same_domain m1 m2.
  Proof.
    unfold map.same_domain, map.sub_domain, map.split.
    intros. destruct H, H0, H1, H2. subst.
    split.
    - intros.
      rewrite map.get_putmany_dec in H1.
      destr (map.get m1r k).
      + inversion H1. subst v1.
        specialize (H0 _ _ E). destruct H0 as [v2 G].
        exists v2. apply map.get_putmany_right. assumption.
      + specialize (H _ _ H1). destruct H as [v2 G].
        exists v2. rewrite map.get_putmany_left. 1: assumption.
        destr (map.get m2r k); [exfalso | reflexivity].
        specialize (H4 _ _ E0). destruct H4 as [v2' G'].
        congruence.
    - intros.
      rewrite map.get_putmany_dec in H1.
      destr (map.get m2r k).
      + inversion H1. subst v1.
        specialize (H4 _ _ E). destruct H4 as [v2 G].
        exists v2. apply map.get_putmany_right. assumption.
      + specialize (H3 _ _ H1). destruct H3 as [v2 G].
        exists v2. rewrite map.get_putmany_left. 1: assumption.
        destr (map.get m1r k); [exfalso | reflexivity].
        specialize (H0 _ _ E0). destruct H0 as [v2' G'].
        congruence.
  Qed.

  Lemma unique_footprint_sep(P Q: map -> Prop):
    unique_footprint P ->
    unique_footprint Q ->
    unique_footprint (P * Q)%sep.
  Proof.
    unfold unique_footprint. intros.
    unfold sep in *.
    destruct H1 as [m1P [m1Q [? [? ?] ] ] ].
    destruct H2 as [m2P [m2Q [? [? ?] ] ] ].
    eapply same_domain_split; cycle 2; eauto.
  Qed.

End Unique.
