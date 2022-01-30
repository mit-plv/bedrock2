Require Export Coq.Lists.List. Export ListNotations.
Require Export Coq.ZArith.ZArith. Open Scope Z_scope.
Require Export coqutil.Word.Interface coqutil.Word.Properties.
Require Export coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.rdelta coqutil.Tactics.destr coqutil.Decidable.
Require Import coqutil.Tactics.rewr coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.ltac_list_ops.
Require Export coqutil.Z.Lia.
Require Export coqutil.Datatypes.PropSet.
Require Export bedrock2.Lift1Prop.
Require Export bedrock2.Map.Separation.
Require Export bedrock2.Map.SeparationLogic.
Require Export bedrock2.Array.
Require Export bedrock2.Scalars.
Require Export bedrock2.ptsto_bytes.
Require Export coqutil.Word.SimplWordExpr.
Require Import coqutil.Tactics.Simp.

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
            solve [blia]
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
  | ptsto_bytes _ ?A _ => A
  | ptsto_word ?A _ => A
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

Ltac word_rep_to_word_ok R :=
  lazymatch constr:(@eq R (word.of_Z 0)) with
  | @eq _ (@word.of_Z _ ?Inst _) => constr:(_: word.ok Inst)
  end.

Ltac wcancel :=
  cancel;
  let OK := lazymatch goal with
            | |- @iff1 (@map.rep (@word.rep ?W ?WordInst) ?V ?M) _ _ =>
              constr:(_: word.ok WordInst)
            end in
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

Ltac simpl_addrs :=
  (* note: it's the user's responsability to ensure that left-to-right rewriting with all
   nat and Z equations terminates, otherwise we'll loop infinitely here *)
  repeat match goal with
         | E: @eq ?T ?LHS _ |- _ =>
           lazymatch T with
           | Z => idtac
           | nat => idtac
           end;
           progress prewrite LHS E
         (* inside the loop because the above rewriting can create new opportunities for simpl_Z_nat *)
         | |- _ => progress simpl_Z_nat
         end.

(* Note that "rewr" only works with equalities, not with iff1, so we use
   iff1ToEq to turn iff1 into eq (requires functional and propositionl extensionality).
   Alternatively, we could use standard rewrite (which might instantiate too many evars),
   or we could make a "seprewrite" which works on "seps [...] [...]" by replacing the
   i-th clause on any side with the rhs of the provided iff1, or we could make a
   seprewrite which first puts the clause to be replaced as the left-most, and then
   eapplies a "Proper_sep_iff1: Proper (iff1 ==> iff1 ==> iff1) sep", but that would
   change the order of the clauses. *)
Ltac get_array_rewr_eq t :=
  lazymatch t with
  | context [ array ?PT ?SZ ?start (?xs ++ ?ys) ] =>
    constr:(iff1ToEq (array_append' PT SZ xs ys start))
  | context [ array ?PT ?SZ ?start (?x :: ?xs) ] =>
    constr:(iff1ToEq (array_cons PT SZ x xs start))
  | context [ array ?PT ?SZ ?start nil ] =>
    constr:(iff1ToEq (array_nil PT SZ start))
  end.

Ltac array_app_cons_sep := rewr get_array_rewr_eq in *.

Ltac wseplog_pre :=
  repeat (autounfold with unf_to_array);
  repeat ( rewr get_array_rewr_eq in |-* ).

Ltac wwcancel :=
  wseplog_pre;
  simpl_addrs;
  wcancel.

Ltac wcancel_assumption := use_sep_assumption; wwcancel.
