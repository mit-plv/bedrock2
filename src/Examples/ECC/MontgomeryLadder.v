Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.SepLocals.
Require Import Rupicola.Examples.ECC.Field.
Require Import Rupicola.Examples.ECC.Point.
Require Import Rupicola.Examples.ECC.DownTo.
Require Import Rupicola.Examples.ECC.CondSwap.
Require Import Rupicola.Examples.ECC.LadderStep.
Require Import Rupicola.Examples.ECC.ScalarField.
Local Open Scope Z_scope.

Section __.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}
          {scalar_field_parameters : ScalarFieldParameters}.
  Context {bignum_representaton : BignumRepresentation}
          {scalar_representation : ScalarRepresentation}.
  Existing Instances spec_of_mul spec_of_square spec_of_add
           spec_of_sub spec_of_scmula24 spec_of_inv spec_of_bignum_copy
           spec_of_bignum_literal spec_of_sctestbit spec_of_ladderstep.

  Context {relax_bounds :
             forall X : bignum,
               bounded_by tight_bounds X ->
               bounded_by loose_bounds X}.
  Hint Resolve relax_bounds : compiler.

  Context (bound : nat).
  Context (bound_pos : (bound > 0)%nat).

  Section Gallina.
    (* Everything in gallina-world is mod M; ideally we will use a type like
       fiat-crypto's F for this *)
    Local Notation "0" := (0 mod M).
    Local Notation "1" := (1 mod M).
    Local Infix "+" := (fun x y => (x + y) mod M).
    Local Infix "-" := (fun x y => (x - y) mod M).
    Local Infix "*" := (fun x y => (x * y) mod M).
    Local Infix "^" := (fun x y => (x ^ y) mod M).

    Definition montladder_gallina (testbit:nat ->bool) (u:Z) : Z :=
      let/d P1 := (1, 0) in
      let/d P2 := (u, 1) in
      let/d swap := false in
      let/d count := bound in
      let/d ''(P1, P2, swap) :=
         downto
           (P1, P2, swap) (* initial state *)
           count
           (fun state i =>
              let '(P1, P2, swap) := state in
              let/d s_i := testbit i in
              let/d swap := xorb swap s_i in
              let/d ''(P1, P2) := cswap swap P1 P2 in
              let/d ''(P1, P2) := ladderstep_gallina u P1 P2 in
              let/d swap := s_i in
              (P1, P2, swap)
           ) in
      let/d ''(P1, P2) := cswap swap P1 P2 in
      let '(x, z) := P1 in
      let/d r := Finv z mod M in
      let/d r := (x * r) in
      r.
  End Gallina.

  Section MontLadder.
    (* need the literal Z form of bound to give to expr.literal *)
    Context (zbound : Z)
            (zbound_small : word.wrap zbound = zbound)
            (zbound_eq : zbound = Z.of_nat bound).

    (* TODO: make Placeholder [Lift1Prop.ex1 (fun x => Bignum p x)], and prove
       an iff1 with Bignum? Then we could even do some loop over the pointers to
       construct the seplogic condition *)
    (* TODO: should montladder return a pointer to the result? Currently writes
       result into U. *)
    Definition MontLadderResult
               (K : scalar)
               (pK pU pX1 pZ1 pX2 pZ2 pA pAA pB pBB pE pC pD pDA pCB : Semantics.word)
               (result : Z)
      : Semantics.mem -> Prop :=
      (liftexists U' X1' Z1' X2' Z2' A' AA' B' BB' E' C' D' DA' CB' : bignum,
         (emp (result = eval U' mod M)
          * (Scalar pK K * Bignum pU U'
             * Bignum pX1 X1' * Bignum pZ1 Z1'
             * Bignum pX2 X2' * Bignum pZ2 Z2'
             * Bignum pA A' * Bignum pAA AA'
             * Bignum pB B' * Bignum pBB BB'
             * Bignum pE E' * Bignum pC C' * Bignum pD D'
             * Bignum pDA DA' * Bignum pCB CB'))%sep).

    Instance spec_of_montladder : spec_of "montladder" :=
      forall!
            (K : scalar)
            (U X1 Z1 X2 Z2 : bignum) (* u, P1, P2 *)
            (A AA B BB E C D DA CB : bignum) (* ladderstep intermediates *)
            (pK pU pX1 pZ1 pX2 pZ2
                pA pAA pB pBB pE pC pD pDA pCB : Semantics.word),
        (fun R m =>
           bounded_by tight_bounds U
           /\ (Scalar pK K * Bignum pU U
               * Placeholder pX1 X1 * Placeholder pZ1 Z1
               * Placeholder pX2 X2 * Placeholder pZ2 Z2
               * Placeholder pA A * Placeholder pAA AA
               * Placeholder pB B * Placeholder pBB BB
               * Placeholder pE E * Placeholder pC C
               * Placeholder pD D * Placeholder pDA DA
               * Placeholder pCB CB * R)%sep m)
          ===>
          "montladder" @
          [pK; pU; pX1; pZ1; pX2; pZ2; pA; pAA; pB; pBB; pE; pC; pD; pDA; pCB]
          ===>
          (MontLadderResult
             K pK pU pX1 pZ1 pX2 pZ2 pA pAA pB pBB pE pC pD pDA pCB
             (montladder_gallina
                (fun i => Z.testbit (sceval K) (Z.of_nat i))
                (eval U mod M))).

    Ltac apply_compile_cswap_nocopy :=
      simple eapply compile_cswap_nocopy with
        (Data :=
           fun p (X : Z) =>
             (Lift1Prop.ex1
                (fun x =>
                   (emp (eval x mod M = X mod M) * Bignum p x)%sep)))
        (tmp:="tmp");
      [ lazymatch goal with
        | |- sep _ _ _ =>
          repeat lazymatch goal with
                 | |- Lift1Prop.ex1 _ _ => eexists
                 | |- eval _ mod _ = _ => eassumption
                 | _ => progress sepsimpl
                 end; ecancel_assumption
        | _ => idtac
        end .. | ];
      [ repeat compile_step .. | ];
      [ try congruence .. | ].

    Ltac compile_custom ::=
      gen_sym_inc;
      let name := gen_sym_fetch "v" in
      cleanup;
      first [ simple eapply compile_downto
            | simple eapply compile_sctestbit with (var:=name)
            | simple eapply compile_point_assign
            | simple eapply compile_bignum_literal
            | simple eapply compile_bignum_copy
            | simple eapply compile_cswap_pair
            | apply_compile_cswap_nocopy
            | simple eapply compile_ladderstep ].

    Definition downto_inv_locals
               (K_ptr X1_ptr Z1_ptr X2_ptr Z2_ptr : word)
               (K_var X1_var Z1_var X2_var Z2_var swap_var : string)
               (gst : (word * word) * (word * word))
               (st : point * point * bool)
      : Semantics.locals -> Prop :=
      let swap := snd st in
      let X1_ptr' := fst (fst gst) in
      let Z1_ptr' := snd (fst gst) in
      let X2_ptr' := fst (snd gst) in
      let Z2_ptr' := snd (snd gst) in
      (emp ((* the pointers may be swapped from their original positions *)
           ((X1_ptr' = X1_ptr
             /\ Z1_ptr' = Z1_ptr
             /\ X2_ptr' = X2_ptr
             /\ Z2_ptr' = Z2_ptr)
            \/ (X1_ptr' = X2_ptr
                /\ Z1_ptr' = Z2_ptr
                /\ X2_ptr' = X1_ptr
                /\ Z2_ptr' = Z1_ptr)))
       * (Var swap_var (word.of_Z (Z.b2z swap)) * Var K_var K_ptr
          * Var X1_var X1_ptr' * Var Z1_var Z1_ptr'
          * Var X2_var X2_ptr' * Var Z2_var Z2_ptr'))%sep.

    Definition downto_inv
               K K_ptr
               A_ptr AA_ptr B_ptr BB_ptr E_ptr C_ptr D_ptr DA_ptr CB_ptr
               (gst : (word * word) * (word * word))
               (st : point * point * bool)
      : Semantics.mem -> Prop :=
      let P1 := fst (fst st) in
      let P2 := snd (fst st) in
      let swap := snd st in
      let X1z := fst P1 in
      let Z1z := snd P1 in
      let X2z := fst P2 in
      let Z2z := snd P2 in
      let X1_ptr := fst (fst gst) in
      let Z1_ptr := snd (fst gst) in
      let X2_ptr := fst (snd gst) in
      let Z2_ptr := snd (snd gst) in
      liftexists X1 Z1 X2 Z2 A AA B BB E C D DA CB,
        (emp (bounded_by tight_bounds X1
              /\ bounded_by tight_bounds Z1
              /\ bounded_by tight_bounds X2
              /\ bounded_by tight_bounds Z2
              /\ X1z mod M = X1z
              /\ Z1z mod M = Z1z
              /\ X2z mod M = X2z
              /\ Z2z mod M = Z2z
              /\ eval X1 mod M = X1z mod M
              /\ eval Z1 mod M = Z1z mod M
              /\ eval X2 mod M = X2z mod M
              /\ eval Z2 mod M = Z2z mod M)
         * (Scalar K_ptr K * Bignum X1_ptr X1 * Bignum Z1_ptr Z1
            * Bignum X2_ptr X2 * Bignum Z2_ptr Z2
            * Placeholder A_ptr A * Placeholder AA_ptr AA
            * Placeholder B_ptr B * Placeholder BB_ptr BB
            * Placeholder E_ptr E * Placeholder C_ptr C
            * Placeholder D_ptr D * Placeholder DA_ptr DA
            * Placeholder CB_ptr CB))%sep.

    Definition downto_ghost_step
               (K : scalar) (st : point * point * bool)
               (gst : (word * word) * (word * word)) (i : nat) :=
      let P1 := fst gst in
      let P2 := snd gst in
      let swap := snd st in
      let swap := xorb swap (Z.testbit (sceval K) (Z.of_nat i)) in
      cswap swap P1 P2.

    Ltac setup_downto_inv_init :=
      lift_eexists; sepsimpl;
      (* first fill in any map.get goals where we know the variable names *)
      lazymatch goal with
      | |- map.get _ ?x = Some _ =>
        tryif is_evar x then idtac
        else (autorewrite with mapsimpl; reflexivity)
      | _ => idtac
      end;
      lazymatch goal with
      | |- (_ * _)%sep _ => ecancel_assumption
      | _ => idtac
      end.

    Ltac solve_downto_inv_subgoals :=
      lazymatch goal with
      | |- map.get _ _ = _ => subst_lets_in_goal; solve_map_get_goal
      | |- bounded_by _ _ => solve [ auto ]
      | |- eval _ mod _ = _ =>
        subst_lets_in_goal; rewrite ?Z.mod_mod by apply M_nonzero;
        first [ reflexivity | assumption ]
      | |- ?x mod M = ?x => subst_lets_in_goal;
                            rewrite ?Z.mod_mod by apply M_nonzero; reflexivity
      | |- ?x => fail "unrecognized side condition" x
      end.

    Lemma eval_fst_cswap s a b A B :
      eval a mod M = A mod M->
      eval b mod M = B mod M ->
      eval (fst (cswap s a b)) mod M = (fst (cswap s A B)) mod M.
    Proof. destruct s; cbn; auto. Qed.

    Lemma eval_snd_cswap s a b A B :
      eval a mod M = A mod M->
      eval b mod M = B mod M ->
      eval (snd (cswap s a b)) mod M = (snd (cswap s A B)) mod M.
    Proof. destruct s; cbn; auto. Qed.

    Local Ltac swap_mod :=
      subst_lets_in_goal;
      repeat lazymatch goal with
             | H : ?x mod M = ?x |- context [cswap _ ?x] => rewrite <-H
             | H : ?x mod M = ?x |- context [cswap _ _ ?x] => rewrite <-H
             end;
      first [apply cswap_cases_fst | apply cswap_cases_snd ];
      auto using Z.mod_mod, M_nonzero.

    (* Adding word.unsigned_of_Z_1 and word.unsigned_of_Z_0 as hints to
       compiler doesn't work, presumably because of the typeclass
       preconditions. This is a hacky workaround. *)
    (* TODO: figure out a cleaner way to do this *)
    Lemma unsigned_of_Z_1 : word.unsigned (word.of_Z 1) = 1.
    Proof. exact word.unsigned_of_Z_1. Qed.
    Lemma unsigned_of_Z_0 : word.unsigned (word.of_Z 0) = 0.
    Proof. exact word.unsigned_of_Z_0. Qed.
    Hint Resolve unsigned_of_Z_0 unsigned_of_Z_1 : compiler.

    Ltac safe_compile_step :=
      compile_step;
      (* first pass fills in some evars *)
      [ repeat compile_step .. | idtac ];
      (* second pass must solve *)
      [ first [ solve [repeat compile_step]
              | solve [straightline_map_solver_locals] ] .. | idtac ].

    (* TODO: move? *)
    Ltac remove_unused_var :=
      let v :=
          (lazymatch goal with
           | |- find _ implementing ?pred ?k
                and-locals-post ?P with-locals ?l
                and-memory _ and-trace _ and-rest _ and-functions _ =>
             lazymatch k with
             | dlet _ _ => fail "compilation not complete!"
             | _ =>
               match l with
               | context [map.put _ ?n] =>
                 lazymatch P with
                 | context [n] => fail
                 | _ => n
                 end
               end
             end
           end) in
      eapply compile_unset with (var := v); [ ];
      push_map_remove.

    Derive montladder_body SuchThat
           (let args := ["K"; "U"; "X1"; "Z1"; "X2"; "Z2";
                           "A"; "AA"; "B"; "BB"; "E"; "C"; "D"; "DA"; "CB"] in
            let montladder := ("montladder", (args, [], montladder_body)) in
            program_logic_goal_for
              montladder
              (ltac:(
                 let callees :=
                     constr:([bignum_literal; bignum_copy; "ladderstep";
                                sctestbit; inv; mul]) in
                 let x := program_logic_goal_for_function
                                montladder callees in
                     exact x)))
           As montladder_body_correct.
    Proof.
      cbv [program_logic_goal_for spec_of_montladder].
      setup.
      repeat safe_compile_step.

      let locals := lazymatch goal with
                    | |- WeakestPrecondition.cmd _ _ _ _ ?l _ => l end in
      sep_from_literal_locals locals.

      let tmp_var := constr:("tmp") in
      let x2_var := constr:("X2") in
      let L := fresh "L" in
      let locals := lazymatch goal with
                    | |- WeakestPrecondition.cmd _ _ _ _ ?l _ => l end in
      remember locals as L;
        simple eapply compile_downto with
            (wcount := word.of_Z zbound)
            (ginit := ((pX1, pZ1), (pX2, pZ2)))
            (ghost_step := downto_ghost_step K)
            (Invl :=
               downto_inv_locals pK pX1 pZ1 pX2 pZ2
                                 _ _ _ x2_var _ _)
            (Inv :=
               downto_inv _ pK pA pAA pB pBB pE pC pD pDA pCB);
        [ .. | subst L | subst L ].
      { cbv [downto_inv_locals].
        sepsimpl; [ tauto | ].
        ecancel_assumption. }
      { cbv [downto_inv].
        setup_downto_inv_init.
        all:solve_downto_inv_subgoals. }
      all:
        lazymatch goal with
        | |- word.unsigned _ = _ =>
          rewrite word.unsigned_of_Z, zbound_small;
            solve [eauto using zbound_eq]
        | |- (0 < _)%nat =>
          subst_lets_in_goal;
            rewrite ?word.unsigned_of_Z, ?zbound_small; lia
        | _ => idtac
        end.
      { (* loop body *)
        intros. clear_old_seps.
        match goal with gst' := downto_ghost_step _ _ _ _ |- _ =>
                                subst gst' end.
        cbv [downto_inv downto_inv_locals] in * |-.
        destruct_products.
        sepsimpl_hyps.

        let H := fresh in
        pose proof (word.unsigned_range (word.of_Z zbound)) as H;
        rewrite word.unsigned_of_Z, zbound_small in H.
        assert (word.unsigned wi = Z.of_nat i) by
            (subst wi; rewrite word.unsigned_of_Z, word.wrap_small by lia;
             reflexivity).

        (* convert locals back to literal map using the separation-logic
           condition; an alternative would be to have all lemmas play nice with
           locals in separation logic *)
        literal_locals_from_sep.

        repeat safe_compile_step.

        match goal with
        | |- context [dlet (ladderstep_gallina _ (?x1, ?z1) (?x2, ?z2))] =>
          replace x1 with (x1 mod M) by swap_mod;
          replace z1 with (z1 mod M) by swap_mod;
          replace x2 with (x2 mod M) by swap_mod;
          replace z2 with (z2 mod M) by swap_mod
        end.

        compile_step.
        all:
          lazymatch goal with
          | |- eval _ mod _ = _ =>
            solve [eauto using eval_fst_cswap, eval_snd_cswap]
          | |- sep _ _ _ =>
            repeat seprewrite (cswap_iff1 Bignum);
              ecancel_assumption
          | _ => idtac
          end.
        all:lazymatch goal with
            | |- map.get _ _ = Some _ =>
              try solve [subst_lets_in_goal; solve_map_get_goal]
            | |- bounded_by _ (fst (cswap _ _ _)) =>
              apply cswap_cases_fst; solve [auto]
            | |- bounded_by _ (snd (cswap _ _ _)) =>
              apply cswap_cases_snd; solve [auto]
            | |- context [WeakestPrecondition.cmd] => idtac
            | _ => eauto
            end.

        repeat safe_compile_step.

        (* TODO: how can this rename happen automatically? *)
        (* the variable under "si" needs to be renamed to "swap" for the next
           iteration of the loop. *)
        let locals := lazymatch goal with
                      | |- WeakestPrecondition.cmd _ _ _ _ ?l _ => l end in
        let b := lazymatch goal with |- context [xorb ?b] => b end in
        let swap_var := lazymatch locals with
                          context [map.put _ ?x (word.of_Z (Z.b2z b))] => x end in
        eapply compile_rename_bool with (var := swap_var);
          [ solve [repeat compile_step] .. | ].
        intro.

        (* unset loop-local variables *)
        repeat remove_unused_var.

        compile_done.
        { (* prove loop body postcondition for locals (invariant held) *)
          cbv [downto_inv_locals downto_ghost_step].
          cbv [LadderStepResult] in *.
          cleanup; sepsimpl_hyps.
          sepsimpl;
            [ lazymatch goal with |- context [cswap ?b] =>
                                  destr b end;
              cbn [cswap fst snd]; tauto | ].
          clear_old_seps.
          rewrite !cswap_pair. cbn [fst snd dlet.dlet].
          let locals := match goal with |- ?P ?l => l end in
          sep_from_literal_locals locals.
          ecancel_assumption. }
        { (* prove loop body postcondition for memory (invariant held) *)
          cbv [downto_inv downto_ghost_step].
          cbv [LadderStepResult] in *.
          cleanup; sepsimpl_hyps.
          repeat match goal with
                 | H : ?x = (_, _) |- context [fst ?x] =>
                   rewrite H; progress cbn [fst snd]
                 end.
          clear_old_seps.
          rewrite cswap_pair; cbn [fst snd].
          lift_eexists.
          sepsimpl.
          all:
            (* first, resolve evars *)
            lazymatch goal with
            | |- sep _ _ _ =>
              change Placeholder with Bignum; ecancel_assumption
            | _ => idtac
            end.
          all:
            (* now solve other subgoals *)
            lazymatch goal with
            | |- eval _ mod _ = _ =>
              subst_lets_in_goal;
                rewrite ?Z.mod_mod by apply M_nonzero; reflexivity
            | |- (eval _ mod _) mod _ = _ =>
              subst_lets_in_goal;
                rewrite ?Z.mod_mod by apply M_nonzero; reflexivity
            | |- bounded_by _ _ => solve [ auto ]
            end. } }
      { (* loop done; rest of function *)
        intros.
        destruct_products.
        cbv [downto_inv downto_inv_locals] in *.
        sepsimpl_hyps.

        (* convert locals back to literal map using the separation-logic
           condition; an alternative would be to have all lemmas play nice with
           locals in separation logic *)
        literal_locals_from_sep.

        repeat safe_compile_step.

        (* pull the eval out of all the swaps so field lemmas work *)
        repeat match goal with
               | x := cswap _ _ _ |- _ => subst x
               | Ha : eval ?A mod M = ?a mod M,
                      Hb : eval ?B mod M = ?b mod M
                 |- context [fst (cswap ?s ?a ?b)] =>
                 replace (fst (cswap s a b)) with (eval (fst (cswap s A B)) mod M)
                   by (destruct s; cbn [cswap fst snd]; congruence)
               end.

        field_compile_step.
        (* TODO: factor all the below into a tactic, they are exactly copy-pasted *)
        all:
          lazymatch goal with
          | |- eval _ mod _ = _ =>
            solve [eauto using eval_fst_cswap, eval_snd_cswap]
          | |- sep _ _ _ =>
            repeat seprewrite (cswap_iff1 Bignum);
              ecancel_assumption
          | _ => idtac
          end.
        all:lazymatch goal with
            | |- map.get _ _ = Some _ =>
              try solve [subst_lets_in_goal; solve_map_get_goal]
            | |- bounded_by _ (fst (cswap _ _ _)) =>
              apply cswap_cases_fst; solve [auto]
            | |- bounded_by _ (snd (cswap _ _ _)) =>
              apply cswap_cases_snd; solve [auto]
            | |- context [WeakestPrecondition.cmd] => idtac
            | _ => eauto
            end.

        repeat safe_compile_step.

        (* the output of this last operation needs to be stored in the pointer
           for the output, so we guide the automation to the right pointer *)
        change Placeholder with Bignum in *.
        clear_old_seps.
        lazymatch goal with
        | H : context [Bignum ?p U] |- _ =>
          change (Bignum p) with (Placeholder p) in H
        end.
        field_compile_step.
        all:
          lazymatch goal with
          | |- eval _ mod _ = _ =>
            solve [eauto using eval_fst_cswap, eval_snd_cswap]
          | |- sep _ _ _ =>
              try ecancel_assumption
          | _ => idtac
          end.
        4:{
          (* TODO: make this a tactic *)
          (* create a new evar to take on the second swap clause *)
          match goal with
            |- (?P * ?R)%sep _ =>
            match P with context [cswap] => idtac end;
            is_evar R;
            let R1 := fresh "R" in
            let R2 := fresh "R" in
            evar (R1 : Semantics.mem -> Prop);
            evar (R2 : Semantics.mem -> Prop);
            unify R (sep R1 R2);
            seprewrite (cswap_iff1 Bignum)
          end.
          ecancel_assumption. }
        all:lazymatch goal with
            | |- map.get _ _ = Some _ =>
              try solve [subst_lets_in_goal; solve_map_get_goal]
            | |- bounded_by _ (fst (cswap _ _ _)) =>
              apply cswap_cases_fst; solve [auto]
            | |- bounded_by _ (snd (cswap _ _ _)) =>
              apply cswap_cases_snd; solve [auto]
            | |- context [WeakestPrecondition.cmd] => idtac
            | _ => eauto
            end.

        repeat safe_compile_step.
        compile_done.
        cbv [MontLadderResult].
        (* destruct the hypothesis identifying the new pointers as some swapping
           of the original ones *)
        match goal with H : (_ = _/\ _) \/ _|- _ =>
                        destruct H; cleanup; subst
        end.
        { lift_eexists.
          sepsimpl; [ reflexivity | ].
          ecancel_assumption. }
        { lift_eexists.
          sepsimpl; [ reflexivity | ].
          ecancel_assumption. } }
    Qed.
  End MontLadder.
End __.

(*
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.
Coercion expr.var : string >-> Syntax.expr.
Local Open Scope bedrock_expr.
Print montladder_body.
*)
(* fun (field_parameters : FieldParameters)
 *   (scalar_field_parameters : ScalarFieldParameters)
 *   (zbound : Z) =>
 * (cmd.call [] bignum_literal [(uintptr_t)1ULL; "X1"];;
 *  cmd.call [] bignum_literal [(uintptr_t)0ULL; "Z1"];;
 *  cmd.call [] bignum_copy ["U"; "X2"];;
 *  cmd.call [] bignum_literal [(uintptr_t)1ULL; "Z2"];;
 *  "v6" = (uintptr_t)0ULL;;
 *  "v7" = (uintptr_t)zboundULL;;
 *  (while ((uintptr_t)0ULL < "v7") {{
 *     "v7" = "v7" - (uintptr_t)1ULL;;
 *     cmd.call ["v8"] sctestbit ["K"; "v7"];;
 *     "v9" = "v6" .^ "v8";;
 *     (if ("v9") {{
 *        (("tmp" = "X1";;
 *          "X1" = "X2");;
 *         "X2" = "tmp");;
 *        cmd.unset "tmp"
 *      }});;
 *     (if ("v9") {{
 *        (("tmp" = "Z1";;
 *          "Z1" = "Z2");;
 *         "Z2" = "tmp");;
 *        cmd.unset "tmp"
 *      }});;
 *     cmd.call [] "ladderstep"
 *       ["U"; "X1"; "Z1"; "X2"; "Z2"; "A"; "AA"; "B"; "BB"; "E"; "C"; "D";
 *       "DA"; "CB"];;
 *     "v6" = "v8";;
 *     cmd.unset "v9";;
 *     cmd.unset "v8";;
 *     /*skip*/
 *   }});;
 *  (if ("v6") {{
 *     (("tmp" = "X1";;
 *       "X1" = "X2");;
 *      "X2" = "tmp");;
 *     cmd.unset "tmp"
 *   }});;
 *  (if ("v6") {{
 *     (("tmp" = "Z1";;
 *       "Z1" = "Z2");;
 *      "Z2" = "tmp");;
 *     cmd.unset "tmp"
 *   }});;
 *  cmd.call [] inv ["Z1"; "A"];;
 *  cmd.call [] mul ["X1"; "A"; "U"];;
 *  /*skip*/)%bedrock_cmd
 *      : FieldParameters -> ScalarFieldParameters -> Z -> cmd
 *)

(*
(* TODO: for some reason the existing notations for these don't print *)
Notation "f ( x , y )" := (cmd.call nil f (cons x (cons y nil))) (at level 40).
Notation "f ( x , y , z )" := (cmd.call nil f (cons x (cons y (cons z nil)))) (at level 40).
Notation "x ( a , b , c , d , e , f , g , h , i , j , k , l , m , n )" :=
  (cmd.call nil x (cons a (cons b (cons c (cons d (cons e (cons f (cons g (cons h (cons i (cons j (cons k (cons l (cons m (cons n nil))))))))))))))) (at level 40).
Notation "unpack! r = f ( x , y )" := (cmd.call (cons r nil) f (cons x (cons y nil))) (at level 40).

Instance fp : FieldParameters :=
  {| M_pos := (2^155-19)%positive;
     a24 := 121665;
     Finv := (fun x => x ^ (x - 2));
     mul := "fe25519_mul";
     add := "fe25519_add";
     sub := "fe25519_sub";
     square := "fe25519_square";
     scmula24 := "fe25519_scmula24";
     inv := "fe25519_inv";
     bignum_copy := "fe25519_copy";
     bignum_literal := "fe25519_encode"
  |}.

Instance sp : ScalarFieldParameters :=
  {| L_pos := (2^252 + 27742317777372353535851937790883648493)%positive;
     sctestbit := "sc25519_testbit";
  |}.

Compute (montladder_body 254).
*)
(* = ("fe25519_encode" ((uintptr_t)1ULL, "X1");;
 *     "fe25519_encode" ((uintptr_t)0ULL, "Z1");;
 *     "fe25519_copy" ("U", "X2");;
 *     "fe25519_encode" ((uintptr_t)1ULL, "Z2");;
 *     "v6" = (uintptr_t)0ULL;;
 *     "v7" = (uintptr_t)254ULL;;
 *     (while ((uintptr_t)0ULL < "v7") {{
 *        "v7" = "v7" - (uintptr_t)1ULL;;
 *        unpack! "v8" = "sc25519_testbit" ("K", "v7");;
 *        "v9" = "v6" .^ "v8";;
 *        (if ("v9") {{
 *           (("tmp" = "X1";;
 *             "X1" = "X2");;
 *            "X2" = "tmp");;
 *           cmd.unset "tmp"
 *         }});;
 *        (if ("v9") {{
 *           (("tmp" = "Z1";;
 *             "Z1" = "Z2");;
 *            "Z2" = "tmp");;
 *           cmd.unset "tmp"
 *         }});;
 *        "ladderstep" ("U", "X1", "Z1", "X2", "Z2", "A", "AA", "B",
 *        "BB", "E", "C", "D", "DA", "CB");;
 *        "v6" = "v8";;
 *        cmd.unset "v9";;
 *        cmd.unset "v8";;
 *        /*skip*/
 *      }});;
 *     (if ("v6") {{
 *        (("tmp" = "X1";;
 *          "X1" = "X2");;
 *         "X2" = "tmp");;
 *        cmd.unset "tmp"
 *      }});;
 *     (if ("v6") {{
 *        (("tmp" = "Z1";;
 *          "Z1" = "Z2");;
 *         "Z2" = "tmp");;
 *        cmd.unset "tmp"
 *      }});;
 *     "fe25519_inv" ("Z1", "A");;
 *     "fe25519_mul" ("X1", "A", "U");;
 *     /*skip*/)%bedrock_cmd
 *  : cmd
 *)
