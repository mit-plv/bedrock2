Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.ECC.Field.
Require Import Rupicola.Examples.ECC.Point.
Require Import Rupicola.Examples.ECC.DownTo.
Require Import Rupicola.Examples.ECC.CondSwap.
Require Import Rupicola.Examples.ECC.LadderStep.
Local Open Scope Z_scope.

Section __.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}.
  Context {bignum_representaton : BignumRepresentation}.
  Existing Instances spec_of_mul spec_of_square spec_of_add
           spec_of_sub spec_of_scmula24 spec_of_inv spec_of_bignum_copy
           spec_of_ladderstep.

  Context {relax_bounds :
             forall X : bignum,
               bounded_by tight_bounds X ->
               bounded_by loose_bounds X}.
  Hint Resolve relax_bounds : compiler.

  Context (bound : nat) (testbit_gallina : nat -> bool).
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

    Definition montladder_gallina (u:Z) : Z :=
      let/d P1 := (1, 0) in
      let/d P2 := (u, 1) in
      let/d swap := false in
      let/d ''(P1, P2, swap) :=
         downto
           (P1, P2, swap) (* initial state *)
           bound
           (fun state i =>
              let '(P1, P2, swap) := state in
              let/d s_i := testbit_gallina i in
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
    Context (testbit : string).
    (* need the literal Z form of bound to give to expr.literal *)
    Context (wbound : word)
            (wbound_eq : word.unsigned wbound = Z.of_nat bound).
    Context (zero : bignum) (zero_bounds : bounded_by tight_bounds zero)
            (eval_zero : eval zero mod M = 0 mod M).
    Context (one : bignum) (one_bounds : bounded_by tight_bounds one)
            (eval_one : eval one mod M = 1 mod M).

    Instance spec_of_literal0 : spec_of (bignum_literal (0 mod M)) :=
      spec_of_bignum_literal zero (bignum_literal (0 mod M)).
    Instance spec_of_literal1 : spec_of (bignum_literal (1 mod M)) :=
      spec_of_bignum_literal one (bignum_literal (1 mod M)).

    Instance spec_of_testbit : spec_of testbit :=
      fun functions =>
        forall (i : word) tr mem,
          WeakestPrecondition.call
            functions testbit tr mem [i]
            (fun tr' m' rets =>
               tr = tr' /\ mem = m'
               /\ let i_nat := Z.to_nat (word.unsigned i) in
                  rets = [word.of_Z (Z.b2z (testbit_gallina i_nat))]).

    Lemma compile_testbit :
      forall (locals: Semantics.locals) (mem: Semantics.mem)
        (locals_ok : Semantics.locals -> Prop)
        tr R functions T (pred: T -> _ -> Prop)
        (i : nat) wi i_var var k k_impl,
        spec_of_testbit functions ->
        word.unsigned wi = Z.of_nat i ->
        map.get locals i_var = Some wi ->
        let v := testbit_gallina i in
        (let head := v in
         find k_impl
         implementing (pred (k head))
         and-locals-post locals_ok
         with-locals (map.put locals var (word.of_Z (Z.b2z head)))
         and-memory mem and-trace tr and-rest R
         and-functions functions) ->
        (let head := v in
         find (cmd.seq (cmd.call [var] testbit [expr.var i_var]) k_impl)
         implementing (pred (dlet head k))
         and-locals-post locals_ok
         with-locals locals
         and-memory mem and-trace tr and-rest R
         and-functions functions).
    Proof.
      repeat straightline'.
      straightline_call.
      repeat straightline'.
      subst_lets_in_goal.
      match goal with H : word.unsigned ?wi = Z.of_nat ?i |- _ =>
                      rewrite H end.
      rewrite Nat2Z.id; eauto.
    Qed.

    (* TODO: make Placeholder [Lift1Prop.ex1 (fun x => Bignum p x)], and prove
       an iff1 with Bignum? Then we could even do some loop over the pointers to
       construct the seplogic condition *)
    (* TODO: should montladder return a pointer to the result? Currently writes
       result into U. *)
    Definition MontLadderResult
               (pU pX1 pZ1 pX2 pZ2 pA pAA pB pBB pE pC pD pDA pCB : Semantics.word)
               (result : Z)
      : Semantics.mem -> Prop :=
      (liftexists U' X1' Z1' X2' Z2' A' AA' B' BB' E' C' D' DA' CB' : bignum,
         (emp (result = eval U' mod M)
         * (Bignum pU U' * Bignum pX1 X1' * Bignum pZ1 Z1'
            * Bignum pX2 X2' * Bignum pZ2 Z2'
            * Bignum pA A' * Bignum pAA AA'
            * Bignum pB B' * Bignum pBB BB'
            * Bignum pE E' * Bignum pC C' * Bignum pD D'
            * Bignum pDA DA' * Bignum pCB CB'))%sep).

    Instance spec_of_montladder : spec_of "montladder" :=
      forall!
            (U X1 Z1 X2 Z2 : bignum) (* u, P1, P2 *)
            (A AA B BB E C D DA CB : bignum) (* ladderstep intermediates *)
            (pU pX1 pZ1 pX2 pZ2
                pA pAA pB pBB pE pC pD pDA pCB : Semantics.word),
        (fun R m =>
           bounded_by tight_bounds U
           /\ (Bignum pU U
               * Placeholder pX1 X1 * Placeholder pZ1 Z1
               * Placeholder pX2 X2 * Placeholder pZ2 Z2
               * Placeholder pA A * Placeholder pAA AA
               * Placeholder pB B * Placeholder pBB BB
               * Placeholder pE E * Placeholder pC C
               * Placeholder pD D * Placeholder pDA DA
               * Placeholder pCB CB * R)%sep m)
          ===>
          "montladder" @
          [pU; pX1; pZ1; pX2; pZ2; pA; pAA; pB; pBB; pE; pC; pD; pDA; pCB]
          ===>
          (MontLadderResult
             pU pX1 pZ1 pX2 pZ2 pA pAA pB pBB pE pC pD pDA pCB
             (montladder_gallina (eval U mod M))).

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
            | simple eapply compile_testbit with (var:=name)
            | simple eapply compile_point_assign
            | simple eapply compile_bignum_literal
            | simple eapply compile_bignum_copy
            | simple eapply compile_cswap_pair
            | apply_compile_cswap_nocopy
            | simple eapply compile_ladderstep ].

    Definition downto_state
               (locals : Semantics.locals)
               X1_ptr_orig Z1_ptr_orig X2_ptr_orig Z2_ptr_orig
               X1_var Z1_var X2_var Z2_var
               swap_var si_var tmp_var
               A_ptr AA_ptr B_ptr BB_ptr E_ptr C_ptr D_ptr DA_ptr CB_ptr :=
      fun l (st : point * point * bool) =>
        let P1 := fst (fst st) in
        let P2 := snd (fst st) in
        let swap := snd st in
        let X1z := fst P1 in
        let Z1z := snd P1 in
        let X2z := fst P2 in
        let Z2z := snd P2 in
        liftexists X1_ptr Z1_ptr X2_ptr Z2_ptr X1 Z1 X2 Z2
                   A AA B BB E C D DA CB,
        (emp (map.only_differ
                locals
                (PropSet.of_list [swap_var; X1_var; Z1_var;
                                    X2_var; Z2_var; si_var; tmp_var]) l
              (* the pointers may be swapped from their original positions *)
              /\ ((X1_ptr = X1_ptr_orig
                   /\ Z1_ptr = Z1_ptr_orig
                   /\ X2_ptr = X2_ptr_orig
                   /\ Z2_ptr = Z2_ptr_orig)
                  \/ (X1_ptr = X2_ptr_orig
                      /\ Z1_ptr = Z2_ptr_orig
                      /\ X2_ptr = X1_ptr_orig
                      /\ Z2_ptr = Z1_ptr_orig))
              /\ map.get l swap_var = Some (word.of_Z (Z.b2z swap))
              /\ map.get l X1_var = Some X1_ptr
              /\ map.get l Z1_var = Some Z1_ptr
              /\ map.get l X2_var = Some X2_ptr
              /\ map.get l Z2_var = Some Z2_ptr
              /\ map.get l tmp_var = None
              /\ bounded_by tight_bounds X1
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
         * (Bignum X1_ptr X1 * Bignum Z1_ptr Z1
            * Bignum X2_ptr X2 * Bignum Z2_ptr Z2
            * Placeholder A_ptr A * Placeholder AA_ptr AA
            * Placeholder B_ptr B * Placeholder BB_ptr BB
            * Placeholder E_ptr E * Placeholder C_ptr C
            * Placeholder D_ptr D * Placeholder DA_ptr DA
            * Placeholder CB_ptr CB))%sep.

    (* TODO: look in fiat-crypto Bedrock/Util for similar lemmas *)
    (* TODO: move *)
    Lemma map_only_differ_put_r m k v :
      map.only_differ m (PropSet.singleton_set k) (map.put m k v).
    Admitted.
    Lemma map_only_differ_subset m1 m2 ks1 ks2 :
      PropSet.subset ks1 ks2 ->
      map.only_differ m1 ks1 m2 ->
      map.only_differ m1 ks2 m2.
    Admitted.
    Lemma of_list_subset_singleton {E} x l :
      @PropSet.subset E (PropSet.singleton_set x) (PropSet.of_list l).
    Admitted.
    Lemma map_get_only_differ_excl_r m1 m2 k ks :
      map.only_differ m1 ks m2 ->
      ~ PropSet.elem_of k ks ->
      map.get m2 k = map.get m1 k.
    Admitted.
    Lemma of_list_elem_of_In {E} l (k : E) :
      PropSet.elem_of k (PropSet.of_list l) <-> In k l.
    Admitted.

    Lemma word_of_small_nat n :
      (Z.of_nat n < 2 ^ Semantics.width) ->
      word.unsigned (word.of_Z (Z.of_nat n)) = Z.of_nat n.
    Admitted.
    Hint Resolve word_of_small_nat : compiler.

    Lemma word_wrap_small x :
      (0 <= x < 2 ^ Semantics.width) ->
      word.wrap x = x.
    Proof. apply Z.mod_small. Qed.

    Ltac prove_downto_state_ok :=
      match goal with
        |- context [downto_state _ ?pX1 ?pZ1 ?pX2 ?pZ2] =>
        cbv[downto_state];
        apply sep_ex1_l; exists pX1;
        apply sep_ex1_l; exists pZ1;
        apply sep_ex1_l; exists pX2;
        apply sep_ex1_l; exists pZ2
      end;
      lift_eexists; sepsimpl;
      (* first fill in any map.get goals where we know the variable names *)
      lazymatch goal with
      | |- map.get _ ?x = Some _ =>
        tryif is_evar x then idtac
        else (autorewrite with mapsimpl; reflexivity)
      | _ => idtac
      end;
      lazymatch goal with
      | |- eval _ mod _ = _ =>
        subst_lets_in_goal;
        rewrite ?Z.mod_mod by apply M_nonzero; reflexivity
      | |- sep _ _ _ => ecancel_assumption
      | _ => idtac
      end;
      lazymatch goal with
      | |- map.get _ _ = _ => subst_lets_in_goal; solve_map_get_goal
      | |- map.only_differ _ _ _ =>
        solve
          [ eauto using map_only_differ_subset, of_list_subset_singleton,
            map_only_differ_put_r ]
      | |- bounded_by _ _ => solve [ auto ]
      | |- ?x mod M = ?x => subst_lets_in_goal;
                            rewrite ?Z.mod_mod by apply M_nonzero; reflexivity
      | |- _ \/ _ => left; ssplit; congruence
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

    Axiom admitt : forall {T}, T.

    Derive montladder_body SuchThat
           (let args := ["U"; "X1"; "Z1"; "X2"; "Z2";
                           "A"; "AA"; "B"; "BB"; "E"; "C"; "D"; "DA"; "CB"] in
            let montladder := ("montladder", (args, [], montladder_body)) in
            program_logic_goal_for
              montladder
              (ltac:(
                 let callees :=
                     constr:([(bignum_literal (0 mod M));
                                (bignum_literal (1 mod M));
                                bignum_copy; "ladderstep"; testbit;
                                  inv; mul]) in
                 let x := program_logic_goal_for_function
                                montladder callees in
                     exact x)))
           As montladder_body_correct.
    Proof.
      cbv [program_logic_goal_for spec_of_montladder].
      cbv [spec_of_literal0 spec_of_literal1].
      replace (bignum_literal (0 mod M))
        with (bignum_literal (eval zero mod M))
        by (rewrite eval_zero; reflexivity).
      replace (bignum_literal (1 mod M))
        with (bignum_literal (eval one mod M))
        by (rewrite eval_one; reflexivity).
      setup.
      repeat safe_compile_step.

      let tmp_var := constr:("tmp") in
      let si_var := constr:("si") in
      let x2_var := constr:("X2") in
      let i := constr:("i") in
      let locals := lazymatch goal with
                    | |- WeakestPrecondition.cmd _ _ _ _ ?l _ => l end in
      simple eapply compile_downto with
                          (i_var := i)
                          (State := downto_state
                                      locals
                                      pX1 pZ1 pX2 pZ2
                                      _ _ x2_var _ _ si_var tmp_var
                                       pA pAA pB pBB pE pC pD pDA pCB);
        lazymatch goal with
        | |- sep _ _ _ => prove_downto_state_ok
        | _ => idtac
        end;
      lazymatch goal with
        | |- word.unsigned _ = Z.of_nat _ =>
          apply wbound_eq
        | |- (0 < _)%nat => subst_lets_in_goal; lia
        | _ => idtac
        end.
      2:{ (* loop body *)
        intros. repeat destruct_one_match.
        (* clear unnecessary locals hypothesis *)
        match goal with H : _ = downto' _ _ _ _ |- _ =>
                        clear H
        end.
        match goal with
          H : context [downto_state] |- _ =>
          match type of H with (?P (?p1, ?p2, ?swap) * ?R)%sep _ =>
                               destruct p1, p2
          end;
            cbv [downto_state] in H
        end.
        sepsimpl_hyps.

        pose proof (word.unsigned_range wbound).
        assert (word.unsigned wi = Z.of_nat i) by
            (subst wi; rewrite word.unsigned_of_Z, word_wrap_small by lia;
             reflexivity).

        (* Since the loop invariant discusses a specific whitelist of variables,
           we need to pass in si specifically *)
        eapply compile_testbit with (wi:=wi) (var:="si");
          [ solve [repeat compile_step] .. | ].

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
        all:
          match goal with
          | H : map.only_differ ?m1 ?ks _
            |- map.get ?m2 ?k = ?val =>
            let H' := fresh in
            subst_lets_in_goal;
            assert (map.get m1 k = val) as H' by solve_map_get_goal;
              autorewrite with mapsimpl;
              erewrite map_get_only_differ_excl_r;
              [ solve [apply H'] | exact H | ]; clear H';
              cbn [In PropSet.elem_of PropSet.of_list];
              clear; intuition; congruence
          | _ => idtac
          end.

        repeat safe_compile_step.

        (* TODO: how can this rename happen automatically? *)
        (* the variable under "si" needs to be renamed to "swap" for the next
           iteration of the loop. *)
        let swap_var := lazymatch goal with
                          H : map.get _ ?x = Some (word.of_Z (Z.b2z _)) |- _ =>
                          x end in
        eapply compile_rename_bool with (var := swap_var);
          [ solve [repeat compile_step] | ].

        compile_done.
        { (* instantiate step_locals *)
          (* N.B. The QED will fail if step_locals is illegally instantiated
             with an expression that relies on state variables, even though the
             tactics will allow it (see
             https://github.com/coq/coq/issues/9937). Therefore, we need to
             manually replace all references to state variables with lookups in
             the locals. *)

          pose (get_or_default :=
                  fun l v => match map.get l v with
                             | Some x => x
                             | None => word.of_Z 0
                             end).
          subst_lets_in_goal.
          let li := lazymatch goal with |- ?step ?li _ = _ => li end in
          repeat match goal with
                 | H : map.get l ?v = Some ?x |- context [?x] =>
                   replace x with (get_or_default li v)
                     by (subst get_or_default; cbv beta;
                         autorewrite with mapsimpl;
                         rewrite H; reflexivity)
                 | H : map.get l ?v = Some (word.of_Z (Z.b2z ?b))
                   |- context [?b] =>
                   replace b with
                       (Z.testbit (word.unsigned (get_or_default li v)) 0)
                     by (subst get_or_default; cbv beta;
                         autorewrite with mapsimpl;
                         rewrite H, word_unsigned_of_Z_b2z;
                         apply Z.b2z_bit0)
                 end.
          subst_lets_in_goal. cbv beta.
          let p :=
              lazymatch goal with
              | |- ?step ?l ?i = ?rhs =>
                  let p := lazymatch (eval pattern i in rhs)
                           with ?f _ => f end in
                  let p := lazymatch (eval pattern l in p)
                           with ?f _ => f end in
                  p
              end in
          instantiate (1:=p).
          reflexivity. }
        { (* prove loop body postcondition (invariant held) *)
          clear_old_seps.
          cbv [LadderStepResult] in *.
          cleanup; sepsimpl_hyps.
          match goal with
          | H : ?x = (_, _) |- context [fst ?x] =>
            rewrite H; progress cbn [fst snd]
          end.
          cbv[downto_state]; lift_eexists.
          sepsimpl.
          all:
          lazymatch goal with
          | |- eval _ mod _ = _ =>
            subst_lets_in_goal;
              rewrite ?Z.mod_mod by apply M_nonzero; reflexivity
          | |- (eval _ mod _) mod _ = _ =>
            subst_lets_in_goal;
              rewrite ?Z.mod_mod by apply M_nonzero; reflexivity
          | |- sep _ _ _ =>
            change Placeholder with Bignum; ecancel_assumption
          | _ => idtac
          end.
          all:
            lazymatch goal with
            | |- bounded_by _ _ => solve [ auto ]
            | |- map.get _ _ = Some _ =>
              subst_lets_in_goal;
                repeat match goal with
                       | H : map.get _ _ = Some _ |- _ => rewrite H
                       | _ => rewrite word_unsigned_of_Z_b2z, Z.b2z_bit0
                       | _ => progress autorewrite with mapsimpl
                       end;
                reflexivity
            | |- map.get _ _ = None =>
              subst_lets_in_goal;
                repeat match goal with
                       | H : map.get _ _ = Some _ |- _ => rewrite H
                       | _ => rewrite word_unsigned_of_Z_b2z, Z.b2z_bit0
                       | _ => progress autorewrite with mapsimpl
                       end;
                solve_map_get_goal
            | |- _ \/ _ =>
              cbv [cswap];
                destruct_one_match; cbn [fst snd]; tauto
            | _ => idtac
            end.
          subst_lets_in_goal.
          (* TODO: this is the proof of only_differ, and requires only_differ_trans as well as annoying elimination of other variables. Not bothering right now because it might not be worth it if I'm going to change the local-variables reasoning anyway *)
          apply admitt. } }
      { (* step_locals won't change i *)
        intros. cbv beta.
        autorewrite with mapsimpl.
        reflexivity. }
      { (* loop done; rest of function *)
        intros.
        match goal with H : _ = downto _ _ _ |- _ => clear H end.
        match goal with
          H : context [downto_state] |- _ =>
          match type of H with (?P ?st * ?R)%sep _ =>
                               destruct st as [ [ [? ?] [? ?] ] ?]
          end;
            cbv [downto_state] in H
        end.
        sepsimpl_hyps.

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
        all:
          match goal with
          | H : map.only_differ ?m1 ?ks _
            |- map.get ?m2 ?k = ?val =>
            let H' := fresh in
            subst_lets_in_goal;
            assert (map.get m1 k = val) as H' by solve_map_get_goal;
              autorewrite with mapsimpl;
              erewrite map_get_only_differ_excl_r;
              [ solve [apply H'] | exact H | ]; clear H';
              cbn [In PropSet.elem_of PropSet.of_list];
              clear; intuition; congruence
          | _ => idtac
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
        all:
          match goal with
          | H : map.only_differ ?m1 ?ks _
            |- map.get ?m2 ?k = ?val =>
            let H' := fresh in
            subst_lets_in_goal;
            assert (map.get m1 k = val) as H' by solve_map_get_goal;
              autorewrite with mapsimpl;
              erewrite map_get_only_differ_excl_r;
              [ solve [apply H'] | exact H | ]; clear H';
              cbn [In PropSet.elem_of PropSet.of_list];
              clear; intuition; congruence
          | _ => idtac
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

(* TODO:
   - fix downto to plug in a literal z instead of Z.of_nat for bound -- maybe require it to be a variable and take it in as an argument
   - fix naming of bignum literal functions
*)
(*
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.
Print montladder_body.
*)
(* montladder_body =
 * fun (semantics : Semantics.parameters)
 *   (field_parameters : FieldParameters)
 *   (bignum_representaton : BignumRepresentation) (testbit : string)
 *   (bound : word) (one zero : bignum) =>
 * (cmd.call [] (bignum_literal (eval one mod M)) [expr.var "X1"];;
 *  cmd.call [] (bignum_literal (eval zero mod M)) [expr.var "Z1"];;
 *  cmd.call [] bignum_copy [expr.var "U"; expr.var "X2"];;
 *  cmd.call [] (bignum_literal (eval one mod M)) [expr.var "Z2"];;
 *  "v6" = (uintptr_t)0ULL;;
 *  ("i" = (uintptr_t)Z.of_nat boundULL;;
 *   while ((uintptr_t)0ULL < expr.var "i") {{
 *     "i" = expr.var "i" - (uintptr_t)1ULL;;
 *     cmd.call ["si"] testbit [expr.var "i"];;
 *     "v8" = expr.var "v6" .^ expr.var "si";;
 *     (if (expr.var "v8") {{
 *        (("tmp" = expr.var "X1";;
 *          "X1" = expr.var "X2");;
 *         "X2" = expr.var "tmp");;
 *        cmd.unset "tmp"
 *      }});;
 *     (if (expr.var "v8") {{
 *        (("tmp" = expr.var "Z1";;
 *          "Z1" = expr.var "Z2");;
 *         "Z2" = expr.var "tmp");;
 *        cmd.unset "tmp"
 *      }});;
 *     cmd.call [] "ladderstep"
 *       [expr.var "U"; expr.var "X1"; expr.var "Z1";
 *       expr.var "X2"; expr.var "Z2"; expr.var "A";
 *       expr.var "AA"; expr.var "B"; expr.var "BB";
 *       expr.var "E"; expr.var "C"; expr.var "D"; expr.var "DA";
 *       expr.var "CB"];;
 *     "v6" = expr.var "si";;
 *     /*skip*/
 *   }});;
 *  (if (expr.var "v6") {{
 *     (("tmp" = expr.var "X1";;
 *       "X1" = expr.var "X2");;
 *      "X2" = expr.var "tmp");;
 *     cmd.unset "tmp"
 *   }});;
 *  (if (expr.var "v6") {{
 *     (("tmp" = expr.var "Z1";;
 *       "Z1" = expr.var "Z2");;
 *      "Z2" = expr.var "tmp");;
 *     cmd.unset "tmp"
 *   }});;
 *  cmd.call [] inv [expr.var "Z1"; expr.var "A"];;
 *  cmd.call [] mul [expr.var "X1"; expr.var "A"; expr.var "U"];;
 *  /*skip*/)%bedrock_cmd
 *      : forall semantics : Semantics.parameters,
 *        FieldParameters ->
 *        forall bignum_representaton : BignumRepresentation,
 *        nat -> string -> word -> bignum -> bignum -> cmd
 *)
