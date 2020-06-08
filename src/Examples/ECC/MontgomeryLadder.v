Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.ECC.Field.
Require Import Rupicola.Examples.ECC.Point.
Require Import Rupicola.Examples.ECC.DownTo.
Require Import Rupicola.Examples.ECC.CondSwap.
Local Open Scope Z_scope.

(* TODO: figure out recursive notation here and move to Notations *)
Local Notation
      "'let/d' '''(' x , y ')' := val 'in' body" :=
  (dlet val
        (fun v =>
           let x := fst v in
           let y := snd v in
           body))
    (at level 4, only parsing).
Local Notation
      "'let/d' '''(' x , y , z ')' := val 'in' body" :=
  (dlet val
        (fun v =>
           let x := fst (fst v) in
           let y := snd (fst v) in
           let z := snd v in
           body))
    (at level 4, only parsing).

(* TODO: copy the specs back over into fiat-crypto and prove that they are
   obeyed to validate the slight rephrasings here *)
Section __.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}.
  Context {bignum_representaton : BignumRepresentation}.
  Existing Instances spec_of_mul spec_of_square spec_of_add
           spec_of_sub spec_of_scmula24 spec_of_inv spec_of_bignum_copy.

  Context {relax_bounds :
             forall X : bignum,
               bounded_by tight_bounds X ->
               bounded_by loose_bounds X}.
  Hint Resolve relax_bounds : compiler.

  Section Gallina.
    Local Infix "+" := (fun x y => (x + y) mod M).
    Local Infix "-" := (fun x y => (x - y) mod M).
    Local Infix "*" := (fun x y => (x * y) mod M).
    Local Infix "^" := (fun x y => (x ^ y) mod M).

    Definition ladderstep_gallina
               (X1: Z) (P1 P2: point)  : (point * point) :=
      let '(X2, Z2) := P1 in
      let '(X3, Z3) := P2 in
      let/d A := X2+Z2 in
      let/d AA := A^2 in
      let/d B := X2-Z2 in
      let/d BB := B^2 in
      let/d E := AA-BB in
      let/d C := X3+Z3 in
      let/d D := X3-Z3 in
      let/d DA := D*A in
      let/d CB := C*B in
      let/d X5 := (DA+CB)^2 in
      let/d Z5 := X1*(DA-CB)^2 in
      let/d X4 := AA*BB in
      let/dZ4 := E*(AA + a24*E) in
      ((X4, Z4), (X5, Z5)).

    Definition montladder bound (testbit:nat->bool) (u:Z) : Z :=
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
              let/d swap := s_i in
              let/d ''(P1, P2) := ladderstep_gallina u P1 P2 in
              (P1, P2, swap)
           ) in
      let/d ''(P1, P2) := cswap swap P1 P2 in
      let '(x, z) := P1 in
      let/d r := (x * Finv z) in
      r.
  End Gallina.

  (* single predicate for all ladderstep end-state information *)
  (* N.B. it's important to leave the associativity of the predicate so that the
     emp is separated from the rest. This way, sepsimpl can easily pull it
     out. If sepsimpl is improved to handle very nested emps, this will not be
     necessary. *)
  Definition LadderStepResult
             (X1 X2 Z2 X3 Z3 : bignum)
             (pX1 pX2 pZ2 pX3 pZ3 : Semantics.word)
             (pA pAA pB pBB pE pC pD pDA pCB : Semantics.word)
             (result : point * point)
    : Semantics.mem -> Prop :=
    (liftexists X4 Z4 X5 Z5 (* output values *)
                A' AA' B' BB' E' C' D' DA' CB' (* new intermediates *)
     : bignum,
       (emp (result = ((eval X4 mod M, eval Z4 mod M),
                       (eval X5 mod M, eval Z5 mod M))
             /\ bounded_by tight_bounds X4
             /\ bounded_by tight_bounds Z4
             /\ bounded_by tight_bounds X5
             /\ bounded_by tight_bounds Z5)
        * (Bignum pX1 X1 * Bignum pX2 X4 * Bignum pZ2 Z4
           * Bignum pX3 X5 * Bignum pZ3 Z5
           * Bignum pA A' * Bignum pAA AA'
           * Bignum pB B' * Bignum pBB BB'
           * Bignum pE E' * Bignum pC C' * Bignum pD D'
           * Bignum pDA DA' * Bignum pCB CB'))%sep).

  Instance spec_of_ladderstep : spec_of "ladderstep" :=
    forall! (X1 X2 Z2 X3 Z3 A AA B BB E C D DA CB : bignum)
          (pX1 pX2 pZ2 pX3 pZ3
               pA pAA pB pBB pE pC pD pDA pCB : Semantics.word),
      (fun R m =>
        bounded_by tight_bounds X1
        /\ bounded_by tight_bounds X2
        /\ bounded_by tight_bounds Z2
        /\ bounded_by tight_bounds X3
        /\ bounded_by tight_bounds Z3
        /\ (Bignum pX1 X1
            * Bignum pX2 X2 * Bignum pZ2 Z2
            * Bignum pX3 X3 * Bignum pZ3 Z3
            * Placeholder pA A * Placeholder pAA AA
            * Placeholder pB B * Placeholder pBB BB
            * Placeholder pE E * Placeholder pC C
            * Placeholder pD D * Placeholder pDA DA
            * Placeholder pCB CB * R)%sep m)
        ===>
        "ladderstep" @ [pX1; pX2; pZ2; pX3; pZ3; pA; pAA; pB; pBB; pE; pC; pD; pDA; pCB]
        ===>
        (LadderStepResult
           X1 X2 Z2 X3 Z3 pX1 pX2 pZ2 pX3 pZ3
           pA pAA pB pBB pE pC pD pDA pCB
           (ladderstep_gallina
              (eval X1) (eval X2, eval Z2) (eval X3, eval Z3))).

  Section MontLadder.
    Context (testbit: string) (testbit_gallina : nat -> bool)
            (bound : word)
            (one zero : bignum) (eval_one : eval one = 1)
            (eval_zero : eval zero = 0).

    Instance spec_of_literal0 : spec_of (bignum_literal 0) :=
      spec_of_bignum_literal zero (bignum_literal 0).
    Instance spec_of_literal1 : spec_of (bignum_literal 1) :=
      spec_of_bignum_literal one (bignum_literal 1).

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
    (* TODO: should montladder return a pointer to the result, or just write
       into P1? *)
    Definition MontLadderResult
               (X1 : bignum) (pX1 : Semantics.word)
               (pU pZ1 pX2 pZ2 pA pAA pB pBB pE pC pD pDA pCB : Semantics.word)
               (result : Z)
      : Semantics.mem -> Prop :=
      (liftexists U' Z1' X2' Z2' A' AA' B' BB' E' C' D' DA' CB' : bignum,
         (emp (result = eval X1 mod M)
         * (Bignum pU U' * Bignum pX1 X1 * Bignum pZ1 Z1'
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
           /\ 0 < word.unsigned bound
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
          [bound; pU; pX1; pZ1; pX2; pZ2; pA; pAA; pB; pBB; pE; pC; pD; pDA; pCB]
          ===>
          (MontLadderResult
             U pU pX1 pZ1 pX2 pZ2 pA pAA pB pBB pE pC pD pDA pCB
             (montladder
                (Z.to_nat (word.unsigned bound)) testbit_gallina (eval U))).

    Ltac compile_custom ::=
      first [ simple eapply compile_downto
            | gen_sym_inc;
              let name := gen_sym_fetch "v" in
              simple eapply compile_testbit with (var:=name)
            | simple eapply compile_point_assign
            | simple eapply compile_bignum_literal
            | simple eapply compile_bignum_copy
            | simple eapply compile_cswap_nocopy ].

    Definition downto_state
               (locals : Semantics.locals)
               X1_var Z1_var X2_var Z2_var swap_var si_var :=
      fun l (st : point * point * bool) =>
        let '(P1, P2, swap) := st in
        let '(X1z, Z1z) := P1 in
        let '(X2z, Z2z) := P2 in
        liftexists X1 Z1 X2 Z2 X1_ptr Z1_ptr X2_ptr Z2_ptr,
        (emp (map.only_differ
                locals
                (PropSet.of_list [swap_var; X1_var; Z1_var;
                                    X2_var; Z2_var; si_var]) l
              /\ map.get l swap_var = Some (word.of_Z (Z.b2z swap))
              /\ map.get l X1_var = Some X1_ptr
              /\ map.get l Z1_var = Some Z1_ptr
              /\ map.get l X2_var = Some X2_ptr
              /\ map.get l Z2_var = Some Z2_ptr
              /\ eval X1 = X1z
              /\ eval Z1 = Z1z
              /\ eval X2 = X2z
              /\ eval Z2 = Z2z)
         * (Bignum X1_ptr X1 * Bignum Z1_ptr Z1
            * Bignum X2_ptr X2 * Bignum Z2_ptr Z2))%sep.

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
      cbv [downto_state];
      repeat lazymatch goal with
               | |- Lift1Prop.ex1 _ _ => eexists
               | _ => progress sepsimpl
             end;
      lazymatch goal with
      | |- eval _ = _ => exact eq_refl
      | |- sep _ _ _ => ecancel_assumption
      | _ => idtac
      end;
      lazymatch goal with
      | |- map.get _ _ = Some _ =>
        subst_lets_in_goal; solve_map_get_goal
      | |- map.only_differ _ _ _ =>
        solve [eauto using map_only_differ_subset,
               of_list_subset_singleton,
               map_only_differ_put_r]
      end.

    Derive montladder_body SuchThat
           (let args := ["bound"; "U"; "X1"; "Z1"; "X2"; "Z2";
                           "A"; "AA"; "B"; "BB"; "E"; "C"; "D"; "DA"; "CB"] in
            let montladder := ("montladder", (args, [], montladder_body)) in
            program_logic_goal_for
              montladder
              (ltac:(
                 let callees :=
                     constr:([(bignum_literal 0); (bignum_literal 1);
                                bignum_copy; "ladderstep"; testbit]) in
                 let x := program_logic_goal_for_function
                                montladder callees in
                     exact x)))
           As montladder_body_correct.
    Proof.
      cbv [program_logic_goal_for spec_of_montladder].
      cbv [spec_of_literal0 spec_of_literal1].
      rewrite <-eval_one, <-eval_zero.
      setup.
      repeat safe_compile_step.

      rewrite Z2Nat.id in * by apply word.unsigned_range.

      let si_var := constr:("si") in
      let i := constr:("i") in
      let locals := lazymatch goal with
                    | |- WeakestPrecondition.cmd _ _ _ _ ?l _ => l end in
      simple eapply compile_downto with
                          (i_var := i)
                          (State := downto_state locals _ _ _ _ _ si_var);
        lazymatch goal with
        | |- sep _ _ _ => prove_downto_state_ok
        | |- word.unsigned _ = Z.of_nat _ =>
          subst_lets_in_goal;
            rewrite Z2Nat.id by apply word.unsigned_range; reflexivity
        | |- (0 < _)%nat =>
          subst_lets_in_goal;
            change 0%nat with (Z.to_nat 0); apply Z2Nat.inj_lt; lia
        | _ => idtac
        end.
      2:{ (* loop body *)
        intros. repeat destruct_one_match.
        cbv [downto_state] in * |- . repeat destruct_one_match_hyp.
        sepsimpl_hyps.

        pose proof (word.unsigned_range bound).
        assert (word.unsigned wi = Z.of_nat i) by
            (subst wi; rewrite word.unsigned_of_Z, word_wrap_small by lia;
             reflexivity).
        (* need to pass in the var manually, because downto_state talks about it
        specifically *)
        (* TODO: do we actually need to know the only_differ part? *)
        eapply compile_testbit with (wi:=wi) (var:="si");
          [ solve [repeat compile_step] .. | ].

        repeat safe_compile_step.
        simple eapply compile_cswap_nocopy.
    Abort.
  End MontLadder.

  Ltac ladderstep_compile_custom :=
    repeat compile_compose_step;
    field_compile_step; [ repeat compile_step .. | ];
    (* if the output we selected was one of the inputs, need to write the
       Placeholder back into a Bignum for the arguments precondition *)
    lazymatch goal with
    | |- sep _ _ _ =>
      change Placeholder with Bignum in * |- ;
      solve [repeat compile_step]
    | _ => idtac
    end;
    [ solve [repeat compile_step] .. | intros ].

  Ltac compile_custom ::= ladderstep_compile_custom.

  Derive ladderstep_body SuchThat
         (let args := ["X1"; "X2"; "Z2"; "X3"; "Z3";
                         "A"; "AA"; "B"; "BB"; "E"; "C";
                           "D"; "DA"; "CB"] in
          let ladderstep := ("ladderstep", (args, [], ladderstep_body)) in
          program_logic_goal_for
            ladderstep
            (ltac:(let x := program_logic_goal_for_function
                              ladderstep [mul;add;sub;square;scmula24] in
                   exact x)))
    As ladderstep_body_correct.
  Proof.
    cbv [program_logic_goal_for spec_of_ladderstep].
    setup.
    repeat safe_compile_step.

    (* by now, we're out of Placeholders; need to decide (manually for now)
       where output gets stored *)
    free pX3; repeat safe_compile_step.
    free pZ3; repeat safe_compile_step.
    free pX2; repeat safe_compile_step.
    free pZ2; repeat safe_compile_step.

    (* done! now just prove postcondition *)
    compile_done. cbv [LadderStepResult].
    repeat lazymatch goal with
           | |- Lift1Prop.ex1 _ _ => eexists
           | |- sep _ _ _ =>
             first [ progress sepsimpl
                   | ecancel_assumption ]
           | _ => idtac
           end.
    all:lazymatch goal with
        | |- bounded_by _ _ => solve [auto with compiler]
        | _ => idtac
        end.
    reflexivity.
  Qed.
End __.

(*
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.
Print ladderstep_body.
*)
(* ladderstep_body =
 *  fun mul add sub square scmula24 : string =>
 *  (cmd.call [] add [expr.var "X2"; expr.var "Z2"; expr.var "A"];;
 *   cmd.call [] square [expr.var "A"; expr.var "AA"];;
 *   cmd.call [] sub [expr.var "X2"; expr.var "Z2"; expr.var "B"];;
 *   cmd.call [] square [expr.var "B"; expr.var "BB"];;
 *   cmd.call [] sub [expr.var "AA"; expr.var "BB"; expr.var "E"];;
 *   cmd.call [] add [expr.var "X3"; expr.var "Z3"; expr.var "C"];;
 *   cmd.call [] sub [expr.var "X3"; expr.var "Z3"; expr.var "D"];;
 *   cmd.call [] mul [expr.var "D"; expr.var "A"; expr.var "DA"];;
 *   cmd.call [] mul [expr.var "C"; expr.var "B"; expr.var "CB"];;
 *   cmd.call [] add [expr.var "DA"; expr.var "CB"; expr.var "X3"];;
 *   cmd.call [] square [expr.var "X3"; expr.var "X3"];;
 *   cmd.call [] sub [expr.var "DA"; expr.var "CB"; expr.var "Z3"];;
 *   cmd.call [] square [expr.var "Z3"; expr.var "Z3"];;
 *   cmd.call [] mul [expr.var "X1"; expr.var "Z3"; expr.var "Z3"];;
 *   cmd.call [] mul [expr.var "AA"; expr.var "BB"; expr.var "X2"];;
 *   cmd.call [] scmula24 [expr.var "E"; expr.var "Z2"];;
 *   cmd.call [] add [expr.var "AA"; expr.var "Z2"; expr.var "Z2"];;
 *   cmd.call [] mul [expr.var "E"; expr.var "Z2"; expr.var "Z2"];;
 *  /*skip*/)%bedrock_cmd
 *      : string -> string -> string -> string -> string -> cmd
 *)
