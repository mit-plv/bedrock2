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
    (* Everything in gallina-world is mod M; ideally we will use a type like
       fiat-crypto's F for this *)
    Local Notation "0" := (0 mod M).
    Local Notation "1" := (1 mod M).
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
              (eval X1 mod M) (eval X2 mod M, eval Z2 mod M)
              (eval X3 mod M, eval Z3 mod M))).

  Section MontLadder.
    Context (testbit: string) (testbit_gallina : nat -> bool)
            (bound : word) (one zero : bignum)
            (one_bounds : bounded_by tight_bounds one)
            (zero_bounds : bounded_by tight_bounds zero)
            (eval_one : eval one mod M = 1 mod M)
            (eval_zero : eval zero mod M = 0 mod M).

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

    (* TODO: move, make more types *)
    Lemma compile_rename_bool :
      forall (locals: Semantics.locals) (mem: Semantics.mem)
        (locals_ok : Semantics.locals -> Prop)
        tr R functions T (pred: T -> _ -> Prop)
        x x_var var k k_impl,
        map.get locals x_var = Some (word.of_Z (Z.b2z x)) ->
        let v := x in
        (let head := v in
         find k_impl
         implementing (pred (k head))
         and-locals-post locals_ok
         with-locals (map.put locals var (word.of_Z (Z.b2z x)))
         and-memory mem and-trace tr and-rest R
         and-functions functions) ->
        (let head := v in
         find (cmd.seq (cmd.set var (expr.var x_var)) k_impl)
         implementing (pred (dlet head k))
         and-locals-post locals_ok
         with-locals locals
         and-memory mem and-trace tr and-rest R
         and-functions functions).
    Proof.
      repeat straightline'. eauto.
    Qed.

    Lemma compile_ladderstep :
      forall (locals: Semantics.locals) (mem: Semantics.mem)
        (locals_ok : Semantics.locals -> Prop)
        tr R R' functions T (pred: T -> _ -> Prop)
        x1 x2 z2 x3 z3
        X1 X1_ptr X1_var X2 X2_ptr X2_var Z2 Z2_ptr Z2_var
        X3 X3_ptr X3_var Z3 Z3_ptr Z3_var
        A A_ptr A_var AA AA_ptr AA_var B B_ptr B_var BB BB_ptr BB_var
        E E_ptr E_var C C_ptr C_var D D_ptr D_var
        DA DA_ptr DA_var CB CB_ptr CB_var
        k k_impl,
        spec_of_ladderstep functions ->
        eval X1 mod M = x1 mod M ->
        eval X2 mod M = x2 mod M ->
        eval Z2 mod M = z2 mod M ->
        eval X3 mod M = x3 mod M ->
        eval Z3 mod M = z3 mod M ->
        bounded_by tight_bounds X1 ->
        bounded_by tight_bounds X2 ->
        bounded_by tight_bounds Z2 ->
        bounded_by tight_bounds X3 ->
        bounded_by tight_bounds Z3 ->
        (Bignum X1_ptr X1
         * Bignum X2_ptr X2 * Bignum Z2_ptr Z2
         * Bignum X3_ptr X3 * Bignum Z3_ptr Z3
         * Placeholder A_ptr A * Placeholder AA_ptr AA
         * Placeholder B_ptr B * Placeholder BB_ptr BB
         * Placeholder E_ptr E * Placeholder C_ptr C
         * Placeholder D_ptr D * Placeholder DA_ptr DA
         * Placeholder CB_ptr CB * R')%sep mem ->
        map.get locals X1_var = Some X1_ptr ->
        map.get locals X2_var = Some X2_ptr ->
        map.get locals Z2_var = Some Z2_ptr ->
        map.get locals X3_var = Some X3_ptr ->
        map.get locals Z3_var = Some Z3_ptr ->
        map.get locals A_var = Some A_ptr ->
        map.get locals AA_var = Some AA_ptr ->
        map.get locals B_var = Some B_ptr ->
        map.get locals BB_var = Some BB_ptr ->
        map.get locals E_var = Some E_ptr ->
        map.get locals C_var = Some C_ptr ->
        map.get locals D_var = Some D_ptr ->
        map.get locals DA_var = Some DA_ptr ->
        map.get locals CB_var = Some CB_ptr ->
        let v := ladderstep_gallina
                   (x1 mod M) (x2 mod M, z2 mod M) (x3 mod M, z3 mod M) in
        (let head := v in
         forall m,
           (LadderStepResult
             X1 X2 Z2 X3 Z3 X1_ptr X2_ptr Z2_ptr X3_ptr
             Z3_ptr A_ptr AA_ptr B_ptr BB_ptr E_ptr C_ptr D_ptr DA_ptr
             CB_ptr head * R')%sep m ->
           (find k_impl
            implementing (pred (k head))
            and-locals-post locals_ok
            with-locals locals
            and-memory m and-trace tr and-rest R
            and-functions functions)) ->
        (let head := v in
         find (cmd.seq
                 (cmd.call [] "ladderstep"
                           [ expr.var X1_var; expr.var X2_var;
                               expr.var Z2_var; expr.var X3_var;
                                 expr.var Z3_var; expr.var A_var;
                                   expr.var AA_var; expr.var B_var;
                                     expr.var BB_var; expr.var E_var;
                                       expr.var C_var; expr.var D_var;
                                         expr.var DA_var; expr.var CB_var ])

                 k_impl)
         implementing (pred (dlet head k))
         and-locals-post locals_ok
         with-locals locals
         and-memory mem and-trace tr and-rest R
         and-functions functions).
    Proof.
      repeat straightline'.
      handle_call; [ solve [eauto] .. | ].
      repeat match goal with H : eval _ mod _ = _ |- _ =>
                             rewrite H in * end.
      auto.
    Qed.

    (* TODO: make Placeholder [Lift1Prop.ex1 (fun x => Bignum p x)], and prove
       an iff1 with Bignum? Then we could even do some loop over the pointers to
       construct the seplogic condition *)
    (* TODO: should montladder return a pointer to the result, or just write
       into P1? *)
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
             pU pX1 pZ1 pX2 pZ2 pA pAA pB pBB pE pC pD pDA pCB
             (montladder
                (Z.to_nat (word.unsigned bound))
                testbit_gallina
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

    (* TODO: move to Tactics *)
    Local Ltac lift_eexists :=
        repeat
          lazymatch goal with
          | |- Lift1Prop.ex1 _ _ => eexists
          | |- sep (Lift1Prop.ex1 _) _ _ => apply sep_ex1_l
          end.

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

    (* TODO: move to cswap *)
    Lemma cswap_iff1
          {T} (pred : word ->T -> Semantics.mem -> Prop) s pa pb a b :
      Lift1Prop.iff1
        ((pred (fst (cswap s pa pb)) (fst (cswap s a b)))
         * pred (snd (cswap s pa pb))
                (snd (cswap s a b)))%sep
        (pred pa a * pred pb b)%sep.
    Proof. destruct s; cbn [cswap fst snd]; ecancel. Qed.

    (* TODO: move to cswap *)
    Lemma map_get_cswap_fst
          {key value} {map : map.map key value}
          (m : map.rep (map:=map)) s ka kb a b :
      map.get m ka = Some a ->
      map.get m kb = Some b ->
      map.get m (fst (cswap s ka kb)) = Some (fst (cswap s a b)).
    Proof. destruct s; cbn [cswap fst fst]; auto. Qed.
    Lemma map_get_cswap_snd
          {key value} {map : map.map key value}
          (m : map.rep (map:=map)) s ka kb a b :
      map.get m ka = Some a ->
      map.get m kb = Some b ->
      map.get m (snd (cswap s ka kb)) = Some (snd (cswap s a b)).
    Proof. destruct s; cbn [cswap fst snd]; auto. Qed.

    (* TODO: move to cswap *)
    Lemma cswap_cases_fst {T} (P : T -> Prop) s a b :
      P a -> P b -> P (fst (cswap s a b)).
    Proof. destruct s; cbn [cswap fst snd]; auto. Qed.
    Lemma cswap_cases_snd {T} (P : T -> Prop) s a b :
      P a -> P b -> P (snd (cswap s a b)).
    Proof. destruct s; cbn [cswap fst snd]; auto. Qed.

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
           (let args := ["bound"; "U"; "X1"; "Z1"; "X2"; "Z2";
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

      rewrite Z2Nat.id in * by apply word.unsigned_range.

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

        pose proof (word.unsigned_range bound).
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

