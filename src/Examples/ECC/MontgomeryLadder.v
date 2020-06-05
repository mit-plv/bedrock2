Require Import Rupicola.Lib.Api.
Local Open Scope Z_scope.

(* TODO: copy the specs back over into fiat-crypto and prove that they are
   obeyed to validate the slight rephrasings here *)
Section __.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {mul add sub square scmula24 inv : string}.
  Context {M a24 : Z}.
  Context {Finv : Z -> Z}. (* modular inverse in Z/M *)

  (* In practice, these would be instantiated as:
     bignum := list word
     eval := (fun ws => Positional.eval weight n (map word.unsigned ws))
     Bignum := (fun addr xs =>
                 (emp (length xs = n) * array scalar addr xs)%sep)
     bounds := list (option zrange)
     bounded_by := (fun bs ws =>
                      list_Z_bounded_by bs (map word.unsigned ws)) *)
  Context {bignum : Type} {eval : bignum -> Z}
          {Bignum : word -> bignum -> Semantics.mem -> Prop}
          {bounds : Type}
          {bounded_by : bounds -> bignum -> Prop}.
  Context {loose_bounds tight_bounds : bounds}
          {relax_bounds :
             forall X : bignum,
               bounded_by tight_bounds X ->
               bounded_by loose_bounds X}.
  Hint Resolve relax_bounds : compiler.

  Section Gallina.
    Local Infix "+" := (fun x y => (x + y) mod M).
    Local Infix "-" := (fun x y => (x - y) mod M).
    Local Infix "*" := (fun x y => (x * y) mod M).
    Local Infix "^" := (fun x y => (x ^ y) mod M).

    Definition point : Type := (Z * Z).

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

    Fixpoint downto_iter (i:nat) : list nat :=
      match i with
      | Datatypes.S i' => cons i' (downto_iter i')
      | O => nil
      end.

    Definition downto
               {state} init count (step:state->nat->state) : state :=
      List.fold_left step (downto_iter count) init.

    Definition cswap (swap:bool) (a b: point) : point * point :=
      if swap then (b, a) else (a, b).

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

    Definition montladder bound (testbit:nat->bool) (u:Z) : Z :=
      let P1 : point := (1, 0) in
      let P2 : point := (u, 1) in
      let swap := false in
      let/d ''(P1, P2, swap) :=
         downto
           (P1, P2, swap) (* initial state *)
           bound (* count *)
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

  Section Field.
    Local Notation unop_spec name op xbounds outbounds :=
      (forall! (x : bignum) (px pout : word) (old_out : bignum),
          (fun Rr mem =>
             bounded_by xbounds x
             /\ (exists Ra, (Bignum px x * Ra)%sep mem)
             /\ (Bignum pout old_out * Rr)%sep mem)
            ===> name @ [px; pout] ===>
            (liftexists out,
             (emp ((eval out mod M = (op (eval x)) mod M)%Z
                   /\ bounded_by outbounds out)
              * Bignum pout out)%sep))
        (only parsing).

    Local Notation binop_spec name op xbounds ybounds outbounds :=
      (forall! (x y : bignum) (px py pout : word) (old_out : bignum),
          (fun Rr mem =>
             bounded_by xbounds x
             /\ bounded_by ybounds y
             /\ (exists Ra, (Bignum px x * Bignum py y * Ra)%sep mem)
             /\ (Bignum pout old_out * Rr)%sep mem)
            ===> name @ [px; py; pout] ===>
            (liftexists out,
             (emp ((eval out mod M = (op (eval x) (eval y)) mod M)%Z
                   /\ bounded_by outbounds out)
              * Bignum pout out)%sep)) (only parsing).

    Instance spec_of_mul : spec_of mul :=
      binop_spec mul Z.mul loose_bounds loose_bounds tight_bounds.
    Instance spec_of_square : spec_of square :=
      unop_spec square (fun x => Z.mul x x) loose_bounds tight_bounds.
    Instance spec_of_add : spec_of add :=
      binop_spec add Z.add tight_bounds tight_bounds loose_bounds.
    Instance spec_of_sub : spec_of sub :=
      binop_spec sub Z.sub tight_bounds tight_bounds loose_bounds.
    Instance spec_of_scmula24 : spec_of scmula24 :=
      unop_spec scmula24 (Z.mul a24) loose_bounds tight_bounds.

    (* TODO: what are the bounds for inv? *)
    Instance spec_of_inv : spec_of inv :=
      unop_spec inv Finv tight_bounds loose_bounds.
  End Field.
  Existing Instances spec_of_mul spec_of_square spec_of_add
           spec_of_sub spec_of_scmula24 spec_of_inv.

  Section Compile.
    (* In compilation, we need to decide where to store outputs. In particular,
       we don't want to overwrite a variable that we want to use later with the
       output of some operation. The [Placeholder] alias explicitly signifies
       which Bignums are overwritable.

       TODO: in the future, it would be nice to be able to look through the
       Gallina code and see which Bignums get used later and which don't. *)
    Definition Placeholder := Bignum.

    Lemma compile_mul :
      forall (locals: Semantics.locals) (mem: Semantics.mem)
        tr R Rin Rout functions T (pred: T -> _ -> Prop)
        (x y out : bignum) x_ptr x_var y_ptr y_var out_ptr out_var
        k k_impl,
        spec_of_mul functions ->
        bounded_by loose_bounds x ->
        bounded_by loose_bounds y ->
        (Bignum x_ptr x * Bignum y_ptr y * Rin)%sep mem ->
        (Placeholder out_ptr out * Rout)%sep mem ->
        map.get locals x_var = Some x_ptr ->
        map.get locals y_var = Some y_ptr ->
        map.get locals out_var = Some out_ptr ->
        let v := (eval x * eval y) mod M in
        (let head := v in
         forall out m,
           eval out mod M = head ->
           bounded_by tight_bounds out ->
           sep (Bignum out_ptr out) Rout m ->
           (find k_impl
            implementing (pred (k (eval out mod M)))
            with-locals locals and-memory m and-trace tr and-rest R
            and-functions functions)) ->
        (let head := v in
         find (cmd.seq
                 (cmd.call [] mul [expr.var x_var; expr.var y_var;
                                     expr.var out_var])
                 k_impl)
         implementing (pred (dlet head k))
         with-locals locals and-memory mem and-trace tr and-rest R
         and-functions functions).
    Proof.
      cbv [Placeholder] in *.
      repeat straightline'.
      handle_call; [ solve [eauto] .. | ].
      sepsimpl.
      repeat match goal with x := _ mod M |- _ =>
                                  subst x end.
      match goal with H : _ mod M = ?x mod M
                      |- context [dlet (?x mod M)] =>
                      rewrite <-H
      end.
      eauto.
    Qed.

    Lemma compile_add :
      forall (locals: Semantics.locals) (mem: Semantics.mem)
        tr R Rin Rout functions T (pred: T -> _ -> Prop)
        (x y out : bignum) x_ptr x_var y_ptr y_var out_ptr out_var
        k k_impl,
        spec_of_add functions ->
        bounded_by tight_bounds x ->
        bounded_by tight_bounds y ->
        (Bignum x_ptr x * Bignum y_ptr y * Rin)%sep mem ->
        (Placeholder out_ptr out * Rout)%sep mem ->
        map.get locals x_var = Some x_ptr ->
        map.get locals y_var = Some y_ptr ->
        map.get locals out_var = Some out_ptr ->
        let v := (eval x + eval y) mod M in
        (let head := v in
         forall out m,
           eval out mod M = head ->
           bounded_by loose_bounds out ->
           sep (Bignum out_ptr out) Rout m ->
           (find k_impl
            implementing (pred (k (eval out mod M)))
            with-locals locals and-memory m and-trace tr and-rest R
            and-functions functions)) ->
        (let head := v in
         find (cmd.seq
                 (cmd.call [] add [expr.var x_var; expr.var y_var;
                                     expr.var out_var])
                 k_impl)
         implementing (pred (dlet head k))
         with-locals locals and-memory mem and-trace tr and-rest R
         and-functions functions).
    Proof.
      cbv [Placeholder] in *.
      repeat straightline'.
      handle_call; [ solve [eauto] .. | ].
      sepsimpl.
      repeat match goal with x := _ mod M |- _ =>
                                  subst x end.
      match goal with H : _ mod M = ?x mod M
                      |- context [dlet (?x mod M)] =>
                      rewrite <-H
      end.
      eauto.
    Qed.

    Lemma compile_sub :
      forall (locals: Semantics.locals) (mem: Semantics.mem)
        tr R Rin Rout functions T (pred: T -> _ -> Prop)
        (x y out : bignum) x_ptr x_var y_ptr y_var out_ptr out_var
        k k_impl,
        spec_of_sub functions ->
        bounded_by tight_bounds x ->
        bounded_by tight_bounds y ->
        (Bignum x_ptr x * Bignum y_ptr y * Rin)%sep mem ->
        (Placeholder out_ptr out * Rout)%sep mem ->
        map.get locals x_var = Some x_ptr ->
        map.get locals y_var = Some y_ptr ->
        map.get locals out_var = Some out_ptr ->
        let v := (eval x - eval y) mod M in
        (let head := v in
         forall out m,
           eval out mod M = head ->
           bounded_by loose_bounds out ->
           sep (Bignum out_ptr out) Rout m ->
           (find k_impl
            implementing (pred (k (eval out mod M)))
            with-locals locals and-memory m and-trace tr and-rest R
            and-functions functions)) ->
        (let head := v in
         find (cmd.seq
                 (cmd.call [] sub [expr.var x_var; expr.var y_var;
                                     expr.var out_var])
                 k_impl)
         implementing (pred (dlet head k))
         with-locals locals and-memory mem and-trace tr and-rest R
         and-functions functions).
    Proof.
      cbv [Placeholder] in *.
      repeat straightline'.
      handle_call; [ solve [eauto] .. | ].
      sepsimpl.
      repeat match goal with x := _ mod M |- _ =>
                                  subst x end.
      match goal with H : _ mod M = ?x mod M
                      |- context [dlet (?x mod M)] =>
                      rewrite <-H
      end.
      eauto.
    Qed.

    Lemma compile_square :
      forall (locals: Semantics.locals) (mem: Semantics.mem)
        tr R Rin Rout functions T (pred: T -> _ -> Prop)
        (x out : bignum) x_ptr x_var out_ptr out_var k k_impl,
        spec_of_square functions ->
        bounded_by loose_bounds x ->
        (Bignum x_ptr x * Rin)%sep mem ->
        (Placeholder out_ptr out * Rout)%sep mem ->
        map.get locals x_var = Some x_ptr ->
        map.get locals out_var = Some out_ptr ->
        let v := (eval x ^ 2) mod M in
        (let head := v in
         forall out m,
           eval out mod M = head ->
           bounded_by tight_bounds out ->
           sep (Bignum out_ptr out) Rout m ->
           (find k_impl
            implementing (pred (k (eval out mod M)))
            with-locals locals and-memory m and-trace tr and-rest R
            and-functions functions)) ->
        (let head := v in
         find (cmd.seq
                 (cmd.call [] square [expr.var x_var; expr.var out_var])
                 k_impl)
         implementing (pred (dlet head k))
         with-locals locals and-memory mem and-trace tr and-rest R
         and-functions functions).
    Proof.
      cbv [Placeholder] in *.
      repeat straightline'.
      handle_call; [ solve [eauto] .. | ].
      sepsimpl.
      repeat match goal with x := _ mod M |- _ =>
                                  subst x end.
      rewrite Z.pow_2_r in *.
      match goal with H : _ mod M = ?x mod M
                      |- context [dlet (?x mod M)] =>
                      rewrite <-H
      end.
      eauto.
    Qed.

    Lemma compile_scmula24 :
      forall (locals: Semantics.locals) (mem: Semantics.mem)
        tr R Rin Rout functions T (pred: T -> _ -> Prop)
        (x out : bignum) x_ptr x_var out_ptr out_var k k_impl,
        spec_of_scmula24 functions ->
        bounded_by loose_bounds x ->
        (Bignum x_ptr x * Rin)%sep mem ->
        (Placeholder out_ptr out * Rout)%sep mem ->
        map.get locals x_var = Some x_ptr ->
        map.get locals out_var = Some out_ptr ->
        let v := (a24 * eval x) mod M in
        (let head := v in
         forall out m,
           eval out mod M = head ->
           bounded_by tight_bounds out ->
           sep (Bignum out_ptr out) Rout m ->
           (find k_impl
            implementing (pred (k (eval out mod M)))
            with-locals locals and-memory m and-trace tr and-rest R
            and-functions functions)) ->
        (let head := v in
         find (cmd.seq
                 (cmd.call [] scmula24 [expr.var x_var; expr.var out_var])
                 k_impl)
         implementing (pred (dlet head k))
         with-locals locals and-memory mem and-trace tr and-rest R
         and-functions functions).
    Proof.
      cbv [Placeholder] in *.
      repeat straightline'.
      handle_call; [ solve [eauto] .. | ].
      sepsimpl.
      repeat match goal with x := _ mod M |- _ =>
                                  subst x end.
      match goal with H : _ mod M = ?x mod M
                      |- context [dlet (?x mod M)] =>
                      rewrite <-H
      end.
      eauto.
    Qed.

    (* noop indicating that the last argument should store output *)
    Definition overwrite1 {A B} := @id (A -> B).
    (* noop indicating that the 2nd-to-last argument should store output *)
    Definition overwrite2 {A B C} := @id (A -> B -> C).

    Lemma compile_compose_l :
      forall (locals: Semantics.locals) (mem: Semantics.mem)
        tr R Rout functions T (pred: T -> _ -> Prop)
        (op1 op2 : Z -> Z -> Z)
        x y z out out_ptr out_var k k_impl,
        (Placeholder out_ptr out * Rout)%sep mem ->
        map.get locals out_var = Some out_ptr ->
        let v := ((op2 (op1 x y mod M) z)) mod M in
        (let head := v in
         (find k_impl
          implementing (pred (dlet (op1 x y mod M)
          (fun xy => dlet ((overwrite2 op2) xy z mod M) k)))
          with-locals locals and-memory mem and-trace tr and-rest R
          and-functions functions)) ->
        (let head := v in
         find k_impl
         implementing (pred (dlet head k))
         with-locals locals and-memory mem and-trace tr and-rest R
         and-functions functions).
    Proof.
      cbv [Placeholder overwrite1 overwrite2] in *.
      repeat straightline'. auto.
    Qed.

    Lemma compile_compose_r :
      forall (locals: Semantics.locals) (mem: Semantics.mem)
        tr R Rout functions T (pred: T -> _ -> Prop)
        (op1 op2 : Z -> Z -> Z)
        x y z out out_ptr out_var k k_impl,
        (Placeholder out_ptr out * Rout)%sep mem ->
        map.get locals out_var = Some out_ptr ->
        let v := ((op2 z (op1 x y mod M))) mod M in
        (let head := v in
         (find k_impl
          implementing (pred (dlet (op1 x y mod M)
          (fun xy => dlet ((overwrite1 op2) z xy mod M) k)))
          with-locals locals and-memory mem and-trace tr and-rest R
          and-functions functions)) ->
        (let head := v in
         find k_impl
         implementing (pred (dlet head k))
         with-locals locals and-memory mem and-trace tr and-rest R
         and-functions functions).
    Proof.
      cbv [Placeholder overwrite1 overwrite2] in *.
      repeat straightline'. auto.
    Qed.

    Lemma compile_overwrite1 :
      forall (locals: Semantics.locals) (mem: Semantics.mem)
        tr R Rin functions T (pred: T -> _ -> Prop)
        (x : Z) (op : Z -> Z -> Z) (y : bignum) y_ptr y_var k k_impl,
        (Bignum y_ptr y * Rin)%sep mem ->
        map.get locals y_var = Some y_ptr ->
        let v := ((overwrite1 op) x (eval y mod M)) mod M in
        let v' := (op x (eval y mod M)) mod M in
        (let __ := 0 in (* placeholder *)
         forall m,
           sep (Placeholder y_ptr y) Rin m ->
           (find k_impl
            implementing (pred (dlet v' k))
            with-locals locals and-memory m and-trace tr and-rest R
            and-functions functions)) ->
        (let head := v in
         find k_impl
         implementing (pred (dlet head k))
         with-locals locals and-memory mem and-trace tr and-rest R
         and-functions functions).
    Proof.
      cbv [Placeholder] in *.
      repeat straightline'. auto.
    Qed.

    Lemma compile_overwrite2 :
      forall (locals: Semantics.locals) (mem: Semantics.mem)
        tr R Rin functions T (pred: T -> _ -> Prop)
        (y : Z) (op : Z -> Z -> Z) (x : bignum) x_ptr x_var k k_impl,
        (Bignum x_ptr x * Rin)%sep mem ->
        map.get locals x_var = Some x_ptr ->
        let v := ((overwrite2 op) (eval x mod M) y) mod M in
        let v' := (op (eval x mod M) y) mod M in
        (let __ := 0 in (* placeholder *)
         forall m,
           sep (Placeholder x_ptr x) Rin m ->
           (find k_impl
            implementing (pred (dlet v' k))
            with-locals locals and-memory m and-trace tr and-rest R
            and-functions functions)) ->
        (let head := v in
         find k_impl
         implementing (pred (dlet head k))
         with-locals locals and-memory mem and-trace tr and-rest R
         and-functions functions).
    Proof.
      cbv [Placeholder] in *.
      repeat straightline'. auto.
    Qed.
  End Compile.

  (* helper for Zpow_mod *)
  Lemma Zpow_mod_nonneg a b m :
    0 <= b -> (a ^ b) mod m = ((a mod m) ^ b) mod m.
  Proof.
    intros. revert a m.
    apply natlike_ind with (x:=b); intros;
      repeat first [ rewrite Z.pow_0_r
                   | rewrite Z.pow_succ_r by auto
                   | reflexivity
                   | solve [auto] ]; [ ].
    Z.push_mod.
    match goal with
      H : context [ (_ ^ _) mod _ = (_ ^ _) mod _ ] |- _ =>
      rewrite H end.
    Z.push_pull_mod. reflexivity.
  Qed.

  (* TODO: upstream to coqutil's Z.pull_mod *)
  Lemma Zpow_mod a b m : (a ^ b) mod m = ((a mod m) ^ b) mod m.
  Proof.
    destruct (Z_le_dec 0 b); auto using Zpow_mod_nonneg; [ ].
    rewrite !Z.pow_neg_r by lia. reflexivity.
  Qed.

  (* TODO: replace with Z.pull_mod once Zpow_mod is upstreamed *)
  Local Ltac pull_mod :=
    repeat first [ progress Z.pull_mod
                 | rewrite <-Zpow_mod ].

  Ltac field_compile_step :=
    Z.push_pull_mod; pull_mod;
    first [ simple eapply compile_mul
          | simple eapply compile_add
          | simple eapply compile_sub
          | simple eapply compile_square
          | simple eapply compile_scmula24 ].

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

  Ltac compile_compose_step :=
    Z.push_mod;
    first [ simple eapply compile_compose_l
          | simple eapply compile_compose_r
          | simple eapply compile_overwrite1
          | simple eapply compile_overwrite2 ];
    [ solve [repeat compile_step] .. | intros ].

  Ltac compile_custom ::=
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

  (* only apply compile_step when repeat_compile_step solves all the side
     conditions but one *)
  Local Ltac safe_compile_step :=
    compile_step; [ solve [repeat compile_step] .. | ].

  Ltac lookup_Bignum_pointer x :=
    lazymatch goal with
    | H : sep _ _ ?m |- context [?m] =>
      lazymatch type of H with
        context [Bignum ?p x] => p
      end
    end.

  Local Ltac overwrite p := change (Bignum p) with (Placeholder p) in *.

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
    overwrite pX3; repeat safe_compile_step.
    overwrite pZ3; repeat safe_compile_step.
    overwrite pX2; repeat safe_compile_step.
    overwrite pZ2; repeat safe_compile_step.

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
