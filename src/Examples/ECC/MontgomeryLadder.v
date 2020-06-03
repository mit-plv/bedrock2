Require Import Rupicola.Lib.Api.

(* TODO: generalize *)
Notation "'liftexists' x .. y ',' P" :=
  (Lift1Prop.ex1
     (fun x =>
        ..
          (Lift1Prop.ex1
             (fun y => P)) .. ))
    (x binder, y binder, only parsing, at level 199).

(* TODO: generalize *)
(* TODO: fix indentation *)
(* precondition is more permissively handled than postcondition in order to
   allow multiple separation-logic preconditions *)
Local Notation "'forall!' x .. y ',' pre '===>' fname '@' args '==>' post" :=
(fun functions =>
   (forall x,
       .. (forall y,
              forall R tr mem,
                pre R mem ->
                WeakestPrecondition.call
                  functions fname tr mem args
                  (postcondition_for post R tr)) ..))
     (x binder, y binder, only parsing, at level 199).

(* TODO: copy the specs back over into fiat-crypto and prove that they are
   obeyed to validate the slight rephrasings here *)
Section __.
  Context {semantics : Semantics.parameters}.
  Context {mul add sub square scmula24 : string}.
  Context {M a24 : Z}.

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
  Context {loose_bounds tight_bounds : bounds}.

  Section Gallina.
    Local Open Scope Z_scope.
    Local Infix "+" := (fun x y => x + y mod M).
    Local Infix "-" := (fun x y => x - y mod M).
    Local Infix "*" := (fun x y => x * y mod M).
    Local Infix "^" := (fun x y => x ^ y mod M).

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
      let/d Z4 := E*(AA + a24*E) in
      ((X4, Z4), (X5, Z5)).

  End Gallina.

  Section Field.
    Local Notation unop_spec name op xbounds outbounds :=
      (forall! (x : bignum) (px pout : word) (old_out : bignum),
          (fun Rr mem =>
             bounded_by xbounds x
             /\ (exists Ra, (Bignum px x * Ra)%sep mem)
             /\ (Bignum pout old_out * Rr)%sep mem)
            ===> name @ [px; pout] ==>
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
             /\ (exists Ra, (Bignum px x * Ra)%sep mem)
             /\ (Bignum pout old_out * Rr)%sep mem)
            ===> name @ [px; py; pout] ==>
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
  End Field.
  Existing Instances spec_of_mul spec_of_square spec_of_add
           spec_of_sub spec_of_scmula24.

  Section Separation.
    Definition bytes_per_word :=
      Z.of_nat (@Memory.bytes_per Semantics.width access_size.word).

    Definition Point (addr : Semantics.word) (P : point)
      : Semantics.mem -> Prop :=
      let px := addr in
      let py := word.add addr (word.of_Z bytes_per_word) in
      liftexists X Y,
      (emp (word.unsigned X = fst P /\ word.unsigned Y = snd P)
       * scalar px X * scalar py Y)%sep.

    Definition TwoPoints (pP1 pP2 : Semantics.word) (Ps : point * point)
      : Semantics.mem -> Prop :=
      (Point pP1 (fst Ps) * Point pP2 (snd Ps))%sep.
  End Separation.

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
            * Bignum pA A * Bignum pAA AA
            * Bignum pB B * Bignum pBB BB
            * Bignum pE E * Bignum pC C * Bignum pD D
            * Bignum pDA DA * Bignum pCB CB
            * R)%sep m)
        ===>
        "ladderstep" @ [pX1; pX2; pZ2; pX3; pZ3; pA; pAA; pB; pBB; pE; pC; pD; pDA; pCB]
        ==>
        (liftexists X4 Z4 X5 Z5 (* output values *)
                    A' AA' B' BB' E' C' D' DA' CB' (* new intermediates *)
         : bignum,
           (emp (ladderstep_gallina
                   (eval X1) (eval X2, eval Z2) (eval X3, eval Z3)
                 = ((eval X4, eval Z4), (eval X5, eval Z5))
                 /\ bounded_by tight_bounds X4
                 /\ bounded_by tight_bounds Z4
                 /\ bounded_by tight_bounds X5
                 /\ bounded_by tight_bounds Z5)
            * Bignum pX1 X1 * Bignum pX2 X4 * Bignum pZ2 Z4
            * Bignum pX3 X5 * Bignum pZ3 Z5
            * Bignum pA A' * Bignum pAA AA'
            * Bignum pB B' * Bignum pBB BB'
            * Bignum pE E' * Bignum pC C' * Bignum pD D'
            * Bignum pDA DA' * Bignum pCB CB')%sep).

  Derive ladderstep_body SuchThat
         (let args := ["pX1"; "pX2"; "pZ2"; "pX3"; "pZ3";
                          "pA"; "pAA"; "pB"; "pBB"; "pE"; "pC";
                            "pD"; "pDA"; "pCB"] in
           let ladderstep := ("ladderstep", (args, [], ladderstep_body)) in
          program_logic_goal_for
            ladderstep
            (ltac:(let x := program_logic_goal_for_function
                              ladderstep [mul;add;sub;square;scmula24] in
                   exact x)))
    As ladderstep_body_correct.
  Abort.

End __.
