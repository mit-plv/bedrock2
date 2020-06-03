Require Import Rupicola.Lib.Api.

Axiom bounds : Type.
Axiom loose_bounds : bounds.
Axiom tight_bounds : bounds.
Axiom list_Z_bounded_by : bounds -> list Z -> Prop.
Axiom Bignum : forall {p : Semantics.parameters},
    word -> list word -> Semantics.mem -> Prop.
Axiom eval : list Z -> Z.
Axiom M : Z.
Axiom n : nat.

Section __.
  Context {semantics : Semantics.parameters}.
  Context {mul add sub square scmula24 : string}.
  Context {a24 : Z}.

  Section Gallina.
    Local Open Scope Z_scope.
    Local Infix "+" := (fun x y => x + y mod M).
    Local Infix "-" := (fun x y => x - y mod M).
    Local Infix "*" := (fun x y => x * y mod M).
    Local Infix "^" := (fun x y => x ^ y mod M).

    Definition point : Type := (Z * Z).

    Definition ladderstep
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
    (* Notations for the specification of a unary operation *)
    Local Notation fieldspec_unop name op xbounds outbounds :=
      (fun functions =>
         forall (wx : list word) (px pout : word) (wold_out : list word)
                (t : Semantics.trace) (m : Semantics.mem)
                (Ra Rr : Semantics.mem -> Prop),
           let x := List.map word.unsigned wx in
           list_Z_bounded_by xbounds x ->
           length (List.map word.unsigned wold_out) = n ->
           (Bignum px wx * Ra)%sep m ->
           (Bignum pout wold_out * Rr)%sep m ->
           WeakestPrecondition.call
             functions name t m [px; pout]
             (fun (t' : Semantics.trace) (m' : Interface.map.rep)
                  (rets : list word) =>
                t = t' /\ rets = [] /\
                (exists wout : list word.rep,
                    let out := List.map word.unsigned wout in
                    (eval out mod M = ((op (eval x)) mod M))%Z
                    /\ list_Z_bounded_by outbounds out
                    /\ (Bignum pout wout * Rr)%sep m'))) (only parsing).

    (* Notations for the specification of a binary operation *)
    Local Notation fieldspec_binop name op xbounds ybounds outbounds :=
      (fun functions =>
         forall (wx wy : list word)
                (px py pout : word) (wold_out : list word)
                (t : Semantics.trace) (m : Semantics.mem)
                (Ra Rr : Semantics.mem -> Prop),
           let x := List.map word.unsigned wx in
           let y := List.map word.unsigned wy in
           list_Z_bounded_by xbounds x ->
           list_Z_bounded_by ybounds y ->
           length (List.map word.unsigned wold_out) = n ->
           (Bignum px wx * Bignum py wy * Ra)%sep m ->
           (Bignum pout wold_out * Rr)%sep m ->
           WeakestPrecondition.call
             functions name t m [px; py; pout]
             (fun (t' : Semantics.trace) (m' : Interface.map.rep)
                  (rets : list word) =>
                t = t' /\ rets = [] /\
                (exists wout : list word.rep,
                    let out := List.map word.unsigned wout in
                    (eval out mod M = ((op (eval x) (eval y)) mod M))%Z
                    /\ list_Z_bounded_by outbounds out
                    /\ (Bignum pout wout * Rr)%sep m'))) (only parsing).

    Instance spec_of_mul : spec_of mul :=
      fieldspec_binop mul Z.mul loose_bounds loose_bounds tight_bounds.
    Instance spec_of_square : spec_of square :=
      fieldspec_unop square (fun x => Z.mul x x) loose_bounds tight_bounds.
    Instance spec_of_add : spec_of add :=
      fieldspec_binop add Z.add tight_bounds tight_bounds loose_bounds.
    Instance spec_of_sub : spec_of sub :=
      fieldspec_binop sub Z.sub tight_bounds tight_bounds loose_bounds.
    Instance spec_of_scmula24 : spec_of scmula24 :=
      fieldspec_unop scmula24 (Z.mul a24) loose_bounds tight_bounds.
  End Field.

End __.
