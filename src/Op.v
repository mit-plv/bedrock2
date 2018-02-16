Require Import bbv.Word.
Require Import compiler.Common.

Inductive binop: Set := OPlus | OMinus | OTimes | OEq | OLt | OAnd.

Definition eval_binop{w: nat}(op: binop)(v1 v2: word w): word w :=
  match op with
  | OPlus => v1 ^+ v2
  | OMinus => v1 ^- v2
  | OTimes => v1 ^* v2
  | OEq => if weq v1 v2 then wone w else wzero w
  | OLt => if wlt_dec v1 v2 then wone w else wzero w
  | OAnd => v1 ^& v2
  end.


Definition eval_binop_nat(op: binop)(v1 v2: nat): nat :=
  match op with
  | OPlus => v1 + v2
  | OMinus => v1 - v2
  | OTimes => v1 * v2
  | OEq => if Nat.eq_dec v1 v2 then 1 else 0
  | OLt => if Compare_dec.lt_dec v1 v2 then 1 else 0
  | OAnd => Z.to_nat (Z.land (Z.of_nat v1) (Z.of_nat v2))
  end.

Definition eval_binop_Z_unbounded(op: binop)(v1 v2: Z): Z :=
  match op with
  | OPlus => v1 + v2
  | OMinus => v1 - v2
  | OTimes => v1 * v2
  | OEq => if dec (v1 = v2) then 1 else 0
  | OLt => if dec (v1 < v2)%Z then 1 else 0
  | OAnd => (Z.land v1 v2)
  end.

Definition eval_binop_Z_bounded(w: nat)(op: binop)(v1 v2: Z): Z :=
  let mask := Z.ones (Z.of_nat w) in
  Z.land mask (eval_binop_Z_unbounded op v1 v2).
