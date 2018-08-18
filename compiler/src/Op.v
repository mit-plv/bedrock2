Require Import compiler.util.Common.
Require Import riscv.Utility.


Inductive binop: Set := OPlus | OMinus | OTimes | OEq | OLt | OAnd.

Definition eval_binop{t: Set}{MW: MachineWidth t}(op: binop)(v1 v2: t): t :=
  match op with
  | OPlus => add v1 v2
  | OMinus => sub v1 v2
  | OTimes => mul v1 v2
  | OEq => if reg_eqb v1 v2 then ZToReg 1 else (ZToReg 0)
  | OLt => if ltu v1 v2 then ZToReg 1 else (ZToReg 0)
  | OAnd => and v1 v2
  end.

Definition eval_binop_word{w: Z}(op: binop)(v1 v2: word w): word w :=
  match op with
  | OPlus => wadd v1 v2
  | OMinus => wsub v1 v2
  | OTimes => wmul v1 v2
  | OEq => if weqb  v1 v2 then ZToWord w 1 else ZToWord w 0
  | OLt => if wultb v1 v2 then ZToWord w 1 else ZToWord w 0
  | OAnd => wand v1 v2
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
