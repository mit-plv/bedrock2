Require Import riscv.Utility.
Require Export bedrock2.Basic_bopnames.

Definition eval_binop{t: Set}{MW: MachineWidth t}(op: bopname)(v1 v2: t): t :=
  match op with
  | bopname.add => add v1 v2
  | bopname.sub => sub v1 v2
  | bopname.mul => mul v1 v2
  | bopname.and => and v1 v2
  | bopname.or  => or  v1 v2
  | bopname.xor => xor v1 v2
  | bopname.sru => srl v1 (regToShamt v2)
  | bopname.slu => sll v1 (regToShamt v2)
  | bopname.srs => sra v1 (regToShamt v2)
  | bopname.ltu => if ltu v1 v2              then ZToReg 1 else ZToReg 0
  | bopname.lts => if signed_less_than v1 v2 then ZToReg 1 else ZToReg 0
  | bopname.eq  => if reg_eqb v1 v2          then ZToReg 1 else ZToReg 0
  end.
