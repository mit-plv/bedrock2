Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import coqutil.Datatypes.List.

(* RISC-V Calling Convention from
   https://raw.githubusercontent.com/riscv-non-isa/riscv-elf-psabi-doc/a855ba3ef4/riscv-cc.adoc

| Name    | ABI Mnemonic | Meaning                | Preserved across calls?

| x0      | zero         | Zero                   | -- (Immutable)
| x1      | ra           | Return address         | No
| x2      | sp           | Stack pointer          | Yes
| x3      | gp           | Global pointer         | -- (Unallocatable)
| x4      | tp           | Thread pointer         | -- (Unallocatable)
| x5-x7   | t0-t2        | Temporary registers    | No
| x8-x9   | s0-s1        | Callee-saved registers | Yes
| x10-x17 | a0-a7        | Argument registers     | No
| x18-x27 | s2-s11       | Callee-saved registers | Yes
| x28-x31 | t3-t6        | Temporary registers    | No
*)

Module reg_class.
  Inductive t := neg | zero | ra | sp | gp | tp | temp | saved | arg | stack_slot.
  Scheme Equality for t.
  Definition eqb := t_beq.
  Local Open Scope bool_scope.

  Definition get(r: Z): t :=
    if r <? 0 then neg else
    if r =? 0 then zero else
    if r =? 1 then ra else
    if r =? 2 then sp else
    if r =? 3 then gp else
    if r =? 4 then tp else
    if (5 <=? r) && (r <=? 7) then temp else
    if (8 <=? r) && (r <=? 9) then saved else
    if (10 <=? r) && (r <=? 17) then arg else
    if (18 <=? r) && (r <=? 27) then saved else
    if (28 <=? r) && (r <=? 31) then temp else
    stack_slot.

  Definition all(class: t): list Z :=
    List.filter (fun r => eqb (get r) class) (List.unfoldn (Z.add 1) 32 0).
End reg_class.
