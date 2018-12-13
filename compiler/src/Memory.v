Require Import riscv.util.Word.
Require Import riscv.util.BitWidths.
Require Import compiler.util.Common.
Require Import riscv.Utility.

Local Open Scope Z_scope.

Section Memory.

  Context {mword: Type}.
  Context {MW: MachineWidth mword}.

  Definition mem := mword -> option mword.

  Definition read_mem(x: mword)(m: mem): option mword :=
    if ((regToZ_unsigned x) mod XLEN_in_bytes) =? 0 then m x else None.

  Definition write_mem(x: mword)(v: mword)(m: mem): option (mem) :=
    match read_mem x m with
    | Some old_value => Some (fun y => if reg_eqb x y then Some v else m y)
    | None => None
    end.

  Definition no_mem: mem := fun x => None.

  Definition zeros_mem(upTo: mword): mem := fun x => if ltu x upTo then Some (ZToReg 0) else None.

End Memory.
