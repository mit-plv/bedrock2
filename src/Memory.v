Require Import bbv.Word.
Require Import riscv.RiscvBitWidths.
Require Import compiler.Common.

Local Open Scope Z.

Section Memory.

  Context {Bw: RiscvBitWidths}.

  Definition mem := word wXLEN -> option (word wXLEN).

  Definition wXLEN_in_bytes: Z :=
    match bitwidth with
    | Bitwidth32 => 4
    | Bitwidth64 => 8
    end.
  
  Definition read_mem(x: word wXLEN)(m: mem): option (word wXLEN) :=
    if dec ((wordToZ x) mod (wXLEN_in_bytes) = 0) then m x else None.

  Definition write_mem(x: word wXLEN)(v: word wXLEN)(m: mem): option (mem) :=
    match read_mem x m with
    | Some old_value => Some (fun y => if dec (x = y) then Some v else m y)
    | None => None
    end.

  Definition no_mem: mem := fun x => None.

  Definition zeros_mem(upTo: word wXLEN): mem := fun x => if wlt_dec x upTo then Some $0 else None.

End Memory.
