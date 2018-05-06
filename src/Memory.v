Require Import bbv.Word.
Require Import compiler.Common.

Section Memory.

  Context {w: nat}.

  Definition mem := word w -> option (word w).

  Definition alignment: nat :=
    if dec (w = 64) then 8 else if dec (w = 32) then 4 else 0.
  
  Definition read_mem(x: word w)(m: mem): option (word w) :=
    if dec ((wordToNat x) mod alignment = 0) then m x else None.

  Definition write_mem(x: word w)(v: word w)(m: mem): option (mem) :=
    match read_mem x m with
    | Some old_value => Some (fun y => if dec (x = y) then Some v else m y)
    | None => None
    end.

  Definition no_mem: mem := fun x => None.

  Definition zeros_mem(upTo: word w): mem := fun x => if wlt_dec x upTo then Some $0 else None.

End Memory.
