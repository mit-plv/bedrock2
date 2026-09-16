Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Bitwidth.
Require Import riscv.Utility.Utility.
Require Import compiler.SeparationLogic.

Open Scope Z_scope.

Section Params1.
  Context {width: Z}.
  Local Notation word := (bits width).

  Record MemoryLayout: Type := {
    code_start: word;
    code_pastend: word;
    heap_start: word;
    heap_pastend: word;
    stack_start: word;
    stack_pastend: word;
  }.

  (* Could also just require disjointness but <= is simpler to state *)
  Record MemoryLayoutOk{BW: Bitwidth width}(ml: MemoryLayout): Prop := {
    code_start_aligned: (Zmod.unsigned ml.(code_start)) mod 4 = 0;
    stack_start_aligned: (Zmod.unsigned ml.(stack_start)) mod bytes_per_word = 0;
    stack_pastend_aligned: (Zmod.unsigned ml.(stack_pastend)) mod bytes_per_word = 0;
    code_pastend_ok: Zmod.unsigned ml.(code_start) <= Zmod.unsigned ml.(code_pastend);
    heap_after_code: Zmod.unsigned ml.(code_pastend) <= Zmod.unsigned ml.(heap_start);
    heap_pastend_ok: Zmod.unsigned ml.(heap_start) <= Zmod.unsigned ml.(heap_pastend);
    stack_after_heap: Zmod.unsigned ml.(heap_pastend) <= Zmod.unsigned ml.(stack_start);
    stack_pastend_ok: Zmod.unsigned ml.(stack_start) <= Zmod.unsigned ml.(stack_pastend);
  }.

End Params1.
