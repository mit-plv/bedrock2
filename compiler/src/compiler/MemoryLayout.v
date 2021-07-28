Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface.
Require Import riscv.Utility.Utility.
Require Import compiler.SeparationLogic.

Open Scope Z_scope.

Section Params1.
  Context {width} {word: word.word width}.

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
    code_start_aligned: (word.unsigned ml.(code_start)) mod 4 = 0;
    stack_start_aligned: (word.unsigned ml.(stack_start)) mod bytes_per_word = 0;
    stack_pastend_aligned: (word.unsigned ml.(stack_pastend)) mod bytes_per_word = 0;
    code_pastend_ok: word.unsigned ml.(code_start) <= word.unsigned ml.(code_pastend);
    heap_after_code: word.unsigned ml.(code_pastend) <= word.unsigned ml.(heap_start);
    heap_pastend_ok: word.unsigned ml.(heap_start) <= word.unsigned ml.(heap_pastend);
    stack_after_heap: word.unsigned ml.(heap_pastend) <= word.unsigned ml.(stack_start);
    stack_pastend_ok: word.unsigned ml.(stack_start) <= word.unsigned ml.(stack_pastend);
  }.

End Params1.
