Require Import end2end.End2EndLightbulb.

Import riscv.Utility.InstructionNotations.
Import BinInt String bedrock2.NotationsCustomEntry.
Import bedrock2.Hexdump.
Local Open Scope hexdump_scope.
Set Printing Width 108.

Goal True.
  pose (SortedList.value (PipelineWithRename.function_positions prog)) as symbols.
  cbv in symbols.

  pose lightbulb_insts as p.
  unfold lightbulb_insts in p.

  let x := eval cbv in (End2EndPipeline.instrencode lightbulb_insts) in idtac x.
Abort.
Unset Printing Width.
