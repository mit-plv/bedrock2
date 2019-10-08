Require Import compilerExamples.FE310Compiler bedrock2.Hexdump.
Local Open Scope hexdump_scope.
Goal True. let x := eval cbv in swap_demo_byte in idtac x. Abort.
