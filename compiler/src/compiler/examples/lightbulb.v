Require Import Coq.Lists.List.
Import ListNotations.
Require Import coqutil.Decidable.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.PipelineWithRename.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import riscv.Utility.Monads.
Require Import compiler.util.Common.
Require Import coqutil.Decidable.
Require        riscv.Utility.InstructionNotations.
Require Import riscv.Platform.MinimalLogging.
Require Import bedrock2.MetricLogging.
Require Import riscv.Platform.MetricMinimal.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
Require Import coqutil.Map.SortedList.
Require Import compiler.StringNameGen.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import bedrock2.Byte.
Require bedrock2.Hexdump.
Require Import bedrock2Examples.SPI.
Require Import bedrock2Examples.LAN9250.
Require Import bedrock2Examples.lightbulb.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope ilist_scope.

Axiom TODO: forall {T: Type}, T.

Local Existing Instance DefaultRiscvState.
Local Existing Instance coqutil.Map.SortedListString.map.
Local Existing Instance coqutil.Map.SortedListString.ok.
Instance flatToRiscvDef_params: FlatToRiscvDef.FlatToRiscvDef.parameters := {
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call retnames fname argnames :=
    if string_dec fname "nop" then [[Addi Register0 Register0 0]]
    else if string_dec fname "MMIOREAD" then
           match retnames, argnames with
           | [res], [addr] => [[ Lw res addr 0 ]]
           | _, _ => nil
           end
    else if string_dec fname "MMIOWRITE" then
           match retnames, argnames with
           | [], [addr; val] => [[ Sw addr val 0 ]]
           | _, _ => nil
           end
    else  nil;
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call_length _ := TODO;
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call_emits_valid _ _ := TODO;
}.
Notation RiscvMachine := MetricRiscvMachine.

Definition params : Pipeline.parameters. simple refine {|
  Pipeline.locals := _;
  Pipeline.Registers := _;
  Pipeline.ext_spec _ _ := TODO;
  Pipeline.ext_guarantee _ := False;
  Pipeline.PRParams := TODO;
|}; unshelve (try exact _); apply TODO. Defined.
Definition flatparams := (FlattenExpr.mk_Syntax_params (@Pipeline.FlattenExpr_parameters params)).
Definition b : @varname flatparams := "b".
Instance pipeline_assumptions: @Pipeline.assumptions params. Admitted.

(* stack grows from high addreses to low addresses, first stack word will be written to
   (stack_pastend-4), next stack word to (stack_pastend-8) etc *)
Definition stack_pastend: Z := 1024*16.

Definition ml: MemoryLayout Semantics.width.
  refine {| MemoryLayout.stack_pastend := word.of_Z stack_pastend; |}.
  all: apply TODO.
Defined.

Definition instrencode p : list byte :=
  let word8s := List.flat_map (fun inst => HList.tuple.to_list (LittleEndian.split 4 (encode inst))) p in
  List.map (fun w => Byte.of_Z (word.unsigned w)) word8s.

Require Import coqutil.Z.HexNotation.
Definition prog := (
  [lan9250_init; lan9250_wait_for_boot; lan9250_mac_write;
  iot; lightbulb; recvEthernet;  lan9250_writeword; lan9250_readword;
  spi_xchg; spi_write; spi_read],
  cmd.seq (@cmd.store flatparams access_size.word (expr.literal (Ox"10012038")) (expr.literal (Z.shiftl (Ox"f") 2))) (
  cmd.seq (@cmd.store flatparams access_size.word (expr.literal (Ox"10012008")) (expr.literal (Z.shiftl 1 23)))
  (@cmd.call flatparams ["_"] "lan9250_init" [])),
  (* @cmd.call flatparams ["_"] "iot" [expr.literal (Ox"80000000")] *)
  @cmd.call flatparams ["_"] "iot" [expr.literal (1024*4)]
  (* (@cmd.call flatparams ["a"; "b"] "lan9250_readword" [expr.literal (Ox"64")]) *)
  (* @cmd.call flatparams ["_"] "spi_write" [expr.literal (Ox"a5")] *)
).

Definition prog_for_compiler :=
  let '(functions, initial, reactive) := prog in
     (@Build_Program (FlattenExpr.mk_Semantics_params (@Pipeline.FlattenExpr_parameters params))
                     _
                     (List.map fst functions)
                     (RegRename.map.putmany_of_pairs map.empty functions)
                     initial
                     reactive).

Definition compiled := compile_prog (p:=params) prog_for_compiler ml.

Import riscv.Utility.InstructionNotations.
Import bedrock2.Hexdump.
Local Open Scope hexdump_scope.
Set Printing Width 108.


Goal True.
  pose (SortedList.value (function_positions (p := params) prog_for_compiler)) as symbols.
  cbv in symbols.

  let r := eval cbv in (([[
                         ]] ++ compiled)%list%Z) in
  pose r as asm.
  Import bedrock2.NotationsCustomEntry.

  (* searching for "addi    x2, x2, -" shows where the functions begin, and the first
     thing they do is to save all used registers onto the stack, so we can look for the
     max there to see how many registers a function needs *)

  let x := eval cbv in (instrencode asm) in
  idtac x.
Abort.

Unset Printing Width.
