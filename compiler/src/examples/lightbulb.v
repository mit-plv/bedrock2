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
Require Import bedrock2.Examples.lightbulb.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope ilist_scope.

Axiom TODO: forall {T: Type}, T.

Local Existing Instance DefaultRiscvState.
Local Existing Instance coqutil.Map.SortedListString.map.
Local Existing Instance coqutil.Map.SortedListString.ok.
Instance flatToRiscvDef_params: FlatToRiscvDef.FlatToRiscvDef.parameters := {
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call argnames fname retnames :=
    if string_dec fname "nop" then
      [[Addi Register0 Register0 0]]
    else
      nil;
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call_length _ := TODO;
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call_emits_valid _ _ := TODO;
}.
Notation RiscvMachine := MetricRiscvMachine.

Instance mapops: RegAlloc.map.ops (SortedListString.map Z). refine (
  {| RegAlloc.map.intersect (s1 s2 : SortedListString.map Z) :=
    {| value := ListLib.list_intersect (fun '(k,v) '(k',v') => andb (_ k k') (_ v v')) (value s1) (value s2); _value_ok := TODO |} |}).
- exact String.eqb.
- exact Z.eqb.
Defined.

Definition params : Pipeline.parameters. simple refine {|
  Pipeline.locals := _;
  Pipeline.Registers := _;
  Pipeline.ext_spec _ _ := TODO;
  Pipeline.ext_guarantee _ := False;
  Pipeline.PRParams := TODO;
  Pipeline.src2imp_ops := mapops;
|}; unshelve (try exact _); apply TODO. Defined.
Definition flatparams := (FlattenExpr.mk_Syntax_params (@Pipeline.FlattenExpr_parameters params)).
Instance pipeline_assumptions: @Pipeline.assumptions params. Admitted.

(* stack grows from high addreses to low addresses, first stack word will be written to
   (stack_pastend-4), next stack word to (stack_pastend-8) etc *)
Definition stack_pastend: Z := 1024.
Definition compile '(functions, initial, reactive) :=
  compile_prog (p:=params) stack_pastend
     (@Build_Program (FlattenExpr.mk_Semantics_params (@Pipeline.FlattenExpr_parameters params))
                     (List.map fst functions)
                     (RegAlloc.map.putmany_of_tuples map.empty functions)
                     initial
                     reactive).

Definition instrencode p : list byte :=
  let word8s := List.flat_map (fun inst => HList.tuple.to_list (LittleEndian.split 4 (encode inst))) p in
  List.map (fun w => Byte.of_Z (word.unsigned w)) word8s.

Definition prog := (
  [iot; lightbulb; recvEthernet],
  @cmd.skip flatparams,
  @cmd.call flatparams [] "iot" []).

Definition dummy_iot :=
let p_addr := "p_addr" in
let bytesWritten := "bytesWritten" in
let recvEthernet := "recvEthernet" in
let lightbulb := "lightbulb" in
let r := "r" in
("iot", ([p_addr], [r], (@cmd.set (@syntax FE310CSemantics.parameters) r (lightbulb.literal (1234))))).

Definition dummy_lightbulb :=
let packet := "packet" in
let len := "len" in
let ethertype := "ethertype" in
let protocol := "protocol" in
let port := "port" in
let mmio_val := "mmio_val" in
let command := "command" in
let MMIOREAD := "MMIOREAD" in
let MMIOWRITE := "MMIOWRITE" in
let r := "r" in
("lightbulb",
([packet; len], [r], (@cmd.set (@syntax FE310CSemantics.parameters) r (lightbulb.literal (321))))).

Definition dummy_recvEthernet :=
let info := "info" in
let rxunused := "rx_unused" in
let rx_status := "rx_status" in
let rx_packet := "rx_packet" in
let c := "c" in
let len_bytes := "len_bytes" in
let len_words := "len_words" in
let word := "word" in
let lan9250_readword := "lan9250_readword" in
let r := "r" in
("recvEthernet",
([rx_packet], [r], (@cmd.set (@syntax FE310CSemantics.parameters) r (lightbulb.literal (432))))).

Definition dummy_prog := (
  [dummy_iot; dummy_lightbulb; recvEthernet],
  @cmd.skip flatparams,
  @cmd.call flatparams [] "iot" []).

Import riscv.Utility.InstructionNotations.
Import bedrock2.Hexdump.
Local Open Scope hexdump_scope.
Set Printing Width 108.


Goal True.
  Time
  let r := eval vm_compute in (([[
                         ]] ++ compile prog)%list%Z) in
  pose r as asm.

  (* searching for "addi    x2, x2, -" shows where the functions begin, and the first
     thing they do is to save all used registers onto the stack, so we can look for the
     max there to see how many registers a function needs *)

  let x := eval cbv in (instrencode asm) in
  idtac x.
Abort.
