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
Definition params : Pipeline.parameters. simple refine {|
  Pipeline.locals := _;
  Pipeline.Registers := _;
  Pipeline.ext_spec _ _ := TODO;
  Pipeline.ext_guarantee _ := False;
  Pipeline.PRParams := TODO;
|}; unshelve (try exact _); apply TODO. Defined.
Definition flatparams := (FlattenExpr.mk_Syntax_params (@Pipeline.FlattenExpr_parameters params)).
Instance pipeline_assumptions: @Pipeline.assumptions params. Admitted.
Instance mapops: RegAlloc.map.ops (SortedListString.map Z). refine (
  {| RegAlloc.map.intersect (s1 s2 : SortedListString.map Z) :=
    {| value := ListLib.list_intersect (fun '(k,v) '(k',v') => andb (_ k k') (_ v v')) (value s1) (value s2); _value_ok := TODO |} |}).
- exact String.eqb.
- exact Z.eqb.
Defined.

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

(*
Import riscv.Utility.InstructionNotations.
Import bedrock2.Hexdump.
Local Open Scope hexdump_scope.
Set Printing Width 108.
*)

Goal compile prog = nil.
  cbv [compile compile_prog functions2Riscv prog].
  match goal with
  | |- context [@flatten_functions ?p ?E ?Fs] =>
    let r := eval cbv in (@flatten_functions p E Fs) in change (@flatten_functions p E Fs) with r
  end.
  cbv [RegAlloc.rename_functions funnames List.map fst].
  cbv [iot lightbulb recvEthernet].

  match goal with
  | |- context [?T] =>
    lazymatch T with
      RegAlloc.rename_function available_registers ?E ?N =>
      assert (T = (nil, nil, FlatImp.SSkip))
    end
  end.
  {
    unfold RegAlloc.rename_function.
    match goal with
    | |- context [@map.get ?k ?v ?m ?K ?M] =>
      let r := eval cbv in (@map.get k v m K M) in change (@map.get k v m K M) with r
    end.
    cbv iota beta.
    unfold RegAlloc.rename_fun.
    progress simpl (RegAlloc.rename_binds ["rx_packet"] available_registers).
    cbv iota beta.
    progress simpl (RegAlloc.rename_binds ["r"]
        [4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26;
        27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 48;
        49; 50; 51; 52]).
    cbv iota beta.
    cbv [RegAlloc.rename_stmt].
    match goal with
    | |- context [RegAlloc.rename ?A ?B ?C] =>
      let r := eval cbv in (RegAlloc.rename A B C) in
          change (RegAlloc.rename  A B C) with r
    end.
    Set Printing Depth 100000.
    cbv iota beta.
    match goal with
    | |- context [@RegAlloc.checker ?srcvar ?impvar ?func ?act ?src2imp ?ops ?m ?s] =>
      set (test := ops)
    end.
    exfalso.

    pose (m1 := map.put (map.put map.empty "a" 1) "b" 2).
    pose (m2 := map.put (map.put map.empty "a" 1) "b" 22).
    cbv in m1.
    cbv in m2.
    pose (m3 := RegAlloc.map.intersect m1 m2).
    unfold RegAlloc.map.intersect, test, mapops in m3.
    subst m1 m2.
    assert (m3 = map.empty). {
      subst test m3.
      unfold ListLib.list_intersect.
      simpl.
      (* intersect now works *)
Abort.

(*
Goal True.
  Time
  let r := eval vm_compute in (([[
                         ]] ++ compile prog)%list%Z) in
  pose r as asm.
  (* {| value := [("iot", 0); ("lightbulb", 112); ("recvEthernet", 132)]; _value_ok := eq_refl |} *)
  Import bedrock2.NotationsCustomEntry.
  Set Printing Width 120.
  Eval cbv in prog.


  let x := eval cbv in (instrencode asm) in
  idtac x.
Abort.
*)
