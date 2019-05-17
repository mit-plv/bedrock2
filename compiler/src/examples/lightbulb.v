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
Require Import bedrock2.Examples.SPI.
Require Import bedrock2.Examples.LAN9250.
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

(*
Definition prog := (
  [iot; lightbulb; recvEthernet; lan9250_readword; spi_write; spi_read],
  @cmd.skip flatparams,
  @cmd.call flatparams [] "iot" []).
*)

Definition prog := (
  [spi_write],
  @cmd.skip flatparams,
  @cmd.call flatparams [] "spi_write" []).

Require Import compiler.RegAlloc.

Goal compile prog = nil.
  cbv [compile prog compile_prog functions2Riscv FlatToRiscvDef.compile_functions compile_main
      FlatToRiscvDef.compile_main].

  match goal with
  | |- context [?T] =>
    match T with
    | RegAlloc.rename_functions ?a ?b ?c =>
      assert (T = map.empty); [|admit];
        let b' := eval cbv in b in change b with b'; simpl c

    end
  end.
  cbv [RegAlloc.rename_functions].
  match goal with
  | |- map.put map.empty _ ?T = _ =>
    assert (T = (nil, nil, FlatImp.SSkip)); [|admit]
  end.

  cbv [rename_function].

  match goal with
  | |- match ?T with _ => _ end = _ =>
    let r := eval cbv in T in change T with r; cbv iota beta
  end.
  match goal with
  | |- match ?T with _ => _ end = _ =>
    assert (T = None); [|admit]
  end.
  cbv [rename_fun].
  match goal with
  | |- match ?T with _ => _ end = _ =>
    let r := eval cbv in T in change T with r; cbv iota beta
  end.
  match goal with
  | |- match ?T with _ => _ end = _ =>
    let r := eval cbv in T in change T with r; cbv iota beta
  end.
  match goal with
  | |- match ?T with _ => _ end = _ =>
    assert (T = None); [|admit]
  end.
  cbv [rename_stmt].
  match goal with
  | |- context [?T] =>
    match T with
    | rename ?a ?b ?c =>
      let T' := eval cbv in T in change T with T'
    end
  end.
  cbv beta iota.
  (* we can see that the checker fails *)


Export bopname.

Notation "a ; b" := (ASSeq a b) (only printing, right associativity,
      at level 50, format "a ; '//' b") : regalloc_scope.
Notation "a '($r' b ')' = c" := (ASLit a b c) (only printing,
      at level 40, format "a '($r' b ')'  =  c") : regalloc_scope.
Notation "a '($r' b ')' = c" := (ASSet a b c) (only printing,
      at level 40, format "a '($r' b ')'  =  c") : regalloc_scope.
Notation "a '($r' b ')' = op c d" := (ASOp a b op c d) (only printing,
      at level 40, format "a '($r' b ')'  =  op  c  d") : regalloc_scope.
Notation "'loop' a 'breakUnless' cond b" := (ASLoop a cond b)
      (only printing, at level 50, a at level 40,
       format "'loop' '[v ' '//' a '//' 'breakUnless'  cond '//' b ']'") : regalloc_scope.
Notation "'skip'" := ASSkip (only printing) : regalloc_scope.

Open Scope regalloc_scope.
(*
  idtac.


  cbv [checker].
  match goal with
  | |- match ?T with _ => _ end = _ =>
    assert (T = None); [|admit]
  end.
  match goal with
  | |- match ?T with _ => _ end = _ =>
    assert (T = None); [|admit]
  end.
  match goal with
  | |- match ?T with _ => _ end = _ =>
    let T' := eval cbv in T in change T with T'
  end.
  cbv beta iota.
  match goal with
  | |- match ?T with _ => _ end = _ =>
    assert (T = None); [|admit]
  end.
  match goal with
  | |- match ?T with _ => _ end = _ =>
    assert (T = None); [|admit]
  end.
  match goal with
  | |- match ?T with _ => _ end = _ =>
    assert (T = None); [|admit]
  end.
  unfold cond_checker.
  match goal with
  | |- match ?T with _ => _ end = _ =>
    assert (T = None); [|admit]
  end.
  match goal with
  | |- map.get ?M ?K = None => simpl M
  end.

  (* one side mapped "busy" to 4 while the other side mapped busy to 8 *)

cbv.

  match goal with
  | |- (let '(a, b, c) := ?B in ?C) = None => idtac B
  end.

  let b := eval cbv delta [rename] in @rename in change @rename with b.
  cbv beta.
  cbv fix beta iota.
  match goal with
  | |- match ?T with _ => _ end = _ =>
    let r := eval cbv in T in change T with r; cbv iota beta
  end.


  cbv.


  simpl.


  cbv.


  cbv.

  simpl.
*)
Abort.

Import riscv.Utility.InstructionNotations.
Import bedrock2.Hexdump.
Local Open Scope hexdump_scope.
Set Printing Width 108.


Goal True.
  Time
  let r := eval vm_compute in (([[
                         ]] ++ compile prog)%list%Z) in
  pose r as asm.
  Import bedrock2.NotationsCustomEntry.

  (* searching for "addi    x2, x2, -" shows where the functions begin, and the first
     thing they do is to save all used registers onto the stack, so we can look for the
     max there to see how many registers a function needs *)

  let x := eval cbv in (instrencode asm) in
  idtac x.
Abort.
