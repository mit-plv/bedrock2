Require Import Coq.ZArith.ZArith.
Require Coq.Strings.String.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.Semantics.
Require Import compiler.SeparationLogic.
Require Import compiler.LowerPipeline.
Require Import compiler.Pipeline.

Section Params1.
  Context {width} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: LeakageSemantics.ExtSpec}.

  Set Implicit Arguments.

  Record ProgramSpec: Type := {
    datamem_start: word;
    datamem_pastend: word;
    (* trace invariant which holds at the beginning (and end) of each loop iteration,
       but might not hold in the middle of the loop because more needs to be appended *)
    goodTrace: Semantics.trace -> Prop;
    (* state invariant which holds at the beginning (and end) of each loop iteration *)
    isReady: Semantics.trace -> mem -> Prop;
  }.

  Definition hl_inv(spec: ProgramSpec)(k: LeakageSemantics.leakage)(t: Semantics.trace)
    (m: mem)(l: locals)(mc: bedrock2.MetricLogging.MetricLog)
    : Prop := (* Restriction: no locals can be shared between loop iterations *)
    spec.(isReady) t m /\ spec.(goodTrace) t.

  Local Set Warnings "-cannot-define-projection".

  Record ProgramSatisfiesSpec(init_f loop_f: String.string)
         (e: list (String.string * (list String.string * list String.string * Syntax.cmd)))
         (spec: ProgramSpec): Prop :=
  {
    funs_valid: valid_src_funs e = true;
    init_code: Syntax.cmd.cmd;
    get_init_code: map.get (map.of_list e : env) init_f = Some (nil, nil, init_code);
    init_code_correct: forall k0 m0 mc0,
        mem_available spec.(datamem_start) spec.(datamem_pastend) m0 ->
        (forall pick_spH : LeakageSemantics.PickSp, MetricLeakageSemantics.exec (map.of_list e) init_code nil k0 m0 map.empty mc0 (hl_inv spec));
    loop_body: Syntax.cmd.cmd;
    get_loop_body: map.get (map.of_list e : env) loop_f = Some (nil, nil, loop_body);
    loop_body_correct: forall k t m l mc,
        hl_inv spec k t m l mc ->
        (forall pick_spH : LeakageSemantics.PickSp, MetricLeakageSemantics.exec (map.of_list e) loop_body k t m l mc (hl_inv spec));
  }.

End Params1.
