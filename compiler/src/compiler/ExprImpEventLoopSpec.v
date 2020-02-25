Require Import Coq.ZArith.ZArith.
Require Coq.Strings.String.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import bedrock2.MetricLogging.
Require Import compiler.SeparationLogic.
Require Import compiler.PipelineWithRename.

Section Params1.
  Context {p: Semantics.parameters}.

  Set Implicit Arguments.

  Record ProgramSpec: Type := {
    datamem_start: Semantics.word;
    datamem_pastend: Semantics.word;
    (* trace invariant which holds at the beginning (and end) of each loop iteration,
       but might not hold in the middle of the loop because more needs to be appended *)
    goodTrace: Semantics.trace -> Prop;
    (* state invariant which holds at the beginning (and end) of each loop iteration *)
    isReady: Semantics.trace -> Semantics.mem -> Prop;
  }.

  Definition hl_inv(spec: ProgramSpec)(t: Semantics.trace)(m: Semantics.mem)
             (l: Semantics.locals)(mc: bedrock2.MetricLogging.MetricLog)
    : Prop := (* Restriction: no locals can be shared between loop iterations *)
    spec.(isReady) t m /\ spec.(goodTrace) t.

  Local Set Warnings "-cannot-define-projection".

  Record ProgramSatisfiesSpec(init_f loop_f: String.string)
         (e: Semantics.env)
         (spec: ProgramSpec): Prop :=
  {
    funs_valid: ExprImp.valid_funs e;
    init_code: Syntax.cmd.cmd;
    get_init_code: map.get e init_f = Some (nil, nil, init_code);
    init_code_correct: forall m0 mc0,
        mem_available spec.(datamem_start) spec.(datamem_pastend) m0 ->
        Semantics.exec e init_code nil m0 map.empty mc0 (hl_inv spec);
    loop_body: Syntax.cmd.cmd;
    get_loop_body: map.get e loop_f = Some (nil, nil, loop_body);
    loop_body_correct: forall t m l mc,
        hl_inv spec t m l mc ->
        Semantics.exec e loop_body t m l mc (hl_inv spec);
  }.

End Params1.
