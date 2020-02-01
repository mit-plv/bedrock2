Require Import Coq.ZArith.ZArith.
Require Coq.Strings.String.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import bedrock2.MetricLogging.
Require Import compiler.SeparationLogic.
Require compiler.ExprImp.

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
    isReady: Semantics.trace -> Semantics.mem -> Semantics.locals -> Prop;
  }.

  Definition mem_available(start pastend: Semantics.word)(m: Semantics.mem): Prop :=
    exists anybytes: list Semantics.byte,
      Z.of_nat (List.length anybytes) = word.unsigned (word.sub pastend start) /\
      array ptsto (word.of_Z 1) start anybytes m.

  Definition hl_inv(spec: ProgramSpec)(t: Semantics.trace)(m: Semantics.mem)(l: Semantics.locals)(mc: MetricLog)
    : Prop := (* Restriction: no locals can be shared between loop iterations *)
    spec.(isReady) t m l /\ spec.(goodTrace) t /\ l = map.empty.

  Record ProgramSatisfiesSpec(init_f loop_f: String.string)
         (e: Semantics.env)
         (spec: ProgramSpec): Prop :=
  {
    funs_valid: ExprImp.valid_funs e;

    init_code_correct: forall m0 mc0,
        mem_available spec.(datamem_start) spec.(datamem_pastend) m0 ->
        Semantics.exec e (Syntax.cmd.call nil init_f nil) nil m0 map.empty mc0 (hl_inv spec);

    loop_body_correct: forall t m l mc,
        hl_inv spec t m l mc ->
        Semantics.exec e (Syntax.cmd.call nil loop_f nil) t m l mc (hl_inv spec);
  }.

End Params1.
