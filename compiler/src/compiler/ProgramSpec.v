Require Import Coq.ZArith.ZArith.
Require Coq.Strings.String.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import bedrock2.MetricLogging.
Require Import compiler.SeparationLogic.
Require compiler.ExprImp.

Section Params0.
  Context {p: Syntax.parameters}
          (Code: Type)
          {env: map.map Syntax.funname (list Syntax.varname * list Syntax.varname * Code)}.

  Set Implicit Arguments.

  Record Program : Type := {
    funnames: list Syntax.funname;
    funimpls: env;
    init_code: Code;
    loop_body: Code;
  }.
End Params0.

Arguments Program {_} _ {_}.

Section Params1.
  Context {p: Semantics.parameters}.
  Variable Code: Type.

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

  Record ProgramSatisfiesSpec
         (prog: Program Code)
         (exec: Semantics.funname_env (list Syntax.varname * list Syntax.varname * Code) ->
                Code -> Semantics.trace -> Semantics.mem -> Semantics.locals -> MetricLog ->
                (Semantics.trace -> Semantics.mem -> Semantics.locals -> MetricLog -> Prop) ->
                Prop)
         (spec: ProgramSpec): Prop :=
  {
    funnames_NoDup: NoDup prog.(funnames);

    (* TODO we should have an iterable map *)
    funnames_matches_dom: forall f,
        map.get prog.(funimpls) f <> None <-> List.In f prog.(funnames);

    init_code_correct: forall m0 mc0,
      mem_available spec.(datamem_start) spec.(datamem_pastend) m0 ->
      exec prog.(funimpls) prog.(init_code) nil m0 map.empty mc0
        (fun t' m' l' mc' => spec.(isReady) t' m' l' /\ spec.(goodTrace) t' /\ l' = map.empty);

    loop_body_correct: forall t m mc,
       spec.(isReady) t m map.empty ->
       spec.(goodTrace) t ->
       exec prog.(funimpls) prog.(loop_body) t m map.empty mc
        (fun t' m' l' mc' => spec.(isReady) t' m' l' /\ spec.(goodTrace) t' /\ l' = map.empty);
  }.

End Params1.
