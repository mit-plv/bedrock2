Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Traces.Trace.

Import TrMonad.

Section Stdout.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok _}.

  Definition write (s: string) : Eventful string unit :=
    {| val := tt; trace := [s] |}.

  Notation Writeful A := (Eventful string A).

  Compute (let/! x := {| val := "A"; trace := [1] |} in
           let/! y := {| val := "B"; trace := [2] |} in
           let/! z := (let/! x := {| val := "C"; trace := [3] |} in
                      let/! y := {| val := "D"; trace := [4] |} in
                      ret (x ++ y)) in
           ret (x ++ y ++ z))%string.

  Notation trace_entry := ((fun (A: Type) (_: list A) => A) _ ([]: Semantics.trace)).

  Definition words_of_const_string (s: string) : list (Semantics.word) :=
    let chars := String.list_byte_of_string s in
    List.map (fun b => word_of_byte b) chars.

  Definition literals_of_const_string (s: string) : list expr :=
    let chars := String.list_byte_of_string s in
    List.map (fun b => expr.literal (byte.unsigned b)) chars.

  Definition trace_entry_of_write (s: string) : trace_entry := (* FIXME *)
    (map.empty, "print", words_of_const_string s, (map.empty, [])).

  Definition tbind {Evt A}
             (tr0: list Evt) (pred: Eventful Evt A -> predicate)
             (k: Eventful Evt A) :=
    pred {| val := k.(val); trace := k.(trace) ++ tr0 |}.

  Lemma compile_print {tr mem locals functions} (s: string) :
    let c := write s in
    forall {B} {pred: Writeful B -> predicate}
      {k: unit -> Writeful B} {k_impl}
      tr0 var,

      (<{ Trace := (trace_entry_of_write s) :: tr;
          Memory := mem;
          Locals := map.put locals var (word.of_Z 0);
          Functions := functions }>
       k_impl
       <{ tbind (s :: tr0) pred (k tt) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.interact [var] "stdout.write" (literals_of_const_string s))
        k_impl
      <{ tbind tr0 pred (bindn [var] c k) }>.
  Proof.
  Admitted.

  Definition hello_world_src (y: Semantics.word) : Eventful string Semantics.word :=
    let/n x := word.of_Z 1 in
    let/! _ := write "hello, world!" in
    let/n out := word.add x y in
    ret out.

  Definition tracebind {Evt A}
             (trace_entry_of_event: Evt -> trace_entry)
             (prog: Eventful Evt A)
             (k: A -> Semantics.trace -> Prop) : Prop :=
    k prog.(val) (List.map trace_entry_of_event prog.(trace)).

  Instance spec_of_hello_word : spec_of "hello_world" :=
    fnspec! "hello_world" y / (R: Semantics.mem -> Prop),
    { requires tr mem := R mem;
      ensures tr' mem' rets :=
        tracebind trace_entry_of_write
                  (hello_world_src y)
                  (fun val tr0 => tr' = tr0 ++ tr /\ (R mem' /\ rets = [val])) }.

  Hint Extern 1 => simple eapply compile_print; shelve : compiler.

  Lemma compile_setup_trace_tbind {tr mem locals functions} :
    forall {Evt A} {pred: A -> _ -> predicate}
      {spec: Eventful Evt A} {cmd}
      (trace_entry_of_event: Evt -> trace_entry)
      retvars,

      (let pred a :=
           wp_bind_retvars
             retvars
             (fun rets tr' mem' locals' =>
                tracebind
                  trace_entry_of_event spec
                  (fun val tr1 =>
                     tr' = tr1 ++ tr /\ pred val rets tr' mem' locals')) in
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       cmd
       <{ tbind [] pred spec }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd
      <{ (fun spec =>
            wp_bind_retvars
              retvars
              (fun rets tr' mem' locals' =>
                 tracebind
                   trace_entry_of_event spec
                   (fun val tr1 =>
                      tr' = tr1 ++ tr /\ pred val rets tr' mem' locals')))
           spec }>.
  Admitted.

  Hint Resolve compile_setup_trace_tbind : compiler_setup.
  Hint Unfold tracebind: compiler_cleanup.
  Hint Unfold tbind: compiler_cleanup.
  Hint Unfold ret: compiler_cleanup.

  Derive hello_world_body SuchThat
         (defn! "hello_world"("y") ~> "out"
              { hello_world_body },
          implements hello_world_src)
  As hello_world_target_correct.
  Proof.
    compile.
  Qed.
End Stdout.

Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.
Arguments hello_world_body /.
Eval cbv in hello_world_body.

Require Import bedrock2.ToCString.
Compute c_func ("hello_world", (["y"], ["out"], hello_world_body)).
