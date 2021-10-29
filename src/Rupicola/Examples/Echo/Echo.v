Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Echo.IO.

(* Import IO. *)

Section Echo.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Definition getw_trace (w: word) : trace_entry :=
    (map.empty (map := mem), "getw", [], (map.empty, [w])).

  Definition putw_trace (w: word) : trace_entry :=
    (map.empty (map := mem), "putw", [w], (map.empty, [])).

  Instance spec_of_getw : spec_of "getw" :=
    fnspec! "getw" ~> r,
    { requires tr mem := True;
      ensures tr' mem' :=
        mem' = mem /\
        tr' = getw_trace r :: tr }.

  Instance spec_of_putw : spec_of "putw" :=
    fnspec! "putw" w ~> r,
    { requires tr mem := True;
      ensures tr' mem' :=
        mem' = mem /\
        r = word.of_Z 0 /\
        tr' = putw_trace w :: tr }.

  Definition trace_entry_of_event (evt: IO.Event word) :=
    match evt with
    | IO.R t => getw_trace t
    | IO.W t => putw_trace t
    end.

  Notation IO := (IO.M word).
  Notation iospec_k := (iospec_k trace_entry_of_event).

  Lemma compile_getw : forall {tr mem locals functions},
    let io: IO _ := Free.Call IO.Read in
    forall {A} {pred: A -> predicate}
      {k: word -> IO A} {k_impl}
      var,

      (_: spec_of "getw") functions ->

      (forall w,
          let evt := getw_trace w in
          <{ Trace := evt :: tr;
             Memory := mem;
             Locals := map.put locals var w;
             Functions := functions }>
          k_impl
          <{ iospec_k (evt :: tr) pred (k w) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (* FIXME cmd.interact? *)
        (cmd.call [var] "getw" [])
        k_impl
      <{ iospec_k tr pred (mbindn [var] io k) }>.
  Proof.
    repeat straightline.
    straightline_call; eauto; [].
    repeat straightline; subst_lets_in_goal.
    eapply WeakestPrecondition_iospec_k_bindn
      with (outa := {| Writer.val := x; Writer.trace := [IO.R x] |}).
    - apply IO.ValidRead with (t := []), IO.ValidPure.
    - intros; eapply H0.
  Qed.

  Lemma compile_putw : forall {tr mem locals functions} (w: word),
    let io: IO unit := Free.Call (IO.Write w) in
    forall {A} {pred: A -> predicate}
      {k: unit -> IO A} {k_impl}
      w_expr var,

      WeakestPrecondition.dexpr mem locals w_expr w ->

      (_: spec_of "putw") functions ->
      let evt := putw_trace w in

      (<{ Trace := evt :: tr;
          Memory := mem;
          Locals := map.put locals var (word.of_Z 0);
          Functions := functions }>
       k_impl
       <{ iospec_k (evt :: tr) pred (k tt) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (* FIXME cmd.interact? *)
        (cmd.call [var] "putw" [w_expr])
        k_impl
      <{ iospec_k tr pred (mbindn [var] io k) }>.
  Proof.
    repeat straightline.
    eexists; split; repeat straightline.
    eapply WeakestPrecondition_dexpr_expr; eauto. (* FIXME what's a cleaner way to do this? *)
    repeat straightline.
    straightline_call; eauto; [].
    repeat straightline; subst_lets_in_goal.
    eapply WeakestPrecondition_iospec_k_bindn
      with (outa := {| Writer.val := tt; Writer.trace := [IO.W w] |}).
    - apply IO.ValidWrite with (t := []), IO.ValidPure.
    - intros; eassumption.
  Qed.

  Definition io_sum : IO unit :=
    let/! w1 := IO.Read in
    let/! w2 := IO.Read in
    let/n sum := word.add w1 w2 in
    let/! _ := IO.Write sum in
    mret tt.

  Instance spec_of_hello_word : spec_of "io_sum" :=
    fnspec! "io_sum" / (R: mem -> Prop),
    { requires tr mem :=
        R mem;
      ensures tr' mem' rets :=
        iospec trace_entry_of_event tr io_sum (fun val tr'' => tr' = tr'' /\ R mem') }.

  Hint Extern 1 => simple eapply compile_putw; shelve : compiler.
  Hint Extern 1 => simple eapply compile_getw; shelve : compiler.

  Derive io_sum_body SuchThat
         (defn! "io_sum"()
              { io_sum_body },
          implements io_sum using ["getw"; "putw"])
  As io_sum_target_correct.
  Proof.
    compile.
  Qed.
End Echo.

Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.
Arguments io_sum_body /.
Eval cbv in io_sum_body.

Require Import bedrock2.ToCString.
Compute c_func ("io_sum", (["y"], ["out"], io_sum_body)).
