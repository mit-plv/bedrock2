Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Echo.IO.

Import IOMonad.

Section Echo.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Definition putw_trace (w: word) : trace_entry :=
    (map.empty (map := mem), "putw", [w], (map.empty, [])).

  Definition getw_trace (w: word) : trace_entry :=
    (map.empty (map := mem), "getw", [], (map.empty, [w])).

  Instance spec_of_putw : spec_of "putw" :=
    fnspec! "putw" w ~> r,
    { requires tr mem := True;
      ensures tr' mem' :=
        mem' = mem /\
        r = word.of_Z 0 /\
        tr' = putw_trace w :: tr }.

  Instance spec_of_getw : spec_of "getw" :=
    fnspec! "getw" ~> r,
    { requires tr mem := True;
      ensures tr' mem' :=
        mem' = mem /\
        tr' = getw_trace r :: tr }.

  Definition trace_entry_of_event (evt: Event word) :=
    match evt with
    | R t => getw_trace t
    | W t => putw_trace t
    end.

  Notation IO := (IO word).
  Notation iospec_k := (iospec_k trace_entry_of_event).

  Lemma compile_putw : forall {tr mem locals functions} (w: word),
    let io: IO unit := Call (Write w) in
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
      <{ iospec_k tr pred (bindn [var] io k) }>.
  Proof.
    repeat straightline.
    eexists; split; repeat straightline.
    eapply WeakestPrecondition_dexpr_expr; eauto. (* FIXME what's a cleaner way to do this? *)
    repeat straightline.
    straightline_call; eauto; [].
    repeat straightline; subst_lets_in_goal.
    eapply WeakestPrecondition_weaken; try eassumption; [].

    unfold bindn, FreeMonad.bindn, Call, iospec_k, iospec, iobind; simpl; intros.
    rewrite tbind_bindn; eassumption.
  Qed.

  Definition hello_world_src (y: word) : Eventful string word :=
    let/n x := word.of_Z 1 in
    let/! _ := write "hello, world!" in
    let/n out := word.add x y in
    ret out.

  Instance spec_of_hello_word : spec_of "hello_world" :=
    fnspec! "hello_world" y / (R: mem -> Prop),
    { requires tr mem :=
        R mem;
      ensures tr' mem' rets :=
        tracebind trace_entry_of_write
                  (hello_world_src y)
                  (fun val tr0 => tr' = tr0 ++ tr /\ (R mem' /\ rets = [val])) }.

  Hint Extern 1 => simple eapply compile_putchars; shelve : compiler.

  Derive hello_world_body SuchThat
         (defn! "hello_world"("y") ~> "out"
              { hello_world_body },
          implements hello_world_src using ["putchars"])
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
