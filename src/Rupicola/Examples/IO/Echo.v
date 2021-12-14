Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.IO.IO.

Section Echo.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Definition readw_trace (w: word) : trace_entry :=
    (map.empty (map := mem), "readw", [], (map.empty, [w])).

  Definition writew_trace (w: word) : trace_entry :=
    (map.empty (map := mem), "writew", [w], (map.empty, [])).

  Definition trace_entry_of_event (evt: IO.Event word) :=
    match evt with
    | IO.R t => readw_trace t
    | IO.W t => writew_trace t
    end.

  Instance spec_of_readw : spec_of "readw" :=
    fnspec! "readw" ~> r,
    { requires tr mem := True;
      ensures tr' mem' :=
        mem' = mem /\
        tr' = trace_entry_of_event (IO.R r) :: tr }.

  Instance spec_of_writew : spec_of "writew" :=
    fnspec! "writew" w,
    { requires tr mem := True;
      ensures tr' mem' :=
        mem' = mem /\
        tr' = trace_entry_of_event (IO.W w) :: tr }.

  Notation IO := (IO.M word).
  Notation iospec := (iospec trace_entry_of_event).
  Notation iospec_k := (iospec_k trace_entry_of_event).

  Lemma compile_readw : forall {tr mem locals functions},
    let io: IO _ := Free.Call IO.Read in
    forall {A} {pred: A -> pure_predicate}
      {k: word -> IO A} {k_impl}
      var,

      (_: spec_of "readw") functions ->

      (forall w,
          let tr := readw_trace w :: tr in
          <{ Trace := tr;
             Memory := mem;
             Locals := map.put locals var w;
             Functions := functions }>
          k_impl
          <{ iospec_k tr pred (k w) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (* FIXME cmd.interact? *)
        (cmd.call [var] "readw" [])
        k_impl
      <{ iospec_k tr pred (mbindn [var] io k) }>.
  Proof.
    repeat straightline.
    straightline_call; eauto; [].
    repeat straightline; subst_lets_in_goal.
    eapply WeakestPrecondition_iospec_k_bindn
      with (wr := {| Writer.val := x; Writer.trace := [IO.R x] |}).
    - apply IO.ValidRead with (t := []), IO.ValidPure.
    - intros; apply H0.
  Qed.

  Lemma compile_writew : forall {tr mem locals functions} (w: word),
    let io: IO unit := Free.Call (IO.Write w) in
    forall {A} {pred: A -> pure_predicate}
      {k: unit -> IO A} {k_impl}
      w_expr var,

      WeakestPrecondition.dexpr mem locals w_expr w ->

      (_: spec_of "writew") functions ->

      (let tr := writew_trace w :: tr in
      <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       k_impl
       <{ iospec_k tr pred (k tt) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (* FIXME cmd.interact? *)
        (cmd.call [] "writew" [w_expr])
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
      with (wr := {| Writer.val := tt; Writer.trace := [IO.W w] |}).
    - apply IO.ValidWrite with (t := []), IO.ValidPure.
    - intros; eassumption.
  Qed.

  Hint Extern 1 => simple eapply compile_writew; shelve : compiler.
  Hint Extern 1 => simple eapply compile_readw; shelve : compiler.

  Definition io_echo : IO unit :=
    let/! w := call! IO.Read in
    let/! _ := call! IO.Write w in
    mret tt.

  Instance spec_of_io_echo : spec_of "io_echo" :=
    fnspec! "io_echo" / (R: mem -> Prop),
    { requires tr mem := R mem;
      ensures tr' mem' rets := iospec tr tr' io_echo (fun _ => R mem') }.

  Derive io_echo_br2fn SuchThat
   (defn! "io_echo"() { io_echo_br2fn },
    implements io_echo using ["readw"; "writew"])
   As io_echo_br2fn_ok.
  Proof. compile. Qed.

  Definition io_sum : IO unit :=
    let/! w1 := call! IO.Read in
    let/! w2 := call! IO.Read in
    let/n sum := word.add w1 w2 in
    let/! _ := call! IO.Write sum in
    mret tt.

  Instance spec_of_io_sum : spec_of "io_sum" :=
    fnspec! "io_sum" / (R: mem -> Prop),
    { requires tr mem := R mem;
      ensures tr' mem' rets := iospec tr tr' io_sum (fun _ => R mem') }.

  Derive io_sum_br2fn SuchThat
         (defn! "io_sum"() { io_sum_br2fn },
          implements io_sum using ["readw"; "writew"])
  As io_sum_br2fn_ok.
  Proof. compile. Qed.

  Definition io_check expected : IO Z :=
    let/! read := call! IO.Read in
    let/! err := if word.eqb (word := word) read expected
                then let/! _ := call! IO.Write (word.of_Z 0) in
                     mret 0
                else let/! _ := call! IO.Write (word.of_Z 42) in
                     mret 42 in
    let/n err := err + 1 in
    mret err.

  Instance spec_of_io_check : spec_of "io_check" :=
    fnspec! "io_check" expected / (R: mem -> Prop),
    { requires tr mem := R mem;
      ensures tr' mem' rets := iospec tr tr' (io_check expected) (fun val => rets = [word.of_Z val] /\ R mem') }.

  Derive io_check_br2fn SuchThat
         (defn! "io_check"("expected") ~> "err" { io_check_br2fn },
          implements io_check using ["readw"; "writew"])
  As io_check_br2fn_ok.
  Proof.
    compile.
  Qed.
End Echo.

From bedrock2 Require Import BasicC64Semantics NotationsCustomEntry.
Compute io_sum_br2fn. (* (word := word) *)
Compute ToCString.c_func io_echo_br2fn.
Compute ToCString.c_func io_sum_br2fn.
Compute ToCString.c_func (io_check_br2fn (word := word)).
