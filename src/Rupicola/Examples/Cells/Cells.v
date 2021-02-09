Require Import Rupicola.Lib.Api.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Record cell := { data : Semantics.word }.

  Definition cell_value (addr: address) (c: cell)
    : Semantics.mem -> Prop :=
    scalar addr c.(data).

  Definition OneCell c_ptr c
    : list word -> Semantics.mem -> Prop :=
    fun _ => cell_value c_ptr c.

  Definition TwoCells a_ptr b_ptr ab
    : list word -> Semantics.mem -> Prop :=
    fun _ =>
      sep (cell_value a_ptr (fst ab)) (cell_value b_ptr (snd ab)).

  Definition get c := c.(data).
  Definition put v (c: cell) := {| data := v |}.

  Lemma compile_get
        {tr mem locals functions} {T} {pred: T -> predicate} :
    forall R c c_ptr c_var k k_impl var,

      sep (cell_value c_ptr c) R mem ->
      map.get locals c_var = Some c_ptr ->

      let v := (get c) in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.load access_size.word (expr.var c_var)))
              k_impl
      <{ pred (nlet [var] v k) }>.
  Proof.
    intros.
    repeat straightline.
    exists (get c).
    split.
    { cbn.
      red.
      exists c_ptr.
      split.
      { eassumption. }
      { eexists; split; [ | reflexivity ].
        eapply load_word_of_sep.
        eassumption. } }
    red; intros.
    eassumption.
  Qed.

  Lemma compile_put
        {tr mem locals functions} {T} {pred: T -> predicate} :
    forall R c c_ptr c_var x x_var k k_impl,

      sep (cell_value c_ptr c) R mem ->
      map.get locals c_var = Some c_ptr ->
      map.get locals x_var = Some x ->

      let v := (put x c) in
      (let v := v in
       forall m,
         sep (cell_value c_ptr v) R m ->
         (<{ Trace := tr;
             Memory := m;
             Locals := locals;
             Functions := functions }>
          k_impl
          <{ pred (k v) }>)) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.store access_size.word (expr.var c_var) (expr.var x_var))
              k_impl
      <{ pred (nlet [c_var] v k) }>.
  Proof.
    intros.
    unfold cell_value in *.
    repeat straightline.
    exists c_ptr; split; eexists; split; eauto.
    - repeat straightline; eexists; split; eauto.
    - repeat straightline; eauto.
  Qed.
End with_parameters.

Hint Unfold OneCell TwoCells : compiler.

Ltac cell_compile_step :=
  first [simple eapply compile_get |
         simple eapply compile_put].

Ltac compile_custom ::=
  cell_compile_step.
