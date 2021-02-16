Require Import Rupicola.Lib.Api.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Record cell := { data : Semantics.word }.

  Definition cell_value (addr: address) (c: cell)
    : Semantics.mem -> Prop :=
    scalar addr c.(data).

  Definition get c := c.(data).
  Definition put v (c: cell) := {| data := v |}.

  Lemma compile_get {tr mem locals functions} (c: cell) :
    let v := get c in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      R c_ptr c_var var,

      sep (cell_value c_ptr c) R mem ->
      map.get locals c_var = Some c_ptr ->

      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.load access_size.word (expr.var c_var)))
              k_impl
      <{ pred (nlet_eq [var] v k) }>.
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

  Lemma compile_put {tr mem locals functions} x c:
    let v := put x c in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      R c_ptr c_var x_var,

      sep (cell_value c_ptr c) R mem ->
      map.get locals c_var = Some c_ptr ->
      map.get locals x_var = Some x ->

      (let v := v in
       forall m,
         sep (cell_value c_ptr v) R m ->
         (<{ Trace := tr;
             Memory := m;
             Locals := locals;
             Functions := functions }>
          k_impl
          <{ pred (k v eq_refl) }>)) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.store access_size.word (expr.var c_var) (expr.var x_var))
              k_impl
      <{ pred (nlet_eq [c_var] v k) }>.
  Proof.
    intros.
    unfold cell_value in *.
    repeat straightline.
    exists c_ptr; split; eexists; split; eauto.
    - repeat straightline; eexists; split; eauto.
    - repeat straightline; eauto.
  Qed.
End with_parameters.

Hint Extern 1 => simple eapply compile_get; shelve : compiler.
Hint Extern 1 => simple eapply compile_put; shelve : compiler.
