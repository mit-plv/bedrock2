Require Import Rupicola.Lib.Api.

Section with_semantics.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Record cell := { data : Semantics.word }.

  Definition cell_value (addr: address) (c: cell) : Semantics.mem -> Prop :=
    scalar addr c.(data).

  Definition TwoCells a_ptr b_ptr ab : Semantics.mem -> Prop :=
    sep (cell_value a_ptr (fst ab)) (cell_value b_ptr (snd ab)).

  Hint Unfold TwoCells : compiler.

  Definition get c := c.(data).
  Definition put v (c: cell) := {| data := v |}.

  Lemma compile_get :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr R R' functions T (pred: T -> _ -> Prop)
           c c_ptr c_var k k_impl,
    forall var,
      sep (cell_value c_ptr c) R' mem ->
      map.get locals c_var = Some c_ptr ->
      let v := (get c) in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-locals-post locals_ok
       with-locals (map.put locals var head)
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.load access_size.word (expr.var c_var)))
                     k_impl)
       implementing (pred (dlet head k))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
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

  Lemma compile_put :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr R R' functions T (pred: T -> _ -> Prop)
           c c_ptr c_var x x_var k k_impl,
      sep (cell_value c_ptr c) R' mem ->
      map.get locals c_var = Some c_ptr ->
      map.get locals x_var = Some x ->
      let v := (put x c) in
      (let head := v in
       forall m,
         sep (cell_value c_ptr head) R' m ->
         (find k_impl
          implementing (pred (k head))
          and-locals-post locals_ok
          with-locals locals
          and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq (cmd.store access_size.word (expr.var c_var) (expr.var x_var))
                     k_impl)
       implementing (pred (dlet head k))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    unfold cell_value in *.
    repeat straightline.
    exists c_ptr.
    split.
    { repeat straightline; eauto. }
    { eexists; split.
      { repeat straightline; eauto. }
      repeat straightline.
      subst v; simpl.
      match goal with
      | [ H: context[WeakestPrecondition.cmd] |- _ ] => apply H
      end.
      eassumption. }
  Qed.
End with_semantics.
Hint Unfold TwoCells : compiler.

Ltac cell_compile_step :=
  gen_sym_inc;
  let name := gen_sym_fetch "v" in
  first [simple eapply compile_get with (var := name) |
         simple eapply compile_put].

Ltac compile_custom ::=
  cell_compile_step.
