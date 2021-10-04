Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Conditionals.

Import ExprReflection.

Tactic Notation "_reify_change_dexpr"
       constr(expr) open_constr(reifier)
       constr(val) constr(reified) constr(bindings) :=
  (* unify expr (compile reified); *)
  change val
    with (er_T2w (expr_denotation := reifier)
                 (interp (er := reifier)
                         (map.of_list (map := SortedListString.map _) bindings)
                         reified)).

Ltac reify_change_dexpr_z :=
  lazymatch goal with
  | [  |- WeakestPrecondition.dexpr _ (map.of_list ?bindings) ?expr ?val ] =>
    lazymatch val with
    | word.of_Z ?z =>
      let z_bindings := zify_bindings bindings in
      let z_bindings := type_term z_bindings in
      let reified := expr_reify_Z z_bindings z in
      _reify_change_dexpr expr expr_Z_denotation val reified z_bindings
    end
  end.

Ltac reify_change_dexpr_w :=
  lazymatch goal with
  | [  |- WeakestPrecondition.dexpr _ (map.of_list ?bindings) ?expr ?val ] =>
    lazymatch type of val with
    | @word.rep _ ?W =>
      let reified := expr_reify_word W bindings val in
      _reify_change_dexpr expr expr_word_denotation val reified bindings
    end
  end.

Ltac reify_change_dexpr_locals :=
  lazymatch goal with
  | [  |- WeakestPrecondition.dexpr _ ?locals _ _ ] =>
    let bindings := map_to_list locals in
    set_change locals with (map.of_list bindings)
  end.

Ltac reify_change_dexpr :=
  lazymatch goal with
  | [  |- WeakestPrecondition.dexpr _ _ _ ?val ] =>
    reify_change_dexpr_locals;
    lazymatch val with
    | word.of_Z ?z => reify_change_dexpr_z
    | _ => reify_change_dexpr_w
    end
  end.

#[export] Hint Extern 8 (WeakestPrecondition.dexpr _ _ _ _) =>
  reify_change_dexpr; compile_prove_reified_dexpr : compiler_side_conditions.

Section with_parameters.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Implicit Type R : mem -> Prop.

  Section Tail.
    Definition min (x y : word) :=
      let/n c := word.ltu x y in
      if c then
        let/n r := x in r
      else
        let/n r := y in r.

    Instance spec_of_min : spec_of "min" :=
      fnspec! "min" (x y: word) ~> z,
      { requires tr mem := True;
        ensures tr' mem' := tr = tr' /\ mem = mem' /\ z = min x y }.

    Hint Extern 2 (IsRupicolaBinding (if _ then _ else _)) => exact true : typeclass_instances.
    Local Hint Extern 1 => simple eapply compile_tail_if; shelve : compiler.

    Derive min_body SuchThat
           (defn! "min"("x", "y") ~> "r"
                { min_body },
            implements min)
           As min_body_correct.
    Proof.
      compile.
    Qed.
  End Tail.

  Section Body.
    Definition minm (x y : word) :=
      let/n r := if word.ltu x y
                then x
                else word.add y (word.of_Z 1) in
      let/n r := word.sub r (word.of_Z 1) in
      r.

    Instance spec_of_minm : spec_of "minm" :=
      fnspec! "minm" (x y: word) / R ~> z,
      { requires tr mem := R mem;
        ensures tr' mem' := tr = tr' /\ R mem' /\ z = minm x y }. (* TODO explain why not mem; = mem *)

    Hint Extern 1 => compile_if; shelve : compiler.

    Derive minm_body SuchThat
           (defn! "minm"("x", "y") ~> "r"
                { minm_body },
            implements minm)
           As minm_body_correct.
    Proof.
      compile.
    Qed.
  End Body.
End with_parameters.
