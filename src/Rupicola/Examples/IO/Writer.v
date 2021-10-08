Require Import Rupicola.Lib.Api.

Set Implicit Arguments.

Module Writer.
Section Writer.
  Context (T: Type).
  Set Primitive Projections.
  Record M A := { val: A; trace: list T }.
  Unset Primitive Projections.

  Local Definition ret {A} (a: A) : M A :=
    {| val := a; trace := [] |}.
  Local Definition bind {A B} (ma: M A) (k: A -> M B) : M B :=
    let b := k ma.(val) in
    {| val := b.(val); trace := b.(trace) ++ ma.(trace) |}.

  Ltac s :=
    unfold bind, ret; simpl;
    rewrite ?List.app_nil_r, ?List.app_assoc;
    firstorder congruence.

  Global Program Instance MonadM : Monad M :=
    {| mret := @ret;
       mbind := @bind |}.
  Obligation 2. Proof. s. Qed.
  Obligation 3. Proof. s. Qed.
End Writer.
End Writer.

Import Writer.

Section with_parameters.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {memT: map.map word Byte.byte}.
  Context {localsT: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok memT}.
  Context {locals_ok : map.ok localsT}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {Evt: Type}.
  Notation Writer := (Writer.M Evt).

  Context (trace_entry_of_event: Evt -> trace_entry (width := width)).

  Notation lift_tr :=
    (List.map trace_entry_of_event).

  Definition wrbind_spec {A} tr0 (wr: Writer A) (pred: A -> Semantics.trace -> Prop) : Prop :=
    pred wr.(val) (lift_tr wr.(trace) ++ tr0).

  Definition wrspec {A} (tr0 tr1: Semantics.trace) (wr: Writer A) (post: A -> Prop) : Prop :=
    wrbind_spec tr0 wr (fun a tr' => tr' = tr1 /\ post a).

  Definition wrspec_k {A} tr0 (pred: A -> pure_predicate) (wr: Writer A) : predicate :=
    fun tr1 mem locals => wrspec tr0 tr1 wr (fun a => pred a mem locals).

  Lemma wrbind_spec_bindn {A B} tr0 pred vars wr (k: A -> Writer B) :
    wrbind_spec (lift_tr wr.(trace) ++ tr0) (k (wr.(val))) pred =
    wrbind_spec tr0 (mbindn vars wr k) pred.
  Proof.
    unfold mbindn, wrbind_spec, mbind; simpl; unfold Writer.bind.
    rewrite map_app, app_assoc; reflexivity.
  Qed.

  Lemma WeakestPrecondition_wrspec_k_bindn {A B} tr0 funcs prog tr mem locals :
    forall vars (wr : Writer A) (k : A -> Writer B) (pred : B -> pure_predicate),
      (WeakestPrecondition.program
         funcs prog tr mem locals
         (wrspec_k (lift_tr wr.(trace) ++ tr0) pred (k wr.(val)))) ->
      WeakestPrecondition.program
        funcs prog tr mem locals
        (wrspec_k tr0 pred (mbindn vars wr k)).
  Proof.
    intros; eapply WeakestPrecondition_weaken; [ | eassumption ].
    unfold wrspec_k, wrspec; intros.
    rewrite <- wrbind_spec_bindn; eauto.
  Qed.

  (* FIXME: is there a way to avoid repeating `tr`? (The problem is that iospec_k needs to connect the traces produced by k and by the bedrock2 program.)
     Can running a program ever shrink the trace? *)

  Lemma compile_setup_wrspec_k {tr mem locals functions} :
    forall {A} {pred: A -> _ -> pure_predicate}
      {spec: Writer A} {cmd}
      retvars,

      (let pred a := wp_pure_bind_retvars retvars (pred a) in
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       cmd
       <{ wrspec_k tr pred spec }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd
      <{ (fun spec =>
            wp_bind_retvars
              retvars
              (fun rets tr' mem' locals' =>
                 wrspec tr tr' spec (fun a => pred a rets mem' locals')))
           spec }>.
  Proof.
    intros; unfold wrspec_k, wrspec, wrbind_spec, wp_bind_retvars, wp_pure_bind_retvars in *.
    use_hyp_with_matching_cmd; cbv beta in *.
    cleanup; subst; eauto 10.
  Qed.
End with_parameters.

#[export] Hint Resolve compile_setup_wrspec_k : compiler_setup_post.
#[export] Hint Extern 1 (mret _ _) => reflexivity : compiler_side_conditions.
#[export] Hint Unfold wrspec_k wrspec wrbind_spec: compiler_cleanup_post.
