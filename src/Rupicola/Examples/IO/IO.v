From Coq Require Logic.Eqdep Sets.Ensembles.
Require Import Rupicola.Lib.Api.
Require Export Rupicola.Examples.IO.Writer.

Open Scope list_scope.

Set Implicit Arguments.
Set Primitive Projections.

Module Observable.
  Import Writer.

  Section Observable.
  Context (T: Type).

  Definition M A := Writer.M T A -> Prop.

  Ltac s :=
    apply Ensembles.Extensionality_Ensembles;
    unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In;
    repeat match goal with
           | _ => reflexivity || eassumption
           | _ => progress (intros; subst; simpl in * )
           | [ H: exists _, _ |- _ ] => destruct H
           | [ H: _ /\ _ |- _ ] => destruct H
           | [  |- exists _, _ ] => eexists
           | [  |- _ /\ _ ] => split
           | _ => rewrite ?List.app_nil_r, ?List.app_assoc
           end.

  Global Program Instance MonadM : Monad M :=
    {| mret {A} (a: A) := fun r => r = {| val := a; trace := [] |};
       mbind {A B} (ma: M A) (k: A -> M B) :=
         fun obs => exists obsA obsB, ma obsA /\ k obsA.(val) obsB /\
                              obs = {| val := obsB.(val);
                                       trace := obsB.(trace) ++ obsA.(trace) |} |}.
  Obligation 1. Proof. s. Qed.
  Obligation 2. Proof. s. Qed.
  Obligation 3. Proof. s. Qed.
  End Observable.
End Observable.

Module IO.
  Import Writer.

  Section IO.
  Context (T: Type).

  Inductive Action : Type -> Type :=
  | Read : Action T
  | Write (w: T) : Action unit.

  Definition M := (@Free.M Action).
  (* Instance Monad : Monad (@Free.M Action) := @Free.Monad Action. *)

  Inductive Event T := R (t: T) | W (t: T).

  Definition interpAction {A} (rw: Action A) : Observable.M (Event T) A :=
    match rw with
    | Read => fun wr => wr.(trace) = [R wr.(val)]
    | Write w => fun wr => wr.(trace) = [W w]
    end.

  Definition interp {A} (spec: M A) : Observable.M (Event T) A :=
    Free.interp (MM' := Observable.MonadM (Event T)) (@interpAction) spec.

  Inductive Valid {A} : IO.M A -> Writer.M (Event T) A -> Prop :=
    | ValidPure a : Valid (Free.Pure a) {| val := a; trace := [] |}
    | ValidRead r k a t :
        Valid (k r) {| val := a; trace := t |} ->
        Valid (Free.Impure Read k) {| val := a; trace := t ++ [R r] |}
    | ValidWrite w k a t :
        Valid (k tt) {| val := a; trace := t |} ->
        Valid (Free.Impure (Write w) k) {| val := a; trace := t ++ [W w] |}.

  Hint Constructors Valid : io.
  Lemma interp_Valid {A} (spec: IO.M A):
    forall obs,
      Valid spec obs <-> interp spec obs.
  Proof.
    induction spec; simpl; unfold mret; intros.
    - split; inversion 1; subst; simpl; eauto with io.
    - split.
      + inversion 1;
          repeat match goal with
                 | _ => progress subst
                 | [ H: existT _ _ _ = _ |- _ ] => apply Eqdep.EqdepTheory.inj_pair2 in H
                 end.
        1: exists {| val := r; trace := [R r] |}, {| val := a; trace := t |}.
        2: exists {| val := tt; trace := [W w] |}, {| val := a; trace := t |}.
        all: firstorder.
      + destruct f; unfold mbind;
          repeat match goal with
                 | [ H: unit |- _ ] => destruct H
                 | [ H: exists _: Writer.M _ _, _ |- _ ] => destruct H as [(?&?) ?]
                 | [ H: _ /\ _ |- _ ] => destruct H
                 | _ => intros; subst; simpl in *
                 end.
        all: firstorder eauto with io.
  Qed.
  End IO.
End IO.

Arguments IO.Read {_} : assert.

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

  Context {T: Type}.
  Notation IO := (IO.M T).
  Notation Event := (IO.Event T).
  Notation Writer := (Writer.M Event).

  Context (trace_entry_of_event: Event -> trace_entry (width := width)).
  Notation wrbind_spec := (wrbind_spec trace_entry_of_event).
  Notation lift_tr := (List.map trace_entry_of_event).

  Definition iobind {A} (io: IO A) (pred: Writer A -> Prop) :=
    (* NOTE: We do not need to capture the fact that all traces are achievable:
       Bedrock2 takes care of that for us (the source program has no control on the
       values returned by "read" *)
    exists wr, IO.Valid io wr /\ pred wr.

  Definition iobind_spec {A} tr0 (io: IO A) (pred: A -> Semantics.trace -> Prop) : Prop :=
    iobind io (fun wr => wrbind_spec tr0 wr pred).

  Definition iospec {A} (tr0 tr1: Semantics.trace) (io: IO A) (post: A -> Prop) : Prop :=
    iobind_spec tr0 io (fun a tr' => tr' = tr1 /\ post a).

  Definition iospec_k {A} tr0 (pred: A -> pure_predicate) (io: IO A) : predicate :=
    fun tr1 mem locals => iospec tr0 tr1 io (fun a => pred a mem locals).

  Lemma iobind_spec_bindn {A B} tr0 pred vars io wr (k : A -> IO B):
      IO.Valid io wr ->
      iobind_spec (List.map trace_entry_of_event wr.(trace) ++ tr0) (k wr.(val)) pred ->
      iobind_spec tr0 (mbindn vars io k) pred.
  Proof.
    unfold iobind_spec, iobind, wrbind_spec.
    intros H (wrb & Hb & Hwr).
    eexists {| val := wrb.(val); trace := wrb.(trace) ++ wr.(trace) |};
      split.
    - apply IO.interp_Valid in H, Hb; apply IO.interp_Valid.
      unfold IO.interp; rewrite <- @Free.interp_mbindn.
      red; red; red; eauto.
    - simpl; rewrite map_app, <- app_assoc; eassumption.
  Qed.

  Lemma WeakestPrecondition_iospec_k_bindn {A B} tr0 funcs prog tr mem locals :
    forall vars (io : IO A) (k : A -> IO B) wr (pred : B -> pure_predicate),
    IO.Valid io wr ->
    (IO.Valid io wr ->
     WeakestPrecondition.program
       funcs prog tr mem locals
       (iospec_k (lift_tr wr.(trace) ++ tr0) pred (k wr.(val)))) ->
    WeakestPrecondition.program
      funcs prog tr mem locals
      (iospec_k tr0 pred (mbindn vars io k)).
  Proof.
    intros; eapply WeakestPrecondition_weaken; [ | eauto ].
    intros; eapply iobind_spec_bindn; eauto.
  Qed.

  Lemma compile_setup_iospec_k {tr mem locals functions} :
    forall {A} {pred: A -> _ -> pure_predicate}
      {spec: IO A} {cmd}
      retvars,

      (let pred a := wp_pure_bind_retvars retvars (pred a) in
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       cmd
       <{ iospec_k tr pred spec }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd
      <{ (fun spec =>
            wp_bind_retvars
              retvars
              (fun rets tr' mem' locals' =>
                 iospec tr tr' spec (fun a => pred a rets mem' locals')))
           spec }>.
  Proof.
    intros; unfold iospec_k, iospec, iobind_spec, wrbind_spec, iobind, wp_bind_retvars, wp_pure_bind_retvars in *.
    use_hyp_with_matching_cmd; simpl in *.
    cleanup; subst; eauto 10.
  Qed.

  (* FIXME can we generalize?  Basically this works with any monad that describes sets of values *)
  Lemma compile_if : forall {tr mem locals functions} (c: bool) {A} (t f: IO A),
    let v := if c then t else f in
    forall {B} {pred: B -> pure_predicate} {val_pred: A -> pure_predicate}
      {k: A -> IO B} {k_impl t_impl f_impl}
      c_expr vars,

      WeakestPrecondition.dexpr mem locals c_expr (word.b2w c) ->

      (let val_pred := val_pred in
       c = true ->
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       t_impl
       <{ iospec_k tr val_pred (mbindn vars t mret) }>) ->
      (let val_pred := val_pred in
       c = false ->
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       f_impl
       <{ iospec_k tr val_pred (mbindn vars f mret) }>) ->
      (forall a mem locals,
         IO.Valid v a ->
         val_pred a.(val) mem locals ->
         let tr := List.map trace_entry_of_event a.(trace) ++ tr in
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       k_impl
       <{ iospec_k tr pred (k a.(val)) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.cond c_expr t_impl f_impl)
        k_impl
      <{ iospec_k tr pred (mbindn vars v k) }>.
  Proof.
    intros * Hc Ht Hf Hk.
    repeat straightline.
    split_if ltac:(repeat straightline'); subst_lets_in_goal.
    eassumption.
    all: rewrite word.unsigned_b2w; cbv [Z.b2z].
    all: destruct_one_match; try congruence; [ ]; intros.
    all: eapply compile_seq; [ (eapply Ht + eapply Hf); reflexivity | ].
    all: intros * (out & Hvalid & <- & Hpred); rewrite mbindn_mret in Hvalid.
    all: eapply WeakestPrecondition_iospec_k_bindn; intros;
      try eapply Hk; eauto.
  Qed.
End with_parameters.

Ltac compile_if tr0 :=
  let vp := infer_val_predicate in
  eapply compile_if with (val_pred := fun args => vp args tr0).

#[export] Hint Extern 1
 (WeakestPrecondition.cmd _ _ ?tr0 _ _ (_ (mbindn _ (if _ then _ else _) _))) =>
  compile_if tr0; shelve : compiler.

#[export] Hint Resolve compile_setup_iospec_k : compiler_setup_post.
#[export] Hint Extern 1 (IO.Valid (mret _) _) => eapply IO.ValidPure : compiler_side_conditions.
#[export] Hint Unfold iospec_k iospec iobind_spec iobind: compiler_cleanup_post.
