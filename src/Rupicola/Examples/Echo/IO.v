Require Import Rupicola.Lib.Api.
Require Coq.Logic.Eqdep Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles.
Open Scope list_scope.

Set Implicit Arguments.

Class Monad (M: Type -> Type) :=
  { mret {A} : A -> M A;
    mbind {A B} : M A -> (A -> M B) -> M B;
    mbindn {A B} (vars: list string) (ma: M A) (kA: A -> M B) : M B :=
      mbind ma kA;

    mbind_mret {A} (ma: M A) : mbind ma mret = ma;
    mret_mbind {A B} a (k: A -> M B) : mbind (mret a) k = k a;
    mbind_mbind {A B C} ma (ka: A -> M B) (kb: B -> M C) :
      mbind (mbind ma ka) kb = mbind ma (fun a => mbind (ka a) kb);

    mbindn_mret {A} vars (ma: M A) : mbindn vars ma mret = ma :=
      mbind_mret _;
    mret_mbindn {A B} vars a (k: A -> M B) : mbindn vars (mret a) k = k a :=
      mret_mbind _ _;
    mbindn_mbindn {A B C} varsa varsb ma (ka: A -> M B) (kb: B -> M C) :
      mbindn varsb (mbindn varsa ma ka) kb = mbindn varsa ma (fun a => mbindn varsb (ka a) kb) :=
      mbind_mbind _ _ _;
  }.

Module Free.
  Section Free.
    Context {F: Type -> Type}.

    Inductive M (A: Type) : Type :=
    | Pure (a: A) : M A
    | Impure X (f: F X) (k: X -> M A) : M A.

    Definition Call {A} (f: F A) := Impure f (@Pure _).

    Definition ret {A} (a: A) : M A := Pure a.

    Fixpoint bind {A B} (f: M A) (kA: A -> M B) : M B :=
      match f with
      | Pure a => kA a
      | Impure f kX => Impure f (fun x => bind (kX x) kA)
      end.

    Ltac s :=
      simpl; eauto using f_equal, FunctionalExtensionality.functional_extensionality.

    Global Program Instance MonadM : Monad M :=
      {| mret := @ret;
         mbind := @bind |}.
    Obligation 1. Proof. induction ma; s. Qed.
    Obligation 3. Proof. induction ma; s. Qed.

    Context {M': Type -> Type} {MM': Monad M'}.
    Context (interpF: forall {A}, F A -> M' A).

    Fixpoint interp {A: Type} (f: M A) : M' A :=
      match f with
      | Pure a => mret a
      | Impure f k => mbind (@interpF _ f) (fun x => interp (k x))
      end.

    Lemma interp_bind {A B}:
      forall (ma: M A) (k: A -> M B),
        mbind (M := M') (interp ma) (fun a => interp (k a)) =
        interp (mbind (M := M) ma k).
    Proof.
      induction ma; simpl; intros.
      all: repeat rewrite ?mret_mbind, ?mbind_mret, ?mbind_mbind; s.
    Qed.
  End Free.
End Free.

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

Module Observable.
  Import Writer.

  Section Observable.
  Context (T: Type).

  Definition M A := Writer.M T A -> Prop.

  (* FIXME: Combine nondeterminism with writer instead of defining from scratch *)
  Definition ret {A} (a: A) : M A := fun r => r = {| val := a; trace := [] |}.
  Definition bind {A B} (ma: M A) (k: A -> M B) : M B :=
    fun obs =>
      exists obsA obsB, ma obsA /\ k obsA.(val) obsB /\
                   obs = {| val := obsB.(val);
                            trace := obsA.(trace) ++ obsB.(trace) |}.

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
    | Read => fun out => out.(trace) = [R out.(val)]
    | Write w => fun out => out.(trace) = [W w]
    end.

  Definition interp {A} (spec: M A) : Observable.M (Event T) A :=
    Free.interp (MM' := Observable.MonadM (Event T)) (@interpAction) spec.

  Lemma interp_bind {A B}:
    forall (ma: M A) (k: A -> M B),
      mbind (interp ma) (fun a => interp (k a)) =
      interp (mbind ma k).
  Proof. intros; apply Free.interp_bind. Qed.

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
    induction spec; simpl; unfold Observable.ret; intros.
    - split; inversion 1; subst; eauto with io.
    - split.
      + inversion 1;
          repeat match goal with
                 | _ => progress subst
                 | [ H: existT _ _ _ = _ |- _ ] => apply Eqdep.EqdepTheory.inj_pair2 in H
                 end;
          unfold Observable.bind.
        1: exists {| val := r; trace := [R r] |}, {| val := a; trace := t |}.
        2: exists {| val := tt; trace := [W w] |}, {| val := a; trace := t |}.
        all: firstorder.
      + destruct f; unfold Observable.bind;
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

Notation "'call!' x" := (Free.Call x) (x at level 200, at level 10).

Notation "'let/!' x 'as' nm := val 'in' body" :=
  (mbindn [nm] val (fun x => body))
    (at level 200, x ident, body at level 200,
     format "'[hv' 'let/!'  x  'as'  nm  :=  val  'in' '//' body ']'").

Notation "'let/!' x := val 'in' body" :=
  (mbindn [IdentParsing.TC.ident_to_string x] val (fun x => body))
    (at level 200, x ident, body at level 200,
     only parsing).

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

  Definition iobind {A} (io: IO A) (pred: Writer A -> Prop) :=
    (* NOTE: We do not need to capture the fact that all traces are achievable:
       Bedrock2 takes care of that for us (the source program has no control on the
       values returned by "read" *)
    exists out, IO.Valid io out /\ pred out.

  Definition trace_entry :=
    Eval cbv beta in ((fun {A} (_: list A) => A) _ ([]: Semantics.trace)).

  Context (trace_entry_of_event: Event -> trace_entry).

  Definition iobind_spec {A} tr0 (io: IO A) (pred: A -> Semantics.trace -> Prop) : Prop :=
    iobind io (fun out => pred out.(val) (List.map trace_entry_of_event out.(trace) ++ tr0)).

  Definition pure_predicate := memT -> localsT -> Prop.
  Definition predicate_of_pure (p: pure_predicate) : predicate :=
    fun tr mem locals => p mem locals.

  Definition iospec_k {A} tr0 (pred: A -> pure_predicate) (io: IO A) : predicate :=
    fun tr mem locals =>
      iobind_spec tr0 io (fun a tr' => tr = tr' /\ pred a mem locals).

  Definition iospec {A} (tr0 tr1: Semantics.trace) (io: IO A) (post: A -> Prop) : Prop :=
    iobind_spec tr0 io (fun a tr' => tr' = tr1 /\ post a).

  Arguments mret : simpl never.
  Arguments mbind : simpl never.

  Lemma iospec_k_bindn {A B} tr0 tr mem locals :
    forall vars (fa : IO A) (k : A -> IO B) outa (pred : B -> pure_predicate),
      IO.Valid fa outa ->
      iospec_k (List.map trace_entry_of_event outa.(trace) ++ tr0) pred (k outa.(val)) tr mem locals ->
      iospec_k tr0 pred (mbindn vars fa k) tr mem locals.
  Proof.
    unfold iospec_k, iospec_k, iobind, mbindn; simpl.
    intros vars * Hv (out & ? & -> & ?).
    eexists {| val := out.(val); trace := out.(trace) ++ outa.(trace) |}.
    repeat split; cbn.
    - apply IO.interp_Valid in H, Hv.
      apply IO.interp_Valid.
      rewrite <- IO.interp_bind.
      red; red; eauto.
    - rewrite map_app, <- app_assoc; reflexivity.
    - eassumption.
  Qed.

  (* Lemma iospec_k_bindn' {A B} tr0 tr mem locals : *)
  (*   forall vars (fa : IO A) (k : A -> IO B) (pred : B -> pure_predicate), *)
  (*     (forall outa, *)
  (*         IO.Valid fa outa -> *)
  (*         iospec_k (List.map trace_entry_of_event outa.(trace) ++ tr0) pred (k outa.(val)) tr mem locals) -> *)
  (*     iospec_k tr0 pred (mbindn vars fa k) tr mem locals. *)
  (* Proof. *)
  (*   unfold iospec_k, iospec_k, iobind, mbindn; simpl. *)
  (*   intros vars * Hv (out & ? & -> & ?). *)
  (*   eexists {| val := out.(val); trace := out.(trace) ++ outa.(trace) |}. *)
  (*   repeat split; cbn. *)
  (*   - apply IO.interp_Valid in H, Hv. *)
  (*     apply IO.interp_Valid. *)
  (*     rewrite <- IO.interp_bind. *)
  (*     red; red; eauto. *)
  (*   - rewrite map_app, <- app_assoc; reflexivity. *)
  (*   - eassumption. *)
  (* Qed. *)

  Lemma WeakestPrecondition_iospec_k_bindn {A B} tr0 funcs prog tr mem locals :
    forall vars (fa : IO A) (k : A -> IO B) outa (pred : B -> pure_predicate),
    IO.Valid fa outa ->
    (IO.Valid fa outa ->
     WeakestPrecondition.program
       funcs prog tr mem locals
       (iospec_k (List.map trace_entry_of_event outa.(trace) ++ tr0)
                 pred (k outa.(val)))) ->
    WeakestPrecondition.program
      funcs prog tr mem locals
      (iospec_k tr0 pred (mbindn vars fa k)).
  Proof.
    intros; eapply WeakestPrecondition_weaken.
    - intros; eapply iospec_k_bindn; eauto.
    - eauto.
  Qed.

  (* FIXME: is there a way to avoid repeating `tr`? (The problem is that iospec_k needs to connect the traces produced by k and by the bedrock2 program.)
     Can running a program ever shrink the trace? *)

  Definition wp_pure_bind_retvars retvars (P: list word -> pure_predicate) :=
    fun mem locals =>
      exists ws, map.getmany_of_list locals retvars = Some ws /\
            P ws mem locals.

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
    intros; unfold iospec_k, iospec, iobind_spec, iobind, wp_bind_retvars, wp_pure_bind_retvars in *.
    use_hyp_with_matching_cmd; simpl in *.
    repeat match goal with
           | [ H: exists _, _ |- _ ] => destruct H
           | [ H: _ /\ _ |- _ ] => destruct H
           | _ => subst; eauto 10
           end.
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
    all: intros * (out & Hvalid & -> & Hpred); rewrite mbindn_mret in Hvalid.
    all: eapply WeakestPrecondition_iospec_k_bindn; intros;
      try eapply Hk; eauto.
  Qed.
End with_parameters.

#[export] Hint Resolve compile_setup_iospec_k : compiler_setup.

#[export] Hint Extern 1 (IO.Valid (mret _) _) => eapply IO.ValidPure : compiler_side_conditions.

#[export] Hint Unfold wp_pure_bind_retvars : compiler_cleanup_post.
#[export] Hint Unfold iospec_k iobind_spec iobind: compiler_cleanup_post.

#[export] Hint Extern 2 (IsRupicolaBinding (mbindn (A := ?A) ?vars _ _)) => exact (RupicolaBinding A vars) : typeclass_instances.
