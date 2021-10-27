Require Import Rupicola.Lib.Api.
Require Coq.Logic.Eqdep Coq.Logic.FunctionalExtensionality.
Open Scope list_scope.

Inductive Free {F: Type -> Type} {A: Type} : Type :=
| Pure (a: A) : Free
| Impure {X} (f: F X) (k: X -> Free) : Free.
Arguments Free: clear implicits.

Definition Call {F} {A} (f: F A) := Impure f Pure.

Module FreeMonad.
  Section FreeMonad.
    Context {F: Type -> Type}.
    Notation Free := (Free F).

    Definition ret {A} (a: A) : Free A := Pure a.
    Fixpoint bind {A B} (f: Free A) (kA: A -> Free B) : Free B :=
      match f with
      | Pure a => kA a
      | Impure f kX => Impure f (fun x => bind (kX x) kA)
      end.
    Definition bindn {A B} (vars: list string) (a: Free A) (kA: A -> Free B) : Free B :=
      bind a kA.

    Ltac s :=
      simpl; try reflexivity;
      eauto using f_equal, FunctionalExtensionality.functional_extensionality.

    Definition bind_ret {A} (ca: Free A) :
      bind ca ret = ca.
    Proof. induction ca; s. Qed.

    Definition ret_bind {A B} a (k: A -> Free B) :
      bind (ret a) k = k a.
    Proof. s. Qed.

    Definition bind_bind {A B C}
               ca (ka: A -> Free B) (kb: B -> Free C) :
      bind (bind ca ka) kb =
      bind ca (fun a => bind (ka a) kb).
    Proof. induction ca; s. Qed.

    Context (M: Type -> Type).
    Context (retM: forall {A}, A -> M A).
    Context (bindM: forall {A B}, (M A) -> (A -> M B) -> M B).
    Context (interpF: forall A, F A -> M A).

    Fixpoint interp {A: Type} (f: Free A) : M A :=
      match f with
      | Pure a => @retM _ a
      | Impure f k => @bindM _ _ (@interpF _ f) (fun x => interp (k x))
      end.
  End FreeMonad.
End FreeMonad.

Module IOMonad.
  Section IOMonad.
  Export FreeMonad.
  Context {T: Type}.

  Inductive Action : Type -> Type :=
  | Read : Action T
  | Write (w: T) : Action unit.

  Definition IO := Free Action.
  Definition ret {A} := @ret Action A.
  Definition bind {A B} := @bind Action A B.
  Definition bindn {A B} := @bindn Action A B.
  Definition bind_ret {A} := @bind_ret A.
  Definition ret_bind {A B} := @ret_bind A B.
  Definition bind_bind {A B C} := @bind_bind A B C.

  Inductive Event := R (t: T) | W (t: T).
  Record Outcome {A} := { val: A; trace: list Event }.
  Arguments Outcome : clear implicits.

  Definition Observable A := Outcome A -> Prop.
  Definition retObs {A} (a: A) : Observable A := fun r => r = {| val := a; trace := [] |}.
  Definition bindObs {A B} (a: Observable A) (k: A -> Observable B) : Observable B :=
    fun obs => exists obsA obsB, a obsA /\ k obsA.(val) obsB /\
                         obs = {| val := obsB.(val);
                                  trace := obsA.(trace) ++ obsB.(trace) |}.

  Definition interpAction {A} (rw: Action A) : Observable A :=
    match rw with
    | Read => fun out => out.(trace) = [R out.(val)]
    | Write w => fun out => out.(trace) = [W w]
    end.

  Definition interpIO {A} (spec: IO A) : Observable A :=
    interp Observable (@retObs) (@bindObs) (@interpAction) spec.

  Inductive ValidIO {A} : IO A -> Outcome A -> Prop :=
    | ValidPure a : ValidIO (Pure a) {| val := a; trace := [] |}
    | ValidRead r k a t :
        ValidIO (k r) {| val := a; trace := t |} ->
        ValidIO (Impure Read k) {| val := a; trace := R r :: t |}
    | ValidWrite w k a t :
        ValidIO (k tt) {| val := a; trace := t |} ->
        ValidIO (Impure (Write w) k) {| val := a; trace := W w :: t |}.

  Hint Constructors ValidIO : io.
  Lemma interpIO_ValidIO {A} (spec: IO A):
    forall obs,
      ValidIO spec obs <-> interpIO spec obs.
  Proof.
    induction spec; simpl; unfold retObs; intros.
    - split; inversion 1; subst; eauto with io.
    - split.
      + inversion 1;
          repeat match goal with
                 | _ => progress subst
                 | [ H: existT _ _ _ = _ |- _ ] => apply Eqdep.EqdepTheory.inj_pair2 in H
                 end;
          unfold bindObs.
        1: exists {| val := r; trace := [R r] |}, {| val := a; trace := t |}.
        2: exists {| val := tt; trace := [W w] |}, {| val := a; trace := t |}.
        all: firstorder.
      + destruct f; unfold bindObs;
          repeat match goal with
                 | [ H: unit |- _ ] => destruct H
                 | [ H: exists _: Outcome _, _ |- _ ] => destruct H as [(?&?) ?]
                 | [ H: _ /\ _ |- _ ] => destruct H
                 | [ H: Build_Outcome _ _ _ = _ |- _ ] => inversion H; subst; clear H
                 | _ => intros; subst; simpl in *
                 end.
          all: firstorder eauto with io.
  Qed.
  End IOMonad.

  Arguments IO: clear implicits.
  Arguments Action: clear implicits.
  Arguments Event : clear implicits.
  Arguments Outcome: clear implicits.
End IOMonad.

Import IOMonad.

Notation "'let/!' x 'as' nm := val 'in' body" :=
  (bindn [nm] (Call val) (fun x => body))
    (at level 200, x ident, body at level 200,
     format "'[hv' 'let/!'  x  'as'  nm  :=  val  'in' '//' body ']'").

Notation "'let/!' x := val 'in' body" :=
  (bindn [IdentParsing.TC.ident_to_string x] (Call val) (fun x => body))
    (at level 200, x ident, body at level 200,
     only parsing).

Require Import Coq.Init.Byte.

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
  Notation IO := (IO T).
  Notation Event := (Event T).
  Notation Outcome := (Outcome T).

  Definition iobind {A} (io: IO A) (pred: Outcome A -> Prop) :=
    (* FIXME: how do I capture the fact that all permissible traces should be achievable? *)
    exists out, ValidIO io out /\ pred out.

  (* Lemma tbind_bindn {A B} (tr0: list Event) (pred: Outcome A -> predicate) *)
  (*       vars (a: IO A) (k: A -> IO B) : *)
  (*   tbind tr0 pred (bindn vars a k) = *)
  (*   tbind (evf.(trace) ++ tr0) pred (k (evf.(val))). *)
  (* Proof. *)
  (*   unfold bindn, tbind, bind; simpl. *)
  (*   rewrite app_assoc; reflexivity. *)
  (* Qed. *)

  Definition trace_entry :=
    Eval cbv beta in ((fun {A} (_: list A) => A) _ ([]: Semantics.trace)).

  Context (trace_entry_of_event: Event -> trace_entry).

  Definition iospec {A} tr0 (io: IO A) (pred: A -> Semantics.trace -> Prop) : Prop :=
    iobind io (fun out => pred out.(val) (List.map trace_entry_of_event out.(trace) ++ tr0)).

  Definition iospec_k {A} tr0 (pred: A -> predicate) (k: IO A) :=
    fun tr mem locals =>
      iospec tr0 k (fun a tr' => tr = tr' /\ pred a tr mem locals).

  (* FIXME: is there a way to avoid repeating `tr`? (The problem is that iospec_k needs to connect the traces produced by k and by the bedrock2 program.)
     Can running a program ever shrink the trace? *)

  Lemma compile_setup_iospec {tr mem locals functions} :
    forall {A} {pred: A -> _ -> predicate}
      {spec: IO A} {cmd}
      retvars,

      (let pred a := wp_bind_retvars retvars (pred a) in
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
                 iospec tr spec (fun val tr1 => tr' = tr1 /\ pred val rets tr' mem' locals')))
           spec }>.
  Proof.
    intros; unfold iospec_k, iospec, iobind, wp_bind_retvars in *.
    use_hyp_with_matching_cmd; simpl in *.
    repeat match goal with
           | [ H: exists _, _ |- _ ] => destruct H
           | [ H: _ /\ _ |- _ ] => destruct H
           | _ => subst
           end.
    eauto 6.
  Qed.
End with_parameters.

Global Hint Unfold iospec_k iospec iobind: compiler_cleanup.
Global Hint Extern 1 (ret _ _) => reflexivity : compiler_cleanup.
Global Hint Resolve compile_setup_iospec : compiler_setup.
Global Hint Extern 2 (IsRupicolaBinding (bindn _ _ _)) => exact true : typeclass_instances.
