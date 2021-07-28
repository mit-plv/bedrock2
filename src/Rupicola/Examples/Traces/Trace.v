Require Import Rupicola.Lib.Api.
Open Scope list_scope.

Set Primitive Projections.
Record Eventful {Evt A} : Type :=
  { val: A; trace: list Evt }.
Arguments Eventful: clear implicits.

Module TrMonad.
  Section TrMonad.
    Context {Evt: Type}.
    Notation Eventful := (Eventful Evt).

    Definition ret {A} (a: A) : Eventful A :=
      {| val := a; trace := [] |}.
    Definition bind {A B}
               (a: Eventful A) (body: A -> Eventful B) : Eventful B :=
      let b := body a.(val) in
      {| val := b.(val); trace := b.(trace) ++ a.(trace) |}.
    Definition bindn {A B} (vars: list string)
               (a: Eventful A) (body: A -> Eventful B) : Eventful B :=
      bind a body.

    Definition equiv {A} (a0 a1: Eventful A) := a0 = a1.

    Ltac s :=
      unfold equiv, bind, ret; simpl;
      rewrite ?List.app_nil_r, ?List.app_assoc;
      firstorder congruence.

    Definition bind_ret {A} (ca: Eventful A) :
      equiv (bind ca ret) ca.
    Proof. s. Qed.

    Definition ret_bind {A B} a (k: A -> Eventful B) :
      equiv (bind (ret a) k) (k a).
    Proof. s. Qed.

    Definition bind_bind {A B C}
               ca (ka: A -> Eventful B) (kb: B -> Eventful C) :
      equiv (bind (bind ca ka) kb)
            (bind ca (fun a => bind (ka a) kb)).
    Proof. s. Qed.
  End TrMonad.
End TrMonad.

Import TrMonad.

Notation "'let/!' x 'as' nm := val 'in' body" :=
  (bindn [nm] val (fun x => body))
    (at level 200, x ident, body at level 200,
     format "'[hv' 'let/!'  x  'as'  nm  :=  val  'in' '//' body ']'").

Notation "'let/!' x := val 'in' body" :=
  (bindn [IdentParsing.TC.ident_to_string x] val (fun x => body))
    (at level 200, x ident, body at level 200,
     only parsing).

Require Import Coq.Init.Byte.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok _}.

  Context {Evt: Type}.
  Notation Eventful := (Eventful Evt).

End with_parameters.

(* Global Hint Unfold pbind: compiler_cleanup. *)
Global Hint Extern 1 (ret _ _) => reflexivity : compiler_cleanup.
(* Global Hint Resolve compile_setup_nondet_pbind : compiler_setup. *)
Global Hint Extern 2 (IsRupicolaBinding (bindn _ _ _)) => exact true : typeclass_instances.
