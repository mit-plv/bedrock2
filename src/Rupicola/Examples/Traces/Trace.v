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

  Definition tbind {A}
             (tr0: list Evt) (pred: Eventful A -> predicate)
             (k: Eventful A) :=
    pred {| val := k.(val); trace := k.(trace) ++ tr0 |}.

  Lemma tbind_bindn {A B} tr0 pred var evf (k: A -> Eventful B) :
    tbind tr0 pred (bindn var evf k) =
    tbind (evf.(trace) ++ tr0) pred (k (evf.(val))).
  Proof.
    unfold bindn, tbind, bind; simpl.
    rewrite app_assoc; reflexivity.
  Qed.

  Notation trace_entry := ((fun (A: Type) (_: list A) => A) _ ([]: Semantics.trace)).

  Definition tracebind {A}
             (trace_entry_of_event: Evt -> trace_entry)
             (prog: Eventful A)
             (k: A -> Semantics.trace -> Prop) : Prop :=
    k prog.(val) (List.map trace_entry_of_event prog.(trace)).

  Lemma compile_setup_trace_tbind {tr mem locals functions} :
    forall {A} {pred: A -> _ -> predicate}
      {spec: Eventful A} {cmd}
      (trace_entry_of_event: Evt -> trace_entry)
      retvars,

      (let pred a :=
           wp_bind_retvars
             retvars
             (fun rets tr' mem' locals' =>
                tracebind
                  trace_entry_of_event spec
                  (fun val tr1 =>
                     tr' = tr1 ++ tr /\ pred val rets tr' mem' locals')) in
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       cmd
       <{ tbind [] pred spec }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd
      <{ (fun spec =>
            wp_bind_retvars
              retvars
              (fun rets tr' mem' locals' =>
                 tracebind
                   trace_entry_of_event spec
                   (fun val tr1 =>
                      tr' = tr1 ++ tr /\ pred val rets tr' mem' locals')))
           spec }>.
  Proof.
    intros; unfold tbind, tracebind, wp_bind_retvars in *.
    use_hyp_with_matching_cmd; cbv beta in *.
    eassumption.
  Qed.
End with_parameters.

Global Hint Unfold tbind: compiler_cleanup.
Global Hint Unfold tracebind: compiler_cleanup.
Global Hint Extern 1 (ret _ _) => reflexivity : compiler_cleanup.
Global Hint Resolve compile_setup_trace_tbind : compiler_setup.
Global Hint Extern 2 (IsRupicolaBinding (bindn _ _ _)) => exact true : typeclass_instances.
