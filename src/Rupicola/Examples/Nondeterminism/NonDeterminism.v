Require Import Rupicola.Lib.Api.

Section Monad.
  Definition Comp A := A -> Prop.

  Definition ret {A} (a: A) : Comp A := fun a' => a' = a.
  Definition bind {A B} (v: Comp A) (body: A -> Comp B) : Comp B :=
    fun b => exists a, v a /\ body a b.
  Definition bindn {A B} (vars: list string) (v: Comp A) (body: A -> Comp B) : Comp B :=
    bind v body.

  Definition pick {A} (P: Comp A) := P.
End Monad.

Notation "'let/+' x 'as' nm := val 'in' body" :=
  (bindn [nm] val (fun x => body))
    (at level 200, x ident, body at level 200,
     format "'[hv' 'let/+'  x  'as'  nm  :=  val  'in' '//' body ']'").

Notation "'let/+' x := val 'in' body" :=
  (bindn [IdentParsing.TC.ident_to_string x] val (fun x => body))
    (at level 200, x ident, body at level 200,
     only parsing).

Notation "%{ x | P }" :=
  (pick (fun x => P))
    (at level 0, x pattern at level 99).

Notation "%{ x : A | P }" :=
  (pick (A := A) (fun x => P))
    (at level 0, x pattern at level 99).

Require Import Coq.Init.Byte.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok _}.

  Definition pbind {A} (pred: A -> predicate) (c: Comp A) : predicate :=
    fun tr mem locals => exists a, c a /\ pred a tr mem locals.

  Lemma WeakestPrecondition_unbind {A B} funcs main t m l post
        (c: Comp A) (k: A -> Comp B) a0 :
    c a0 ->
    WeakestPrecondition.program funcs main t m l (pbind post (k a0)) ->
    WeakestPrecondition.program funcs main t m l (pbind post (bind c k)).
  Proof.
    unfold pbind, bind; intros * Hc;
      eapply WeakestPrecondition_weaken; eauto; cbv beta.
    clear - Hc; intros; firstorder.
  Qed.

  Lemma WeakestPrecondition_unbindn {A B} funcs main t m l post
        vars (c: Comp A) (k: A -> Comp B) a0 :
    c a0 ->
    (c a0 -> WeakestPrecondition.program funcs main t m l (pbind post (k a0))) ->
    WeakestPrecondition.program funcs main t m l (pbind post (bindn vars c k)).
  Proof.
    intros; eapply WeakestPrecondition_unbind; eauto.
  Qed.

  Lemma compile_setup_nondet_pbind {tr mem locals functions} :
    forall {A} {pred: A -> _ -> predicate}
      {spec: Comp A} {cmd}
      retvars,

      (let pred a := wp_bind_retvars retvars (pred a) in
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       cmd
       <{ pbind pred spec }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd
      <{ (fun spec =>
            wp_bind_retvars
              retvars
              (fun rets tr' mem' locals' =>
                 exists a, spec a /\ pred a rets tr' mem' locals'))
           spec }>.
  Proof.
    intros; unfold pbind, wp_bind_retvars in *.
    use_hyp_with_matching_cmd; cbv beta in *.
    clear - H0; firstorder.
  Qed.
End with_parameters.

Global Hint Unfold pbind: compiler_cleanup.
Global Hint Extern 1 (ret _ _) => reflexivity : compiler_cleanup.
Global Hint Resolve compile_setup_nondet_pbind : compiler_setup.
Global Hint Extern 2 (IsRupicolaBinding (bindn _ _ _)) => exact true : typeclass_instances.
