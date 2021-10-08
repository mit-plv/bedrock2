Require Import Rupicola.Lib.Api.

Definition Comp A := A -> Prop.

Module NDMonad.
  Definition ret {A} (a: A) : Comp A := fun a' => a' = a.
  Definition bind {A B} (v: Comp A) (body: A -> Comp B) : Comp B :=
    fun b => exists a, v a /\ body a b.
  Definition bindn {A B} (vars: list string) (v: Comp A) (body: A -> Comp B) : Comp B :=
    bind v body.

  Definition equiv {A} (a0 a1: Comp A) :=
    forall v, a0 v <-> a1 v.

  Definition bind_ret {A} (ca: Comp A) :
     equiv (bind ca ret) ca.
  Proof. firstorder congruence. Qed.

  Definition ret_bind {A B} a (k: A -> Comp B) :
      equiv (bind (ret a) k) (k a).
  Proof. firstorder congruence. Qed.

  Definition bind_bind {A B C}
             ca (ka: A -> Comp B) (kb: B -> Comp C) :
    equiv (bind (bind ca ka) kb)
          (bind ca (fun a => bind (ka a) kb)).
  Proof. firstorder congruence. Qed.

  Definition pick {A} (P: A -> Prop) : Comp A := P.

  Definition any {A} (ca: Comp A) := (exists a, ca a).
  Definition intersection {A} (ca ca': Comp A) :=
    fun a => ca a /\ ca' a.

  Definition propbind {A} (c: Comp A) (P: A -> Prop) : Prop :=
    any (intersection c P).
End NDMonad.

Import NDMonad.

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
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Definition pbind {A} (pred: A -> predicate) (c: Comp A) : predicate :=
    (* Morally a bind, but unfolding the definition saves us from having to build a triple *)
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

  Lemma compile_setup_nondet_pbind : forall {tr mem locals functions},
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
      <{ (fun spec => (* FIXME add a definition to make specs more readable *)
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

#[export] Hint Resolve compile_setup_nondet_pbind : compiler_setup_post.
#[export] Hint Extern 1 (ret _ _) => reflexivity : compiler_side_conditions.
#[export] Hint Extern 2 (IsRupicolaBinding (bindn (A := ?A) ?vars _ _)) => exact (RupicolaBinding A vars) : typeclass_instances.

#[export] Hint Unfold pbind: compiler_cleanup_post.
