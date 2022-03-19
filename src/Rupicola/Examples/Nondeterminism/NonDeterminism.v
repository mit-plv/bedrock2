Require Import Rupicola.Lib.Api.
Require Import Ensembles.

Module ND.
  Definition M A := A -> Prop.

  Ltac s :=
    apply Extensionality_Ensembles; unfold Same_set, Included, In;
    firstorder congruence.

  Global Program Instance MonadM : Monad M :=
    {| mret {A} (a: A) := fun a' => a' = a;
       mbind {A B} (ma: M A) (k: A -> M B) :=
         fun b => exists a, ma a /\ k a b |}.
  Obligation 1. Proof. s. Qed.
  Obligation 2. Proof. s. Qed.
  Obligation 3. Proof. s. Qed.

  Definition pick {A} (P: A -> Prop) : M A := P.
End ND.

Import ND.

Notation "'let/+' x 'as' nm := val 'in' body" :=
  (mbindn [nm] val (fun x => body))
    (at level 200, x name, body at level 200,
     format "'[hv' 'let/+'  x  'as'  nm  :=  val  'in' '//' body ']'").

Notation "'let/+' x := val 'in' body" :=
  (mbindn [IdentParsing.TC.ident_to_string x] val (fun x => body))
    (at level 200, x name, body at level 200,
     only parsing).

Notation "%{ x | P }" :=
  (pick (fun x => P))
    (at level 0, x pattern at level 99).

Notation "%{ x : A | P }" :=
  (pick (A := A) (fun x => P))
    (at level 0, x pattern at level 99).

Definition ndbind {A} (c: M A) (pred: A -> Prop) :=
  exists a, c a /\ pred a.

Notation ndspec := ndbind.

Lemma ndbind_bindn {A B} pred vars (c: M A) a (k : A -> M B):
  c a ->
  ndbind (k a) pred ->
  ndbind (mbindn vars c k) pred.
Proof. unfold ndspec, mbindn, mbind. simpl. firstorder idtac. Qed.

Section with_parameters.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Definition ndspec_k {A} (pred: A -> predicate) (c: M A) : predicate :=
    fun tr mem locals => ndspec c (fun a => pred a tr mem locals).

  Lemma WeakestPrecondition_ndspec_k_bindn {A B} funcs prog t m l post
        vars (c: M A) a (k: A -> M B) :
    c a ->
    WeakestPrecondition.program funcs prog t m l (ndspec_k post (k a)) ->
    WeakestPrecondition.program funcs prog t m l (ndspec_k post (mbindn vars c k)).
  Proof.
    unfold ndspec_k; intros.
    eapply WeakestPrecondition_weaken; [ | eauto].
    eauto using ndbind_bindn.
  Qed.

  Lemma compile_setup_ndspec_k : forall {tr mem locals functions},
    forall {A} {pred: A -> _ -> predicate}
      {spec: M A} {cmd}
      retvars,

      (let pred a := wp_bind_retvars retvars (pred a) in
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       cmd
       <{ ndspec_k pred spec }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd
      <{ (fun spec =>
            wp_bind_retvars
              retvars
              (fun rets tr' mem' locals' =>
                 ndspec spec (fun a => pred a rets tr' mem' locals')))
           spec }>.
  Proof.
    intros; unfold ndbind, wp_bind_retvars in *.
    use_hyp_with_matching_cmd; cbv beta in *.
    clear - H0; firstorder.
  Qed.
End with_parameters.

#[export] Hint Resolve compile_setup_ndspec_k : compiler_setup_post.
#[export] Hint Unfold ndspec_k ndspec ndbind: compiler_cleanup_post.
#[export] Hint Extern 1 (mret _ _) => reflexivity : compiler_side_conditions.
