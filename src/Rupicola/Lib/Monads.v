From Coq Require Import Strings.String Logic.FunctionalExtensionality.
From Rupicola.Lib Require Import Core.

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
    mret_mbindn {A B} vars a (k: A -> M B) : mbindn vars (mret a) k = nlet vars a k :=
      mret_mbind _ _;
    mbindn_mbindn {A B C} varsa varsb ma (ka: A -> M B) (kb: B -> M C) :
      mbindn varsb (mbindn varsa ma ka) kb = mbindn varsa ma (fun a => mbindn varsb (ka a) kb) :=
      mbind_mbind _ _ _;
  }.

Arguments mret : simpl never.
Arguments mbind : simpl never.
Arguments mbindn : simpl never.

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

    Lemma interp_mbind {A B} (ma: M A) (k: A -> M B) :
      mbind (M := M') (interp ma) (fun a => interp (k a)) =
      interp (mbind (M := M) ma k).
    Proof.
      induction ma; simpl; intros.
      all: repeat rewrite ?mret_mbind, ?mbind_mret, ?mbind_mbind; s.
    Qed.

    Lemma interp_mbindn {A B} vars (ma: M A) (k: A -> M B) :
      mbindn vars (M := M') (interp ma) (fun a => interp (k a)) =
      interp (mbindn vars (M := M) ma k).
    Proof. apply interp_mbind. Qed.
  End Free.
End Free.

#[export] Hint Extern 2 (IsRupicolaBinding (mbindn (A := ?A) ?vars _ _)) => exact (RupicolaBinding A vars) : typeclass_instances.

Hint Rewrite @mbindn_mbindn @mret_mbindn : compiler_cleanup.
