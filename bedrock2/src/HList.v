Require Import Coq.Lists.List.
Require Import bedrock2.PrimitivePair. Import pair.
Local Set Universe Polymorphism.
Fixpoint arrows (argts : list Type) : Type -> Type :=
  match argts with
  | nil => fun ret => ret
  | cons T argts' => fun ret => T -> arrows argts' ret
  end.

Fixpoint hlist (argts : list Type) : Type :=
  match argts with
  | nil => unit
  | cons T argts' => T * hlist argts'
  end.

Module hlist.
  Fixpoint apply {argts : list Type} : forall {P} (f : arrows argts P) (args : hlist argts), P :=
    match argts return forall {P} (f : arrows argts P) (args : hlist argts), P with
    | nil => fun P f _ => f
    | cons T argts' => fun P f '(x, args') => apply (f x) args'
    end.
  
  Fixpoint binds {argts : list Type} : forall {P} (f : hlist argts -> P), arrows argts P :=
    match argts return forall {P} (f : hlist argts -> P), arrows argts P with
    | nil => fun P f => f tt
    | cons T argts' => fun P f x => binds (fun xs' => f (x, xs'))
    end.

  Fixpoint foralls {argts : list Type} : forall (P : hlist argts -> Type), Type :=
    match argts with
    | nil => fun P => P tt
    | cons T argts' => fun P => forall x:T, foralls (fun xs' => P (x, xs'))
    end.

  Fixpoint existss {argts : list Type} : forall (P : hlist argts -> Prop), Prop :=
    match argts with
    | nil => fun P => P tt
    | cons T argts' => fun P => exists x:T, existss (fun xs' => P (x, xs'))
    end.

  Lemma foralls_forall {argts} {P} : @foralls argts P -> forall x, P x.
  Proof.
    revert P; induction argts as [|A argts']; intros P.
    { destruct x; eauto. }
    { cbn. intros H xs.
      refine (IHargts' (fun xs' => P (xs.(1), xs')) _ _); eauto. }
  Qed.

  Lemma existss_exists {argts} {P} : @existss argts P -> exists x, P x.
  Proof.
    revert P; induction argts as [|A argts']; intros P.
    { intro. exists tt. eauto. }
    { cbn. intros [x xs'].
      destruct (IHargts' (fun xs' => P (x, xs'))); eauto. }
  Qed.
End hlist.

Definition tuple A n := hlist (Coq.Lists.List.repeat A n).
Definition ufunc A n := arrows (Coq.Lists.List.repeat A n).
Module tuple.
  Notation apply := hlist.apply.
  Definition binds {A n} := hlist.existss (argts:=Coq.Lists.List.repeat A n).
  Definition foralls {A n} := hlist.foralls (argts:=Coq.Lists.List.repeat A n).
  Definition existss {A n} := hlist.existss (argts:=Coq.Lists.List.repeat A n).

  Section WithA.
    Context {A : Type}.
    Fixpoint to_list {n : nat} : tuple A n -> list A :=
      match n with
      | O => fun _ => nil
      | S n => fun '(x, xs') => cons x (to_list xs')
      end.
  End WithA.
End tuple.
