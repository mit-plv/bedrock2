Require Import PyLevelLang.Language.
Require Import coqutil.Map.Interface.

Fixpoint interp_type (t : type) :=
  match t with
  | TInt => Z
  | TBool => bool
  | TString => string
  | TPair t1 t2 => prod (interp_type t1) (interp_type t2)
  | TList t' => list (interp_type t')
  | TEmpty => unit
  end.

Fixpoint default_val (t : type) : interp_type t :=
  match t as t' return interp_type t' with
  | TInt => 0%Z
  | TBool => false
  | TString => EmptyString
  | TPair t1 t2 => (default_val t1, default_val t2)
  | TList t' => nil
  | TEmpty => tt
  end.

Section WithMap.
  Context {locals: map.map string {t & interp_type t}} {locals_ok: map.ok locals}.
End WithMap.
