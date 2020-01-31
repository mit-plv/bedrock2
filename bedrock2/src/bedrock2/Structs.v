(* macros for implementing simple types.
 *)
Require Coq.Lists.List.
Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax.

Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.
Require coqutil.Datatypes.String.

(* a simple language of statically known types
 * note(gmm): named types are not included, they can be represented using
 * Gallina names, e.g.
 *
 *  Definition foo_t : type := Struct ...
 *
 *  Definition bar_t : type := Array 3 foo_t.
 *)
Inductive type :=
| Struct (_ : list (string * type))
| Array  (_ : nat) (_ : type)
| Bytes  (_ : Z).

Fixpoint sizeof (s : type) {struct s} : Z :=
  match s with
  | Struct ls =>
    let sizes := List.map (fun '(_,t) => sizeof t) ls in
    List.fold_left Z.add sizes 0%Z
  | Array n t => Z.of_nat n * sizeof t
  | Bytes z => z
  end.

Definition is_scalar (s : type) : option Z :=
  match s with
  | Bytes n => Some n
  | _ => None
  end.

Inductive path_fragment {e : Type} :=
| Sub   (_ : e)
| Field (_ : string).
Arguments path_fragment _ : clear implicits.

Definition path e := list (path_fragment e).

Section path_lookup.
  Context {T : Type} (ksuccess : Z -> type -> T) (kerr : T).

  Fixpoint field_lookup (offset : Z) (f : string) (l : list (string * type))
           {struct l}
  : T :=
    match l with
    | nil => kerr
    | cons (n, t) ls =>
      if String.eqb f n
      then ksuccess offset t
      else field_lookup (sizeof t + offset) f ls
    end.

  Definition path_fragment_lookup (field : path_fragment Z) (s : type) : T :=
    match s , field with
    | Struct s , Field f =>
      field_lookup 0 f s
    | Array n t , Sub i =>
      if Z.ltb i (Z.of_nat n)
      then ksuccess (Z.mul i (sizeof t)) t
      else kerr
    | _ , _ => kerr
    end.
End path_lookup.

Inductive PathError {T} : Type :=
  mk_PathError (t : type) (f : path_fragment T).
Arguments PathError _ : clear implicits.
Inductive NotAScalar : Type :=
  mk_NotAScalar (t : type).

(* this is (essentially) the specification for `gen_access` *)
Fixpoint path_lookup (o : Z) (p : path Z) (s : type)
: PathError _ + (type * Z) :=
  match p with
  | nil => inr (s, o)
  | cons f fs =>
    path_fragment_lookup
      (fun o' t => path_lookup (o' + o) fs t)
      (inl (mk_PathError s f)) f s
  end.

Section syntax.
  Variable bop_add : bopname.
  Variable bop_mul : bopname.

  Fixpoint gen_access (e : expr.expr) (t : type) (fs : path expr.expr)
  : PathError _ + (type * expr.expr) :=
    match fs with
    | nil => inr (t, e)
    | cons f fs =>
      match t , f with
      | Array _ t , Sub i =>
        let offset_e := expr.op bop_mul i (expr.literal (sizeof t)) in
        let e := expr.op bop_add e offset_e in
        gen_access e t fs
      | Struct fields , Field n =>
        let success offset t' :=
            gen_access (expr.op bop_add e (expr.literal offset)) t' fs
        in
        path_fragment_lookup success (inl (mk_PathError t f))
                             (Field n) (Struct fields)
      | _ , _ => inl (mk_PathError t f)
      end
    end.
End syntax.

Module demo.
  Import Coq.Lists.List.

  Local Open Scope list_scope.
  Local Open Scope string_scope.

  (* some examples *)
  Example word : type := Bytes 4.
  Example char_array n : type := Array n (Bytes 1).
  Example first_last : type :=
    Struct (("first", char_array 15) :: ("last", char_array 15) :: nil).
  Example employees : type :=
    Array 3 first_last.

  Inductive inspect{T: Type}: T -> Prop := .
  Local Notation "t : T" := (@inspect T t) (only printing, at level 200).

  Goal inspect (sizeof word). cbv. Abort.
  Goal inspect (sizeof (char_array 20)). cbv. Abort.
  Goal inspect (sizeof first_last). cbv. Abort.
  Goal inspect (sizeof employees). unfold employees. unfold first_last. simpl. Abort.

  Goal inspect (path_lookup 0 (Sub 1 :: nil)%Z employees). cbv. Abort.
  Goal inspect (path_lookup 0 (Sub 1 :: Field "last" :: nil)%Z employees). cbv. Abort.
  Goal inspect (path_lookup 0 (Sub 1 :: Field "last" :: Sub 2 :: nil)%Z employees). cbv. Abort.

  Goal forall add mul base,
      inspect (@gen_access add mul base employees (Sub (expr.literal 1) :: nil)).
    intros. cbv. Abort.
  Goal forall add mul base,
      inspect (@gen_access add mul base employees (Sub (expr.literal 1) :: Field "last" :: nil)).
    intros. cbv. Abort.
  Goal forall add mul base,
      inspect (@gen_access add mul base employees (Sub (expr.literal 1) :: Field "last" :: Sub (expr.literal 2) :: nil)).
    intros. cbv. Abort.
End demo.
