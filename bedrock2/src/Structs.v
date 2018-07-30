Require Import bedrock2.Macros bedrock2.Syntax bedrock2.BasicALU.

Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String bedrock2.String.
  
  Inductive struct :=
| Struct (_ : list (string * (Z + struct))).
Definition type : Type := Z + struct.

Fixpoint sizeof_struct (s : struct) {struct s} : Z :=
  match s with
  | (Struct ls) =>
    (fix sizeof_fields (l : list _) {struct l} : Z :=
       match l with
       | nil => 0%Z
       | cons (_, f) l' =>
         Z.add (match f with inl s => s | inr s' => sizeof_struct s' end)
               (sizeof_fields l')
       end
    ) ls
  end.

Definition sizeof (s:type) : Z :=
  match s with
  | inl s => s
  | inr s => sizeof_struct s
  end.

Definition slookup (field : string) (s : struct) : option (Z * type) :=
  match s with
  | (Struct ls) =>
    (fix llookup (l : list _) {struct l} : option (Z * type) :=
       match l with
       | nil => None
       | cons (f, ftype) l' =>
         if string_eqb f field
         then Some (0, ftype)
         else match llookup l' with
              | None => None
              | Some (o, t) => Some (Z.add (sizeof ftype) o, t)
              end
       end
    ) ls
  end%Z.

Fixpoint rlookup fieldnames (s : type) : option (Z * type) :=
  match fieldnames, s with
  | nil, r => Some (0, r)
  | cons f fieldnames', inr s =>
    match slookup f s with
    | None => None
    | Some (o, s') =>
      match rlookup fieldnames' s' with
      | None => None
      | Some (o', s') => Some (Z.add o o', s')
      end
    end
  | _, _ => None
  end%Z.

Inductive NO_SUCH_FIELD {T} (ctx:T) : Set := mk_NO_SUCH_FIELD.
Inductive TYPE_IS_NOT_SCALAR {T} (ctx:T) : Set := mk_TYPE_IS_NOT_SCALAR.
Definition scalar {T} (ctx : T) (r :  option (Z * type)) :
  match r with
  | None => NO_SUCH_FIELD ctx
  | Some (_, inr a) => TYPE_IS_NOT_SCALAR (a, ctx)
  | Some (n, inl s) => Z * Z
  end :=
  match r with
  | None => mk_NO_SUCH_FIELD ctx
  | Some (_, inr a) => mk_TYPE_IS_NOT_SCALAR (a, ctx)
  | Some (n, inl s) => (n, s)
  end.