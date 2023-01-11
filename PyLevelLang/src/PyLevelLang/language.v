(* First attempt at translating high-level language specification into Coq
   (psvenk, 2023-01-09) *)

Require Import String.
Require Import ZArith.
(* Require Import List. *)

Inductive type : Type :=
  | TInt
  | TBool
  | TString
  | TProd (t1 t2 : type)
  | TList (t : type)
  | TRecord (_ : list type).
  (* TODO: This could be written as [TRecord (_ : list (string * type))], but I
     decided to write out definitions with unnamed tuples for the time being for
     convenience *)

(* "Pre-expression": untyped expressions from surface-level parsing. *)
Inductive pexpr : Type :=
  | PEVar (x : string)
  | PELoc (l : string)
  | PEInt (n : Z)
  | PEBool (b : bool)
  | PEString (s : string)
  | PEProd (e1 e2 : pexpr)
  | PEList (es : list pexpr)
  | PERecord (xs : list (string * pexpr))
  | PEProj (rec : pexpr) (i : Z)
  | PERange (lo hi : pexpr)
  | PEFlatmap (e1 : pexpr) (x : string) (e2 : pexpr)
  | PEIf (e1 e2 e3 : pexpr)
  | PELet (x : string) (e1 e2 : pexpr).

(* Typed expressions. Most of the type checking is enforced in the GADT itself
   via Coq's type system, but some of it needs to be done in the [elaborate]
   function below *)
Inductive expr : type -> Type :=
  | EVar (t : type) (x : string) : expr t
  | ELoc (t : type) (l : string) : expr t
  | EInt (n : Z) : expr TInt
  (* TODO: ultimately use a more efficient implementation than Z for arbitrarily
     large integers; this can probably be taken care of by compiling to
     Bedrock *)
  | EBool (b : bool) : expr TBool
  | EString (s : string) : expr TString
  | EProd (t1 t2 : type) (e1 : expr t1) (e2 : expr t2) : expr (TProd t1 t2)
  | EList (t : type) (es : list (expr t)) : expr (TList t)
  | ERecord (ts : list type) (xs : list {t & expr t}) : expr (TRecord ts)
  (* TODO: In this case, [ts = map (@projT1 type expr) xs] should be satisfied
     (that is, the types in [xs] should correspond to [ts], and [xs] and [ts]
     should have the same length); however; I can't figure out a way to enforce
     this constraint in the GADT without violating the strict positivity
     requirement for inductive definitions. *)
  | EProj (t_rec t_field : type) (rec : expr t_rec) (i : Z) : expr t_field
  | ERange (lo hi : expr TInt) : expr (TList TInt)
  | ELet (t1 t2 : type) (x : string) (e1 : expr t1) (e2 : expr t2) : expr t2
  | EIf (t : type) (e1 : expr TBool) (e2 e3 : expr t) : expr t
  | EFlatmap (t : type) (e1 : expr (TList t)) (x : string) (e2 : expr (TList t))
      : expr (TList t).

Inductive command : Type :=
  | CNop
  | CChain (c1 c2 : command)
  | CLet (t: type) (x : string) (e : expr t) (c : command)
  | CLetMut (t : type) (l : string) (e : expr t) (c : command)
  | CIf (e : expr TBool) (c1 c2 : command)
  | CForeach (t: type) (x : string) (e : expr (TList t)) (c : command).

(* Type checks a [pexpr] and possibly emits a typed expression
   Checks scoping and field names/indices (for records) *)
Theorem elaborate : pexpr -> option {t & expr t}.
Proof. Admitted.
(* TODO: implement this function. This will probably have to take a store
   (assigning variable names to types and values) as an argument. *)
