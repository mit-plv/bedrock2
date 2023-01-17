Require Export String.
Require Export ZArith.
Require Export List.

(* Casts one type to another, provided that they are equal
   https://stackoverflow.com/a/52518299 *)
Definition cast {T : Type} {T1 T2 : T} (H : T1 = T2) (f: T -> Type) (x : f T1) :
  f T2 :=
  eq_rect T1 f x T2 H.

Inductive type : Type :=
  | TInt
  | TBool
  | TString
  | TPair (t1 t2 : type)
  | TList (t : type)
  | TEmpty. (* "Empty" type: its only value should be the empty tuple () *)

(* Types whose values can be compared *)
Definition can_eq (t : type) : bool :=
  match t with
  | TInt | TBool | TString | TEmpty => true
  | _ => false
  end.

Scheme Equality for type. (* creates type_beq and type_eq_dec *)

Declare Scope pylevel_scope. Local Open Scope pylevel_scope.
Notation "t1 =? t2" := (type_beq t1 t2) (at level 70) : pylevel_scope.

(* Constants *)
Inductive const : type -> Type :=
  | CInt (n : Z) : const TInt
  | CBool (b : bool) : const TBool
  | CString (s : string) : const TString
  | CNil (t : type) : const (TList t)
  | CEmpty : const TEmpty.

(* Unary operators (untyped) *)
Inductive punop : Type :=
  | PONeg
  | PONot
  | POLength
  | POLengthString
  | POFst
  | POSnd.

(* Unary operators (typed) *)
Inductive unop : type -> type -> Type :=
  | ONeg : unop TInt TInt
  | ONot : unop TBool TBool
  | OLength : forall t, unop (TList t) TInt
  | OLengthString : unop TString TInt
  | OFst : forall t1 t2, unop (TPair t1 t2) t1
  | OSnd : forall t1 t2, unop (TPair t1 t2) t2.

(* Binary operators (untyped) *)
Inductive pbinop : Type :=
  | POPlus
  | POMinus
  | POTimes
  | PODiv
  | POMod
  | POAnd
  | POOr
  | POConcat
  | POConcatString
  | POLess
  | POEq
  | PORepeat
  | POPair
  | POCons
  | PORange.

(* Binary operators (typed) *)
Inductive binop : type -> type -> type -> Type :=
  | OPlus : binop TInt TInt TInt
  | OMinus : binop TInt TInt TInt
  | OTimes : binop TInt TInt TInt
  | ODiv : binop TInt TInt TInt (* TODO: support option types? *)
  | OMod : binop TInt TInt TInt
  | OAnd : binop TBool TBool TBool
  | OOr : binop TBool TBool TBool
  | OConcat : forall t, binop (TList t) (TList t) (TList t)
  | OConcatString : binop TString TString TString
  | OLess : binop TInt TInt TBool
  | OEq : forall t, can_eq t = true -> binop t t TBool
  | ORepeat : forall t, binop TInt t (TList t)
  | OPair : forall t1 t2, binop t1 t2 (TPair t1 t2)
  | OCons : forall t, binop t (TList t) (TList t)
  | ORange : binop TInt TInt (TList TInt).

(* "Pre-expression": untyped expressions from surface-level parsing. *)
Inductive pexpr : Type :=
  | PEVar (x : string)
  | PEConst {t : type} (c : const t)
  | PESingleton (p : pexpr)
  | PEUnop (po : punop) (p : pexpr)
  | PEBinop (po : pbinop) (p1 p2 : pexpr)
  | PEFlatmap (p1 : pexpr) (x : string) (p2 : pexpr)
  | PEIf (p1 p2 p3 : pexpr)
  | PELet (x : string) (p1 p2 : pexpr)
  | PERecord (ps : list pexpr)
  | PEProj (p : pexpr) (i : nat).

(* Typed expressions. Most of the type checking is enforced in the GADT itself
   via Coq's type system, but some of it needs to be done in the `elaborate`
   function below *)
Inductive expr : type -> Type :=
  | EVar (t : type) (x : string) : expr t
  | ELoc (t : type) (l : string) : expr t
  | EConst {t : type} (c : const t) : expr t
  | EUnop {t1 t2 : type} (o : unop t1 t2) (e : expr t1) : expr t2
  | EBinop {t1 t2 t3 : type} (o : binop t1 t2 t3) (e1 : expr t1) (e2: expr t2) : expr t3
  | EFlatmap {t : type} (e1 : expr (TList t)) (x : string) (e2 : expr (TList t))
      : expr (TList t)
  | EIf {t : type} (e1 : expr TBool) (e2 e3 : expr t) : expr t
  | ELet {t1 t2 : type} (x : string) (e1 : expr t1) (e2 : expr t2) : expr t2.

Inductive command : Type :=
  | CSkip
  | CSeq (c1 c2 : command)
  | CLet (t : type) (x : string) (e : expr t) (c : command)
  | CLetMut (t : type) (l : string) (e : expr t) (c : command)
  | CIf (e : expr TBool) (c1 c2 : command)
  | CForeach (t : type) (x : string) (e : expr (TList t)) (c : command).
