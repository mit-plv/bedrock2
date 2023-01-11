(* First attempt at translating high-level language specification into Coq
   (psvenk, 2023-01-09) *)
(* Changed records, started filling out elaborate 
   (mhulse, 2023-01-10) *)

Require Import String.
Require Import ZArith.
Require Import List.

Inductive type : Type :=
  | TInt
  | TBool
  | TString
  | TPair (t1 t2 : type)
  | TList (t : type)
  | TEmpty. (* "Empty" type: its only value should be the empty tuple () *)

(* Construct a "record" type using a list of types *)
Fixpoint TRecord (l : list type) : type :=
  match l with
  (* This creates the issue of having the empty type as the last element *)
  | nil => TEmpty
  | t :: ts => TPair t (TRecord ts)
  end.

(* "Pre-expression": untyped expressions from surface-level parsing. *)
Inductive pexpr : Type :=
  | PEVar (x : string)
  | PELoc (l : string)
  | PEInt (n : Z)
  | PEBool (b : bool)
  | PEString (s : string)
  | PEPair (e1 e2 : pexpr)
  | PEFst (p: pexpr)
  | PESnd (p: pexpr)
  | PEList (es : list pexpr)
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
  | EPair (t1 t2 : type) (e1 : expr t1) (e2 : expr t2) : expr (TPair t1 t2)
  | EFst (t1 t2 : type) (e : expr (TPair t1 t2)) : expr t1
  | ESnd (t1 t2 : type) (e : expr (TPair t1 t2)) : expr t2
  | EList (t : type) (es : list (expr t)) : expr (TList t)
  | ERange (lo hi : expr TInt) : expr (TList TInt)
  | ELet (t1 t2 : type) (x : string) (e1 : expr t1) (e2 : expr t2) : expr t2
  | EIf (t : type) (e1 : expr TBool) (e2 e3 : expr t) : expr t
  | EFlatmap (t : type) (e1 : expr (TList t)) (x : string) (e2 : expr (TList t))
      : expr (TList t).

Inductive command : Type :=
  | CSkip
  | CSeq (c1 c2 : command)
  | CLet (t: type) (x : string) (e : expr t) (c : command)
  | CLetMut (t : type) (l : string) (e : expr t) (c : command)
  | CIf (e : expr TBool) (c1 c2 : command)
  | CForeach (t: type) (x : string) (e : expr (TList t)) (c : command).


(* A few helper functions *)
(* Takes an integer n and a natural number c' and returns a 
   list of TInt expressions corresponding to [n, n + c) *)
Fixpoint EIntRange (s : Z)  (c: nat) : list (expr TInt) :=
  match ct with
  | 0 => nil
  | S c' => EInt s :: EIntRange (s + 1) c'
  end.

(* clips an integer to be positive, then turns it into a natural *)
Definition znatclip (n : Z) : nat := Z.to_nat (Z.max n 0).

(* Type checks a [pexpr] and possibly emits a typed expression
   Checks scoping and field names/indices (for records) *)
(* TODO: take context into account for variables, locations, and let expressions *)   
Theorem elaborate : pexpr -> option {t & expr t}.
Proof. 
  intro p.
  induction p.

  (* PEVar x *)
  - admit.

  (* PELoc l *)
  - admit.

  (* PEInt n *)
  - exact (Some (existT expr TInt (EInt n))).

  (* PEBool n *)
  - exact (Some (existT expr TBool (EBool b))).

  (* PEString s *)
  - exact (Some (existT expr TString (EString s))).

  (* PEPair e1 e2 *)
  - exact (match IHp1, IHp2 with
           | Some (existT _ t1 e1'), Some (existT _ t2 e2') 
               => Some (existT expr (TPair t1 t2) (EPair t1 t2 e1' e2'))
           | _, _ => None
           end).

  (* PEFst p *)
  - exact (match IHp with
           | Some (existT _ tp (EPair t1 t2 e1 e2)) => Some (existT expr t1 e1)
           | _ => None
           end).

  (* PESnd p *)
  - exact (match IHp with
           | Some (existT _ tp (EPair t1 t2 e1 e2)) => Some (existT expr t2 e2)
           | _ => None
           end).

  (* PEList es *)
  - induction

  (* PERange lo hi *)
  - exact (match IHp1, IHp2 with
           | Some (existT _ TInt (EInt lo)), Some (existT _ TInt (EInt hi))
               => Some (existT expr (TList TInt) (EList TInt (EIntRange lo (znatclip (hi - lo)))))
           | _, _ => None
           end).

  (* PEFlatmap e1 x e2 *)
  - admit.

  (* PEIf e1 e2 e3 *)
  - exact (match IHp1 with
           | Some (existT _ TBool (EBool b)) => match b with 
                                                | true => IHp2 
                                                | false => IHp3
                                                end
           | _ => None
           end).

  (* PELet x e1 e2 *)
  - admit.
Admitted.
