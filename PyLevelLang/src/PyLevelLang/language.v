Require Import String.
Require Import ZArith.
Require Import List.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Datatypes.Result.
Import ResultMonadNotations.

Inductive type : Type :=
  | TInt
  | TBool
  | TString
  | TPair (t1 t2 : type)
  | TList (t : type)
  | TEmpty. (* "Empty" type: its only value should be the empty tuple () *)

Scheme Equality for type. (* creates type_beq and type_eq_dec *)

Declare Scope pylevel_scope. Local Open Scope pylevel_scope.
Notation "t1 =? t2" := (type_beq t1 t2) (at level 70) : pylevel_scope.

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
  | PEPair (p1 p2 : pexpr)
  | PEFst (p: pexpr)
  | PESnd (p: pexpr)
  | PENil (t : type)
  | PEList (ps : list pexpr)
  | PERange (lo hi : pexpr)
  | PEFlatmap (p1 : pexpr) (x : string) (p2 : pexpr)
  | PEIf (p1 p2 p3 : pexpr)
  | PELet (x : string) (p1 p2 : pexpr).

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
  match c with
  | 0 => nil
  | S c' => EInt s :: EIntRange (s + 1) c'
  end.

Fixpoint interp_type (t: type) :=
  match t with
  | TInt => Z
  | TBool => bool
  | TString => string
  | TPair t1 t2 => prod (interp_type t1) (interp_type t2)
  | TList u => list (interp_type u)
  | TEmpty => unit
  end.

(* Casts one type to another, provided that they are equal
   https://stackoverflow.com/a/52518299 *)
Definition cast {T1 T2 : Type} (H : T1 = T2) (x : T1) : T2 :=
  eq_rect T1 (fun T3 : Type => T3) x T2 H.

Section WithMap.
  (* abstract all functions in this section over the implementation of the map,
     and over its spec (map.ok) *)
  Context {locals: map.map string {t & interp_type t}} {locals_ok: map.ok locals}.
  (* Type checks a [pexpr] and possibly emits a typed expression
     Checks scoping and field names/indices (for records) *)
  (* TODO: make casting work *)
  (* TODO: take context into account for variables, locations, and flatmap and
     let expressions *)   
  Fixpoint elaborate (p : pexpr) : result {t & expr t}.
  Proof. 
    refine (
    match p with
    | PEVar x => _
    | PELoc l => _
    | PEInt n =>
        Success (existT _ _ (EInt n))
    | PEBool b =>
        Success (existT _ _ (EBool b))
    | PEString s =>
        Success (existT _ _ (EString s))
    | PEPair p1 p2 =>
        '(existT _ t1 e1) <- elaborate p1 ;;
        '(existT _ t2 e2) <- elaborate p2 ;;
        Success (existT _ _ (EPair t1 t2 e1 e2))
    | PEFst p' =>
        '(existT _ t' e') <- elaborate p' ;;
        match e' with
        | EPair t1 t2 e1 e2 =>
            Success (existT _ _ (EFst _ _ (EPair t1 t2 e1 e2)))
        | _ => error:("PEFst applied to non-pair")
        end
    | PESnd p' =>
        '(existT _ t' e') <- elaborate p' ;;
        match e' with
        | EPair t1 t2 e1 e2 =>
            Success (existT _ _ (ESnd _ _ (EPair t1 t2 e1 e2)))
        | _ => error:("PESnd applied to non-pair")
        end
    | PENil t =>
        Success (existT _ _ (EList t nil))
    | PEList ps =>
        match ps with
        | nil => error:("PEList with empty list (use PENil)")
        | p' :: ps' =>
            '(existT _ t' e') <- elaborate p' ;;
            match ps' with
            | nil =>
                Success (existT _ _ (EList t' (e' :: nil)))
            | _ =>
                '(existT _ _ e'') <- elaborate (PEList ps') ;;
                match e'' with
                | EList t'' es' =>
                    if t' =? t''
                    then Success (existT _ _ (EList t' (cast _ (cast _ e' :: es'))))
                    else error:("PEList with mismatched types")
                | _ => error:("Cons with non-list (unreachable)")
                end
            end
        end
    | PERange lo hi =>
        '(existT _ t_lo e_lo) <- elaborate lo ;;
        '(existT _ t_hi e_hi) <- elaborate hi ;;
        if andb (t_lo =? TInt) (t_hi =? TInt)
        then Success (existT _ _ (ERange (cast _ e_lo) (cast _ e_hi)))
        else error:("PERange with non-integer(s)")
    | _ => _
    end).

    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.
End WithMap.
