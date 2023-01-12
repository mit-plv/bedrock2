Require Import String.
Require Import ZArith.
Require Import List.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
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

(* Unary operators *)
Inductive unop : type -> Type :=
  | ONeg : unop TInt
  | ONot : unop TBool.

(* Binary operators *)
Inductive binop : type -> Type :=
  | OPlus : binop TInt
  | OMinus : binop TInt
  | OTimes : binop TInt
  | ODiv : binop TInt
  | OMod : binop TInt
  | OAnd : binop TBool
  | OOr : binop TBool
  | OConcatString : binop TString
  | OConcatList : forall t, binop (TList t).

(* "Pre-expression": untyped expressions from surface-level parsing. *)
Inductive pexpr : Type :=
  | PEVar (x : string)
  | PEInt (n : Z)
  | PEBool (b : bool)
  | PEString (s : string)
  | PEPair (p1 p2 : pexpr)
  | PEFst (p: pexpr)
  | PESnd (p: pexpr)
  | PENil (t : type)
  | PECons (p1 p2 : pexpr)
  | PERange (lo hi : pexpr)
  | PEFlatmap (p1 : pexpr) (x : string) (p2 : pexpr)
  | PEIf (p1 p2 p3 : pexpr)
  | PELet (x : string) (p1 p2 : pexpr)
  | PEUnop (t : type) (o : unop t) (p : pexpr)
  | PEBinop (t : type) (o : binop t) (p1 p2 : pexpr).

(* Typed expressions. Most of the type checking is enforced in the GADT itself
   via Coq's type system, but some of it needs to be done in the `elaborate`
   function below *)
Inductive expr : type -> Type :=
  | EVar (t : type) (x : string) : expr t
  | ELoc (t : type) (l : string) : expr t
  | EInt (n : Z) : expr TInt
  | EBool (b : bool) : expr TBool
  | EString (s : string) : expr TString
  | EPair (t1 t2 : type) (e1 : expr t1) (e2 : expr t2) : expr (TPair t1 t2)
  | EFst (t1 t2 : type) (e : expr (TPair t1 t2)) : expr t1
  | ESnd (t1 t2 : type) (e : expr (TPair t1 t2)) : expr t2
  | ENil (t : type) : expr (TList t)
  | ECons (t : type) (e1 : expr t) (e2 : expr (TList t)) : expr (TList t)
  | ERange (lo hi : expr TInt) : expr (TList TInt)
  | EFlatmap (t : type) (e1 : expr (TList t)) (x : string) (e2 : expr (TList t))
      : expr (TList t)
  | EIf (t : type) (e1 : expr TBool) (e2 e3 : expr t) : expr t
  | ELet (t1 t2 : type) (x : string) (e1 : expr t1) (e2 : expr t2) : expr t2
  | EUnop (t : type) (o : unop t) (e : expr t) : expr t
  | EBinop (t : type) (o : binop t) (e1 e2 : expr t) : expr t.

Inductive command : Type :=
  | CSkip
  | CSeq (c1 c2 : command)
  | CLet (t: type) (x : string) (e : expr t) (c : command)
  | CLetMut (t : type) (l : string) (e : expr t) (c : command)
  | CIf (e : expr TBool) (c1 c2 : command)
  | CForeach (t: type) (x : string) (e : expr (TList t)) (c : command).


(* A few helper functions *)
Fixpoint interp_type (t : type) :=
  match t with
  | TInt => Z
  | TBool => bool
  | TString => string
  | TPair t1 t2 => prod (interp_type t1) (interp_type t2)
  | TList t' => list (interp_type t')
  | TEmpty => unit
  end.

(* Casts one type to another, provided that they are equal
   https://stackoverflow.com/a/52518299 *)
Definition cast {T : Type} {T1 T2 : T} (H : T1 = T2) (f: T -> Type) (x : f T1) :
  f T2 :=
  eq_rect T1 f x T2 H.

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
  (* abstract all functions in this section over the implementation of the map,
     and over its spec (map.ok) *)
  Context {tenv: map.map string (type * bool)} {tenv_ok: map.ok tenv}.
  Context {locals: map.map string {t & interp_type t}} {locals_ok: map.ok locals}.

  (* Type checks a `pexpr` and possibly emits a typed expression
     Checks scoping for variables/locations *)
  Fixpoint elaborate (G : tenv) (p : pexpr) : result {t & expr t} :=
    match p with
    | PEVar x =>
        match map.get G x with
        | Some (t, false) =>
            Success (existT _ _ (EVar t x))
        | Some (t, true) =>
            Success (existT _ _ (ELoc t x))
        | None => error:("PEVar with undefined variable")
        end
    | PEInt n =>
        Success (existT _ _ (EInt n))
    | PEBool b =>
        Success (existT _ _ (EBool b))
    | PEString s =>
        Success (existT _ _ (EString s))
    | PEPair p1 p2 =>
        '(existT _ t1 e1) <- elaborate G p1 ;;
        '(existT _ t2 e2) <- elaborate G p2 ;;
        Success (existT _ _ (EPair t1 t2 e1 e2))
    | PEFst p' =>
        '(existT _ t' e') <- elaborate G p' ;;
        match t' as t'' return expr t'' -> _ with
        | TPair t1 t2 => fun e' =>
            Success (existT _ _ (EFst _ _ e'))
        | _ => fun _ => error:("PEFst applied to non-pair")
        end e'
    | PESnd p' =>
        '(existT _ t' e') <- elaborate G p' ;;
        match t' as t'' return expr t'' -> _ with
        | TPair t1 t2 => fun e' =>
            Success (existT _ _ (ESnd _ _ e'))
        | _ => fun _ => error:("PESnd applied to non-pair")
        end e'
    | PENil t =>
        Success (existT _ _ (ENil t))
    | PECons p1 p2 =>
        '(existT _ t1 e1) <- elaborate G p1 ;;
        '(existT _ t2 e2) <- elaborate G p2 ;;
        match t2 with
        | TList _ =>
            match type_eq_dec t2 (TList t1) with
            | left H =>
                Success (existT _ _ (ECons t1 e1 (cast H _ e2)))
            | _ => error:("PECons with mismatched types")
            end
        | _ => error:("PECons with non-list")
        end
    | PERange lo hi =>
        '(existT _ t_lo e_lo) <- elaborate G lo ;;
        '(existT _ t_hi e_hi) <- elaborate G hi ;;
        match type_eq_dec t_lo TInt, type_eq_dec t_hi TInt with
        | left Hlo, left Hhi =>
            Success (existT _ _ (ERange (cast Hlo _ e_lo) (cast Hhi _ e_hi)))
        | _, _ => error:("PERange with non-integer(s)")
        end
    | PEFlatmap p1 x p2 =>
        '(existT _ t1 e1) <- elaborate G p1 ;;
        let G' := map.put G x (t1, false) in
        '(existT _ t2 e2) <- elaborate G' p2 ;;
        match t1 as t1' return expr t1' -> _ with
        | TList t' => fun e1 =>
            match type_eq_dec t2 (TList t') with
            | left H2 =>
                Success (existT _ _ (EFlatmap t' e1 x (cast H2 _ e2)))
            | _ => error:("PEFlatmap with mismatched types")
            end
        | _ => fun _ => error:("PEFlatmap with non-list")
        end e1
    | PEIf p1 p2 p3 =>
        '(existT _ t1 e1) <- elaborate G p1 ;;
        '(existT _ t2 e2) <- elaborate G p2 ;;
        '(existT _ t3 e3) <- elaborate G p3 ;;
        match t1 as t' return expr t' -> _ with
        | TBool => fun e1 =>
            match type_eq_dec t3 t2 with
            | left H =>
                Success (existT _ _ (EIf t2 e1 e2 (cast H _ e3)))
            | _ => error:("PEIf with mismatched types")
            end
        | _ => fun _ => error:("PEIf with non-boolean condition")
        end e1
    | PELet x p1 p2 =>
        '(existT _ t1 e1) <- elaborate G p1 ;;
        let G' := map.put G x (t1, false) in
        '(existT _ t2 e2) <- elaborate G' p2 ;;
        Success (existT _ _ (ELet t1 t2 x e1 e2))
    | PEUnop t o p' =>
        '(existT _ t' e') <- elaborate G p' ;;
        match type_eq_dec t' t with
        | left H =>
            Success (existT _ _ (EUnop t o (cast H _ e')))
        | _ => error:("PEUnop with mismatched types")
        end
    | PEBinop t o p1 p2 =>
        '(existT _ t1 e1) <- elaborate G p1 ;;
        '(existT _ t2 e2) <- elaborate G p2 ;;
        match type_eq_dec t1 t, type_eq_dec t2 t with
        | left H1, left H2 =>
            Success (existT _ _ (EBinop t o (cast H1 _ e1) (cast H2 _ e2)))
        | _, _ => error:("PEBinop with mismatched types")
        end
    end.
End WithMap.

Section Examples.
  Instance tenv : map.map string (type * bool) := SortedListString.map _.
  Instance tenv_ok : map.ok tenv := SortedListString.ok _.

  Definition ex1 : pexpr :=
    PECons (PEInt 1) (PECons (PEInt 2) (PECons (PEInt 3) (PECons (PEInt 4) (PENil TInt)))).
  Compute (elaborate map.empty ex1).

  Definition ex2 : pexpr :=
    PECons (PEString "a") (PECons (PEInt 2) (PECons (PEInt 3) (PECons (PEInt 4) (PENil TInt)))).
  Compute (elaborate map.empty ex2).

  Definition ex3 : pexpr :=
    PEFst (PELet "x" (PEInt 42) (PEPair (PEVar "x") (PEVar "x"))).
  Compute (elaborate map.empty ex3).

  Definition ex4 : pexpr :=
    PEFst (PELet "x" (PEInt 42) (PEPair (PEVar "x") (PEVar "y"))).
  Compute (elaborate map.empty ex4).

  Definition ex5 : pexpr :=
    PEPair (PEInt 42) (PEPair (PEBool true) (PEString "hello")).
  Compute (elaborate map.empty ex5).
End Examples.
