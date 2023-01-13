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

(* Constants *)
Inductive const : type -> Type :=
  | CInt (n : Z) : const TInt
  | CBool (b : bool) : const TBool
  | CString (s : string) : const TString
  | CNil (t : type) : const (TList t).

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
  | OEq : forall t, binop t t TBool
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
  | PELet (x : string) (p1 p2 : pexpr).

(* Typed expressions. Most of the type checking is enforced in the GADT itself
   via Coq's type system, but some of it needs to be done in the `elaborate`
   function below *)
Inductive expr : type -> Type :=
  | EVar (t : type) (x : string) : expr t
  | ELoc (t : type) (l : string) : expr t
  | EConst (t : type) (c : const t) : expr t
  | EUnop (t1 t2 : type) (o : unop t1 t2) (e : expr t1) : expr t2
  | EBinop (t1 t2 t3 : type) (o : binop t1 t2 t3) (e1 : expr t1) (e2: expr t2) : expr t3
  | EFlatmap (t : type) (e1 : expr (TList t)) (x : string) (e2 : expr (TList t))
      : expr (TList t)
  | EIf (t : type) (e1 : expr TBool) (e2 e3 : expr t) : expr t
  | ELet (t1 t2 : type) (x : string) (e1 : expr t1) (e2 : expr t2) : expr t2.

Inductive command : Type :=
  | CSkip
  | CSeq (c1 c2 : command)
  | CLet (t : type) (x : string) (e : expr t) (c : command)
  | CLetMut (t : type) (l : string) (e : expr t) (c : command)
  | CIf (e : expr TBool) (c1 c2 : command)
  | CForeach (t : type) (x : string) (e : expr (TList t)) (c : command).


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

Definition elaborate_unop (po : punop) (t1 : type) : result {t2 & unop t1 t2} :=
  match po with
  | PONeg =>
      match t1 with
      | TInt =>
          Success (existT _ _ ONeg)
      | _ => error:("PONeg with wrong type")
      end
  | PONot =>
      match t1 with
      | TBool =>
          Success (existT _ _ ONot)
      | _ => error:("PONot with wrong type")
      end
  | POLength =>
      match t1 with
      | TList t =>
          Success (existT _ _ (OLength t))
      | _ => error:("POLength with wrong type")
      end
  | POLengthString =>
      match t1 with
      | TString =>
          Success (existT _ _ OLengthString)
      | _ => error:("POLengthString with wrong type")
      end
  | POFst =>
      match t1 with
      | TPair t1' t2' =>
          Success (existT _ _ (OFst t1' t2'))
      | _ => error:("POFst with wrong type")
      end
  | POSnd =>
      match t1 with
      | TPair t1' t2' =>
          Success (existT _ _ (OSnd t1' t2'))
      | _ => error:("POSnd with wrong type")
      end
  end.

Definition elaborate_binop (po : pbinop) (t1 : type) (t2 : type) :
  result {t3 & binop t1 t2 t3} :=
  match po with
  | POPlus =>
      match t1, t2 with
      | TInt, TInt =>
          Success (existT _ _ OPlus)
      | _, _ => error:("POPlus with wrong types")
      end
  | POMinus =>
      match t1, t2 with
      | TInt, TInt =>
          Success (existT _ _ OMinus)
      | _, _ => error:("POMinus with wrong types")
      end
  | POTimes =>
      match t1, t2 with
      | TInt, TInt =>
          Success (existT _ _ OTimes)
      | _, _ => error:("POTimes with wrong types")
      end
  | PODiv =>
      match t1, t2 with
      | TInt, TInt =>
          Success (existT _ _ ODiv)
      | _, _ => error:("PODiv with wrong types")
      end
  | POMod =>
      match t1, t2 with
      | TInt, TInt =>
          Success (existT _ _ OMod)
      | _, _ => error:("POMod with wrong types")
      end
  | POAnd =>
      match t1, t2 with
      | TBool, TBool =>
          Success (existT _ _ OAnd)
      | _, _ => error:("POAnd with wrong types")
      end
  | POOr =>
      match t1, t2 with
      | TBool, TBool =>
          Success (existT _ _ OOr)
      | _, _ => error:("POOr with wrong types")
      end
  | POConcat =>
      match t1, t2 with
      | TList t1, TList t2 =>
          match type_eq_dec t1 t2 with
          | left H =>
              let o : binop (TList t1) (TList t2) _ :=
                cast H (fun t => binop _ (TList t) _) (OConcat t1) in
              Success (existT _ _ o)
          | _ => error:("POConcat with mismatched types")
          end
      | _, _ => error:("POConcat with wrong types")
      end
  | POConcatString =>
      match t1, t2 with
      | TString, TString =>
          Success (existT _ _ OConcatString)
      | _, _ => error:("POConcatString with wrong types")
      end
  | POLess =>
      match t1, t2 with
      | TInt, TInt =>
          Success (existT _ _ OLess)
      | _, _ => error:("POLess with wrong types")
      end
  | POEq =>
      match type_eq_dec t1 t2 with
      | left H =>
          let o : binop t1 t2 _ :=
            cast H (fun t => binop _ t _) (OEq t1) in
          Success (existT _ _ o)
      | _ => error:("POEq with wrong types")
      end
  | PORepeat =>
      match t1 with
      | TInt =>
          Success (existT _ _ (ORepeat t2))
      | _ => error:("PORepeat with wrong type")
      end
  | POPair =>
      Success (existT _ _ (OPair t1 t2))
  | POCons =>
      match t2 with
      | TList t2 =>
          match type_eq_dec t1 t2 with
          | left H =>
              let o : binop t1 (TList t2) _ :=
                cast H (fun t => binop _ (TList t) _) (OCons t1) in
              Success (existT _ _ o)
          | _ => error:("POCons with mismatched types")
          end
      | _ => error:("POCons with wrong types")
      end
  | PORange =>
      match t1, t2 with
      | TInt, TInt =>
          Success (existT _ _ ORange)
      | _, _ => error:("PORange with wrong types")
      end
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
    | PEConst c =>
        Success (existT _ _ (EConst _ c))
    | PESingleton p' =>
        '(existT _ t' e') <- elaborate G p' ;;
        Success (existT _ _ (EBinop _ _ _ (OCons _) e' (EConst _ (CNil t'))))
    | PEUnop po p1 =>
        '(existT _ t1 e1) <- elaborate G p1 ;;
        '(existT _ t2 o) <- elaborate_unop po t1 ;;
        Success (existT _ _ (EUnop t1 t2 o e1))
    | PEBinop po p1 p2 =>
        '(existT _ t1 e1) <- elaborate G p1 ;;
        '(existT _ t2 e2) <- elaborate G p2 ;;
        '(existT _ t3 o) <- elaborate_binop po t1 t2 ;;
        Success (existT _ _ (EBinop t1 t2 t3 o e1 e2))
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
    end.
End WithMap.

Section Examples.
  Instance tenv : map.map string (type * bool) := SortedListString.map _.
  Instance tenv_ok : map.ok tenv := SortedListString.ok _.

  Definition ex1 : pexpr :=
    PEBinop POCons (PEConst (CInt 1)) (
      PEBinop POCons (PEConst (CInt 2)) (
        PEBinop POCons (PEConst (CInt 3)) (
          PESingleton (PEConst (CInt 4))))).
  Compute (elaborate map.empty ex1).

  Definition ex2 : pexpr :=
    PEBinop POCons (PEConst (CString "a")) (
      PEBinop POCons (PEConst (CInt 2)) (
        PEBinop POCons (PEConst (CInt 3)) (
          PESingleton (PEConst (CInt 4))))).
  Compute (elaborate map.empty ex2).

  Definition ex3 : pexpr :=
    PEUnop POFst (PELet "x" (
      PEConst (CInt 42)) (PEBinop POPair (PEVar "x") (PEVar "x"))).
  Compute (elaborate map.empty ex3).

  Definition ex4 : pexpr :=
    PEUnop POFst (PELet "x" (
      PEConst (CInt 42)) (PEBinop POPair (PEVar "x") (PEVar "y"))).
  Compute (elaborate map.empty ex4).

  Definition ex5 : pexpr :=
    PEBinop POPair (PEConst (CInt 42)) (
      PEBinop POPair (PEConst (CBool true)) (PEConst (CString "hello"))).
  Compute (elaborate map.empty ex5).
End Examples.
