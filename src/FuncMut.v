Require Import Coq.Lists.List.
Import ListNotations.
Require Import compiler.Decidable.
Require Import compiler.Monad.
Require Import compiler.Op.

(* A mix between imperative and functional:
   It has expressions and lets, but mutable arrays.
   NOTE: Not suitable to encode for-loops which modify local variables, because all local vars
   are immutable.
*)

Definition listUpdate{E: Type}(l: list E)(i: nat)(e: E): list E :=
  firstn i l ++ [e] ++ skipn (S i) l.

Section FuncMut.

  Context {var: Set}.
  Context {eq_var_dec: DecidableEq var}.

  (* dim 0 = immutable nat
     dim 1 = Array of immutable nats (but updatable)
     dim 2 = Array of references to dim 1 Array
     etc
  *)

  Inductive val: Set :=
  | VNat(v: nat): val
  | VRef(i: nat): val.

  Definition Array := list val. (* could be heterogeneous, but we'll (almost) rule that out *)

  Fixpoint NewArray(sz: nat): Array :=
    match sz with
    | O => []
    | S m => VNat 0 :: (NewArray m)
    end.

  Definition Store := list Array.

  Inductive expr: Set :=
  | ERef(i: nat): expr (* a reference into the store *)
  | ELit(v: nat): expr
  | EVar(x: var): expr
  | EOp(e1: expr)(op: binop)(e2: expr): expr
  | ELet(x: var)(e1: expr)(e2: expr): expr
  | ENewArray(size: expr): expr (* returns a reference to a newly allocated array *)
  | EGet(a: expr)(i: expr): expr
  | EUpdate(a: expr)(i: expr)(v: expr): expr (* returns reference to in-place modified array *).

  Definition force_nat(v: val): option nat :=
    match v with
    | VNat a => Some a
    | VRef _ => None
    end.

  Definition force_ref(v: val): option nat :=
    match v with
    | VNat _ => None
    | VRef i => Some i
    end.

  (* returns val and state in which the val has to be considered if it's a reference *)
  Fixpoint interp_expr(ctx: var -> option val)(e: expr)(s: Store){struct e}: option (val * Store) :=
    match e with
    | ERef i => Some (VRef i, s)
    | ELit v => Some (VNat v, s)
    | EVar x => v <- ctx x; Some (v, s)
    | EOp e1 op e2 =>
        res1 <- interp_expr ctx e1 s;
        let '(v1, s1) := res1 in
        i1 <- force_nat v1;
        res2 <- interp_expr ctx e2 s1;
        let '(v2, s2) := res2 in
        i2 <- force_nat v2;
        Some (VNat (eval_binop_nat op i1 i2), s2)
    | ELet x e1 e2 =>
        res1 <- interp_expr ctx e1 s;
        let '(v1, s1) := res1 in
        interp_expr (fun x0 => if eq_var_dec x0 x then Some v1 else ctx x0) e2 s1
    | ENewArray size =>
        r <- interp_expr ctx size s;
        let '(size, s1) := r in
        size <- force_nat size;
        let i := length s1 in Some (VRef i, s1 ++ [NewArray size])
    | EGet a i =>
        ar <- interp_expr ctx a s;
        let '(av, s1) := ar in
        aref <- force_ref av;
        aa <- nth_error s1 aref;
        ir <- interp_expr ctx i s1;
        let '(iv, s2) := ir in
        ii <- force_nat iv;
        e <- nth_error aa ii;
        Some (e, s2)
    | EUpdate a i v =>
        ares <- interp_expr ctx a s;
        let '(av, s1) := ares in
        aref <- force_ref av;
        aa <- nth_error s1 aref;
        ires <- interp_expr ctx i s1;
        let '(iv, s2) := ires in
        ii <- force_nat iv;
        vres <- interp_expr ctx v s2;
        let '(vv, s3) := vres in
        let aa' := listUpdate aa ii vv in
        let s4 := listUpdate s3 aref aa' in
        Some (av, s4)
    end.

End FuncMut.
