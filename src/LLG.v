Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import compiler.Decidable.
Require Import compiler.Op.
Require Import compiler.member.

(* Note: you can't ask an array for its length *)
Class IsArray(T E: Type) := mkIsArray {
  defaultElem: E;
  get: T -> nat -> E;
  update: T -> nat -> E -> T;
  newArray: nat -> T
}.

Definition listUpdate{E: Type}(l: list E)(i: nat)(e: E): list E :=
  firstn i l ++ [e] ++ skipn (S i) l.

Definition listFill{E: Type}(e: E): nat -> list E :=
  fix rec(n: nat) := match n with
  | O => nil
  | S m => e :: rec m
  end.

Instance ListIsArray: forall (T: Type) (d: T), IsArray (list T) T := fun T d => {|
  defaultElem := d;
  get := fun l i => nth i l d;
  update := listUpdate;
  newArray := listFill d
|}.


(* Low-Level Gallina *)
Section LLG.

  Context {var: Set}.
  Context {eq_var_dec: DecidableEq var}.

  (* isomorphic to nat *)
  Inductive type: Set :=
  | TNat: type
  | TArray: type -> type.

  Definition extend{l}(G: member l -> type)(x: var)(t: type): member (x :: l) -> type :=
    fun m => match m with (* (fancy return clause inferred) *)
    | member_here _ _ => fun _ => t
    | member_there _ _ m' => fun G => G m'
    end G.

  Inductive expr: forall l: list var, (member l -> type) -> type -> Set :=
  | ELit{l G}(v: nat): expr l G TNat
  | EVar{l G}(m: member l): expr l G (G m)
  | EOp{l G}(e1: expr l G TNat)(op: binop)(e2: expr l G TNat): expr l G TNat
  | ELet{l G t1 t2}(x: var)(e1: expr l G t1)(e2: expr (x :: l) (extend G x t1) t2): expr l G t2.

(*
  | ENewArray(n: nat){l: list var}(size: expr l 0): expr l (S n)
  | EGet{n: nat}{l1 l2: list var}(a: expr l1 (S n))(i: expr l2 0): expr (l1 ++ l2) n
  | EUpdate{n: nat}{l1 l2 l3: list var}(a: expr l1 (S n))(i: expr l2 0)(v: expr l3 n):
      expr (l1 ++ l2 ++ l3) (S n)
   (* TODO allow several updated vars
  | EFor{n2 n3: nat}{l1 l2 l3: list var}(i: var)(to: expr l1 0)(updates: var)(body: expr l2 n2)
      (rest: expr l3 n3):
      expr ([updates] ++ l1 ++ (remove eq_var_dec i l2) ++ l3) n3 *)
  .
*)

  Definition interp_type: type -> Type :=
    fix rec(t: type): Type := match t with
    | TNat => nat
    | TArray t' => list (rec t')
    end.

  Definition interp_type_IsArray(t: type): IsArray (list (interp_type t)) (interp_type t) :=
    match t with
    | TNat => ListIsArray nat 0
    | TArray _ => ListIsArray _ nil
    end.

  Definition extend_vals:
    forall {l} (G: member l -> type)(vals: forall m: member l, interp_type (G m))
    (x: var)(t: type)(v: interp_type t),
    forall m: member (x :: l), interp_type (extend G x t m).
    intros.
    apply (destruct_member m).
    - intro E. subst m. simpl. exact v.
    - intros m' E. subst m. simpl. exact (vals m').
  Defined.

  Definition interp_expr:
    forall {l G t}(e: expr l G t)(vals: forall x: member l, interp_type (G x)), interp_type t :=
    fix rec l G t (e: expr l G t) {struct e} :=
      match e in (expr l G t) return ((forall x: member l, interp_type (G x)) -> interp_type t) with
      | ELit v => fun vals => v
      | EVar m => fun vals => vals m
      | EOp e1 op e2 => fun vals => eval_binop_nat op (rec _ _ _ e1 vals) (rec _ _ _ e2 vals)
      | @ELet l G t1 t2 x e1 e2 => fun vals =>
          let r1 := rec _ _ _ e1 vals in
          let vals' := extend_vals G vals x t1 r1 in
          rec _ _ _ e2 vals'
      end.

End LLG.

Definition test1(v1 v2: nat): nat := let x1 := v1 in let x2 := v2 in x1.

Definition myvar := nat.
Definition var_x1: myvar := 1.
Definition var_x2: myvar := 2.

Definition empty_types: member (@nil myvar) -> type. intro. inversion H. Defined.
Definition empty_vals: forall m : member (@nil myvar), interp_type (empty_types m).
  intro. inversion m. Defined.

Definition x1_in_x2x1: member [var_x2; var_x1]. apply member_there. apply member_here. Defined.
Definition x2_in_x2x1: member [var_x2; var_x1]. apply member_here. Defined.

Definition test1a(v1 v2: nat): expr (@nil myvar) empty_types TNat :=
  ELet var_x1 (ELit v1) (ELet var_x2 (ELit v2) (EVar x1_in_x2x1)).

Definition interp_expr'{t}(e: expr (@nil myvar) empty_types t): interp_type t :=
  interp_expr e empty_vals.

Goal forall v1 v2, test1 v1 v2 = interp_expr' (test1a v1 v2).
  intros. reflexivity.
Qed.

Definition ListWithDefault0IsArray := ListIsArray nat 0.
Existing Instance ListWithDefault0IsArray.

Definition test2(i v: nat): nat :=
  let x1 := newArray 3 in
  let x2 := update x1 i v in
  get x2 i.

(*
Definition test2a(i v: nat): expr (@nil myvar) 0 :=
  ELet var_x1 (ENewArray 0 (ELit 3))
  (ELet var_x2 (EUpdate (EVar 1 var_x1) (ELit i) (ELit v))
  (EGet (EVar 1 var_x2) (ELit i))).

Goal forall i v, Some (test2 i v) = interp_expr' (test2a i v).
  intros. unfold interp_expr', interp_expr. reflexivity.
Qed.
*)
