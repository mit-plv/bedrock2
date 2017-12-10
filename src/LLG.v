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

(*
  Definition fill_in_type(x: var)(t: nat)(l: list var)(types: member (remove eq_var_dec x l) -> nat):
    (member l -> nat) :=
    fun m => match (eq_var_dec (member_get m) x) with
      | left _ => t
      | right NEq => types (member_remove eq_var_dec x l m NEq)
      end.

  Definition fill_in_val(x: var)(t: nat)(v: interp_type t)(l: list var)
    (R: member (remove eq_var_dec x l) -> nat)
    (vals: forall m : member (remove eq_var_dec x l), interp_type (R m)):
    (forall m: member l, interp_type (fill_in_type x t l R m)).
    intro m.
    unfold fill_in_type.
    destruct (eq_var_dec (member_get m) x).
    + exact v.
    + apply (vals (member_remove eq_var_dec x l m n)).
  Defined.
*)

(*  Definition fill_in_val{tx: nat}(x: var)(v: interp_type tx)(l: list var)
    (R: member (remove eq_var_dec x l) -> V)
    (vals: forall (m: member (remove eq_var_dec x l)), R m):
    (forall (m: member l), R m). :=
    fun m => match (eq_var_dec (member_get m) x) with
      | left _ => t
      | right NEq => types (member_remove eq_var_dec x l m NEq)
      end.
*)
(*
  Definition fill_in_val{V: Type}(x: var)(v: V)(l: list var)(R: member (remove eq_var_dec x l) -> V)
    (vals: forall (m: member (remove eq_var_dec x l)), R m):
    (forall (m: member l), R m). :=
    fun m => match (eq_var_dec (member_get m) x) with
      | left _ => t
      | right NEq => types (member_remove eq_var_dec x l m NEq)
      end.
*)

(*
  Definition update_vals(l: list var)(types: member l -> Type)(i: member l)(v: types i)
    (vals: forall m : member l, types m):
           forall m : member l, types m.
    intro m.
    (* destruct (eq_var_dec (member_get i) (member_get m)). bad because member_get not injective *)
    destruct (eq_member_dec _ i m).
    - rewrite <- e. exact v.
    - exact (vals m).
  Defined.
*)

Require Import lib.LibTactics.


  Definition interp_expr{l G t}: 
    forall (e: expr l G t)(vals: forall x: member l, interp_type (G x)), interp_type t.
    refine (fix rec (e: expr l G t)(vals: forall x: member l, interp_type (G x))
               {struct e}: interp_type t :=
      match e with
      | ELit v => _
      | EVar m => _
      | EOp e1 op e2 => _
      | ELet x e1 e2 => _
      end).
      - exact v.
      - Fail exact (vals m).
  Abort.

  Definition interp_expr{l G t}: 
    forall (e: expr l G t)(vals: forall x: member l, interp_type (G x)), interp_type t.
    refine (fix rec (e: expr l G t) :=
      match e in (expr l G t) return ((forall x: member l, interp_type (G x)) -> interp_type t) with
      | ELit v => fun vals => v
      | EVar m => fun vals => vals m
      | EOp e1 op e2 => fun vals => _
      | ELet x e1 e2 => _
      end).
      - Fail exact (eval_binop_nat op (rec e1 vals) (rec e2 vals)).
  Abort.

  Definition extend_vals:
    forall {l} (G: member l -> type)(vals: forall m: member l, interp_type (G m))
    (x: var)(t: type)(v: interp_type t),
    forall m: member (x :: l), interp_type (extend G x t m).
    Admitted. (*
  refine (fun l G vals x t v m => 
    match m with
    | member_here _ _ => fun l G vals m => _
    | member_there _ _ _ => fun l G vals m => _
    end l G vals).

  Definition extend_vals:
    forall l (G: member l -> type)(vals: forall m: member l, interp_type (G m))
    (x: var)(t: type)(v: interp_type t),
    forall m: member (x :: l) -> interp_type (extend G x t m).
  refine (fun l G vals x t v m => 
    match m with
    | member_here _ _ => fun l G vals m => _
    | member_there _ _ _ => fun l G vals m => _
    end l G vals).
    - unfold extend. 

  Definition extend_vals{l}(G: member l -> type)(vals: forall m: member l, interp_type (G m))
    (x: var)(t: type)(v: interp_type t):
    forall m: member (x :: l) -> interp_type (extend G x t m) :=
    refine (
    intro m. destruct m.
    
     :=
    fun m => match m with (* (fancy return clause inferred) *)
    | member_here _ _ => fun _ => t
    | member_there _ _ m' => fun G => G m'
    end G.
*)

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

(*
  Fixpoint interp_expr{n: nat}{l: list var}
    (e: expr l n) (types: member l -> nat)
    {struct e}:
      option ((forall x: member l, interp_type (types x)) -> interp_type n).
    destruct e eqn: E.
    - simpl. apply Some. intro vals. exact v.
    - destruct (Nat.eq_dec n (types (member_here x []))).
      + subst n. apply Some.
        intro vals. set (v := vals (member_here x nil)).
        apply v.
      + exact None. (* error: types list doesn't match *)
    - set (o1 := interp_expr _ l1 e0_1 (fun m => types (member_app_r l1 l2 m))).
      simpl in o1.
      destruct o1 as [f1|].
      + set (o2 := interp_expr _ l2 e0_2 (fun m => types (member_app_l l1 l2 m))).
        simpl in o2.
        destruct o2 as [f2|].
        * apply Some. intro vals.
          specialize (f1 (fun m => vals (member_app_r l1 l2 m))).
          specialize (f2 (fun m => vals (member_app_l l1 l2 m))).
          exact (eval_binop_nat op f1 f2).
        * exact None.
      + exact None.
    - set (o1 := interp_expr n1 l1 e0_1
        (fun (m: member l1) => types (member_app_r l1 (remove eq_var_dec x l2) m))).
      destruct o1 as [f1|].
      + set (types' := (fun m => types (member_app_l l1 (remove eq_var_dec x l2) m))).
        set (types'' := fill_in_type x n1 l2 types').
        set (o2 := interp_expr n2 l2 e0_2 types'').
        destruct o2 as [f2|].
        * apply Some. intro vals.
          specialize (f1 (fun (m: member l1) => vals  (member_app_r l1 (remove eq_var_dec x l2) m))).
          set (vals' := (fun m => vals (member_app_l l1 (remove eq_var_dec x l2) m))).
          replace (forall m : member (remove eq_var_dec x l2),
                   interp_type (types (member_app_l l1 (remove eq_var_dec x l2) m)))
             with (forall m : member (remove eq_var_dec x l2),
                   interp_type (types' m)) in vals'
             by (subst types'; reflexivity).
          subst types''.
          set (vals'' := fill_in_val x n1 f1 l2 types' vals').
          exact (f2 vals'').
        * exact None.
      + exact None.
    - set (o := interp_expr 0 l e0 types).
      simpl in o.
      destruct o as [f|].
      + apply Some. intro vals.
        specialize (f vals).
        exact (@newArray _ _ (interp_type_IsArray n) f).
      + exact None.
    - set (o1 := interp_expr _ l1 e0_1 (fun m => types (member_app_r l1 l2 m))).
      simpl in o1.
      destruct o1 as [f1|].
      + set (o2 := interp_expr _ l2 e0_2 (fun m => types (member_app_l l1 l2 m))).
        simpl in o2.
        destruct o2 as [f2|].
        * apply Some. intro vals.
          specialize (f1 (fun m => vals (member_app_r l1 l2 m))).
          specialize (f2 (fun m => vals (member_app_l l1 l2 m))).
          exact (@get _ _ (interp_type_IsArray n) f1 f2).
        * exact None.
      + exact None.
    - set (o1 := interp_expr _ l1 e0_1
        (fun m => types (member_app_13 l1 l2 l3 m))).
      simpl in o1.
      destruct o1 as [f1|].
      + set (o2 := interp_expr _ l2 e0_2 (fun m => types (member_app_23 l1 l2 l3 m))).
        simpl in o2.
        destruct o2 as [f2|].
        * set (o3 := interp_expr _ l3 e0_3 (fun m => types (member_app_33 l1 l2 l3 m))).
          destruct o3 as [f3|].
          { apply Some. intro vals.
            specialize (f1 (fun m => vals  (member_app_13 l1 l2 l3 m))).
            specialize (f2 (fun m => vals  (member_app_23 l1 l2 l3 m))).
            specialize (f3 (fun m => vals  (member_app_33 l1 l2 l3 m))).
            exact (@update _ _ (interp_type_IsArray n) f1 f2 f3). }
          { exact None. }
        * exact None.
      + exact None.
  Defined.
*)
End LLG.
(*
Definition test1(v1 v2: nat): nat := let x1 := v1 in let x2 := v2 in x1.

Definition myvar := nat.
Definition var_x1: myvar := 1.
Definition var_x2: myvar := 2.

Definition test1a(v1 v2: nat): expr (@nil myvar) 0 :=
  ELet var_x1 (ELit v1) (ELet var_x2 (ELit v2) (EVar 0 var_x1)).

Definition empty_types: member (@nil myvar) -> nat. intro. inversion H. Defined.
Definition empty_vals: forall m : member (@nil myvar), interp_type (empty_types m).
  intro. inversion m. Defined.

Definition interp_expr'{n: nat}(e: expr (@nil myvar) n): option (interp_type n) :=
  match interp_expr e empty_types with
  | Some f => Some (f empty_vals)
  | None => None
  end.

Goal forall v1 v2, Some (test1 v1 v2) = interp_expr' (test1a v1 v2).
  intros. reflexivity.
Qed.

Definition ListWithDefault0IsArray := ListIsArray nat 0.
Existing Instance ListWithDefault0IsArray.

Definition test2(i v: nat): nat :=
  let x1 := newArray 3 in
  let x2 := update x1 i v in
  get x2 i.

Definition test2a(i v: nat): expr (@nil myvar) 0 :=
  ELet var_x1 (ENewArray 0 (ELit 3))
  (ELet var_x2 (EUpdate (EVar 1 var_x1) (ELit i) (ELit v))
  (EGet (EVar 1 var_x2) (ELit i))).

Goal forall i v, Some (test2 i v) = interp_expr' (test2a i v).
  intros. unfold interp_expr', interp_expr. reflexivity.
Qed.
*)
