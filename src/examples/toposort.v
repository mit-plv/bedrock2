Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.

(* Note: you can't ask an array for its length *)
Class IsArray(T E: Set) := mkIsArray {
  defaultElem: E;
  get: T -> nat -> E;
  update: T -> nat -> E -> T;
  newArray: nat -> T
}.

Definition listUpdate{E: Set}(l: list E)(i: nat)(e: E): list E :=
  firstn i l ++ [e] ++ skipn (S i) l.

Definition listFill{E: Set}(e: E): nat -> list E :=
  fix rec(n: nat) := match n with
  | O => nil
  | S m => e :: rec m
  end.

Instance ListIsArray: forall (T: Set) (d: T), IsArray (list T) T := fun T d => {|
  defaultElem := d;
  get := fun l i => nth i l d;
  update := listUpdate;
  newArray := listFill d
|}.

Notation "'for' m 'from' 0 'to' N 'updating' ( s1 ) {{ b }} ;; rest" :=
  (let s1 :=
    (fix rec(n: nat) := match n with
     | 0 => s1
     | S m => let s1 := rec m in b
     end) N
  in rest)
  (at level 20, right associativity).

Notation "'for' m 'from' 0 'to' N 'updating' ( s1 ',' s2 ) {{ b }} ;; rest" :=
  (let '(s1, s2) :=
    (fix rec(n: nat) := match n with
     | 0 => (s1, s2)
     | S m =>
         let '(s1, s2) := rec m in b
     end) N
  in rest)
  (at level 20, right associativity).

Notation "'for' m 'from' 0 'to' N 'updating' ( s1 , s2 , s3 ) {{ b }} ;; rest" :=
  (let '(s1, s2, s3) :=
    (fix rec(n: nat) := match n with
     | 0 => (s1, s2, s3)
     | S m =>
         let '(s1, s2, s3) := rec m in b
     end) N
  in rest)
  (at level 20, right associativity).

Notation "'for' m 'from' 0 'to' N 'updating' ( s1 , s2 , s3 , s4 ) {{ b }} ;; rest" :=
  (let '(s1, s2, s3, s4) :=
    (fix rec(n: nat) := match n with
     | 0 => (s1, s2, s3, s4)
     | S m =>
         let '(s1, s2, s3, s4) := rec m in b
     end) N
  in rest)
  (at level 20, right associativity).

Notation "'for' m 'from' 0 'to' N 'updating' ( s1 , s2 , s3 , s4 , s5 ) {{ b }} ;; rest" :=
  (let '(s1, s2, s3, s4, s5) :=
    (fix rec(n: nat) := match n with
     | 0 => (s1, s2, s3, s4, s5)
     | S m =>
         let '(s1, s2, s3, s4, s5) := rec m in b
     end) N
  in rest)
  (at level 20, right associativity).

Section toposort.
  Context {Array: Set -> Set}.
  (*Context {ArrayIsArray: forall (E: Set), IsArray (Array E) E}.*)
  Context {NatArrayIsArray: IsArray (Array nat) nat}.
  Context {NatArrayArrayIsArray: IsArray (Array (Array nat)) (Array nat)}.

  Definition increment(a: Array nat)(i: nat): Array nat :=
    update a i (S (get a i)).

  Definition decrement(a: Array nat)(i: nat): Array nat :=
    update a i (pred (get a i)).

  Definition toposort
    (N: nat) (* number of nodes *)
    (A: Array (Array nat)) (* adjacency list for each node *)
    (outDegs: Array nat) (* out-degrees; outDegs[i] = length of A[i] *)
  : Array nat (* returns topologically sorted list *) :=
  let todo := newArray N in
  let todoSize := 0 in
  let inDegs := newArray N in
  for i from 0 to N updating (inDegs) {{
    update inDegs i 0
  }} ;;
  for i from 0 to N updating (inDegs) {{
    for j from 0 to (get outDegs i) updating (inDegs) {{
      increment inDegs (get (get A i) j)
    }} ;;
    inDegs
  }} ;;
  for i from 0 to N updating (todoSize, todo) {{ 
     if get inDegs i =? 0 then
      let todo := update todo todoSize i in
      let todoSize := S todoSize in
      (todoSize, todo)
    else
      (todoSize, todo)
  }} ;;
  let res := newArray N in
  for resSize from 0 to N updating (todoSize, todo, res, inDegs) {{
    let todoSize := pred todoSize in
    let n := get todo todoSize in
    let res := update res resSize n in
    for j from 0 to (get outDegs n) updating (todoSize, todo, inDegs) {{
      let inDegs := decrement inDegs (get (get A n) j) in
      if get inDegs (get (get A n) j) =? 0 then
        let todo := update todo todoSize (get (get A n) j) in
        let todoSize := S todoSize in
        (todoSize, todo, inDegs)
      else
        (todoSize, todo, inDegs)
    }} ;;
    (todoSize, todo, res, inDegs)
  }} ;;
  res.



(*




  Definition toposort
    (N: nat) (* number of nodes *)
    (A: Array (Array nat)) (* adjacency list for each node *)
    (outDegs: Array nat) (* out-degrees; outDegs[i] = length of A[i] *)
  : Array nat (* returns topologically sorted list *) :=
  let todo := newArray N in
  let todoSize := 0 in
  let inDegs := newArray N in
  let inDegs := forLoop inDegs N (fun i inDegs =>
    update inDegs i 0
  ) in
  let inDegs := forLoop inDegs N (fun i inDegs =>
    forLoop inDegs (get outDegs i) (fun j inDegs =>
      increment inDegs (get (get A i) j)
    )
  ) in
  let '(_, todoSize, todo) := forLoop (tt, todoSize, todo) N (fun i p =>
    let '(_, todoSize, todo) := p in
    let '(_, todoSize, todo) :=
    if get inDegs i =? 0 then
      let todo := update todo todoSize i in
      let todoSize := S todoSize in
      (tt, todoSize, todo)
    else
      (tt, todoSize, todo)
    in (tt, todoSize, todo)
  ) in
  let '(_, _, res, _) := forLoop (todoSize, todo, newArray N, inDegs) N (fun resSize p =>
    let '(todoSize, todo, res, inDegs) := p in
    let todoSize := pred todoSize in
    let n := get todo todoSize in
    let res := update res resSize n in
    let '(todoSize, todo, inDegs) := forLoop (todoSize, todo, inDegs) (get outDegs n) (fun j p =>
      let '(todoSize, todo, inDegs) := p in
      let inDegs := decrement inDegs (get (get A n) j) in
      if get inDegs (get (get A n) j) =? 0 then
        let todo := update todo todoSize (get (get A n) j) in
        let todoSize := S todoSize in
        (todoSize, todo, inDegs)
      else
        (todoSize, todo, inDegs)
    ) in
    (todoSize, todo, res, inDegs)
  ) in 
  res.
*)
End toposort.

Definition N := 6.
Definition a0 := [5].
Definition a1 := [2; 5].
Definition a2 := @nil nat.
Definition a3 := [1; 2].
Definition a4 := [1; 5].
Definition a5 := [2].
Definition A := [a0; a1; a2; a3; a4; a5].
Definition outDegs := map (@length nat) A.

Definition toposort2 := @toposort list (ListIsArray nat 0) (ListIsArray (list nat) []).

Definition result: list nat := toposort2 N A outDegs.

Goal result = [4; 3; 1; 0; 5; 2]. reflexivity. Qed.


Definition toposort3(N: nat)(A: list (list nat))(outDegs: list nat): list nat.
  set (t := toposort2 N A outDegs).
  cbv beta delta [
    toposort2 toposort increment decrement
  ] in t.
  match goal with
  | t := ?a |- _ => exact a
  end.
Defined.

Print toposort3. (* not quite what we want *)

Definition toposort4 := ltac:(let res := eval cbv beta delta [
    toposort2 toposort increment decrement
  ] in
  (fun N A outDegs => toposort2 N A outDegs) in exact res).

Print toposort4.

Definition toposort5 := ltac:(let res := eval cbv beta delta [
    toposort2 toposort increment decrement
  ] in
  (toposort2 N A outDegs) in exact res).

Print toposort5. (* this expression should hopefully be easy to reify *)

Require Import compiler.Decidable.

(* Low-Level Gallina *)
Section LLG.

  Context {var: Set}.
  Context {eq_var_dec: DecidableEq var}.
  
  Inductive expr: nat -> Set :=
  | EVar{n: nat}(x: var): expr n
  | ELet{n1 n2: nat}(x: var)(e1: expr n1)(e2: expr n2): expr n2
  | ENewArray{n: nat}(size: expr 0)(init: expr n): expr (S n)
  | EGet{n: nat}(a: expr (S n))(i: expr 0): expr n
  | EUpdate{n: nat}(a: expr (S n))(i: expr 0)(v: expr n): expr (S n)
  | EFor{n: nat}(i: var)(to: expr 0)(updates: var (* TODO allow several *))(body: expr n): expr n
  .

  Definition interp_type: nat -> Type :=
    fix rec(n: nat): Type := match n with
    | O => nat
    | S m => list (rec m)
    end.

  Definition interp_expr{n: nat}: expr n -> option (interp_type n) :=
    fix rec(e: expr n) := match e with
    | EVar x => None
    | ELet x e1 e2 => None 
    | ENewArray size init => None
    | EGet a i => None
    | EUpdate a i v => None
    | EFor i to updates body => None
    end.
  (* how to deal with binders? Actually, if e has a free variable of type T, 
     the return type of interp_expr should be "option (T -> ...)" instead *)

End LLG.


