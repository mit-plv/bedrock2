Require Import Coq.Logic.Classical_Prop.
Require Import compiler.util.Common.

(* Interpreting counterexamples output by Z3 *)

Ltac prepare_counterex :=
(* intro as much as we can *)
repeat intro;
(* map to fun *)
repeat match goal with
       | m: map _ _ |- _ =>
         let f := fresh "f" in
         let H := fresh "HE" in
         remember (get m) as f eqn: H;
           clear m H
       end;
(* clear everything except used vars and Props *)
repeat match goal with
       | H: ?T |- _ =>
         match type of T with
         | Prop => fail 1
         | _ => clear H
         end
       end.

Ltac disj_to_set d :=
  lazymatch d with
    | (_ = ?v1 \/ ?rest) =>
      let s := disj_to_set rest in
      constr:(union (singleton_set v1) s)
    | (_ = ?v1) => constr:(singleton_set v1)
    | _ => fail "did not expect" d
  end.

Ltac universe_of T :=
  let _ := match tt with
           | _ => constr:(@singleton_set T _)
           | _ => fail 1000 "no set instance found for" T
           end in
  match goal with
  | H: forall (x: T), _ |- _ =>
    let dummyT := match type of H with
                  | forall (x: T), x = ?v1 => constr:(v1)
                  | forall (x: T), x = ?v1 \/ _ => constr:(v1)
                  end in
    let P' := type of (H dummyT) in
    disj_to_set P'
  end.

Inductive ____BEGIN_counterexample____: Prop :=
  mk_BEGIN_counterexample: ____BEGIN_counterexample____.
Inductive ____END_counterexample____: Prop :=
  mk_END_counterexample: ____END_counterexample____.
Inductive ____cardinality_constraint: Prop :=
  mk_cardinality_constraint: ____cardinality_constraint.

Tactic Notation "(model" tactic(t) :=
  pose proof mk_BEGIN_counterexample; t.
Tactic Notation ")" :=
  pose proof mk_END_counterexample.
Tactic Notation ";;" "universe" "for" constr(T) ":" tactic(t) := t.
Tactic Notation ";;" ident(v1) tactic(t) := t.
Tactic Notation ";;" ident(v1) ident(v2) tactic(t) := t.
Tactic Notation ";;" ident(v1) ident(v2) ident(v3) tactic(t) := t.
Tactic Notation ";;" ident(v1) ident(v2) ident(v3) ident(v4) tactic(t) := t.
Tactic Notation ";;" "-----------" tactic(t) := t.
Tactic Notation ";;" "definitions" "for" "universe" "elements:" tactic(t) := t.
Tactic Notation "(declare-fun" ident(x) "()" constr(T) ")" tactic(t) :=
  (assert (x: T) by admit); t.
Tactic Notation "(define-fun" ident(x) "()" constr(T) constr(v) ")" tactic (t) :=
  let E := fresh "E" in (assert (x = v) as E by admit);
  rewrite E in *;
  t.
Tactic Notation "(define-fun" ident(f) "(" "(" ident(x) constr(T) ")" ")" constr(U)
       constr(body) ")" tactic(t) :=
  let E := fresh "E" in (assert (f = fun (x: T) => body) as E by admit);
  rewrite E in *;
  t.
Tactic Notation "(define-fun" ident(f) "(" "(" ident(x) constr(T) ")" ")" "Bool"
       "false" ")" tactic(t) :=
  let E := fresh "E" in (assert (f = empty_set) as E by admit);
  rewrite E in *;
  t.
Tactic Notation "(define-fun" ident(f) "(" "(" ident(x) constr(T) ")" ")" "Bool"
       "true" ")" tactic(t) :=
  let s := universe_of T in
  let E := fresh "E" in (assert (f = s) as E by admit);
  rewrite E in *;
  t.

Tactic Notation ";;" "cardinality" "constraint:" constr(P) tactic(t) :=
  pose proof mk_cardinality_constraint; assert P by admit; t.

(* Gallina notations to parse cardinality constraints: *)
Notation "'forall' '(' '(' a T ')' ')' body" := (forall (a: T), body)
   (at level 200, a at level 0, T at level 0, body at level 0, only parsing).
Notation "'or' A B" := (Logic.or A B)
   (at level 10, A at level 0, B at level 0, only parsing).
Notation "= A B" := (@eq _ A B)
   (at level 10, A at level 0, B at level 0, only parsing).
