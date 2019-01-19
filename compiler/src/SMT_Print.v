Require Import Coq.Logic.Classical_Prop.
Require Import compiler.util.Common.

(* print goal in smt-lib2 *)

Definition marker(P: Prop): Prop := P.
Definition marker2(P: Prop): Prop := P.

Lemma EE: forall AA (P: AA -> Prop), (exists a: AA, ~ P a) <-> ~ forall (a: AA), P a.
Proof.
  intros. split.
  - intros. destruct H as [a H]. intro. apply H. auto.
  - intro. destruct (classic (exists a : AA, ~ P a)) as [C | C]; [assumption|].
    exfalso. apply H. intro. destruct (classic (P a)) as [D | D]; [assumption |].
    exfalso. apply C. exists a. assumption.
Qed.

Lemma K: forall (P Q: Prop), (~ marker (P -> Q)) <-> marker (~ (P -> Q)).
Proof.
  cbv [marker]. intros. reflexivity.
Qed.

Definition Func(A B: Type) := A -> B.

Ltac smtify :=
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
       end;
(* revert all Props *)
repeat match goal with
       | H: ?T |- _ =>
         match type of T with
         | Prop => revert H
         end
       end;
(* express set operations in terms of "_ \in _" *)
unfold subset;
repeat (setoid_rewrite union_spec ||
        setoid_rewrite intersect_spec ||
        setoid_rewrite diff_spec);
(* protect functions from being treated as implications *)
repeat match goal with
       | x: ?T1 -> ?T2 |- _ => change (Func T1 T2) in x
       end;
(* mark where hyps begin *)
match goal with
| |- ?G => change (marker G)
end;
(* revert vars *)
repeat match goal with
       | x: ?T |- _ =>
         match T with
         | Type => fail 1
         | SetFunctions _ => fail 1
         | MapFunctions _ _ => fail 1
         | _ => idtac
         end;
           revert x
       end;
(* negate goal *)
match goal with
| |- ?P => assert (~P); [|admit]
end;
(* "not forall" to "exists such that not" *)
repeat match goal with
 | |- context[~ (forall (x: ?T), _)] =>
   (assert (forall (P: T -> Prop), (exists x: T, ~ P x) <-> ~ (forall x: T, P x)) as EEE
    by apply EE);
   setoid_rewrite <- EEE;
   clear EEE
end;
(* push "not" into marker *)
setoid_rewrite K;
(* marker for check_sat *)
match goal with
| |- ?P => change (marker2 P)
end.

(* SMT notations *)
Notation "'forall' '((' a T '))' body" := (forall (a: T), body)
   (at level 10, body at level 0, format "forall  (( a  T )) '//' body", only printing).
Notation "'and' A B" := (Logic.and A B) (at level 10, A at level 0, B at level 0).
Notation "'or' A B" := (Logic.or A B) (at level 10, A at level 0, B at level 0).
Notation "'implies' A B" := (A -> B) (at level 10, A at level 0, B at level 0).
Notation "= A B" := (@eq _ A B) (at level 10, A at level 0, B at level 0, only printing).
Notation "E x" := (contains E x) (at level 10, E at level 0, x at level 0, only printing).
Notation "= x y" := (contains (singleton_set x) y) (at level 10, x at level 0, y at level 0, only printing).
Notation "'not' A" := (not A) (at level 10, A at level 0).
Notation "'(assert' P ')'" := (marker P)
                                (at level 10, P at level 0,
                                 format "(assert  P )").
Notation "'(declare-const' a T ')' body" :=
  (ex (fun (a: T) => body))
    (at level 10, body at level 10,
     format "(declare-const  a  T ')' '//' body").
Notation "'(declare-fun' f '(' A ')' B ')' body" :=
  (ex (fun (f: Func A B) => body))
    (at level 10, body at level 10,
     format "(declare-fun  f  '(' A ')'  B ')' '//' body").
Notation "'(declare-fun' a '(' T ')' 'Bool)' body" :=
  (ex (fun (a: set T) => body))
    (at level 10, body at level 10,
     format "(declare-fun  a  '(' T ')'  'Bool)' '//' body").
Notation "'(declare-sort' 'var)' '(declare-sort' 'reg)' x '(check-sat)' '(get-model)'" :=
  (marker2 x) (at level 200, format "'(declare-sort'  'var)' '//' '(declare-sort'  'reg)' '//' x '//' '(check-sat)' '//' '(get-model)'").
