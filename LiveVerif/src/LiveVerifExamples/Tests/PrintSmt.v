From Coq Require Import ZArith.
Require Import coqutil.Word.Interface.
From Coq Require Import Classical_Prop.
Require Import coqutil.Tactics.ident_ops.

Ltac eval_constant_pows :=
  repeat match goal with
         | |- context[Z.pow ?x ?y] =>
             lazymatch isZcst x with
             | true => lazymatch isZcst y with
                       | true => let r := eval cbv in (Z.pow x y) in
                                 change (Z.pow x y) with r
                       end
             end
         end.

Lemma ExistsNot_NotForall: forall AA (P: AA -> Prop), (exists a: AA, ~ P a) <-> ~ forall (a: AA), P a.
Proof.
  intros. split.
  - intros. destruct H as [a H]. intro. apply H. auto.
  - intro. destruct (classic (exists a : AA, ~ P a)) as [C | C]; [assumption|].
    exfalso. apply H. intro. destruct (classic (P a)) as [D | D]; [assumption |].
    exfalso. apply C. exists a. assumption.
Qed.

Inductive Name := mkName (f: unit -> unit).
Notation "'name:(' x )" := (mkName (fun x: unit => x)) (format "name:( x )").

Definition smtFalseAlias := False.
Definition smtGoalMarker(P: Prop) := P.
Definition namedSmtGoalMarker(width: Z)(n: Name)(P: Prop) := P.

Ltac markSmtGoal :=
  lazymatch goal with
  | |- ?g => change (smtGoalMarker g)
  end.

Ltac markNamedSmtGoal width name :=
  lazymatch goal with
  | |- ?g => change (namedSmtGoalMarker width name g)
  end.

Ltac unmarkSmtGoal :=
  lazymatch goal with
  | |- smtGoalMarker ?g => change g
  | |- namedSmtGoalMarker _ _ ?g => change g
  end.

(* turns
     forall x1 ... xN, P
   into
     forall x1 ... xN, ~ P -> smtFalseAlias
   where the xi can be (dependent) variables or (non-dependent) hypotheses in any order.
   Also clears unused non-Prop variables. *)
Ltac by_contradiction :=
  eapply NNPP;
  let C := fresh "C" in
  intro C;
  repeat lazymatch type of C with
  | ~ forall x, _ =>
      eapply ExistsNot_NotForall in C;
      with_unprimed_fresh x (fun f => destruct C as [f C])
  end;
  change smtFalseAlias;
  repeat lazymatch goal with
         | H: ?T |- _ => lazymatch T with
                         | word.word _ => fail
                         | @word.ok _ _ => fail
                         | _ => lazymatch type of T with
                                | Prop => revert H
                                (* clear unused variables, because otherwise the notations
                                   print it as an assert instead of declare-const *)
                                | _ => clear H || revert H
                                end
                         end
         end.

Ltac undo_by_contradiction :=
  intros;
  lazymatch goal with
  | C: not _ |- smtFalseAlias => apply C; clear C
  end.

Ltac log_goal_as_smt name :=
  eval_constant_pows;
  by_contradiction;
  let width := lazymatch goal with
               | word: word.word ?width |- _ => width
               end in
  (* markNamedSmtGoal width name; *)
  markSmtGoal;
  lazymatch goal with
  | |- ?g => idtac g
  end;
  unmarkSmtGoal;
  undo_by_contradiction.

Declare Custom Entry smt_sort.
Declare Custom Entry smt_expr.
Declare Custom Entry smt_goal.
Declare Custom Entry smt_func.

(* Goal Structure: *)

(* TODO conflicts with SuppressibleWarnings, probably better to not do this at all
Notation "g" := (smtGoalMarker g)
  (at level 100, g custom smt_goal at level 3, only printing). *)

Notation "'(BEGIN' 'SMT' 'QUERY)' g '(END' 'SMT' 'QUERY)'" := (smtGoalMarker g)
  (at level 10, g custom smt_goal at level 3,
   format "(BEGIN  SMT  QUERY) '//' g '//' (END  SMT  QUERY)").

(* bash syntax to print to a file *)
Notation "'cat' > './width' W / x '.smt2' << ' 'SMTQUERY' ' g 'SMTQUERY'" :=
  (namedSmtGoalMarker W (mkName (fun x => x)) g)
  (at level 0, g custom smt_goal at level 3, only printing,
   format "cat  >  ./width W / x .smt2  << ' SMTQUERY ' '//' g '//' SMTQUERY").

(* bash syntax to print to feed to z3's stdin *)
Notation "'time' 'z3' '-in' << ' 'SMTQUERY' ' g 'SMTQUERY'" :=
  (smtGoalMarker g)
  (at level 0, g custom smt_goal at level 3, only printing,
   format "time  z3  -in  << ' SMTQUERY ' '//' g '//' SMTQUERY").

Notation "'(declare-const' x T ) P" := (forall x: T, P)
  (in custom smt_goal at level 3, x name, T custom smt_sort, right associativity,
   format "(declare-const  x  T ) '//' P").

(* TODO recursive notation for any number of parameters? *)
Notation "'(declare-fun' x ( A1 ) R ) P" := (forall x: A1 -> R, P)
  (in custom smt_goal at level 3, x name, A1 custom smt_sort, R custom smt_sort,
   right associativity,
   format "(declare-fun  x  ( A1 )  R ) '//' P").

Notation "'(assert' P ) Q" := (P -> Q)
  (in custom smt_goal at level 3, P custom smt_expr, right associativity,
   format "(assert  P ) '//' Q").

Notation "'(check-sat)'" := smtFalseAlias (in custom smt_goal).


(* Sorts: *)

Notation "'(_' 'BitVec' Width ')'" := (@word.rep Width _)
  (in custom smt_sort, Width constr at level 0).
Notation "'Int'" := Z
  (in custom smt_sort).
Notation "'Bool'" := bool
  (in custom smt_sort, only printing).
Notation "'Bool'" := Prop
  (in custom smt_sort, only printing).
(* hides Bool notations?
Notation "x" := x
  (in custom smt_sort at level 0, x constr at level 0). *)

(* Expressions: *)

Notation "( 'an' 'd' a b )" := (andb a b)
  (in custom smt_expr at level 0, format "( an d  a  b )", only printing).
Notation "( 'o' 'r' a b )" := (orb a b)
  (in custom smt_expr at level 0, format "( o r  a  b )", only printing).
Notation "( 'no' 't' P )" := (negb P)
  (in custom smt_expr at level 0, format "( no t  P )", only printing).

Notation "( 'and' a b )" := (and a b)
  (in custom smt_expr at level 0, format "( and  a  b )").
Notation "( 'or' a b )" := (or a b)
  (in custom smt_expr at level 0, format "( or  a  b )").
Notation "( 'not' P )" := (not P)
  (in custom smt_expr at level 0, format "( not  P )").
Notation "'true'" := True
  (in custom smt_expr at level 0).
Notation "'false'" := False
  (in custom smt_expr at level 0).

(*
Notation "( 'ite' c a b )" :=
  (match c with
   | true => a
   | false => b
   end)
  (in custom smt_expr at level 0, format "( ite  c  a  b )").
*)
Notation "( 'ite' c a b )" := (if c then a else b)
  (in custom smt_expr at level 0, format "( ite  c  a  b )").


(* Note: these are needed to compete against standard notations in order to be
   considered at least as specific as them (which would fail if we only relied on
   our custom function application notation) *)
Notation "( 'not' ( = a b ) )" := (not (eq a b))
  (in custom smt_expr at level 0, only printing,
   format "( 'not'  ( =  a  b ) )").
Notation "'(and'  (<=  x  y )  (<=  y  z ) )" := (and (Z.le x y) (Z.le y z))
  (in custom smt_expr at level 0, only printing).
Notation "'(and'  (<=  x  y )  (<  y  z ) )" := (and (Z.le x y) (Z.lt y z))
  (in custom smt_expr at level 0, only printing).
Notation "'(and'  (<  x  y )  (<=  y  z ) )" := (and (Z.lt x y) (Z.le y z))
  (in custom smt_expr at level 0, only printing).
Notation "'(and'  (<  x  y )  (<  y  z ) )" := (and (Z.lt x y) (Z.lt y z))
  (in custom smt_expr at level 0,only printing).

Notation "'(='  a  b )" := (eq a b)
  (in custom smt_expr at level 0).
Notation "'(<='  a  b )" := (Z.le a b)
  (in custom smt_expr at level 0).
Notation "'(<'  a  b )" := (Z.lt a b)
  (in custom smt_expr at level 0).
Notation "(-  a  b )" := (Z.sub a b)
  (in custom smt_expr at level 0).
Notation "(-  a )" := (Z.opp a)
  (in custom smt_expr at level 0).
Notation "(+  a  b )" := (Z.add a b)
  (in custom smt_expr at level 0).
Notation "(*  a  b )" := (Z.mul a b)
  (in custom smt_expr at level 0).

Notation "'(bv2int'  a )" := (word.unsigned a)
  (in custom smt_expr at level 0).
Notation "'((_'  'int2bv'  Width )  x )" := (@word.of_Z Width _ x)
  (in custom smt_expr at level 0, Width constr at level 0).

Notation "'(bvneg'  a )" := (word.opp a)
  (in custom smt_expr at level 0).
Notation "'(bvadd'  a  b )" := (word.add a b)
  (in custom smt_expr at level 0).
Notation "'(bvsub'  a  b )" := (word.sub a b) (* NONSTANDARD *)
  (in custom smt_expr at level 0).
(*
Notation "'(bvadd'  a  '(bvneg'  b ) )" := (word.sub a b)
  (in custom smt_expr at level 0).
*)
Notation "'(bvult'  a  b )" := (word.ltu a b)
  (in custom smt_expr at level 0).

Notation "( f  a )" := (f a)
  (in custom smt_expr at level 0,
   f custom smt_func at level 0, a custom smt_expr at level 0).

Notation "( f  a1 a2 )" := (f a1 a2)
  (in custom smt_expr at level 0,
   f custom smt_func at level 0,
   a1 custom smt_expr at level 0, a2 custom smt_expr at level 0).

(* fallback for variables and Z literals *)
Notation "x" := x
  (in custom smt_expr at level 0, x constr at level 0).

(* Function names that are variables: *)
Notation "f" := f
  (in custom smt_func at level 0, f ident, only printing).
