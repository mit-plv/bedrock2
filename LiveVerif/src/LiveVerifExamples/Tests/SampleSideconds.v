Require Import LiveVerif.LiveVerifLib.

Ltac standalone_solver_step :=
  first
      [ (* tried first because it also solves some goals of shape (_ = _) and (_ /\ _) *)
        zify_hyps; zify_goal; xlia zchecker
      | (* manually chosen set of safe_implication steps: *)
        lazymatch goal with
        | |- ?xs ++ ?ys1 = ?xs ++ ?ys2 => f_equal
        | |- ?xs1 ++ ?ys = ?xs2 ++ ?ys => f_equal
        end
      (* from step_hook in tree_set: *)
      | lazymatch goal with
        | |- ?A \/ ?B =>
            tryif (assert_succeeds (assert (~ A) by (zify_hyps; zify_goal; xlia zchecker)))
            then right else
            tryif (assert_succeeds (assert (~ B) by (zify_hyps; zify_goal; xlia zchecker)))
            then left else fail
        end
      | lazymatch goal with
        | H: _ \/ _ |- _ =>
            destruct H; try (exfalso; congruence);
            [ ]
        end
      | lazymatch goal with
        | |- ?P /\ ?Q =>
            split
        | |- _ = _ =>
            careful_reflexivity_step_hook
        | |- impl1 ?lhs ?rhs =>
            careful_reflexivity_step_hook
        | |- iff1 _ _ =>
            careful_reflexivity_step_hook
        | |- forall _, _ =>
            intros
        end
      | solve [intuition idtac]
    ].

(* TODO investigate why standalone_solver_step is not as powerful as step *)

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

Require Import Coq.Logic.Classical_Prop.

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
  | ~ forall H, _ =>
      eapply ExistsNot_NotForall in C;
      let name := fresh (*H*) in (* TODO filter out single quotes *)
      destruct C as [name C]
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


Section Tests.

(* configurable to any concrete bitwidth, so that slow bitblasting can be tested
   with small bitwidths such as 8 *)
Local Notation width := 7 (only parsing).

Context {word: word.word width} {word_ok: word.ok word}.
Local Open Scope word_scope.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
Local Hint Mode Word.Interface.word - : typeclass_instances.

Add Ring wring : (Properties.word.ring_theory (word := word))
      ((*This preprocessing is too expensive to be always run, especially if
         we do many ring_simplify in a sequence, in which case it's sufficient
         to run it once before the ring_simplify sequence.
         preprocess [autorewrite with rew_word_morphism],*)
       morphism (Properties.word.ring_morph (word := word)),
       constants [Properties.word_cst]).

Definition prelude1 := tt.
Notation "'#!/bin/sh'" := prelude1 (only printing).
Definition prelude2 := tt.
Notation "'set' '-e'" := prelude2 (only printing).
Goal True. let p1 := prelude1 in let p2 := prelude2 in idtac p1; idtac p2. Abort.

Ltac t name :=
  log_goal_as_smt name;
  repeat standalone_solver_step.

Goal forall (a b r : word) (c : bool),
 c = word.ltu a b ->
 r = (if c then a else b) -> \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b.
Proof. t name:(ltu_ite). Qed.

(* TODO replace Z.min by def and support for define-fun
Goal forall (a b c : word) (r : word),
 \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b ->
 forall (s : word),
 \[r] < \[c] /\ s = r \/ \[c] <= \[r] /\ s = c ->
 \[s] = Z.min \[a] (Z.min \[b] \[c]).
Proof. t name:(min2_1). Qed.
*)

Goal forall (l: word),
 l <> /[0] ->
 \[l] = 0 ->
 False.
Proof. t name:(int2bv_roundtrip_contrad_0). Qed.

Goal forall (l: word) (z: Z),
 l <> /[z] ->
 \[l] = z ->
 False.
Proof. t name:(int2bv_roundtrip_contrad). Qed.

Goal forall (p v : word) (s : Z -> Prop) (res : word),
 res = /[0] ->
 forall a : word,
 a = p ->
(* TODO forall notations!   (forall x : Z, ~ s x) -> *)
 a = /[0] ->
 ~ s \[v] ->
 (\[res] = 1 /\ s \[v] \/ \[res] = 0 /\ ~ s \[v]).
Proof. t name:(tree_set_r1). Qed.

Goal forall (fib: word -> word) (n : word),
 n <> /[0] ->
 forall (v : Z) (i' a' : word),
 a' = fib (i' ^- /[1]) ->
 forall t a b i : word,
 v = \[n] - \[i'] ->
 1 <= \[i'] <= \[n] ->
 \[i'] < \[n] ->
 a = fib i' ->
 t = a' ^+ fib i' -> b = t -> i = i' ^+ /[1] ->
 a = fib (i ^- /[1]).
Proof.
  t name:(fib1).
  unfold don't_know_how_to_prove. subst. bottom_up_simpl_in_goal. reflexivity.
Qed.

Goal forall (fib: word -> word) (n : word),
 n <> /[0] ->
 forall (v : Z) (i a : word),
 a = fib (i ^- /[1]) ->
 forall b : word,
 b = fib i ->
 v = \[n] - \[i] ->
 1 <= \[i] <= \[n] ->
 \[n] <= \[i] ->
 b = fib n.
Proof.
  t name:(fib2). unfold don't_know_how_to_prove. f_equal. ZnWords.
Qed.

Goal forall (in0 in1 in2 : Z) (w0 : word),
 w0 = /[in0] ->
 forall (w2'' w1 w2 : word) (c c' : bool),
 c' = negb (word.ltu /[in0] /[in1]) && negb (word.ltu /[in2] /[in1]) ->
 c = negb (word.ltu /[in0] /[in2]) && negb (word.ltu /[in1] /[in2]) ->
 w2'' = (if c then /[in0] else /[in2]) ->
 0 <= in0 < 2 ^ width ->
 w1 = (if c' then /[in0] else /[in1]) ->
 w2 = (if c' then /[in2] else w2'') ->
 forall (c0 : bool),
 c0 = word.ltu w2 w1 ->
 0 <= in1 < 2 ^ width ->
 0 <= in2 < 2 ^ width ->
 (if c' then in1 else if c then in2 else in0) <=
   \[if c0 then w2 else w1] <= \[if c0 then w1 else w2].
Proof. t name:(sort3). Qed.

Goal forall (v : word) (s0 : Z -> Prop) (a' : word) (res a : word) (v1 : Z),
 s0 v1 ->
(* (forall x : Z, ~ (s0 x /\ x < v1)) -> TODO forall, but it's not needed here *)
 res = /[0] ->
 a' <> /[0] ->
 forall here : word,
 here = /[v1] ->
 \[v] < v1 ->
 a = /[0] ->
 ~ (s0 \[v] /\ \[v] < v1) ->
 \[res] = 0 /\ ~ s0 \[v].
Proof. t name:(tree_set_not_and1). Qed.

Goal forall (v : word) (s0 : Z -> Prop) (a' : word) (res a : word) (v1 : Z),
 s0 v1 ->
(* (forall x : Z, ~ (s0 x /\ x < v1)) -> TODO forall, but not actually needed here *)
 res = /[0] ->
 a' <> /[0] ->
 forall here : word,
 here = /[v1] ->
 \[v] < v1 ->
 a = /[0] ->
 ~ (s0 \[v] /\ \[v] < v1) ->
 (\[res] = 1 /\ s0 \[v] \/ \[res] = 0 /\ ~ s0 \[v]).
Proof. t name:(tree_set_not_and2). Qed.

Import ZList.List.ZIndexNotations.
Local Open Scope zlist_scope.

Ltac t ::= repeat standalone_solver_step.

Goal forall (b n : word) (bs : list Z),
 len bs = \[n] ->
 forall (i : word),
 \[b] < 2 ^ 8 -> i = /[0] -> List.repeatz \[b] \[i] ++ bs[\[i]:] = bs.
Proof. t. Qed.

Goal forall (l : list word) (lDone lTodo : list word),
 forall (x : word) (l' : list word),
 lTodo = x :: l' ->
 l = lDone ++ lTodo ->
 l = (lDone ++ [|x|]) ++ l'.
Proof. t. Qed.

End Tests.
