Require Import compiler.Set.
Require Export Coq.omega.Omega.

Class NameGen(var vars st: Type){varsSet: set vars var} := mkNameGen {
  genFresh: st -> (var * st);
  allFreshVars: st -> vars;
  genFresh_spec: forall (s s': st) (x: var),
    genFresh s = (x, s') ->
    x \in allFreshVars s /\
    ~ x \in allFreshVars s' /\
    subset (allFreshVars s') (allFreshVars s)
  (* could also say
     allFreshVars s' = diff (allFreshVars s) (singleton_set x)
     but that's unnecessarily strong and requires set equality *)
}.

Instance NatNameGen: NameGen nat (nat -> Prop) nat := {|
  genFresh := fun s => (s, S s);
  allFreshVars := fun s => fun x => s <= x
|}.
  intros. inversion H; subst. unfold subset. simpl. intuition omega.
Qed.


Definition multipick{T: Type}(E: Type){s: set T E}(pick: T -> E): nat -> T -> T :=
  fix rec(n: nat) := match n with
  | O => fun _ => empty_set
  | S m => fun names => 
             let newName := pick names in
             union (singleton_set newName) (rec m (diff names (singleton_set newName)))
  end.

Definition nth_pick{T: Type}(E: Type){s: set T E}(pick: T -> E): nat -> T -> E :=
  fix rec(n: nat) := match n with
  | O => fun names => pick names
  | S m => fun names =>
             let thrownAway := pick names in
             let newNames := diff names (singleton_set thrownAway) in
             rec m newNames
  end.

Definition infNameSupply{T: Type}(E: Type){s: set T E}(pick: T -> E)(names: T): Prop :=
  forall m n, nth_pick E pick m names <> nth_pick E pick n names.


Require Import compiler.Common.
Require compiler.ExprImp.
Require compiler.FlatImp.

Section FlattenExpr.

  Context {w: nat}. (* bit width *)
  Context {state: Type}.
  Context {var: Set}.
  Context {vars: Type}.
  Context {varset: set vars var}.
  Context {NGstate: Type}.
  Context {NG: NameGen var vars NGstate}.

  (* returns and var into which result is saved, and new (smaller) set of fresh vars *)
  Fixpoint flattenExpr(ngs: NGstate)(e: @ExprImp.expr w var): (@FlatImp.stmt w var * var * NGstate) :=
    match e with
    | ExprImp.ELit n =>
        let '(x, ngs') := genFresh ngs in
        (FlatImp.SLit x n, x, ngs')
    | ExprImp.EVar x =>
        (FlatImp.SSkip, x, ngs)
    | ExprImp.EOp op e1 e2 =>
        let '(s1, r1, ngs') := flattenExpr ngs e1 in
        let '(s2, r2, ngs'') := flattenExpr ngs' e2 in
        let '(x, ngs''') := genFresh ngs'' in
        (FlatImp.SSeq s1 (FlatImp.SSeq s2 (FlatImp.SOp x op r1 r2)), x, ngs''')
    end.

End FlattenExpr.


