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
