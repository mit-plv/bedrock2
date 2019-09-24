Require Import coqutil.Macros.subst coqutil.Macros.unique.

Notation "' x <- a | y ; f" :=
  (match a with
   | x => f
   | _ => y
   end)
  (right associativity, at level 70, x pattern).

Notation "'bind_ex' x <- a ; f" :=
  (subst! a for a' in exists x, a' x /\ f)
  (only parsing, right associativity, at level 60, f at level 200).
Notation "'bind_ex_Some' x <- a ; f" :=
  (subst! a for a' in exists x, a' = Some x /\ f)
  (only parsing, right associativity, at level 60, f at level 200).
Notation "'bind_eq' x <- a ; f" :=
  (subst! a for a' in forall x, x = a' -> f)
  (only parsing, right associativity, at level 60, f at level 200).
