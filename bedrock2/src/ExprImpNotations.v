Require Import compiler.ExprImp.
Require Import riscv.util.BitWidths.
Require Import compiler.util.Common.
Require Import compiler.NameWithEq.
Require Import compiler.Op.

Require Import riscv.util.BitWidth32.

Open Scope Z_scope.

Instance ZName: NameWithEq := {| name := Z |}.

Definition var: Set := (@name ZName).

Definition Const(c: Z): expr := ELit (ZToWord _ c).
Coercion Const: Z >-> expr.

Definition Var(i: var): expr := EVar i.
Coercion Var: var >-> expr.


Notation "a + b" := (EOp OPlus a b) (at level 50, left associativity): ExprImpScope.
Notation "a - b" := (EOp OMinus a b) (at level 50, left associativity): ExprImpScope.
Notation "a * b" := (EOp OTimes a b) (at level 40, left associativity): ExprImpScope.
Notation "a == b" := (EOp OEq a b) (at level 70, no associativity): ExprImpScope.
Notation "a < b" := (EOp OLt a b) (at level 70, no associativity): ExprImpScope.
Notation "a 'and' b" := (EOp OAnd a b) (at level 81, left associativity): ExprImpScope.

Infix "<-*" := SLoad (no associativity, at level 90): ExprImpScope.
Infix "*<-" := SStore (no associativity, at level 90): ExprImpScope.
Infix "<--" := SSet (no associativity, at level 90): ExprImpScope.

Notation "'If' c 'then' a 'else' b 'fi'" := (SIf c a b)
  (at level 95, c at level 0): ExprImpScope.
Notation "'If' c 'then' a 'fi'" := (SIf c a SSkip)
  (at level 95, c at level 0): ExprImpScope.

Infix ";" := SSeq (right associativity, at level 92): ExprImpScope.
Notation "'while' c 'do' b 'done'" := (SWhile c b) (at level 95): ExprImpScope.

Open Scope ExprImpScope.

Delimit Scope ExprImpScope with src.
