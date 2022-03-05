Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import bedrock2.Map.SeparationLogic.


Ltac get_type x :=
  let tx := type of x in
  let __ := match constr:(Set) with
            | _ => tryif has_evar tx
                   then fail 1 "type of" x "should be fully determined, but is" tx
                   else idtac
            end in
  tx.

(* might insert a coercion, or use subsumption to turn `nat: Set` into `nat: Type` *)
Ltac has_type x T :=
  tryif (let _ := constr:(x: T) in idtac) then idtac
  else fail 0 x "does not have type" T.

Ltac binop cl x y :=
  (* At the moment, we require both the type of x and y to be fully determined
     (no evars), but later we might be more adventurous and allow the type of
     one operand to determine the type of the other.
     But then we'll have to reconsider what to do about coercions. *)
  let tx := get_type x in
  let ty := get_type y in
  (* unify instead of constr_eq because has_type also uses unification *)
  tryif unify tx ty then
    (* beta gets rid of cast and of eta expansion in case of prod used for Set *)
    let r := eval cbv beta in ((_: cl tx) x y) in exact r
  else
    tryif has_type x ty then
      tryif has_type y tx then
        fail "bidirectional coercion between" tx "and" ty
             "makes" cl "of" x "and" y "ambiguous"
      else
        (* will coerce type of x to ty *)
        let r := eval cbv beta in ((_: cl ty) x y) in exact r
    else
      tryif has_type y tx then
        (* will coerce type of y to tx *)
        let r := eval cbv beta in ((_: cl tx) x y) in exact r
      else
        fail "operands" x "and" y "have incompatible types" tx "and" ty.


Declare Scope oo_scope.
Local Open Scope oo_scope.

Definition Multiplication(T: Type) := T -> T -> T.
Existing Class Multiplication.
#[export] Hint Mode Multiplication + : typeclass_instances.

#[export] Hint Extern 1 (Multiplication nat) => exact Nat.mul : typeclass_instances.
#[export] Hint Extern 1 (Multiplication N) => exact N.mul : typeclass_instances.
#[export] Hint Extern 1 (Multiplication Z) => exact Z.mul : typeclass_instances.
#[export] Hint Extern 1 (Multiplication Set) => exact prod : typeclass_instances.
#[export] Hint Extern 1 (Multiplication Prop) => exact prod : typeclass_instances.
#[export] Hint Extern 1 (Multiplication Type) => exact prod : typeclass_instances.
#[export] Hint Extern 1 (Multiplication (@word.rep ?wi ?wo)) =>
  exact (@word.mul wi wo) : typeclass_instances.
#[export] Hint Extern 1 (Multiplication (@map.rep ?K ?V ?M -> Prop)) =>
  exact (@sep K V M) : typeclass_instances.

Notation "x * y" := (ltac:(binop Multiplication x y)) (only parsing) : oo_scope.
Notation "x * y" := (Nat.mul x y) (only printing): oo_scope.
Notation "x * y" := (N.mul x y) (only printing): oo_scope.
Notation "x * y" := (Z.mul x y) (only printing): oo_scope.
Notation "x * y" := (prod x y) (only printing): oo_scope.
Notation "x * y" := (word.mul x y) (only printing): oo_scope.
Notation "x * y" := (sep x y) (only printing): oo_scope.


Definition Addition(T: Type) := T -> T -> T.
Existing Class Addition.
#[export] Hint Mode Addition + : typeclass_instances.

#[export] Hint Extern 1 (Addition nat) => exact Nat.add : typeclass_instances.
#[export] Hint Extern 1 (Addition N) => exact N.add : typeclass_instances.
#[export] Hint Extern 1 (Addition Z) => exact Z.add : typeclass_instances.
#[export] Hint Extern 1 (Addition (@word.rep ?wi ?wo)) =>
  exact (@word.add wi wo) : typeclass_instances.

Notation "x + y" := (ltac:(binop Addition x y)) (only parsing) : oo_scope.
Notation "x + y" := (Nat.add x y) (only printing): oo_scope.
Notation "x + y" := (N.add x y) (only printing): oo_scope.
Notation "x + y" := (Z.add x y) (only printing): oo_scope.
Notation "x + y" := (word.add x y) (only printing): oo_scope.

(* Tests:

Goal False.
  has_type 4%nat nat.
  let T := open_constr:(_: Type) in has_type 3 T; idtac T.
  Fail has_type 4%nat unit.
  has_type nat Set.
  has_type nat Type.
  has_type (fun (x: Set) => (x * x)%type) (Set -> Set).
  has_type (fun (x: Type) => (x * x)%type) (Set -> Set).
  has_type (fun (x: Type) => (x * x)%type) (Set -> Type).
  Fail has_type (fun (x: Set) => (x * x)%type) (Type -> Type).
  Fail has_type (fun (x: Set) => (x * x)%type) (Type -> Set).
Abort.

Fail Check (fun a b => a * b).
Fail Check (fun a (b: Z) => a * b).
Fail Check (fun (a: nat) b => a * b).
Check (fun (a b: nat) => a * b).
Fail Check (fun (a: nat) (b: Z) => a * b).
Fail Check (tt * 2).
Fail Check (tt * tt).
Check (nat * Z)%type.
Check (nat * Z).
Check (nat * Set).
Check (nat * Type).

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Check (fun (P Q: mem -> Prop) => P * Q).

  Local Coercion Z.of_nat : nat >-> Z.
  Local Coercion word.unsigned : word.rep >-> Z.

(*  Local Set Printing Coercions.*)

  Check (fun (x: word) => x: Z).
  Check (fun (x: nat) => x: Z).

  (*
  New coercion path [word_to_nat; Z.of_nat] : word.rep >-> Z is ambiguous with existing
  [word.unsigned] : word.rep >-> Z. [ambiguous-paths,typechecker]
  Coercion word_to_nat(w: word): nat := Z.to_nat (word.unsigned w).
  *)

  Check (fun (a: nat) (b: Z) => a * b).
  Check (fun (a: Z) (b: nat) => a * b).
  Check (fun (a: Z) (b: nat) (c: Z) => a * b * c).
  Check (fun (a b c: Z) => a * b * c).
  Check (fun (a: nat) (b: nat) (c: Z) => a * b * c).

  Fail Check (fun (x: word) (y: mem -> Prop) => x * y).

  Check (fun (P Q R: mem -> Prop) m => (P * Q * R) m).
End WithParameters.
*)
