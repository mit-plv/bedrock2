(* Notations to display a list of sepapp predicates as a bullet point list *)

From Coq Require Import ZArith.
Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.SepLib.
Require Import bedrock2.sepapp.

Declare Scope sepapp_bullets_scope.
(* No scope delimiting key so that closing the scope deactivates the notation instead
   of still printing it, but with %scope_key *)

Notation "<{ + x + .. + y + z }>" :=
  (sepapps (cons (mk_sized_predicate x _) ..
              (cons (mk_sized_predicate y _) (cons (mk_sized_predicate z _) nil)) ..))
  (at level 0, x at level 39, y at level 39, z at level 39,
   only printing,
   format "<{ '[v '  +  '[' x ']' '//' +  ..  '//' +  '[' y ']' '//' +  '[' z ']'  ']' }>")
  : sepapp_bullets_scope.

Notation "<{ + x + .. + y + z }>" :=
  (sepapps (cons (mk_inferred_size_predicate x) ..
              (cons (mk_inferred_size_predicate y) (cons (mk_inferred_size_predicate z) nil)) ..))
  (at level 0, x at level 39, y at level 39, z at level 39,
   only parsing)
  : sepapp_bullets_scope.

Require Import bedrock2.SepBulletPoints.

Section NotationTests.
  Context {width : Z} {BW : Bitwidth.Bitwidth width}
          {word : Interface.word.word width}
          {mem : map.map word Init.Byte.byte}.

  (* local, just for testing, real definition is elsewhere *)
  Context (scalar: word -> word -> mem -> Prop).

  Local Hint Extern 1 (SepLib.PredicateSize (scalar ?v)) => exact 4%Z : typeclass_instances.

  Local Open Scope sep_bullets_scope.
  Local Open Scope sepapp_bullets_scope.

  Goal Some (fun (a v: word) =>
               <{ + (scalar v) + (scalar v) }> a) = None.
  Abort.

  Goal (forall (addr: word) (v: word) (current_mem: mem),
          <{ + scalar v + scalar v }> addr current_mem).
  Proof.
    intros.
    match goal with |- ?G => enough G as M end.
  Abort.

  Context (a b c d e f g h: word) (frobnicate: word -> word -> word) (v: word).

  Let bigclause := <{
     + scalar v
     + scalar v
     + scalar (frobnicate (frobnicate (frobnicate v (frobnicate v v)) (frobnicate
          (frobnicate v (frobnicate v v)) (frobnicate v (frobnicate v v)))) (frobnicate v v))
     + scalar v
     + scalar v
     + scalar v
     + scalar (frobnicate (frobnicate (frobnicate v (frobnicate v v)) (frobnicate
          (frobnicate v (frobnicate v v)) (frobnicate v (frobnicate v v)))) (frobnicate v v))
  }> (frobnicate (frobnicate (frobnicate v (frobnicate v v)) (frobnicate
          (frobnicate v (frobnicate v v)) (frobnicate v (frobnicate v v)))) (frobnicate v v)).

  Goal forall m, bigclause m.
  Proof.
    intros. subst bigclause. match goal with |- ?G => enough G end.
  Abort.

  Goal forall m, <{ * bigclause * bigclause }> m.
  Proof.
    intros. subst bigclause. match goal with |- ?G => enough G end.
  Abort.

End NotationTests.
