(* Notations to display a list of separation logic predicates as a bullet point list *)

Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation.

Declare Scope sep_bullets_scope.
(* No scope delimiting key so that closing the scope deactivates the notation instead
   of still printing it, but with %scope_key *)

Notation "<{ * x * .. * y * z }>" :=
  (sep x .. (sep y z) ..)
  (at level 0, x at level 39, y at level 39, z at level 39,
   format "<{ '[v '  *  '[' x ']' '//' *  ..  '//' *  '[' y ']' '//' *  '[' z ']'  ']' }>")
  : sep_bullets_scope.

Section NotationTests.
  Context {width : BinInt.Z} {word : Word.Interface.word width}
          {mem : map.map word Byte.byte}.

  (* local, just for testing, real definition is elsewhere *)
  Let at_addr(addr: word)(clause: word -> mem -> Prop): mem -> Prop := clause addr.
  Local Notation "addr |-> clause" := (at_addr addr clause)
    (at level 25, format "'[' addr  |->  clause ']'").

  Context (scalar: word -> word -> mem -> Prop).

  Local Open Scope sep_bullets_scope.

  Goal Some (fun (a b: word) (v: word) =>
               <{ * (a |-> scalar v) * (b |-> scalar v) }>) = None.
  Abort.

  Goal (forall (a b: word) (v: word) (current_mem: mem),
          <{ * (a |-> scalar v) * (b |-> scalar v) }> current_mem).
  Proof.
    intros.
    match goal with |- ?G => enough G as M end. Abort.

  Context (a b c d e f g h: word) (frobnicate: word -> word -> word) (v: word).

  Let manyseps := <{
     * a |-> scalar v * b |-> scalar v * emp True * c |-> scalar v
     * d |->  scalar v
     * e |-> scalar (frobnicate (frobnicate (frobnicate v (frobnicate v v)) (frobnicate
          (frobnicate v (frobnicate v v)) (frobnicate v (frobnicate v v)))) (frobnicate v v))
     * f |-> scalar v
     * (frobnicate (frobnicate (frobnicate v (frobnicate v v)) (frobnicate
          (frobnicate v (frobnicate v v)) (frobnicate v (frobnicate v v)))) (frobnicate v v)) |->
       scalar v
     * h |-> (scalar v) * emp True
     * (frobnicate (frobnicate (frobnicate v (frobnicate v v)) (frobnicate
          (frobnicate v (frobnicate v v)) (frobnicate v (frobnicate v v)))) (frobnicate v v)) |->
       scalar (frobnicate (frobnicate (frobnicate v (frobnicate v v)) (frobnicate
          (frobnicate v (frobnicate v v)) (frobnicate v (frobnicate v v)))) (frobnicate v v))
  }>.

  Goal forall m, manyseps m.
  Proof.
    intros. subst manyseps. match goal with |- ?G => enough G end.
  Abort.

  (* TODO reactivate notations for impl1/iff1, which should use seps *)

  Goal forall (a b: word) (v: word),
    impl1 <{ * a |-> scalar v
       * b |-> scalar v
       * emp True
    }> <{
       * b |-> scalar v
       * a |-> scalar v
    }>.
  Proof. intros. match goal with |- ?G => enough G end. Abort.

  Goal forall (a b: word) (v: word),
    impl1 manyseps <{
       * b |-> scalar v
       * a |-> scalar v
    }>.
  Proof. intros. subst manyseps. match goal with |- ?G => enough G end. Abort.

  Goal forall (a b: word) (v: word),
    iff1 manyseps <{
       * b |-> scalar v
       * a |-> scalar v
    }>.
  Proof. intros. subst manyseps. match goal with |- ?G => enough G end. Abort.

End NotationTests.
