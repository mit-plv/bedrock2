(* Notations to display a list of separation logic predicates as a bullet point list *)

Require Import coqutil.Map.Interface coqutil.Word.Interface.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation.

Declare Scope sep_list_scope.
Delimit Scope sep_list_scope with sep_list.

Notation "* x * y * .. * z" :=
  (@cons (@map.rep _ _ _ -> Prop) x
    (@cons (@map.rep _ _ _ -> Prop) y
      .. (@cons (@map.rep _ _ _ -> Prop) z nil) .. ))
  (at level 39, x at level 39, y at level 39, z at level 39,
   (* starting with a space to make sure we never create an opening comment *)
   format " '[v' *  x  '//' *  y  '//' *  ..  '//' *  z  ']'")
  : sep_list_scope.

Notation "* x" :=
  (@cons (@map.rep _ _ _ -> Prop) x nil)
  (at level 39, x at level 39,
   (* starting with a space to make sure we never create an opening comment *)
   format " '[v' *  x ']'")
  : sep_list_scope.

Declare Scope seps_impl_scope.
Open Scope seps_impl_scope.

Notation "m 'satisfies' <{ l }>" := (seps l%sep_list m)
  (at level 10,
   format "'[v' m  'satisfies'  <{ '//'  l '//' }> ']'")
  : seps_impl_scope.

Notation "<{ l1 }> ==> <{ l2 }>" := (impl1 (seps l1%sep_list) (seps l2%sep_list))
  (at level 10,
   format "'[v' <{ l1 '//' }>  ==>  <{ '//'   l2 '//' }> ']'")
  : seps_impl_scope.

Notation "<{ l1 }> <==> <{ l2 }>" := (iff1 (seps l1%sep_list) (seps l2%sep_list))
  (at level 10,
   format "'[v' <{ l1 '//' }>  <==>  <{ '//'   l2 '//' }> ']'")
  : seps_impl_scope.


Section NotationTests.
  Context {width : BinInt.Z} {word : Word.Interface.word width}
          {mem : map.map word Byte.byte}.

  (* local, just for testing, real definition is elsewhere *)
  Let at_addr(addr: word)(clause: word -> mem -> Prop): mem -> Prop := clause addr.
  Local Notation "addr |-> clause" := (at_addr addr clause)
    (at level 25, format "addr  |->  '[' clause ']'").

  Context (scalar: word -> word -> mem -> Prop).

  Goal Some (fun (a b: word) (v: word) =>
               seps ( * (a |-> scalar v) * (b |-> scalar v) * (emp True) )%sep_list) = None.
  Abort.

  Goal (forall (a b: word) (v: word) (current_mem: mem),
          seps ( * a |-> scalar v * b |-> scalar v * emp True )%sep_list current_mem).
  Proof. intros. (*
  Note how `satisfies` does not increase the indentation of the `*` bullet points,
  each bullet point is indented by just two spaces:

  current_mem satisfies <{
    * a |-> scalar v
    * b |-> scalar v
    * emp True
  }>
  *)
  match goal with |- ?G => enough G as M end. Abort.

  Context (a b c d e f g h: word) (frobnicate: word -> word -> word) (v: word).

  Let manyseps := (
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
  )%sep_list.

  Goal forall (a b c d e f g h: word) (frobnicate: word -> word -> word) (v: word) (m: mem),
     m satisfies <{ manyseps }>.
  Proof.
    intros. subst manyseps. match goal with |- ?G => enough G end.
  Abort.

  Goal forall (a b: word) (v: word),
    <{ * a |-> scalar v
       * b |-> scalar v
       * emp True
    }> ==> <{
       * b |-> scalar v
       * a |-> scalar v
    }>.
  Proof. intros. match goal with |- ?G => enough G end. Abort.

  Goal forall (a b: word) (v: word),
    <{ manyseps }> ==> <{
       * b |-> scalar v
       * a |-> scalar v
    }>.
  Proof. intros. subst manyseps. match goal with |- ?G => enough G end. Abort.

  Goal forall (a b: word) (v: word),
    <{ manyseps }> <==> <{
       * b |-> scalar v
       * a |-> scalar v
    }>.
  Proof. intros. subst manyseps. match goal with |- ?G => enough G end. Abort.

End NotationTests.
