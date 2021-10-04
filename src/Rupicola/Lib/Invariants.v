Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.
Require Import Rupicola.Lib.Tactics.
Require Import Rupicola.Lib.Compiler.

(*|
Predicate inference (no allocation)
-----------------------------------

Mutating a heap object:
  >>> locals := [["p0" ← p0]] :: …
  >>> pred := P p0 v0 ⋆ Q p1 v1 ⋆ R
  >>> vars := ["p0"]
  val_pred := fun v0' l m => l = locals /\ P p0 v0' ⋆ Q p1 v1 ⋆ R

Mutating a local binding:
  >>> locals := [["x" ← x]] :: …
  >>> pred := P p0 v0 ⋆ Q p1 v1 ⋆ R
  >>> vars := ["x"]
  val_pred := fun x' l m => l = [["x" <- x']] :: … /\ P p0 v0 ⋆ Q p1 v1 ⋆ R

Creating a local binding:
  >>> locals := [["x" ← x]] :: …
  >>> pred := P p0 v0 ⋆ Q p1 v1 ⋆ R
  >>> vars := ["y"]
  val_pred := fun y l m => l = [["y" <- y]] :: locals /\ P p0 v0 ⋆ Q p1 v1 ⋆ R

Handling multiple bindings:
  >>> locals := [["p0" ← p0]] :: [["x" ← x]] …
  >>> pred := P p0 v0 ⋆ Q p1 v1 ⋆ R
  >>> vars := ["p0", "x"]
  val_pred := fun '\< v0', x' \> l m => l = [["p0" ← p0]] :: [["x" ← x']] … /\ P p0 v0' ⋆ Q p1 v1 ⋆ R

Not supported yet: using a conditional to assign a pointer to another one.
|*)

(* FIXME loops should work this way too for the value part (not for the index
     part) instead of generalizing all instances of the value. *)

Ltac substitute_target var repl pred locals :=
  (** Replace the target of `var` with `repl` in `pred` and `locals`. **)
  lazymatch locals with
  | context LOC [map.put ?m var ?v] =>
    lazymatch pred with
    | context PR [sep (?P v _) ?R] =>
      let pred := context PR [sep (P v repl) R] in
      constr:((pred, locals))
    | _ =>
      let locals := context LOC [map.put m var repl] in
      constr:((pred, locals))
    end
  | _ =>
    constr:((pred, map.put locals var repl))
  end.

Ltac substitute_targets vars repls pred locals :=
  (** Replace targets of `vars` in `pred` and `locals` with `repls`. **)
  lazymatch vars with
  | [] => constr:((pred, locals))
  | ?var :: [] =>
    substitute_target var repls pred locals
  | ?var :: ?vars  =>
    match substitute_target var (P2.car repls) pred locals with
    | (?pred, ?locals) => substitute_targets vars (P2.cdr repls) pred locals
    end
  | _ => fail "substitute_targets:" vars "should be a list"
  end.

(* This replaces apply_tuple_references.  FIXME move *)
Ltac make_uncurried_application args_tuple curried_fn :=
  lazymatch type of args_tuple with
  | P2.prod _ _ =>
    let fn := constr:(curried_fn (P2.car args_tuple)) in
    let fn := make_uncurried_application (P2.cdr args_tuple) fn in
    fn
  | _ =>
    constr:(curried_fn args_tuple)
  end.

Ltac make_uncurried_argtype fn_type :=
  lazymatch fn_type with
  | ?A -> ?B -> ?C =>
    let bc := make_uncurried_argtype (B -> C) in
    constr:(P2.prod A bc)
  | ?A -> ?B => constr:(A)
  | ?A => fail "Not a function"
  end.

Ltac uncurry fn :=
  let arrows := type of fn in
  let argtype := make_uncurried_argtype arrows in
  constr:(fun args_tuple: argtype =>
            ltac:(let body := make_uncurried_application args_tuple fn in
                  exact body)).

Ltac infer_val_predicate'' vars args tr pred locals :=
  match substitute_targets vars args pred locals with
  | (?pred, ?locals) =>
    constr:(fun tr' mem' locals' =>
              tr' = tr /\
              locals' = locals /\
              pred mem')
  end.

Ltac infer_val_predicate' argstype vars tr pred locals :=
  let val_pred :=
      constr:(fun (args: argstype) =>
                ltac:(let f := infer_val_predicate'' vars args tr pred locals in
                      exact f)) in
  eval cbv beta in val_pred.

Ltac infer_val_predicate :=
  lazymatch goal with
  | [ |- WeakestPrecondition.cmd
          _ _ ?tr ?mem ?locals
          (_ (nlet_eq ?vars ?v _)) ] =>
    lazymatch goal with
    | [ H: ?pred mem |- _ ] =>
      let argstype := type of v in
      infer_val_predicate' argstype vars tr pred locals
    end
  end.

Section Examples.
  Context {width: Z} {BW: Bitwidth width}.
  Context {word: word.word width} {word_ok : word.ok word}.
  Context {locals: map.map string word} {locals_ok : map.ok locals}.
  Context {mem: map.map word byte} {mem_ok : map.ok mem}.

  Section Substitution.
    Context {A: Type} (ptr: word) (a a': A) (R: mem -> Prop)
            (rp: word -> A -> mem -> Prop).

    (* Mutating a heap object *)
    Check ltac:(let r := substitute_target
                          "ptr" a'
                          (rp ptr a ⋆ R)
                          (map.put (map := locals) map.empty "ptr" ptr) in
                exact r).

    Context (v v': word) (pred: mem -> Prop).

    (* Mutating a local variable *)
    Check ltac:(let r := substitute_target
                          "v" v'
                          pred (map.put (map := locals) map.empty "v" v) in
                exact r).

    Context (x y: word).

    (* Creating a local variable *)
    Check ltac:(let r := substitute_target
                          "y" y
                          pred (map.put (map := locals) map.empty "x" x) in
                exact r).

    (* All three types of changes at once *)
    Check ltac:(let r := substitute_targets
                          ["ptr"; "v"; "y"]
                          (\< a', v', y \>)
                          (rp ptr a ⋆ R)
                          (map.put (map := locals)
                                   (map.put map.empty "v" v) "ptr" ptr) in
                exact r).
  End Substitution.

  Section ValInference.
    Context (tr: Semantics.trace) {A} (ptr v v' y: word) (a a': A) (R: mem -> Prop)
            (rp: word -> A -> mem -> Prop).

    Check ltac:(let t := infer_val_predicate'
                          (\<< A , word , word \>>)
                          ["ptr"; "v"; "y"]
                          tr
                          (rp ptr a ⋆ R)
                          (map.put (map := locals)
                                   (map.put map.empty "v" v) "ptr" ptr)
                in exact t).
  End ValInference.
End Examples.
