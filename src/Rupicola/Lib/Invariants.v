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
    | context PR [?P v _] => (* Ideally we'd match a full conjunct *)
      let pred := context PR [P v repl] in
      constr:((pred, locals))
    | _ =>
      lazymatch type of repl with
      | word.rep =>
        let locals := context LOC [map.put m var repl] in
        constr:((pred, locals))
      | ?t =>
        fail "Invariant inference failure.
Looking to replace target of" var "with" repl ".
Variable" var "contains" v ".
Since" repl "is of type" t "(not word)," v "should be a pointer.
However, the current memory" pred "does not mention" v
      end
    end
  | _ =>
    lazymatch type of repl with
    | word.rep =>
      constr:((pred, map.put locals var repl))
    | ?t =>
      fail "Invariant inference failure.
Looking to bind" var "to" repl ".
Variable" var "is not declared yet,
but" repl "is of type" t "(not word)."
           "Rupicola does not know how to allocate fresh (non-word) objects.
Did you mean to use a different variable name?"
      end
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

Ltac make_predicate vars args tr pred locals :=
  lazymatch substitute_targets vars args pred locals with
  | (?pred, ?locals) =>
    constr:(fun tr' mem' locals' =>
              tr' = tr /\ locals' = locals /\ pred mem')
  end.

Ltac _infer_predicate_from_context k :=
  lazymatch goal with
  | [ |- WeakestPrecondition.cmd
          _ _ ?tr ?mem ?locals (_ (nlet_eq ?vars ?v _)) ] =>
    lazymatch goal with
    | [ H: ?pred mem |- _ ] =>
      let argstype := type of v in
      k argstype vars tr pred locals
    end
  end.

Ltac infer_val_predicate' argstype vars tr pred locals :=
  let val_pred :=
      constr:(fun (args: argstype) =>
                ltac:(let f := make_predicate vars args tr pred locals in
                      exact f)) in
  eval cbv beta in val_pred.

Ltac infer_val_predicate :=
  _infer_predicate_from_context infer_val_predicate'.

Ltac make_loop_predicate idxvar idxarg vars args tr pred locals :=
  lazymatch substitute_target idxvar idxarg pred locals with
  | (?pred, ?locals) => make_predicate vars args tr pred locals
  end.

Ltac infer_loop_predicate' argstype vars tr pred locals :=
  (* Like make_predicate, but with one distinguished binding for `idx` at
     the front. *)
  match argstype with
  | \<< ?idxtype, ?argstype \>> =>
    match vars with
    | ?idxvar :: ?vars =>
      let val_pred :=
          constr:(fun (idx: idxtype) (args: argstype) =>
                    ltac:(let f := make_loop_predicate
                                    idxvar idx vars args tr pred locals in
                          exact f)) in
      eval cbv beta in val_pred
    end
  end.

Ltac infer_loop_predicate :=
  _infer_predicate_from_context infer_loop_predicate'.

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

  Section LoopInference.
    Context (tr: Semantics.trace) {A} (ptr v v' from: word) (a a': A) (R: mem -> Prop)
            (rp: word -> A -> mem -> Prop).

    Check ltac:(let t := infer_loop_predicate'
                          (\<< word, A, word \>>)
                          ["from"; "ptr"; "v"]
                          tr
                          (rp ptr a ⋆ R)
                          (map.put (map := locals)
                                   (map.put (map.put map.empty "v" v)
                                            "from" from) "ptr" ptr)
                in exact t).
  End LoopInference.
End Examples.
