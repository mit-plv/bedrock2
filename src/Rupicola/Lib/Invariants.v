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

Ltac fail_inference_obj_in_scalar var v t pred :=
  fail "
Invariant inference failure while try to generalize over" var "

- Variable" var "initially held" v "
- The generalized value we are substituting has type" t ", which is not a word.

This suggests that" v "is a pointer to an object, and that we should
generalize that object, not the pointer.

However, the current memory" pred "does not mention" v ".".

Ltac fail_inference_fresh_obj var t pred :=
  fail "
Invariant inference failure while try to generalize over" var "

- Variable" var "is not declared yet,
- The generalized value we are substituting has type" t ", which is not a word.

Rupicola does not know how to allocate fresh non-word objects.
Did you mean to use a different variable name?".

Ltac infer_word_instance locals :=
  lazymatch type of locals with
  | map.rep (map := ?ls) =>
    lazymatch type of ls with
    | map.map _ (word.rep (word := ?W)) => constr:(W)
    end
  end.

Ltac check_scalar W repl :=
  lazymatch type of repl with
  (* FIXME | byte => *)
  | word.rep => constr:(Some repl)
  | Z => constr:(Some (word.of_Z (word := W) repl))
  | nat => constr:(Some (word.of_Z (word := W) (Z.of_nat repl)))
  | bool => constr:(Some (word.b2w (word := W) repl))
  | _ => constr:(@None unit)
  end.

Ltac substitute_target var repl pred locals :=
  (** Replace the target of `var` with `repl` in `pred` and `locals`. **)
  let t := type of repl in
  let W := infer_word_instance locals in
  lazymatch locals with
  | context LOC [map.put ?m var ?v] =>
    lazymatch pred with
    | context PR [?P v _] => (* Ideally we'd match a full conjunct *)
      let pred := context PR [P v repl] in
      constr:((pred, locals))
    | _ =>
      lazymatch check_scalar W repl with
      | Some ?repl =>
        let locals := context LOC [map.put m var repl] in
        constr:((pred, locals))
      | _ => fail_inference_obj_in_scalar var v t pred
      end
    end
  | _ =>
    lazymatch check_scalar W repl with
    | Some ?repl =>
      constr:((pred, map.put locals var repl))
    | _ => fail_inference_fresh_obj var t pred
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

Ltac make_loop_predicate from_var from_arg to_var to_val vars args tr pred locals :=
  lazymatch substitute_target from_var from_arg pred locals with
  | (?pred, ?locals) =>
    lazymatch substitute_target to_var to_val pred locals with
    | (?pred, ?locals) => make_predicate vars args tr pred locals
    end
  end.

Ltac infer_loop_predicate'
     from_var to_var to_val
     argstype vars tr pred locals :=
  (** Like `make_predicate`, but with a binding for `idx` at the front. *)
  let idxtype := type of to_val in
  let val_pred :=
      constr:(fun (idx: idxtype) (args: argstype) =>
                ltac:(let f := make_loop_predicate
                                from_var idx to_var to_val
                                vars args tr pred locals in
                      exact f)) in
  eval cbv beta in val_pred.

Ltac infer_loop_predicate from_var to_var to_val :=
  _infer_predicate_from_context
    ltac:(infer_loop_predicate' from_var to_var to_val).

Ltac make_loop_predicate_continued idxvar idxarg vars args tr pred locals :=
  lazymatch substitute_target idxvar idxarg pred locals with
  | (?pred, ?locals) => make_predicate vars args tr pred locals
  end.

Ltac infer_loop_predicate_continued' argstype vars tr pred locals :=
  (** Like `make_predicate`, but with a binding for `idx` at the front. *)
  match argstype with
  | \<< ?idxtype, ?argstype \>> =>
    match vars with
    | ?idxvar :: ?vars =>
      let val_pred :=
          constr:(fun (idx: idxtype) (args: argstype) =>
                    ltac:(let f := make_loop_predicate_continued
                                    idxvar idx vars args tr pred locals in
                          exact f)) in
      eval cbv beta in val_pred
    end
  end.

Ltac infer_loop_predicate_continued :=
  _infer_predicate_from_context infer_loop_predicate_continued'.

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

    Check ltac:(let t := infer_loop_predicate_continued'
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
