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
  fail 99 "
Invariant inference failure while try to generalize over" var "

- Variable" var "initially held" v "
- The generalized value we are substituting has type" t ", which is not a word.

This suggests that" v "is a pointer to an object, and that we should
generalize that object, not the pointer.

However, the current memory" pred "does not mention" v ".".

Ltac fail_inference_fresh_obj var t pred :=
  fail 99 "
Invariant inference failure while trying to generalize over" var "

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
  | word.rep => constr:(Some repl)
  | Z => constr:(Some (word.of_Z (word := W) repl))
  | nat => constr:(Some (word.of_Z (word := W) (Z.of_nat repl)))
  | bool => constr:(Some (word.b2w (word := W) repl))
  | Init.Byte.byte => constr:(Some (word.of_Z (word := W) (byte.unsigned repl)))
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
          _ _ ?tr ?mem ?locals (_ ?prog) ] =>
    lazymatch goal with
    | [ H: ?pred mem |- _ ] =>
      match is_rupicola_binding prog with
      | RupicolaBinding ?A ?vars =>
        k A vars tr pred locals
      | NotARupicolaBinding =>
        fail 0 prog "does not look like a let-binding"
      end
    | _ => fail 0 "No hypothesis mentions memory" mem
    end
  | [ |- ?g ] => fail 0 g "is not a Rupicola goal"
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
End Examples.
