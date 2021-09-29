Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.
Require Import Rupicola.Lib.Tactics.
Require Import Rupicola.Lib.Compiler.

Section Conditionals.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {memT: map.map word Byte.byte}.
  Context {localsT: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok memT}.
  Context {locals_ok : map.ok localsT}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Definition nlet_id {A} {v: A} : nlet_eq_k (fun _ => A) v := fun x _ => x.

  (* TODO add FAQ entry on nlet_eq here (plus no let t := t since that's not compiled yet) *)
  Lemma compile_if {tr mem locals functions} (c: bool) {A} (t f: A) :
    let v := if c then t else f in
    forall {P} {pred: P v -> predicate} {val_pred: A -> predicate}
      {k: nlet_eq_k P v} {k_impl t_impl f_impl}
      c_var vars,

      map.get locals c_var = Some (b2w c) ->

      (let val_pred := val_pred in
       c = true ->
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       t_impl
       <{ val_pred (nlet_eq vars t nlet_id) }>) ->
      (let val_pred := val_pred in
       c = false ->
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       f_impl
       <{ val_pred (nlet_eq vars f nlet_id) }>) ->
      (let v := v in
       forall tr mem locals,
         val_pred v tr mem locals ->
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.cond (expr.var c_var) t_impl f_impl)
        k_impl
      <{ pred (nlet_eq vars v k) }>.
  Proof.
    intros * Hc Ht Hf Hk.
    repeat straightline.
    split_if ltac:(repeat straightline'); subst_lets_in_goal.
    all: rewrite word.unsigned_of_Z_b2z; cbv [Z.b2z].
    all: destruct_one_match; try congruence; [ ]; intros.
    all: eapply compile_seq; eauto.
  Qed.

  Lemma compile_tail_if {tr mem locals functions} (c: bool) {A} (t f: A) :
    let v := if c then t else f in
    forall {pred: A -> predicate} {t_impl f_impl}
      c_var,

      map.get locals c_var = Some (b2w c) ->

      (c = true ->
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       t_impl
       <{ pred t }>) ->
      (c = false ->
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       f_impl
       <{ pred f }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.cond (expr.var c_var) t_impl f_impl
      <{ pred v }>.
  Proof.
    intros * Hc Ht Hf.
    repeat straightline'.
    split_if ltac:(repeat straightline'); subst_lets_in_goal.
    all: rewrite word.unsigned_of_Z_b2z; cbv [Z.b2z].
    all: destruct_one_match; try congruence; [ ]; intros.
    all: eauto.
  Qed.
End Conditionals.

(*|
Value predicate inference (no allocation)
-----------------------------------------

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

Ltac substitute_if_target var repl pred locals :=
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

Ltac substitute_if_targets vars repls pred locals :=
  lazymatch vars with
  | [] => constr:((pred, locals))
  | ?var :: [] =>
    substitute_if_target var repls pred locals
  | ?var :: ?vars  =>
    match substitute_if_target var (P2.fst repls) pred locals with
    | (?pred, ?locals) => substitute_if_targets vars (P2.snd repls) pred locals
    end
  end.

(* This replaces apply_tuple_references.  FIXME move *)
Ltac make_uncurried_application args_tuple curried_fn :=
  lazymatch type of args_tuple with
  | P2.prod _ _ =>
    let fn := constr:(curried_fn (P2.fst args_tuple)) in
    let fn := make_uncurried_application (P2.snd args_tuple) fn in
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

Ltac infer_val_predicate :=
  lazymatch goal with
  | [ |- WeakestPrecondition.cmd
          _ _ ?tr ?mem ?locals
          (_ (nlet_eq ?vars ?v _)) ] =>
    lazymatch goal with
    | [ H: ?pred mem |- _ ] =>
      let argtype := type of v in
      let val_pred := constr:(fun (args_tuple: argtype) =>
                               ltac:(match substitute_if_targets vars args_tuple pred locals with
                                     | (?pred, ?locals) =>
                                       let f := constr:(fun tr' mem' locals' =>
                                                         tr' = tr /\
                                                         locals' = locals /\
                                                         pred mem') in
                                       exact f
                                     end)) in
      eval cbv beta in val_pred
    end
  end.

Ltac compile_if :=
  lazymatch goal with
  | [ |- WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ (if _ then _ else _) _)) ] =>
    let vp := infer_val_predicate in
    simple eapply compile_if with (val_pred := vp)
  end.

(* FIXME add hint *)
