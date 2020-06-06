Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.
Require Export Rupicola.Lib.Gensym.
Require Import Rupicola.Lib.Tactics.

Section with_semantics.
  Context {semantics : Semantics.parameters}.

  Lemma compile_skip :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R functions T (pred: T -> _ -> Prop) head,
      sep (pred head) R mem ->
      (find cmd.skip
       implementing (pred head)
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    red; red; eauto.
  Qed.

  Lemma compile_constant :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R functions T (pred: T -> _ -> Prop) z k k_impl,
    forall var,
      let v := word.of_Z z in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       with-locals (map.put locals var head)
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.literal z)) k_impl)
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    eassumption.
  Qed.

  Lemma compile_bool :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R functions T (pred: T -> _ -> Prop) (b : bool) k k_impl,
    forall var,
      let v := b in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       with-locals (map.put locals var (word.of_Z (Z.b2z b)))
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.literal (Z.b2z b))) k_impl)
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    eassumption.
  Qed.

  (* FIXME add let pattern to other lemmas *)
  Lemma compile_add :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R (* R' *) functions T (pred: T -> _ -> Prop) x x_var y y_var k k_impl,
    forall var,
      (* WeakestPrecondition.dexpr mem locals (expr.var x_var) x -> *)
      (* WeakestPrecondition.dexpr mem locals (expr.var y_var) y -> *)
      map.get locals x_var = Some x ->
      map.get locals y_var = Some y ->
      let v := word.add x y in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       with-locals (map.put locals var head)
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.op bopname.add (expr.var x_var) (expr.var y_var)))
                     k_impl)
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    eexists; split.
    { repeat straightline.
        exists x; split; try eassumption.
        repeat straightline.
        exists y; split; try eassumption.
        reflexivity. }
    red.
    eassumption.
  Qed.
End with_semantics.

Ltac setup_step :=
  match goal with
  | _ => progress (cbv zeta; unfold program_logic_goal_for)
  | [  |- forall _, _ ] => intros
  | [  |- exists _, _ ] => eexists
  | [  |- _ /\ _ ] => split
  | [  |- context[postcondition_for _ _ _] ] =>
    set (postcondition_for _ _ _)
  | _ => reflexivity
  | _ => cbn
  end.

Ltac term_head x :=
  match x with
  | ?f _ => term_head f
  | _ => x
  end.

Ltac setup :=
  repeat setup_step;
  repeat match goal with
         | [ H := _ |- _ ] => subst H
         end;
  match goal with
  | [  |- context[postcondition_for (?pred ?spec) ?R ?tr] ] =>
    change (fun x y _ => postcondition_for (pred spec) R tr x y [])
      with (postcondition_norets (pred spec) R tr);
    let hd := term_head spec in
    unfold hd
  end;
  cleanup.

Ltac lookup_variable m val :=
  lazymatch m with
  | map.put _ ?k val => constr:(k)
  | map.put ?m' _ _ => lookup_variable m' val
  end.

Ltac solve_map_get_goal :=
  lazymatch goal with
  | [  |- map.get ?m _ = Some ?val ] =>
    let var := lookup_variable m val in
    instantiate (1 := var);
    rewrite ?map.get_put_diff by congruence;
    apply map.get_put_same
  end.

Create HintDb compiler.

Ltac compile_basics :=
  gen_sym_inc;
  let name := gen_sym_fetch "v" in
  first [simple eapply compile_constant with (var := name) |
         simple eapply compile_bool with (var := name) |
         simple eapply compile_add with (var := name) ].

Ltac compile_custom := fail.

Ltac compile_step :=
  lazymatch goal with
  | [  |- let _ := _ in _ ] => intros
  | [  |- WeakestPrecondition.cmd _ _ _ _ _ _ ] =>
    try clear_old_seps;
    first [compile_custom | compile_basics ]
  | [  |- sep _ _ _ ] =>
    autounfold with compiler in *;
    cbn [fst snd] in *;
    ecancel_assumption
  | [  |- map.get _ _ = Some _ ] => solve_map_get_goal
  | _ => eauto with compiler
  end.

(* only apply compile_step when repeat_compile_step solves all the side
     conditions but one *)
Ltac safe_compile_step :=
  compile_step; [ solve [repeat compile_step] .. | ].

Ltac compile_done := simple eapply compile_skip; repeat compile_step.

Ltac compile :=
  setup; repeat compile_step; compile_done.
