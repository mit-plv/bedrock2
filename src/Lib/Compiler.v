Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.
Require Export Rupicola.Lib.Gensym.
Require Import Rupicola.Lib.Tactics.

Section with_semantics.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok _}.

  Lemma compile_skip :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : _ -> Prop)
           tr R functions T (pred: T -> _ -> Prop) head,
      locals_ok locals ->
      sep (pred head) R mem ->
      (find cmd.skip
       implementing (pred head)
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    red; ssplit; try red; eauto.
  Qed.

  Lemma compile_constant :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr R functions T (pred: T -> _ -> Prop) z k k_impl,
    forall var,
      let v := word.of_Z z in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-locals-post locals_ok
       with-locals (map.put locals var head)
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.literal z)) k_impl)
       implementing (pred (dlet head k))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    eassumption.
  Qed.

  Lemma compile_nat_constant :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr R functions T (pred: T -> _ -> Prop)
           (n : nat) (zn : Z) k k_impl,
    forall var,
      zn = Z.of_nat n ->
      let v := n in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-locals-post locals_ok
       with-locals (map.put locals var (word.of_Z zn))
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.literal zn)) k_impl)
       implementing (pred (dlet head k))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    eassumption.
  Qed.

  Lemma compile_false :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr R functions T (pred: T -> _ -> Prop) k k_impl,
    forall var,
      let v := false in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-locals-post locals_ok
       with-locals (map.put locals var (word.of_Z (Z.b2z head)))
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.literal 0)) k_impl)
       implementing (pred (dlet head k))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    eassumption.
  Qed.

  Lemma compile_true :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr R functions T (pred: T -> _ -> Prop) k k_impl,
    forall var,
      let v := true in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-locals-post locals_ok
       with-locals (map.put locals var (word.of_Z (Z.b2z head)))
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.literal 1)) k_impl)
       implementing (pred (dlet head k))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    eassumption.
  Qed.

  (* TODO : move? *)
  Lemma word_unsigned_of_Z_b2z b :
    word.unsigned (word.of_Z (Z.b2z b)) = Z.b2z b.
  Proof.
    destruct b; cbn [Z.b2z];
      auto using word.unsigned_of_Z_0, word.unsigned_of_Z_1.
  Qed.
  Lemma Z_lxor_xorb a b : Z.lxor (Z.b2z a) (Z.b2z b) = Z.b2z (xorb a b).
  Proof. destruct a, b; reflexivity. Qed.

  Lemma compile_xorb :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr R functions T (pred: T -> _ -> Prop)
           x x_var y y_var k k_impl,
    forall var,
      map.get locals x_var = Some (word.of_Z (Z.b2z x)) ->
      map.get locals y_var = Some (word.of_Z (Z.b2z y)) ->
      let v := xorb x y in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-locals-post locals_ok
       with-locals (map.put locals var (word.of_Z (Z.b2z head)))
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.op bopname.xor (expr.var x_var) (expr.var y_var)))
                     k_impl)
       implementing (pred (dlet head k))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    eexists; split.
    { repeat straightline.
      eexists; split; [ eassumption | ].
      repeat straightline.
      eexists; split; [ eassumption | ].
      reflexivity. }
    red.
    match goal with
      H : context [map.put locals var ?v1]
      |- context [map.put locals var ?v2] =>
      replace v2 with v1; [ exact H | ]
    end.
    rewrite <-(word.of_Z_unsigned (word.xor _ _)).
    rewrite word.unsigned_xor_nowrap.
    rewrite !word_unsigned_of_Z_b2z, Z_lxor_xorb.
    reflexivity.
  Qed.

  Lemma compile_add :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr R functions T (pred: T -> _ -> Prop)
           x x_var y y_var k k_impl,
    forall var,
      map.get locals x_var = Some x ->
      map.get locals y_var = Some y ->
      let v := word.add x y in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-locals-post locals_ok
       with-locals (map.put locals var head)
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.op bopname.add (expr.var x_var) (expr.var y_var)))
                     k_impl)
       implementing (pred (dlet head k))
       and-locals-post locals_ok
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

  (* TODO: make more types *)
  (* N.B. this should *not* be added to any compilation tactics, since it will
     always apply; it needs to be applied manually *)
  Lemma compile_rename_bool :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      (locals_ok : Semantics.locals -> Prop)
      tr R functions T (pred: T -> _ -> Prop)
      x x_var var k k_impl,
      map.get locals x_var = Some (word.of_Z (Z.b2z x)) ->
      let v := x in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-locals-post locals_ok
       with-locals (map.put locals var (word.of_Z (Z.b2z x)))
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.var x_var)) k_impl)
       implementing (pred (dlet head k))
       and-locals-post locals_ok
       with-locals locals
       and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'. eauto.
  Qed.

  Lemma postcondition_for_postcondition_norets
        locals_ok {T} (pred : T -> _)
        spec k R tr mem locals functions :
    WeakestPrecondition.cmd
      (WeakestPrecondition.call functions)
      k tr mem locals
      (postcondition_norets locals_ok (pred spec) R tr) ->
    WeakestPrecondition.cmd
      (WeakestPrecondition.call functions)
      k tr mem locals
      (fun tr' m' _ =>
         postcondition_for (pred spec) R tr tr' m' []).
  Proof.
    cbv [postcondition_norets]; intros.
    eapply Proper_cmd;
      [ solve [apply Proper_call] | repeat intro
        | eassumption ].
    cleanup; eauto.
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
  | [  |- context[postcondition_for (?pred ?spec)] ] =>
    let hd := term_head spec in unfold hd
  end;
  apply postcondition_for_postcondition_norets
    with (locals_ok := fun _ => True);
  cleanup.

Ltac lookup_variable m val :=
  lazymatch m with
  | map.put _ ?k val => constr:(k)
  | map.put ?m' _ _ => lookup_variable m' val
  end.

Ltac solve_map_get_goal :=
  match goal with
  | [  |- map.get ?m _ = Some ?val ] =>
    let var := lookup_variable m val in
    instantiate (1 := var);
    rewrite ?map.get_put_diff by congruence;
    apply map.get_put_same
  | [  |- map.get ?m _ = None ] =>
    rewrite ?map.get_put_diff by congruence;
    apply map.get_empty
  | [ H : map.get ?m1 _ = Some ?val |- map.get ?m2 _ = Some ?val ] =>
    rewrite ?map.get_put_diff; [ apply H | congruence .. ]
  | [ H : map.get _ ?k = None  |- map.get _ ?k = None ] =>
    rewrite ?map.get_put_diff; [ apply H | congruence .. ]
  end.

Create HintDb compiler.

Ltac compile_basics :=
  gen_sym_inc;
  let name := gen_sym_fetch "v" in
  first [simple eapply compile_constant with (var := name) |
         simple eapply compile_false with (var := name) |
         simple eapply compile_true with (var := name) |
         simple eapply compile_nat_constant with (var := name) |
         simple eapply compile_xorb with (var := name) |
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
  | [  |- map.get _ _ = _ ] =>
    first [ solve_map_get_goal
          | progress subst_lets_in_goal; solve_map_get_goal ]
  | _ => eauto with compiler
  end.

(* only apply compile_step when repeat_compile_step solves all the side
     conditions but one *)
Ltac safe_compile_step :=
  compile_step; [ solve [repeat compile_step] .. | ].

Ltac compile_done := simple eapply compile_skip; repeat compile_step.

Ltac compile :=
  setup; repeat compile_step; compile_done.
