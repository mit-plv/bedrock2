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
           tr retvars rets R functions T
           (pred: T -> list word -> _ -> Prop) head,
      locals_ok locals ->
      map.getmany_of_list locals retvars = Some rets ->
      sep (pred head rets) R mem ->
      (find cmd.skip
       implementing (pred head)
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    red; ssplit; eauto.
  Qed.

  Lemma compile_constant :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr retvars R functions T (pred: T -> _ -> _ -> Prop) z k k_impl,
    forall var,
      let v := word.of_Z z in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-returning retvars
       and-locals-post locals_ok
       with-locals (map.put locals var head)
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.literal z)) k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
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
           tr retvars R functions T (pred: T -> _ -> _ -> Prop)
           (n : nat) (zn : Z) k k_impl,
    forall var,
      zn = Z.of_nat n ->
      let v := n in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-returning retvars
       and-locals-post locals_ok
       with-locals (map.put locals var (word.of_Z zn))
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.literal zn)) k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
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
           tr retvars R functions T (pred: T -> _ -> _ -> Prop) k k_impl,
    forall var,
      let v := false in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-returning retvars
       and-locals-post locals_ok
       with-locals (map.put locals var (word.of_Z (Z.b2z head)))
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.literal 0)) k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
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
           tr retvars R functions T (pred: T -> _ -> _ -> Prop) k k_impl,
    forall var,
      let v := true in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-returning retvars
       and-locals-post locals_ok
       with-locals (map.put locals var (word.of_Z (Z.b2z head)))
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.literal 1)) k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    eassumption.
  Qed.

  Lemma compile_xorb :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr retvars R functions T (pred: T -> _ -> _ -> Prop)
           x x_var y y_var k k_impl,
    forall var,
      map.get locals x_var = Some (word.of_Z (Z.b2z x)) ->
      map.get locals y_var = Some (word.of_Z (Z.b2z y)) ->
      let v := xorb x y in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-returning retvars
       and-locals-post locals_ok
       with-locals (map.put locals var (word.of_Z (Z.b2z head)))
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.op bopname.xor (expr.var x_var) (expr.var y_var)))
                     k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
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
    rewrite !word.unsigned_of_Z_b2z, Z.lxor_xorb.
    reflexivity.
  Qed.

  Lemma compile_add :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr retvars R functions T (pred: T -> _ -> _ -> Prop)
           x x_var y y_var k k_impl,
    forall var,
      map.get locals x_var = Some x ->
      map.get locals y_var = Some y ->
      let v := word.add x y in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-returning retvars
       and-locals-post locals_ok
       with-locals (map.put locals var head)
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.op bopname.add (expr.var x_var) (expr.var y_var)))
                     k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
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

  Lemma compile_eqb :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr retvars R functions T (pred: T -> _ -> _ -> Prop)
           x x_var y y_var k k_impl,
    forall var,
      map.get locals x_var = Some x ->
      map.get locals y_var = Some y ->
      let v := word.eqb x y in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-returning retvars
       and-locals-post locals_ok
       with-locals (map.put locals var (word.of_Z (Z.b2z head)))
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq
               (cmd.set var (expr.op bopname.eq
                                     (expr.var x_var) (expr.var y_var)))
               k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros. repeat straightline'.
    subst_lets_in_goal.
    rewrite word.unsigned_eqb in *. cbv [Z.b2z] in *.
    destruct_one_match; eauto.
  Qed.

  (* TODO: make more types *)
  (* N.B. this should *not* be added to any compilation tactics, since it will
     always apply; it needs to be applied manually *)
  Lemma compile_rename_bool :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      (locals_ok : Semantics.locals -> Prop)
      tr retvars R functions T (pred: T -> _ -> _ -> Prop)
      x x_var var k k_impl,
      map.get locals x_var = Some (word.of_Z (Z.b2z x)) ->
      let v := x in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-returning retvars
       and-locals-post locals_ok
       with-locals (map.put locals var (word.of_Z (Z.b2z x)))
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.var x_var)) k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals
       and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'. eauto.
  Qed.

  (* N.B. this should *not* be added to any compilation tactics, since it will
     always apply; it needs to be applied manually *)
  Lemma compile_unset :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      (locals_ok : Semantics.locals -> Prop)
      tr retvars R functions T (pred: T -> _ -> _ -> Prop)
      var k k_impl,
      (find k_impl
       implementing (pred k)
       and-returning retvars
       and-locals-post locals_ok
       with-locals (map.remove locals var)
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (find (cmd.seq (cmd.unset var) k_impl)
       implementing (pred k)
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals
       and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'. eauto.
  Qed.

  (* N.B. should only be added to compilation tactics that solve their subgoals,
  since this applies to any shape of goal *)
  Lemma compile_pointer :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr retvars R' R functions T (pred: T -> _ -> _ -> Prop)
           {data} (Data : Semantics.word -> data -> Semantics.mem -> Prop)
           x_var x_ptr (x : data) k k_impl var,
      (Data x_ptr x * R')%sep mem ->
      map.get locals x_var = Some x_ptr ->
      let v := x in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-returning retvars
       and-locals-post locals_ok
       with-locals (map.put locals var x_ptr)
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq (cmd.set var (expr.var x_var)) k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline'.
    eassumption.
  Qed.

  Lemma compile_if_word :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr retvars R functions T (pred: T -> _ -> _ -> Prop)
           t_var f_var (t f : word) (c : bool) c_var
           k k_impl var,
      map.get locals c_var = Some (word.of_Z (Z.b2z c)) ->
      map.get locals t_var = Some t ->
      map.get locals f_var = Some f ->
      let v := if c then t else f in
      (let head := v in
        find k_impl
        implementing (pred (k head))
        and-returning retvars
        and-locals-post locals_ok
        with-locals (map.put locals var head)
        and-memory mem and-trace tr and-rest R
        and-functions functions) ->
      (let head := v in
       find (cmd.seq
               (cmd.cond (expr.var c_var)
                         (cmd.set var (expr.var t_var))
                         (cmd.set var (expr.var f_var)))
               k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline'.
    split_if ltac:(repeat straightline').
    { subst_lets_in_goal. rewrite word.unsigned_of_Z_b2z.
      cbv [Z.b2z]; destruct_one_match; try congruence; [ ].
      intros. repeat straightline'. eauto. }
    { subst_lets_in_goal. rewrite word.unsigned_of_Z_b2z.
      cbv [Z.b2z]; destruct_one_match; try congruence; [ ].
      intros. repeat straightline'. eauto. }
  Qed.

  Lemma compile_if_pointer :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr retvars Rt Rf R functions T (pred: T -> _ -> _ -> Prop)
           {data} (Data : Semantics.word -> data -> Semantics.mem -> Prop)
           t_var f_var t_ptr f_ptr (t f : data) (c : bool) c_var
           k k_impl var,
      (Data t_ptr t * Rt)%sep mem ->
      (Data f_ptr f * Rf)%sep mem ->
      map.get locals c_var = Some (word.of_Z (Z.b2z c)) ->
      map.get locals t_var = Some t_ptr ->
      map.get locals f_var = Some f_ptr ->
      let v := if c then t else f in
      (let head := v in
        find k_impl
        implementing (pred (k head))
        and-returning retvars
        and-locals-post locals_ok
        with-locals (map.put locals var (if c then t_ptr else f_ptr))
        and-memory mem and-trace tr and-rest R
        and-functions functions) ->
      (let head := v in
       find (cmd.seq
               (cmd.cond (expr.var c_var)
                         (cmd.set var (expr.var t_var))
                         (cmd.set var (expr.var f_var)))
               k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline'.
    split_if ltac:(repeat straightline').
    { subst_lets_in_goal. rewrite word.unsigned_of_Z_b2z.
      cbv [Z.b2z]; destruct_one_match; try congruence; [ ].
      intros. repeat straightline'. eauto. }
    { subst_lets_in_goal. rewrite word.unsigned_of_Z_b2z.
      cbv [Z.b2z]; destruct_one_match; try congruence; [ ].
      intros. repeat straightline'. eauto. }
  Qed.

  Lemma postcondition_func_norets_postcondition_cmd
        post k R tr mem locals functions :
    WeakestPrecondition.cmd
      (WeakestPrecondition.call functions)
      k tr mem locals
      (postcondition_cmd
         (fun _ => True) post [] R tr) ->
    WeakestPrecondition.cmd
      (WeakestPrecondition.call functions)
      k tr mem locals
      (fun tr' m' _ =>
         postcondition_func_norets post R tr tr' m' []).
  Proof.
    cbv [postcondition_func_norets
           postcondition_func postcondition_cmd]; intros.
    eapply Proper_cmd;
      [ solve [apply Proper_call] | repeat intro
        | eassumption ].
    sepsimpl; cleanup; eauto; [ ].
    match goal with H : map.getmany_of_list _ [] = Some _ |- _ =>
                    inversion H; clear H; subst
    end.
    eauto.
  Qed.

  Lemma getmany_list_map l :
    forall a vs (P :_ -> Prop),
      map.getmany_of_list l a = Some vs ->
      P vs ->
      WeakestPrecondition.list_map (WeakestPrecondition.get l) a P.
  Proof.
    induction a; cbn [WeakestPrecondition.list_map
                        WeakestPrecondition.list_map_body]; intros;
      match goal with
      | H : map.getmany_of_list _ [] = _ |- _ => cbn in H; congruence
      | H : map.getmany_of_list _ (_ :: _) = _ |- _ =>
        pose proof (map.getmany_of_list_exists_elem
                      _ _ _ _ ltac:(eauto using in_eq) H);
          cbn in H
      end.
      cleanup; eexists; ssplit; [ eassumption | ].
      repeat destruct_one_match_hyp; try congruence; [ ].
      repeat match goal with
             | H : Some _ = Some _ |- _ =>
               inversion H; clear H; subst
             end.
      eapply IHa; eauto.
  Qed.

  Lemma postcondition_func_postcondition_cmd
        (spec : list word -> Semantics.mem -> Prop)
        k R tr mem locals retvars n functions :
    length retvars = n ->
    (WeakestPrecondition.cmd
       (WeakestPrecondition.call functions)
       k tr mem locals
       (postcondition_cmd
          (fun _ => True) spec retvars R tr)) ->
    WeakestPrecondition.cmd
      (WeakestPrecondition.call functions)
      k tr mem locals
      (fun tr' m' l =>
         WeakestPrecondition.list_map
           (WeakestPrecondition.get l) retvars
           (fun rets : list word =>
              postcondition_func
                (fun rets =>
                   (emp (length rets = n) * (spec rets))%sep)
                R tr tr' m' rets)).
  Proof.
    cbv [postcondition_func postcondition_cmd]; intros.
    cleanup.
    use_hyp_with_matching_cmd; cleanup; subst.
    eapply getmany_list_map; sepsimpl; eauto.
    eauto using map.getmany_of_list_length, eq_sym.
  Qed.
End with_semantics.

Ltac term_head x :=
  match x with
  | ?f _ => term_head f
  | _ => x
  end.

Ltac setup :=
  cbv [program_logic_goal_for];
  (* modified version of a clause in straightline *)
  (intros; WeakestPrecondition.unfold1_call_goal;
   (cbv beta match delta [WeakestPrecondition.call_body]);
   lazymatch goal with
   | |- if ?test then ?T else _ =>
     replace test with true by reflexivity; change_no_check T
   end; cbv beta match delta [WeakestPrecondition.func]);
  repeat straightline; subst_lets_in_goal; cbn [length];
  first [ apply postcondition_func_norets_postcondition_cmd
        | apply postcondition_func_postcondition_cmd;
          [ cbn [length]; reflexivity | ] ];
   match goal with
   | |- context [ postcondition_cmd _ (fun r => _ ?spec r) ] =>
         let hd := term_head spec in
         unfold hd
   end.

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
         simple eapply compile_add with (var := name) |
         simple eapply compile_eqb with (var := name) |
         simple eapply compile_if_word with (var := name) |
         simple eapply compile_if_pointer with (var := name) ].

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
  | [  |- map.getmany_of_list _ [] = Some _ ] => reflexivity
  | _ => eauto with compiler
  end.

(* only apply compile_step when repeat_compile_step solves all the side
     conditions but one *)
Ltac safe_compile_step :=
  compile_step; [ solve [repeat compile_step] .. | ].

Ltac compile_done := simple eapply compile_skip; repeat compile_step.

Ltac compile :=
  setup; repeat compile_step; compile_done.
