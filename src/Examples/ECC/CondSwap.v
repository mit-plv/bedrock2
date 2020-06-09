Require Import Rupicola.Lib.Api.

Section Gallina.
  Definition cswap {T} (swap:bool) (a b: T) : T * T :=
    if swap then (b, a) else (a, b).
End Gallina.

Section Compile.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  (* There are two ways cswap could be compiled; you can either swap the local
     variables (the pointers), or you can leave the pointers and copy over the
     data. This version swaps the pointers without doing any copying. *)
  Lemma compile_cswap_nocopy :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr R R' functions T (pred: T -> _ -> Prop)
      {data} (x y : data) swap swap_var x_var x_ptr y_var y_ptr k k_impl
      (Data : word -> data -> Semantics.mem -> Prop) tmp,
      x_var <> y_var ->
      map.get locals swap_var = Some (word.of_Z (Z.b2z swap)) ->
      map.get locals x_var = Some x_ptr ->
      map.get locals y_var = Some y_ptr ->
      (* tmp is a strictly temporary variable, confined to one part of the
         if-clause; it gets unset after use *)
      map.get locals tmp = None ->
      (Data x_ptr x * Data y_ptr y * R')%sep mem ->
      let v := cswap swap x y in
      (let head := v in
       (find k_impl
        implementing (pred (k head))
        and-locals-post locals_ok
        with-locals
               (map.put (map.put locals
                                 x_var (fst (cswap swap x_ptr y_ptr)))
                        y_var (snd (cswap swap x_ptr y_ptr)))
        and-memory mem and-trace tr and-rest R
        and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.cond
                  (expr.var swap_var)
                  (cmd.seq
                     (cmd.seq
                        (cmd.seq
                           (cmd.set tmp (expr.var x_var))
                           (cmd.set x_var (expr.var y_var)))
                        (cmd.set y_var (expr.var tmp)))
                     (cmd.unset tmp))
                  (cmd.skip))
               k_impl)
       implementing (pred (dlet head k))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'.
    destr (tmp =? x_var); [ congruence | ].
    destr (tmp =? y_var); [ congruence | ].
    destruct swap; cbn [Z.b2z cswap fst snd] in *;
      split_if ltac:(repeat straightline');
    try (subst_lets_in_goal;
         rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1;
         congruence); [ | ].
    { repeat straightline'.
      match goal with
      | H : WeakestPrecondition.cmd _ _ _ _ ?l1 _
        |- WeakestPrecondition.cmd _ _ _ _ ?l2 _ =>
        replace l2 with l1; [ exact H | apply map.map_ext ]
      end.
      subst_lets_in_goal. intros.
      rewrite !map.get_remove_dec, !map.get_put_dec.
      repeat destruct_one_match; congruence. }
    { repeat straightline'.
      match goal with
      | H : WeakestPrecondition.cmd _ _ _ _ ?l1 _
        |- WeakestPrecondition.cmd _ _ _ _ ?l2 _ =>
        replace l2 with l1; [ exact H | apply map.map_ext ]
      end.
      subst_lets_in_goal. intros.
      rewrite !map.get_put_dec.
      repeat destruct_one_match; congruence. }
  Qed.

  Lemma compile_cswap_pair :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr R functions T (pred: T -> _ -> Prop)
      {data} (x1 x2 y1 y2 : data) swap k k_impl,
      let v := cswap swap (x1,x2) (y1,y2) in
      (let __ := 0 in (* placeholder *)
       (find k_impl
        implementing (pred (dlet (cswap swap x1 y1)
                                 (fun xy1 =>
                                    dlet (cswap swap x2 y2)
                                         (fun xy2 =>
                                            let x := (fst xy1, fst xy2) in
                                            let y := (snd xy1, snd xy2) in
                                            k (x, y)))))
        and-locals-post locals_ok
        with-locals locals
        and-memory mem and-trace tr and-rest R
        and-functions functions)) ->
      (let head := v in
       find k_impl
       implementing (pred (dlet head k))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'.
    subst_lets_in_goal.
    destruct swap; cbv [cswap dlet] in *; cbn [fst snd] in *.
    all:eauto.
  Qed.
End Compile.
