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
      tr retvars R R' functions
      T (pred: T -> list word -> _ -> Prop)
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
        and-returning retvars
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
       and-returning retvars
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
           tr retvars R functions
           T (pred: T -> list word -> _ -> Prop)
      {data} (x y : data * data) swap k k_impl,
      let v := cswap swap x y in
      (let __ := 0 in (* placeholder *)
       (find k_impl
        implementing (pred (dlet (cswap swap (fst x) (fst y))
                                 (fun xy1 =>
                                    dlet (cswap swap (snd x) (snd y))
                                         (fun xy2 =>
                                            let x := (fst xy1, fst xy2) in
                                            let y := (snd xy1, snd xy2) in
                                            k (x, y)))))
        and-returning retvars
        and-locals-post locals_ok
        with-locals locals
        and-memory mem and-trace tr and-rest R
        and-functions functions)) ->
      (let head := v in
       find k_impl
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'.
    subst_lets_in_goal. destruct_products.
    destruct swap; cbv [cswap dlet] in *; cbn [fst snd] in *.
    all:eauto.
  Qed.
End Compile.

Section Helpers.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Lemma cswap_iff1
        {T} (pred : word ->T -> Semantics.mem -> Prop) s pa pb a b :
    Lift1Prop.iff1
      ((pred (fst (cswap s pa pb)) (fst (cswap s a b)))
       * pred (snd (cswap s pa pb))
              (snd (cswap s a b)))%sep
      (pred pa a * pred pb b)%sep.
  Proof. destruct s; cbn [cswap fst snd]; ecancel. Qed.

  Lemma map_get_cswap_fst
        {key value} {map : map.map key value}
        (m : map.rep (map:=map)) s ka kb a b :
    map.get m ka = Some a ->
    map.get m kb = Some b ->
    map.get m (fst (cswap s ka kb)) = Some (fst (cswap s a b)).
  Proof. destruct s; cbn [cswap fst fst]; auto. Qed.

  Lemma map_get_cswap_snd
        {key value} {map : map.map key value}
        (m : map.rep (map:=map)) s ka kb a b :
    map.get m ka = Some a ->
    map.get m kb = Some b ->
    map.get m (snd (cswap s ka kb)) = Some (snd (cswap s a b)).
  Proof. destruct s; cbn [cswap fst snd]; auto. Qed.

  Lemma cswap_cases_fst {T} (P : T -> Prop) s a b :
    P a -> P b -> P (fst (cswap s a b)).
  Proof. destruct s; cbn [cswap fst snd]; auto. Qed.

  Lemma cswap_cases_snd {T} (P : T -> Prop) s a b :
    P a -> P b -> P (snd (cswap s a b)).
  Proof. destruct s; cbn [cswap fst snd]; auto. Qed.

  Lemma cswap_pair {A B} b (x y : A * B) :
    cswap b x y =
    (fst (cswap b (fst x) (fst y)), fst (cswap b (snd x) (snd y)),
     (snd (cswap b (fst x) (fst y)), snd (cswap b (snd x) (snd y)))).
  Proof. destruct b; destruct_products; reflexivity. Qed.
End Helpers.
