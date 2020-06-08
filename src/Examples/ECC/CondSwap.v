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
      {data} (x y : data) swap x_var x_ptr y_var y_ptr k k_impl
      (Data : word -> data -> Semantics.mem -> Prop) var,
      x_var <> y_var ->
      x_var <> var ->
      var <> y_var ->
      map.get locals x_var = Some x_ptr ->
      map.get locals y_var = Some y_ptr ->
      (Data x_ptr x * Data y_ptr y * R')%sep mem ->
      let v := cswap swap x y in
      (let head := v in
       (find k_impl
        implementing (pred (k head))
        and-locals-post locals_ok
        with-locals
               (map.put (map.put (map.put locals var x_ptr) x_var y_ptr)
                        y_var x_ptr)
        and-memory mem and-trace tr and-rest R
        and-functions functions)) ->
      (let head := v in
       find (cmd.seq
               (cmd.seq
                  (cmd.seq
                     (cmd.set var (expr.var x_var))
                     (cmd.set x_var (expr.var y_var)))
                  (cmd.set y_var (expr.var var)))
               k_impl)
       implementing (pred (dlet head k))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'. subst_lets_in_goal. eauto.
  Qed.
End Compile.
