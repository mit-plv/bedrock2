Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Conditionals.

Section Gallina.
  Definition cswap {T} (swap: bool) (a b: T) : T * T :=
    if swap then (b, a) else (a, b).
End Gallina.

Section Compile.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  (* FIXME cswap should be compilable as-is; no need for a lemma. *)
  (* There are two ways cswap could be compiled; you can either swap the local
     variables (the pointers), or you can leave the pointers and copy over the
     data. This version swaps the pointers without doing any copying. *)
  Lemma compile_cswap_nocopy : forall {tr} {mem: mem} {locals: locals} {functions} (swap: bool) {A} (x y: A),
    let v := cswap swap x y in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      R (Data : word -> A -> _ -> Prop)
      swap_var x_var x_ptr y_var y_ptr tmp,

      map.get locals swap_var = Some (word.of_Z (Z.b2z swap)) ->
      map.get locals x_var = Some x_ptr ->
      map.get locals y_var = Some y_ptr ->

      (* tmp is a strictly temporary variable, confined to one part of the
         if-clause; it gets unset after use *)
      map.get locals tmp = None ->
      (Data x_ptr x * Data y_ptr y * R)%sep mem ->

      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put (map.put locals x_var (fst (cswap swap x_ptr y_ptr))) y_var
                      (snd (cswap swap x_ptr y_ptr));
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
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
        k_impl
      <{ pred (nlet_eq [x_var; y_var] v k) }>.
  Proof.
    intros; subst v; unfold cswap.
    simple eapply compile_if with
        (val_pred := fun _ tr' mem' locals' =>
                      tr' = tr /\
                      mem' = mem0 /\
                      locals' =
                      let locals := map.put locals0 x_var (if swap then y_ptr else x_ptr) in
                      let locals := map.put locals y_var (if swap then x_ptr else y_ptr) in
                      locals);
      repeat compile_step;
      repeat straightline'; subst_lets_in_goal; cbn; ssplit; eauto.
    - rewrite !map.remove_put_diff, !map.remove_put_same, map.remove_not_in by congruence.
      reflexivity.
    - rewrite (map.put_noop x_var x_ptr), map.put_noop by assumption.
      reflexivity.
    - cbv beta in *; repeat compile_step; cbn.
      destruct swap; eassumption.
  Qed.

  Lemma compile_cswap_pair : forall {tr mem locals functions} (swap: bool) {A} (x y: A * A),
    let v := cswap swap x y in
    forall {T} {pred: T -> predicate}
      {k: (A * A) * (A * A) -> T} {k_impl},
      (let __ := 0 in (* placeholder FIXME why? *)
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       k_impl
       <{ pred (dlet (cswap swap (fst x) (fst y))
                     (fun xy1 =>
                        dlet (cswap swap (snd x) (snd y))
                             (fun xy2 =>
                                let x := (fst xy1, fst xy2) in
                                let y := (snd xy1, snd xy2) in
                                k (x, y)))) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      k_impl
      <{ pred (dlet v k) }>.
  Proof.
    repeat straightline'.
    subst_lets_in_goal. destruct_products.
    destruct swap; cbv [cswap dlet] in *; cbn [fst snd] in *.
    all:eauto.
  Qed.
End Compile.

Section Helpers.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Lemma cswap_iff1
        {T} (pred : word ->T -> mem -> Prop) s pa pb a b :
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
