Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Nondeterminism.NonDeterminism.

Import NDMonad.

Section Peek.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok _}.

  Definition Bag := list word.

  Definition bag_at (addr: word) (b: Bag) :=
    Lift1Prop.ex1 (fun words =>
                     emp (forall x, List.In x words <-> List.In x b) *
                     array scalar (word.of_Z (Memory.bytes_per_word Semantics.width))
                           addr words)%sep.

  Definition peek (l: Bag) := %{ x | List.In x l }.

  Lemma compile_peek {tr mem locals functions} (b: Bag) :
    let c := peek b in
    forall {B} {pred: B -> predicate}
      {k: word -> Comp B} {k_impl}
      R b_ptr b_var var,

      b <> [] ->
      (bag_at b_ptr b * R)%sep mem ->
      map.get locals b_var = Some b_ptr ->

      (forall v,
          c v ->
          <{ Trace := tr;
             Memory := mem;
             Locals := map.put locals var v;
             Functions := functions }>
          k_impl
          <{ pbind pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.load access_size.word (expr.var b_var))) k_impl
      <{ pbind pred (bindn [var] c k) }>.
  Proof.
    destruct b as [|w b]; try congruence.
    intros * Hnn [ws [Hin Hm]%sep_assoc%sep_emp_l]%sep_ex1_l Hl Hk.
    destruct ws as [| w' ws]; [ exfalso; eapply Hin; red; eauto | ].
    eexists; split.
    - eexists; split; eauto.
      eexists; split; eauto.
      eapply load_word_of_sep.
      seprewrite_in uconstr:(@array_cons) Hm.
      ecancel_assumption.
    - eapply WeakestPrecondition_unbindn; [ | intros; apply Hk; eauto ].
      apply Hin; red; eauto.
  Qed.

  Definition nondet_sum_src (b: Bag) :=
    let/+ x := peek b in
    let/+ y := peek b in
    let/n out := word.add x y in
    ret out.

  Instance spec_of_nondet_sum : spec_of "nondet_sum" :=
    let pre b b_ptr R tr mem :=
        b <> [] /\
        (bag_at b_ptr b * R)%sep mem in
    let post b b_ptr R tr mem tr' mem' rets :=
        exists v, (nondet_sum_src b) v /\ tr' = tr /\
             rets = [v] /\ (bag_at b_ptr b * R)%sep mem' in
      fun functions =>
        forall b b_ptr R,
        forall tr mem,
          pre b b_ptr R tr mem ->
          WeakestPrecondition.call
            functions "nondet_sum" tr mem [b_ptr]
            (post b b_ptr R tr mem).

  Hint Extern 1 => simple eapply compile_peek; shelve : compiler.

  Derive nondet_sum_body SuchThat
         (defn! "nondet_sum"("b") ~> "out"
              { nondet_sum_body },
          implements nondet_sum_src)
  As nondet_sum_target_correct.
  Proof.
    compile.
  Qed.
End Peek.

Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.
Arguments nondet_sum_body /.
Eval simpl in nondet_sum_body.
