Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Nondeterminism.NonDeterminism.

Section Peek.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Definition Bag := list word.

  Definition bag_at (addr: word) (b: Bag) :=
    Lift1Prop.ex1 (fun words =>
                     emp (forall x, List.In x words <-> List.In x b) *
                     array scalar (word.of_Z (Memory.bytes_per_word width))
                           addr words)%sep.

  Definition peek (l: Bag) := %{ x | List.In x l }.

  Lemma compile_peek : forall {tr mem locals functions} (b: Bag),
    let c := peek b in
    forall {B} {pred: B -> predicate}
      {k: word -> ND.M B} {k_impl}
      R b_ptr b_expr var,

      b <> [] ->
      (bag_at b_ptr b * R)%sep mem ->
      WeakestPrecondition.dexpr mem locals b_expr b_ptr ->

      (forall v,
          c v ->
          <{ Trace := tr;
             Memory := mem;
             Locals := map.put locals var v;
             Functions := functions }>
          k_impl
          <{ ndspec_k pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.load access_size.word b_expr)) k_impl
      <{ ndspec_k pred (mbindn [var] c k) }>.
  Proof.
    destruct b as [|w b]; try congruence.
    intros * Hnn [ws [Hin Hm]%sep_assoc%sep_emp_l]%sep_ex1_l Hl Hk.
    destruct ws as [| w' ws]; [ exfalso; eapply Hin; red; eauto | ].
    eexists; split; repeat straightline.
    - eapply WeakestPrecondition_dexpr_expr; eauto.
      eexists; split; eauto.
      eapply load_word_of_sep.
      seprewrite_in uconstr:(@array_cons) Hm.
      ecancel_assumption.
    - eapply WeakestPrecondition_ndspec_k_bindn; [ | intros; apply Hk; eauto ].
      all: apply Hin; red; eauto.
  Qed.

  Definition nondet_sum_src (b: Bag) :=
    let/+ x := peek b in
    let/+ y := peek b in
    let/n out := word.add x y in
    mret out.

  Instance spec_of_nondet_sum : spec_of "nondet_sum" :=
    fnspec! "nondet_sum" b_ptr / b R,
      { requires tr mem :=
          b <> [] /\ (bag_at b_ptr b ⋆ R) mem;
        ensures tr' mem' rets :=
          ndspec (nondet_sum_src b) (fun v =>
             tr' = tr /\ rets = [v] /\ (bag_at b_ptr b ⋆ R) mem') }.

  Hint Extern 1 => simple eapply compile_peek; shelve : compiler.

  Derive nondet_sum_br2fn SuchThat
         (defn! "nondet_sum"("b") ~> "out"
              { nondet_sum_br2fn },
          implements nondet_sum_src)
  As nondet_sum_br2fn_ok.
  Proof.
    compile.
  Qed.
End Peek.

From bedrock2 Require Import BasicC64Semantics NotationsCustomEntry.
Compute nondet_sum_br2fn. (* (word := word) *)
