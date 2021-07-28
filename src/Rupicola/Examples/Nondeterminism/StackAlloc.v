Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Examples.Nondeterminism.NonDeterminism.

Require Import coqutil.Byte.
Open Scope Z_scope.

Import NDMonad.

Section Peek.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok _}.

  Definition stack_alloc (nbytes: nat) : Comp (list byte) :=
    %{ ls: list byte | List.length ls = nbytes }.

  Definition bytes_at addr data :=
    listarray_value AccessByte addr data.

  Lemma compile_stack_alloc {tr mem locals functions} (nbytes: nat):
    let c := stack_alloc nbytes in
    forall {B} {pred: B -> predicate}
      {k: list byte -> Comp B} {k_impl}
      (R: _ -> Prop) var,
      R mem ->
      Z.of_nat nbytes mod Memory.bytes_per_word Semantics.width = 0 ->
      (forall ptr (bs: ListArray.t byte) mem,
          List.length bs = nbytes ->
          (sizedlistarray_value AccessByte ptr nbytes bs * R)%sep mem ->
          let pred g tr' mem' locals' :=
              exists R' bs',
                (sizedlistarray_value AccessByte ptr nbytes bs' * R')%sep mem' /\
                forall mem'', R' mem'' -> pred g tr' mem'' locals' in
          <{ Trace := tr;
             Memory := mem;
             Locals := map.put locals var ptr;
             Functions := functions }>
          k_impl
          <{ pbind pred (k bs) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.stackalloc var (Z.of_nat nbytes) k_impl
      <{ pbind pred (bindn [var] c k) }>.
  Proof.
    red; red; cbn; intros * Hmem Hmod Hkimpl.
    split; eauto; red. intros ptr mStack mCombined Hany Hsplit.
    generalize Hany; intros [bs [Hbs Hlen]]%anybytes_to_array_1.
    rewrite Nat2Z.id in Hlen.
    eapply WeakestPrecondition_weaken; cycle 1.
    - apply Hkimpl; eauto.
      apply sep_comm; exists mem, mStack;
        eauto using sizedlistarray_value_of_array.
    - intros tr' mem' locals' (b & Hk & (R' & bs' & (mR' & mStack' & Hsplit' & HR' & Hbs')%sep_comm & Hpred')).
      eexists; eexists; split; [|split].
      + subst nbytes.
        rewrite <- (length_of_sizedlistarray_value _ _ _ _ _ Hbs').
        apply array_1_to_anybytes.
        eapply array_of_sizedlistarray_value in Hbs'.
        apply Hbs'.
      + eassumption.
      + unfold pbind, bindn, bind; cbn; eauto 6.
  Qed.

  Lemma stackalloc_universal_bound :
    forall z,
      Z.modulo z 8 = 0 ->
      Z.modulo z (Memory.bytes_per_word Semantics.width) = 0.
  Proof.
    intros z Hmod.
    destruct Semantics.width_cases as [-> | ->];
      unfold Memory.bytes_per_word, Z.div; simpl.
    2: eauto.
    - apply Z_div_exact_full_2 in Hmod; try congruence; rewrite Hmod.
      apply Zmod_divides; try congruence.
      exists (2 * (z / 8)); ring.
  Qed.

  Definition nondet_xor_src (w: word) :=
    let/+ bs := stack_alloc 8 in
    let/n idx := 0%nat in
    let/n undef := ListArray.get bs idx in
    let/n out := w in
    let/n out := word.xor (word_of_byte undef) out in
    let/n out := word.xor (word_of_byte undef) out in
    ret out.

  Lemma nondef_xor_id w w' : nondet_xor_src w w' -> w = w'.
  Proof. unfold nondet_xor_src; unfold bindn, bind, stack_alloc, pick, ret, nlet.
     intros (bs & Hlen & ->).
     apply word.unsigned_inj. unfold byte.unsigned.
     rewrite !word.unsigned_xor_nowrap, !word.unsigned_of_Z.
     rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l; reflexivity.
  Qed.

  Implicit Type R : Semantics.mem -> Prop.
  Instance spec_of_nondet_xor : spec_of "nondet_xor" :=
    fnspec! "nondet_xor" w0 / R,
    { requires fns tr mem := R mem;
      ensures tr' mem' rets :=
        propbind (nondet_xor_src w0)
                 (fun w => tr' = tr /\ R mem' /\ rets = [w]) }.

  Import SizedListArrayCompiler.
  Hint Extern 1 => simple eapply compile_stack_alloc; shelve : compiler.

  Hint Resolve stackalloc_universal_bound : compiler_cleanup.

  Derive nondet_xor_body SuchThat
         (defn! "nondet_xor"("w") ~> "out"
              { nondet_xor_body },
          implements nondet_xor_src)
  As nondet_xor_target_correct.
  Proof.
    compile.
  Qed.
End Peek.

Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.
Arguments nondet_xor_body /.
Eval cbv in nondet_xor_body.
