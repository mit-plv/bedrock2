Require Import Rupicola.Lib.Api.
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
    array scalar8 (word.of_Z 1) addr data.

  Lemma compile_stack_alloc {tr mem locals functions} (nbytes: nat):
    let c := stack_alloc nbytes in
    forall {B} {pred: B -> predicate}
      {k: list byte -> Comp B} {k_impl}
      (R: _ -> Prop) var,
      R mem ->
      Z.of_nat nbytes mod Memory.bytes_per_word Semantics.width = 0 ->
      (forall ptr bs mem,
          List.length bs = nbytes ->
          (bytes_at ptr bs * R)%sep mem ->
          let pred g tr' mem' locals' :=
              exists R',
                (bytes_at ptr bs * R')%sep mem' /\
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
      apply sep_comm; exists mem, mStack; eauto.
    - intros tr' mem' locals' (b & Hk & (R' & (mR' & mStack' & Hsplit' & HR' & Hbs')%sep_comm & Hpred')).
      eexists; eexists; split; [|split].
      + subst nbytes; apply array_1_to_anybytes.
        eassumption.
      + eassumption.
      + unfold pbind, bindn, bind; cbn; eauto 6.
  Qed.

  (* FIXME deduplicate with Loops.v *)
  Lemma compile_nth {tr mem locals functions} (a: list byte) (idx: nat):
    let v := nth idx a Byte.x00 in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl : cmd}
      R a_var a_ptr idx_var (var : string),

      (idx < Datatypes.length a)%nat ->

      sep (bytes_at a_ptr a) R mem ->
      map.get locals a_var = Some a_ptr ->
      map.get locals idx_var = Some (word.of_Z (Z.of_nat idx)) ->

      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (word.of_Z (Byte.byte.unsigned v));
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.set
           var
           (expr.load
              access_size.one
              (expr.op bopname.add
                       (expr.var a_var)
                       (expr.op bopname.mul
                                (expr.literal 1)
                                (expr.var idx_var)))))
        k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof.
    cbn; intros Hlt *.
    pose proof word.unsigned_range (word.of_Z (Z.of_nat idx)) as (Hge & _).

    eexists; split; cbn; [ | eassumption ].
    exists a_ptr; split; [ eassumption | ]; cbn.
    exists (word.of_Z (Z.of_nat idx)); split; [ eassumption | ]; cbn.
    eexists; split; [ | reflexivity ].

    eapply load_one_of_sep.
    unfold bytes_at in *.
    once (seprewrite_in open_constr:(array_index_nat_inbounds
                                       _ _ _ _ idx) H0).
    { lia. }

    rewrite word.ring_morph_mul, !word.of_Z_unsigned in H5 by lia.
    rewrite <- nth_default_eq.
    rewrite List.hd_skipn_nth_default.
    ecancel_assumption.
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
    let/n undef := nth idx bs Byte.x00 in
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
    fnspec "nondet_xor" w0 / R,
    { requires tr mem := R mem;
      ensures tr' mem' rets :=
        propbind (nondet_xor_src w0)
                 (fun w => tr' = tr /\ R mem' /\ rets = [w]) }.

  Hint Extern 1 => simple eapply compile_stack_alloc; shelve : compiler.
  Hint Extern 1 => simple eapply compile_nth; shelve : compiler.
  Hint Extern 10 => simple eapply compile_copy_word; shelve : compiler.

  Hint Resolve stackalloc_universal_bound : compiler_cleanup.
  Hint Extern 20 => lia : compiler_cleanup.

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
Eval simpl in nondet_xor_body.
