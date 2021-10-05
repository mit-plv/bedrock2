Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.
Require Import Rupicola.Lib.Tactics.

Section CompilerBasics.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {memT: map.map word Byte.byte}.
  Context {localsT: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok memT}.
  Context {locals_ok : map.ok localsT}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Lemma compile_word_of_Z_constant {tr mem locals functions} (z: Z) :
    let v := word.of_Z z in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      var,
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal z)) k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof. repeat straightline; eassumption. Qed.

  Lemma compile_word_constant {tr mem locals functions} (w: word) :
    forall {P} {pred: P w -> predicate}
      {k: nlet_eq_k P w} {k_impl}
      var,
      <{ Trace := tr;
         Memory := mem;
         Locals := map.put locals var w;
         Functions := functions }>
      k_impl
      <{ pred (k w eq_refl) }> ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal (word.unsigned w))) k_impl
      <{ pred (nlet_eq [var] w k) }>.
  Proof. repeat straightline; subst_lets_in_goal; rewrite word.of_Z_unsigned; eauto. Qed.

  Lemma compile_Z_constant {tr mem locals functions} z :
    let v := z in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      var,
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (word.of_Z v);
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal z)) k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof. repeat straightline; eassumption. Qed.

  Lemma compile_nat_constant {tr mem locals functions} n :
    let v := n in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      var,
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (word.of_Z (Z.of_nat v));
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal (Z.of_nat n))) k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof. repeat straightline; eassumption. Qed.

  Lemma compile_bool_constant {tr mem locals functions} b :
    let v := b in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      var,
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (word.b2w v);
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal (Z.b2z v))) k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof. repeat straightline; eassumption. Qed.

  Lemma compile_binop_xxx {T} T2w op f
        (H: forall x y: T, T2w (f x y) = Semantics.interp_binop op (T2w x) (T2w y))
        {tr mem locals functions} (x y: T) :
    let v := f x y in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      x_var y_var var,
      map.get locals x_var = Some (T2w x) ->
      map.get locals y_var = Some (T2w y) ->
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (T2w v);
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.op op (expr.var x_var) (expr.var y_var)))
              k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof. repeat (eexists; split; eauto). Qed.

  Notation unfold_id term :=
    ltac:(let tm := fresh in pose term as tm;
          change (id ?x) with x in (type of tm);
          let t := type of tm in
          exact (tm: t)) (only parsing).

  Definition compile_word_add :=
    unfold_id (@compile_binop_xxx _ id bopname.add word.add ltac:(reflexivity)).
  Definition compile_word_sub :=
    unfold_id (@compile_binop_xxx _ id bopname.sub word.sub ltac:(reflexivity)).
  Definition compile_word_mul :=
    unfold_id (@compile_binop_xxx _ id bopname.mul word.mul ltac:(reflexivity)).
  Definition compile_word_mulhuu :=
    unfold_id (@compile_binop_xxx _ id bopname.mulhuu word.mulhuu ltac:(reflexivity)).
  Definition compile_word_divu :=
    unfold_id (@compile_binop_xxx _ id bopname.divu word.divu ltac:(reflexivity)).
  Definition compile_word_remu :=
    unfold_id (@compile_binop_xxx _ id bopname.remu word.modu ltac:(reflexivity)).
  Definition compile_word_and :=
    unfold_id (@compile_binop_xxx _ id bopname.and word.and ltac:(reflexivity)).
  Definition compile_word_or :=
    unfold_id (@compile_binop_xxx _ id bopname.or word.or ltac:(reflexivity)).
  Definition compile_word_xor :=
    unfold_id (@compile_binop_xxx _ id bopname.xor word.xor ltac:(reflexivity)).
  Definition compile_word_sru :=
    unfold_id (@compile_binop_xxx _ id bopname.sru word.sru ltac:(reflexivity)).
  Definition compile_word_slu :=
    unfold_id (@compile_binop_xxx _ id bopname.slu word.slu ltac:(reflexivity)).
  Definition compile_word_srs :=
    unfold_id (@compile_binop_xxx _ id bopname.srs word.srs ltac:(reflexivity)).

  Definition compile_Z_add :=
    @compile_binop_xxx _ word.of_Z bopname.add Z.add word.ring_morph_add.
  Definition compile_Z_sub :=
    @compile_binop_xxx _ word.of_Z bopname.sub Z.sub word.ring_morph_sub.
  Definition compile_Z_mul :=
    @compile_binop_xxx _ word.of_Z bopname.mul Z.mul word.ring_morph_mul.
  Definition compile_Z_and :=
    @compile_binop_xxx _ word.of_Z bopname.and Z.land word.morph_and.
  Definition compile_Z_or :=
    @compile_binop_xxx _ word.of_Z bopname.or Z.lor word.morph_or.
  Definition compile_Z_xor :=
    @compile_binop_xxx _ word.of_Z bopname.xor Z.lxor word.morph_xor.

  Lemma compile_binop_xxb {T} T2w op (f: T -> T -> bool)
        (H: forall x y, word.b2w (f x y) = Semantics.interp_binop op (T2w x) (T2w y))
        {tr mem locals functions} (x y: T) :
    let v := f x y in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      x_var y_var var,
      map.get locals x_var = Some (T2w x) ->
      map.get locals y_var = Some (T2w y) ->
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (word.b2w v);
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.op op (expr.var x_var) (expr.var y_var)))
              k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof. repeat (eexists; split; eauto). Qed.

  Ltac compile_binop_wwb_t :=
    unfold id; cbn; intros; destruct_one_match; reflexivity.

  Definition compile_word_lts :=
    unfold_id (@compile_binop_xxb _ id bopname.lts word.lts ltac:(compile_binop_wwb_t)).
  Definition compile_word_ltu :=
    unfold_id (@compile_binop_xxb _ id bopname.ltu word.ltu ltac:(compile_binop_wwb_t)).
  Definition compile_word_eqb :=
    unfold_id (@compile_binop_xxb _ id bopname.eq word.eqb ltac:(compile_binop_wwb_t)).

  Lemma bool_word_eq_compat {T} (T2w: T -> word) (eqb: T -> T -> bool)
        (T2w_inj: forall x y, T2w x = T2w y -> x = y)
        (eqb_compat: forall x y, eqb x y = true <-> x = y) :
    forall x y,
      word.b2w (eqb x y) =
      (if word.eqb (T2w x) (T2w y) then word.of_Z 1 else word.of_Z 0) :> word.
  Proof.
    intros; rewrite word.unsigned_eqb.
    destruct eqb eqn:Hb; destruct Z.eqb eqn:Hz; try reflexivity.
    - apply eqb_compat in Hb; subst.
      apply Z.eqb_neq in Hz; congruence.
    - apply Z.eqb_eq, word.unsigned_inj, T2w_inj in Hz; subst.
      rewrite (proj2 (eqb_compat _ _)) in Hb; congruence.
  Qed.

  Ltac compile_binop_bbb_t lemma :=
    unfold word.b2w; intros x y; cbn;
    match goal with
    | [  |- _ = ?w ] =>
      rewrite <- (word.of_Z_unsigned w);
      rewrite lemma, !word.unsigned_of_Z_b2z; destruct x, y; reflexivity
    end.

  Notation cbv_beta_b2w x :=
    ltac:(pose proof x as x0;
         change ((fun b => word.b2w b) ?y) with (word.b2w y : word) in (type of x0);
         let t := type of x0 in exact (x: t)) (only parsing).

  Definition compile_bool_eqb :=
    cbv_beta_b2w (@compile_binop_xxb
                    _ (fun x => word.b2w x) bopname.eq Bool.eqb
                    (bool_word_eq_compat (fun w => word.b2w w) _ word.b2w_inj Bool.eqb_true_iff)).

  (* FIXME add comparisons on bytes *)

  Definition compile_bool_andb :=
    cbv_beta_b2w (@compile_binop_xxb
                    _ (fun x => word.b2w x) bopname.and andb
                    ltac:(compile_binop_bbb_t word.unsigned_and_nowrap)).
  Definition compile_bool_orb :=
    cbv_beta_b2w (@compile_binop_xxb
                    _ (fun x => word.b2w x) bopname.or orb
                    ltac:(compile_binop_bbb_t word.unsigned_or_nowrap)).
  Definition compile_bool_xorb :=
    cbv_beta_b2w (@compile_binop_xxb
                    _ (fun x => word.b2w x) bopname.xor xorb
                    ltac:(compile_binop_bbb_t word.unsigned_xor_nowrap)).

  Lemma compile_copy_word {tr mem locals functions} v0 :
    let v := v0 in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      src_var dst_var,
      map.get locals src_var = Some v0 ->
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals dst_var v;
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set dst_var (expr.var src_var)) k_impl
      <{ pred (nlet_eq [dst_var] v k) }>.
  Proof.
    repeat straightline'; eauto.
  Qed.

  Lemma compile_copy_byte {tr mem locals functions} (b: byte) :
    let v := b in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      src_var dst_var,
      map.get locals src_var = Some (word_of_byte b) ->
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals dst_var (word_of_byte v);
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set dst_var (expr.var src_var)) k_impl
      <{ pred (nlet_eq [dst_var] v k) }>.
  Proof.
    repeat straightline'; eauto.
  Qed.
End CompilerBasics.

Module NoExprReflectionCompiler.
  #[export] Hint Extern 10 => simple eapply compile_word_constant; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_word_of_Z_constant; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_Z_constant; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_nat_constant; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_bool_constant; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_word_add; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_word_sub; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_word_mul; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_word_mulhuu; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_word_divu; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_word_remu; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_word_and; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_word_or; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_word_xor; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_word_sru; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_word_slu; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_word_srs; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_Z_add; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_Z_sub; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_Z_mul; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_Z_and; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_Z_or; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_Z_xor; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_word_lts; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_word_ltu; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_word_eqb; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_bool_eqb; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_bool_andb; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_bool_orb; shelve : compiler.
  #[export] Hint Extern 10 => simple eapply compile_bool_xorb; shelve : compiler.
End NoExprReflectionCompiler.
