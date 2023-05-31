Require Import PyLevelLang.Language.
Require Import PyLevelLang.Interpret.
Require Import PyLevelLang.Elaborate.
Require bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import coqutil.Datatypes.Result.
Import ResultMonadNotations.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Map.MapEauto.
Require Import coqutil.Byte coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Word.Properties.

Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.fwd.

Definition compile_atom {t : type} (a : atom t) : result Syntax.expr :=
  match a with
  | AWord z => Success (Syntax.expr.literal z)
  | ABool b => Success (Syntax.expr.literal (Z.b2z b))
  | AInt _ | AString _ | ANil _ | AEmpty => error:("unimplemented")
  end.

Definition compile_unop {t1 t2 : type} (o : unop t1 t2) :
  result (Syntax.expr -> Syntax.expr) :=
  match o with
  | OWNeg =>
      Success (Syntax.expr.op Syntax.bopname.sub (Syntax.expr.literal 0))
  | ONot =>
      Success (Syntax.expr.op Syntax.bopname.sub (Syntax.expr.literal 1))
  | ONeg
  | OLength _
  | OLengthString
  | OFst _ _ _
  | OSnd _ _ _
  | OIntToString =>
      error:("unimplemented")
  end.

Definition compile_binop {t1 t2 t3 : type} (o : binop t1 t2 t3) :
  result (Syntax.expr -> Syntax.expr -> Syntax.expr) :=
  match o with
  | OWPlus =>
      Success (Syntax.expr.op Syntax.bopname.add)
  | OWMinus =>
      Success (Syntax.expr.op Syntax.bopname.sub)
  | OWTimes =>
      Success (Syntax.expr.op Syntax.bopname.mul)
  | OWDivU =>
      Success (Syntax.expr.op Syntax.bopname.divu)
  | OWModU =>
      Success (Syntax.expr.op Syntax.bopname.remu)
  | OAnd =>
      Success (Syntax.expr.op Syntax.bopname.and)
  | OOr =>
      Success (Syntax.expr.op Syntax.bopname.or)
  | OConcat _
  | OConcatString =>
      error:("unimplemented")
  | OWLessU =>
      Success (Syntax.expr.op Syntax.bopname.ltu)
  | OWLessS =>
      Success (Syntax.expr.op Syntax.bopname.lts)
  | OEq _ H =>
      Success (Syntax.expr.op Syntax.bopname.eq)
  | OPlus
  | OMinus
  | OTimes
  | OWDivS
  | ODiv
  | OWModS
  | OMod
  | OLess
  | ORepeat _
  | OPair _ _ _
  | OCons _
  | ORange
  | OWRange =>
      error:("unimplemented")
  end.

Fixpoint compile_expr {t : type} (e : expr t) : result (Syntax.cmd * Syntax.expr) :=
  match e with
  | EAtom a =>
      e' <- compile_atom a;;
      Success (Syntax.cmd.skip, e')
  | EUnop o e1 =>
      f <- compile_unop o;;
      '(c1, e1') <- compile_expr e1;;
      Success (c1, f e1')
  | EBinop o e1 e2 =>
      f <- compile_binop o;;
      '(c1, e1') <- compile_expr e1;;
      '(c2, e2') <- compile_expr e2;;
      Success (Syntax.cmd.seq c1 c2, f e1' e2')
  | _ => error:("unimplemented")
  end.

Section WithMap.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {tenv : map.map string (type * bool)} {tenv_ok : map.ok tenv}.
  Context {locals: map.map string {t & interp_type (word := word) t}} {locals_ok: map.ok locals}.
  Context {locals': map.map string word} {locals'_ok: map.ok locals'}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: ExtSpec}.

  (* Relation between source language and target language values,
   * denoting that two values are equivalent for a given type *)
  Inductive value_relation : forall {t : type}, interp_type t -> word -> Prop :=
    | RWord (w : word) : value_relation (t := TWord) w w
    | RBool (b : bool) : value_relation (t := TBool) b (word.of_Z (Z.b2z b)).

  Lemma RBool' (b : bool) (w : word) : w = word.of_Z (Z.b2z b) ->
    value_relation (t := TBool) b w.
  Proof.
    intros [= ->].
    apply RBool.
  Qed.

  (* Relation between source language and target language locals maps,
   * denoting that the source language locals are a "subset" of the target
   * language locals *)
  Definition locals_relation (lo : locals) (l : locals') : Prop :=
    map.forall_keys (fun key =>
    match map.get lo key with
    | Some (existT _ _ val) => match map.get l key with
                               | Some val' => value_relation val val'
                               | None => False
                               end
    | None => True
    end) lo.

  Lemma locals_relation_extends (lo : locals) (l l' : locals') :
    map.extends l' l -> locals_relation lo l -> locals_relation lo l'.
  Proof.
    intros Hex.
    apply weaken_forall_keys.
    intros key Hl.
    destruct map.get as [s|]; try easy.
    destruct s as [t val].
    destruct (map.get l key) as [v|] eqn:E.
    - apply (Properties.map.extends_get (m1 := l) (m2 := l')) in E;
      [| assumption].
      now rewrite E.
    - destruct Hl.
  Qed.

  Lemma interp_type_eq : forall {t : type} (e : expr t) (w : interp_type t) (l : locals),
    (existT interp_type t w =
    existT interp_type t (interp_expr l e)) ->
    (interp_expr l e) = w.
  Proof.
    intros.
    inversion_sigma.
    rewrite <- Eqdep_dec.eq_rect_eq_dec in H0.
    * easy.
    * exact type_eq_dec.
  Qed.

  Lemma eval_map_extends_locals : forall e (m : mem) (l l' : locals') w,
    map.extends l' l ->
    eval_expr m l e = Some w ->
    eval_expr m l' e = Some w.
  Proof.
    induction e; intros m l l' w H Hl.
    - (* Syntax.expr.literal *)
      exact Hl.
    - (* Syntax.expr.var *)
      simpl in Hl. simpl. unfold map.extends in H.
      now apply H.
    - (* Syntax.expr.inlinetable *)
      simpl in Hl. simpl.
      specialize IHe with (m := m) (1 := H).
      destruct (eval_expr m l e); try easy.
      specialize IHe with (w := r) (1 := eq_refl).
      now rewrite IHe.
    - (* Syntax.expr.load *)
      simpl in Hl. simpl.
      specialize IHe with (m := m) (1 := H).
      destruct (eval_expr m l e); try easy.
      specialize IHe with (w := r) (1 := eq_refl).
      now rewrite IHe.
    - (* Syntax.expr.op *)
      simpl in Hl. simpl.
      destruct (eval_expr m l e1) as [r1 |] eqn:H1; try easy.
      destruct (eval_expr m l e2) as [r2 |] eqn:H2; try easy.
      specialize IHe1 with (m := m) (w := r1) (1 := H) (2 := H1).
      specialize IHe2 with (m := m) (w := r2) (1 := H) (2 := H2).
      now rewrite IHe1, IHe2.
    - (* Syntax.expr.ite *)
      simpl in Hl. simpl.
      destruct (eval_expr m l e1) as [r1 |] eqn:H1; try easy.
      specialize IHe1 with (m := m) (w := r1) (1 := H) (2 := H1).
      rewrite IHe1.
      destruct word.eqb.
      + destruct (eval_expr m l e3) as [r3 |] eqn:H3; try easy.
        apply IHe3 with (l' := l') in H3; try assumption.
        now rewrite H3.
      + destruct (eval_expr m l e2) as [r2 |] eqn:H2; try easy.
        apply IHe2 with (l' := l') in H2; try assumption.
        now rewrite H2.
  Qed.

  (* TODO allow arbitrary tenv *)
  Lemma compile_correct : forall {t} (e : expr t) (c : Syntax.cmd) (e' : Syntax.expr),
    wf map.empty e ->
    compile_expr e = Success (c, e') -> forall tr m l,
    exec map.empty c tr m l (fun tr' m' l' => exists (w : word),
      eval_expr m' l' e' = Some w /\
      (forall (lo : locals), locals_relation lo l ->
      value_relation (interp_expr lo e) w) /\
      m' = m /\
      map.extends l' l
    ).
  Proof.
    intros t. induction e; intros c e' He He' tr m l; try easy.
    - (* EAtom a *)
      unfold compile_expr in He'.
      fwd.
      apply exec.skip.
      destruct a; try easy.
      + (* AInt n *)
        injection E as [= <-].
        simpl.
        exists (word.of_Z (word.wrap n)).
        ssplit; try easy;
        rewrite <- word.unsigned_of_Z, word.of_Z_unsigned; try easy.
        intros lo Hlo.
        apply RWord.
      + (* ABool b *)
        injection E as [= <-].
        simpl.
        exists (word.of_Z (Z.b2z b)).
        ssplit; try easy.
        intros lo Hlo.
        apply RBool.
    - (* EUnop o e *)
      destruct o; try easy.
      all:
        simpl in He';
        simpl;
        fwd;
        inversion He;
        apply Eqdep_dec.inj_pair2_eq_dec in H4 as [= ->]; try exact type_eq_dec;
        specialize IHe with (2 := eq_refl);
        eapply exec.weaken; [ now apply IHe |];
        cbv beta;
        intros tr' m' l' Hw;
        fwd;
        eexists;
        ssplit;
        [ simpl; now fwd
        |
        | reflexivity
        | assumption ];
        intros lo Hlo;
        specialize Hwp1 with (1 := Hlo);
        inversion Hwp1;
        subst;
        repeat lazymatch goal with
        | h: existT _ _ _ = existT _ _ _ |- _ =>
            apply interp_type_eq in h
        end;
        subst.
      + (* OWNeg *)
        rewrite Properties.word.sub_0_l.
        apply RWord.
      + (* ONot *)
        rewrite <- Properties.word.ring_morph_sub.
        destruct (interp_expr lo e); apply RBool.
    - (* EBinop o e1 e2 *)
      destruct o; try easy.
      all:
        simpl in He';
        simpl;
        fwd;
        inversion He;
        apply Eqdep_dec.inj_pair2_eq_dec in H5 as [= ->]; try exact type_eq_dec;
        injection H6 as [= ->];
        apply Eqdep_dec.inj_pair2_eq_dec in H5 as [= ->]; try exact type_eq_dec;
        specialize IHe1 with (2 := eq_refl);
        specialize IHe2 with (2 := eq_refl);
        eapply exec.seq; [ now apply IHe1 |];
        cbv beta;
        intros tr' m' l' Hw;
        fwd;
        eapply exec.weaken; [ now apply IHe2 |];
        cbv beta;
        intros tr'' m'' l'' Hw';
        fwd;
        eexists;
        ssplit;
        [ simpl; fwd;
          apply eval_map_extends_locals with (l' := l'') in Hwp0;
          [| assumption];
          now rewrite Hwp0
        |
        | reflexivity
        | now apply extends_trans with l' ].
      1-9:
        intros lo Hlo;
        specialize Hwp1 with (1 := Hlo);
        assert (Hlo' : locals_relation lo l');
        [ now apply locals_relation_extends with (l := l) | ];
        specialize Hw'p1 with (1 := Hlo');
        inversion Hwp1; inversion Hw'p1;
        subst;
        repeat lazymatch goal with
        | h: existT _ _ _ = existT _ _ _ |- _ =>
            apply interp_type_eq in h
        end;
        subst;
        set (v1 := interp_expr _ e1);
        set (v2 := interp_expr _ e2).
      1-5:
        (* OWPlus, OWMinus, OWTimes, OWDivU, OWModU *)
        apply RWord.
      1-2:
        (* OAnd, OOr *)
        destruct v1, v2;
          simpl;
          apply RBool';
          apply word.unsigned_inj;
          simpl Z.b2z;
          try rewrite word.unsigned_and_nowrap;
          try rewrite word.unsigned_or_nowrap;
          now try rewrite word.unsigned_of_Z_0;
          try rewrite word.unsigned_of_Z_1.
      + (* OWLessU *)
        destruct (word.ltu v1 v2);
        apply RBool.
      + (* OWLessS *)
        destruct (word.lts v1 v2);
        apply RBool.
      + (* OEq *)
        destruct t;
        intros lo Hlo;
        specialize Hwp1 with (1 := Hlo);
        assert (Hlo' : locals_relation lo l');
        (now apply locals_relation_extends with (l := l)) ||
        specialize Hw'p1 with (1 := Hlo');
        try easy; unfold eqb_values.
        * (* TWord *)
          inversion Hwp1; inversion Hw'p1.
          repeat (repeat lazymatch goal with
          | h: existT _ _ _ = existT _ _ _ |- _ =>
              apply interp_type_eq in h
          end;
          subst).
          destruct (word.eqb _ _);
          apply RBool.
        * (* TBool *)
          inversion Hwp1; inversion Hw'p1.
          repeat (repeat lazymatch goal with
          | h: existT _ _ _ = existT _ _ _ |- _ =>
              apply interp_type_eq in h
          end;
          subst).
          set (b1 := interp_expr _ e1).
          set (b2 := interp_expr _ e2).
          destruct b1, b2.
          all:
            apply RBool';
            simpl;
            rewrite word.unsigned_eqb;
            try rewrite word.unsigned_of_Z_0;
            now try rewrite word.unsigned_of_Z_1.
  Qed.

End WithMap.

Compute (compile_expr (EAtom (AWord 4))).
Compute (compile_expr (EAtom (ABool true))).
Compute (compile_expr (EAtom (ABool false))).
Compute (compile_expr (EBinop OOr (EAtom (ABool true)) (EAtom (ABool false)))).
Compute (compile_expr (EBinop OWPlus (EAtom (AWord 1)) (EAtom (AWord 1)))).
