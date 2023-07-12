Require Import PyLevelLang.Language.
Require Import PyLevelLang.Interpret.
Require Import PyLevelLang.Elaborate.
Require bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import coqutil.Datatypes.Result.
Import ResultMonadNotations.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Map.MapEauto.
Require Import coqutil.Byte coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Word.Properties.
Require Import compiler.NameGen.

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

Section Map.
  Context {key value : Type} {map : map.map key value} {map_ok : map.ok map}.
  Definition map_values (m : map) : list value := map.fold (fun acc k v => cons v acc) nil m.
End Map.

Section NameGen.
  Context {NGstate : Type}
          {NG : NameGen string NGstate}
          {namemap : map.map string string}
          {namemap_ok : map.ok namemap}.

  Fixpoint compile_expr {t : type} (e : expr t) (nm : namemap) (st : NGstate) :
    result (Syntax.cmd * Syntax.expr * namemap * NGstate) :=
    match e with
    | EVar _ x | ELoc _ x =>
        match map.get nm x with
        | Some x' =>
            Success (Syntax.cmd.skip, Syntax.expr.var x', nm, st)
        | None =>
            error:("variable x not mapped in target language (unreachable)")
        end
    | EAtom a =>
        e' <- compile_atom a;;
        Success (Syntax.cmd.skip, e', nm, st)
    | EUnop o e1 =>
        f <- compile_unop o;;
        '(c1, e1', _, _) <- compile_expr e1 nm st;;
        Success (c1, f e1', nm, st)
    | EBinop o e1 e2 =>
        f <- compile_binop o;;
        '(c1, e1', _, _) <- compile_expr e1 nm st;;
        '(c2, e2', _, _) <- compile_expr e2 nm st;;
        Success (Syntax.cmd.seq c1 c2, f e1' e2', nm, st)
    | ELet x e1 e2 =>
        '(c1, e1', _, _) <- compile_expr e1 nm st;;
        '(c2, e2', _, _) <- compile_expr e2 nm st;;
        let '(x', st') := genFresh st in
        let nm' := map.put nm x x' in
        Success (Syntax.cmd.seq c1 (Syntax.cmd.seq (Syntax.cmd.set x' e1') c2), e2', nm', st')
    | _ => error:("unimplemented")
    end.
End NameGen.

Section WithMap.
  Context {width : Z} {BW : Bitwidth width} {word : word.word width} {mem : map.map word byte}
          {word_ok : word.ok word} {mem_ok : map.ok mem}
          {tenv : map.map string (type * bool)} {tenv_ok : map.ok tenv}
          {locals : map.map string {t & interp_type (word := word) t}} {locals_ok : map.ok locals}
          {locals' : map.map string word} {locals'_ok : map.ok locals'}
          {env : map.map String.string (list String.string * list String.string * Syntax.cmd)}
          {ext_spec : ExtSpec}
          {NGstate : Type}
          {NG : NameGen string NGstate}
          {namemap : map.map string string}
          {namemap_ok : map.ok namemap}.

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
  Definition locals_relation (lo : locals) (l : locals') (nm : namemap) : Prop :=
    map.forall_keys (fun x =>
    match map.get lo x, map.get nm x with
    | Some (existT _ _ val), Some x' =>
        match map.get l x' with
        | Some val' => value_relation val val'
        | None => False
        end
    | _, _ => True
    end) lo.

  Lemma locals_relation_extends (lo : locals) (l l' : locals') (nm : namemap) :
    map.extends l' l -> locals_relation lo l nm -> locals_relation lo l' nm.
  Proof.
  Admitted.
  (*   intros Hex. *)
  (*   apply weaken_forall_keys. *)
  (*   intros key Hl. *)
  (*   destruct map.get as [s|]; try easy. *)
  (*   destruct s as [t val]. *)
  (*   destruct (map.get l key) as [v|] eqn:E. *)
  (*   - apply (Properties.map.extends_get (m1 := l) (m2 := l')) in E; *)
  (*     [| assumption]. *)
  (*     now rewrite E. *)
  (*   - destruct Hl. *)
  (* Qed. *)

  Lemma locals_relation_get (lo : locals) (l : locals') (nm : namemap) :
    locals_relation lo l nm ->
    forall (x x' : string) (t : type) (s : {t & interp_type t}),
    map.get lo x = Some s ->
    map.get nm x = Some x' -> exists (w : word),
    map.get l x' = Some w.
  Proof.
  Admitted.
  (*   intros Hl x t s Hs. *)
  (*   unfold locals_relation, map.forall_keys in Hl. *)
  (*   specialize Hl with (1 := Hs). *)
  (*   rewrite Hs in Hl. *)
  (*   destruct map.get. *)
  (*   - now exists r. *)
  (*   - destruct s, Hl. *)
  (* Qed. *)

  Lemma locals_relation_put (lo : locals) (l : locals') (nm : namemap) :
    locals_relation lo l nm ->
    forall (x x' : string) (t : type) (v : interp_type t) (w : word),
    value_relation v w ->
    map.get nm x = Some x' ->
    locals_relation (set_local lo x v) (map.put l x' w) nm.
  Proof.
  Admitted.
  (*   intros Hl x t v w Hvw. *)
  (*   unfold locals_relation, map.forall_keys, set_local. *)
  (*   intros x' [t' v']. *)
  (*   repeat rewrite Properties.map.get_put_dec. *)
  (*   destruct (x =? x')%string. *)
  (*   - easy. *)
  (*   - intros Hx'. fwd. *)
  (*     unfold locals_relation, map.forall_keys in Hl. *)
  (*     specialize Hl with (1 := Hx'). *)
  (*     rewrite Hx' in Hl. *)
  (*     assumption. *)
  (* Qed. *)

  Definition tenv_relation (G : tenv) (lo : locals) : Prop :=
    map.forall_keys (fun key =>
    match map.get G key with
    | Some (t, _) => match map.get lo key with
                     | Some (existT _ t' _) => t = t'
                     | None => False
                     end
    | None => True
    end) G.

  Lemma tenv_relation_get (G : tenv) (lo : locals) :
    tenv_relation G lo -> forall (x : string) (t : type) (b : bool),
    map.get G x = Some (t, b) -> exists (v : interp_type t),
    map.get lo x = Some (existT _ t v).
  Proof.
    intros Hlo x t b Htb.
    unfold tenv_relation, map.forall_keys in Hlo.
    specialize Hlo with (1 := Htb).
    rewrite Htb in Hlo.
    destruct map.get.
    - destruct s. subst. now exists i.
    - destruct Hlo.
  Qed.

  Lemma tenv_relation_put (G : tenv) (lo : locals) :
    tenv_relation G lo ->
    forall (x : string) (t : type) (b : bool) (v : interp_type t),
    tenv_relation (map.put G x (t, b)) (set_local lo x v).
  Proof.
    intros Hlo x t b v.
    unfold tenv_relation, map.forall_keys, set_local.
    intros x' [t' b'].
    repeat rewrite Properties.map.get_put_dec.
    destruct (x =? x')%string.
    - easy.
    - intros Hx'. fwd.
      unfold tenv_relation, map.forall_keys in Hlo.
      specialize Hlo with (1 := Hx').
      rewrite Hx' in Hlo.
      assumption.
  Qed.

  Lemma proj_expected_existT (t : type) (v : interp_type t) :
    v = proj_expected t (existT interp_type t v).
  Proof.
    unfold proj_expected.
    simpl.
    case type_eq_dec eqn:E; [| easy].
    unfold cast.
    rewrite (Eqdep_dec.UIP_dec type_eq_dec e eq_refl).
    trivial.
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

  (* Lemma compile_nm_extends : *)
  (*   forall {t} (e : expr t) (c : Syntax.cmd) (e' : Syntax.expr) *)
  (*   (nm nm' : namemap), *)
  (*   compile_expr e nm = Success (c, e', nm') -> *)
  (*   map.extends nm' nm. *)
  (* Proof. *)
  (*   intros t. induction e; intros c e' nm nm' He'; try easy. *)
  (*   all: try (unfold compile_expr in He'; now fwd). *)
  (*   unfold compile_expr in He'. *)
  (*   fold (compile_expr (t := t1)) in He'. *)
  (*   fold (compile_expr (t := t2)) in He'. *)
  (*   fwd. *)
  (*   unfold map.extends. *)
  (*   intros x0 w Hw. *)
  (*   rewrite Properties.map.get_put_dec. *)
  (*   destruct (x =? x0)%string; [| assumption]. *)
  (*   specialize genFresh_spec with (1 := E1) as H. *)

  Lemma compile_locals_relation :
    forall {t} (e : expr t) (c : Syntax.cmd) (e' : Syntax.expr)
    (lo : locals) (l : locals') (nm nm' : namemap) (st st' : NGstate),
    locals_relation lo l nm ->
    compile_expr e nm st = Success (c, e', nm', st') ->
    locals_relation lo l nm'.
  Proof.
  Admitted.

  Lemma compile_correct :
    forall {t} (e : expr t) (c : Syntax.cmd) (e' : Syntax.expr)
    (G : tenv) (lo : locals) (nm nm' : namemap) (st st' : NGstate),
    tenv_relation G lo ->
    wf G e ->
    compile_expr e nm st = Success (c, e', nm', st') -> forall tr m l,
    locals_relation lo l nm ->
    exec map.empty c tr m l (fun tr' m' l' => exists (w : word),
      eval_expr m' l' e' = Some w /\
      value_relation (interp_expr lo e) w /\
      m' = m /\
      map.extends l' l
    ).
  Proof.
    intros t. induction e; intros c e' G lo nm nm' st st' Hlo He He' tr m l Hl; try easy.
    1-2:
      (* EVar x, ELoc x *)
      unfold compile_expr in He';
      fwd;
      simpl;
      rename s into x';
      apply exec.skip;
      inversion_clear He;
      destruct (tenv_relation_get _ lo Hlo _ _ _ H) as [v Hv];
      destruct (locals_relation_get _ l _ Hl  _ x' t _ Hv) as [w Hw]; [easy |];
      exists w;
      ssplit; try easy;
      unfold get_local;
      rewrite Hv;
      unfold locals_relation, map.forall_keys in Hl;
      specialize Hl with (1 := Hv);
      rewrite Hv, E, Hw in Hl;
      now rewrite <- proj_expected_existT.
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
        apply RWord.
      + (* ABool b *)
        injection E as [= <-].
        simpl.
        exists (word.of_Z (Z.b2z b)).
        ssplit; try easy.
        apply RBool.
    - (* EUnop o e *)
      destruct o; try easy.
      all:
        simpl in He';
        simpl;
        fwd;
        inversion He;
        apply Eqdep_dec.inj_pair2_eq_dec in H4 as [= ->]; try exact type_eq_dec;
        specialize IHe with (1 := Hlo) (2 := H2) (3 := E);
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
        inversion Hwp1;
        subst;
        repeat (repeat lazymatch goal with
        | h: existT _ _ _ = existT _ _ _ |- _ =>
            apply interp_type_eq in h
        end;
        subst).
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
        specialize IHe1 with (1 := Hlo) (2 := H3) (3 := E);
        specialize IHe2 with (1 := Hlo) (2 := H7) (3 := E0);
        eapply exec.seq; [ now apply IHe1 |];
        cbv beta;
        intros tr' m' l' Hw;
        fwd;
        eapply exec.weaken; [
          apply IHe2;
          assumption || now apply locals_relation_extends with (l := l)
        |];
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
    - (* ELet x e1 e2 *)
      unfold compile_expr in He'.
      fold (compile_expr (t := t1)) in He'.
      fold (compile_expr (t := t2)) in He'.
      fwd;
      rename e into e1', e' into e2';
      rename c0 into c1, c1 into c2;
      rename r into nm1, r0 into nm2;
      rename s into x', E1 into En;
      rename E into E1, E0 into E2.
      inversion He;
      repeat lazymatch goal with
      | h: existT _ _ _ = existT _ _ _ |- _ =>
          apply Eqdep_dec.inj_pair2_eq_dec in h as [= ->]; try exact type_eq_dec
      end;
      subst;
      rename H3 into He1, H6 into He2.

      eapply exec.seq.
      { apply IHe1 with (1 := Hlo) (2 := He1) (3 := E1) (4 := Hl). }
      cbv beta.
      intros tr' m' l' Hw.
      fwd.

      apply exec.seq with (mid := fun tr'' m'' l'' => m'' = m /\ l'' = map.put l' x' w).
      {
        eapply exec.set.
        + exact Hwp0.
        + now split.
      }
      intros tr'' m'' l'' Hw'.
      fwd.
      eassert (H : interp_expr lo (ELet x e1 e2) = interp_expr _ _) by now simpl.
      rewrite H. clear H.

      eapply exec.weaken.
      {
        apply IHe2 with (2 := He2) (3 := E2) (lo := (set_local lo x (interp_expr lo e1))).
        + now apply tenv_relation_put.
        + admit.
        (* + apply locals_relation_put. *)
        (*   * now apply locals_relation_extends with l. *)
        (*   * assumption. *)
        (*   * *)
      }
      cbv beta.
      intros tr''' m''' l''' [w0 H].
      fwd.
      exists w0. ssplit.
      + easy.
      + exact Hp1.
      + reflexivity.
      + apply extends_trans with (map.put l' x' w). { assumption. }
        apply put_extends_l. 2: assumption.
        admit.
  Admitted.

End WithMap.

Compute (compile_expr (EAtom (AWord 4))).
Compute (compile_expr (EAtom (ABool true))).
Compute (compile_expr (EAtom (ABool false))).
Compute (compile_expr (EBinop OOr (EAtom (ABool true)) (EAtom (ABool false)))).
Compute (compile_expr (EBinop OWPlus (EAtom (AWord 1)) (EAtom (AWord 1)))).
