Require Import PyLevelLang.Language.
Require Import PyLevelLang.Interpret.
Require Import PyLevelLang.Elaborate.
Require bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import coqutil.Datatypes.Result.
Import ResultMonadNotations.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
Require Import coqutil.Byte coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Word.Properties.

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
  | OSnd _ _ _ =>
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
  | ORange =>
      error:("unimplemented")
  end.

Fixpoint compile_expr {t : type} (e : expr t) : result Syntax.expr :=
  match e with
  | EAtom a => compile_atom a
  | EUnop o e1 =>
      f <- compile_unop o;;
      e1' <- compile_expr e1;;
      Success (f e1')
  | EBinop o e1 e2 =>
      f <- compile_binop o;;
      e1' <- compile_expr e1;;
      e2' <- compile_expr e2;;
      Success (f e1' e2')
  | _ => error:("unimplemented")
  end.

Definition compile_expr' {t : type} (e : expr t) : result (Syntax.cmd * Syntax.expr) :=
  e' <- compile_expr e;;
  Success (Syntax.cmd.skip, e').

Section WithMap.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {tenv : map.map string (type * bool)} {tenv_ok : map.ok tenv}.
  Context {locals: map.map string {t & interp_type (word := word) t}} {locals_ok: map.ok locals}.
  Context {locals': map.map string word} {locals'_ok: map.ok locals}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: ExtSpec}.

  Inductive value_relation : forall {t : type}, interp_type t -> word -> Prop :=
    | RWord (w : word) : value_relation (t := TWord) w w
    | RBool (b : bool) : value_relation (t := TBool) b (word.of_Z (Z.b2z b)).

  Lemma RBool' (b : bool) (w : word) : w = word.of_Z (Z.b2z b) ->
    value_relation (t := TBool) b w.
  Proof.
    intros [= ->].
    apply RBool.
  Qed.

  (* Prove lemmas for opposite directions *)

  (* Definition compile_value {t : type} (v : interp_type t) : result word := *)
  (*   match t as t' return interp_type t' -> _ with *)
  (*   | TInt => fun v => Success (word.of_Z v) *)
  (*   | TBool => fun v => Success (word.of_Z (Z.b2z v)) *)
  (*   | _ => fun _ => error:("unimplemented") *)
  (*   end v. *)

  Lemma interp_type_eq : forall {t : type} (e : expr t) (w : interp_type t),
    (existT interp_type t w =
    existT interp_type t (interp_expr (locals := locals) map.empty e)) ->
    (interp_expr map.empty e) = w.
  Proof.
    intros.
    inversion_sigma.
    rewrite <- Eqdep_dec.eq_rect_eq_dec in H0.
    * easy.
    * exact type_eq_dec.
  Qed.

  Lemma compile_correct : forall {t} (e : expr t) (e' : Syntax.expr),
    wf map.empty e ->
    compile_expr e = Success e' -> exists w,
    eval_expr_old map.empty map.empty e' = Some w /\
    value_relation (interp_expr map.empty e) w.
  Proof.
    intros t. induction e; intros e' He He'; try easy.
    - (* EAtom a *)
      destruct a; try easy.
      + (* AInt n *)
        injection He' as [= <-].
        simpl.
        exists (word.of_Z (word.wrap n)).
        split; rewrite <- word.unsigned_of_Z, word.of_Z_unsigned; try easy.
        apply RWord.
      + (* ABool b *)
        injection He' as [= <-].
        simpl.
        exists (word.of_Z (Z.b2z b)).
        split; try easy.
        apply RBool.
    - (* EUnop o e *)
      destruct o; try easy.
      all:
        simpl in He';
        simpl;
        fwd;
        inversion He;
        apply Eqdep_dec.inj_pair2_eq_dec in H4 as [= ->]; try exact type_eq_dec;
        specialize IHe with (1 := H2) (2 := eq_refl);
        fwd;
        eexists.
      + (* OWNeg *)
        split.
        * simpl. fwd.
          now rewrite Properties.word.sub_0_l.
        * inversion IHep1. rewrite H6 in H5.
          rewrite (interp_type_eq _ _ H5).
          apply RWord.
      + (* ONot *)
        split.
        * simpl. now fwd.
        * inversion IHep1.
          rewrite (interp_type_eq _ _ H5).
          rewrite <- Properties.word.ring_morph_sub.
          destruct b; apply RBool.
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
        specialize IHe1 with (1 := H3) (2 := eq_refl);
        specialize IHe2 with (1 := H7) (2 := eq_refl);
        fwd;
        eexists.
      1, 2, 3, 4, 5:
        (* OWPlus, OWMinus, OWTimes, OWDivU, OWModU *)
        split;
        [ simpl; now fwd
        | inversion IHe1p1; inversion IHe2p1;
          rewrite H6 in H5; rewrite H9 in H8;
          rewrite (interp_type_eq _ _ H5);
          rewrite (interp_type_eq _ _ H8);
          apply RWord ].
      1, 2:
        (* OAnd, OOr *)
        split;
        [ simpl; now fwd
        | inversion IHe1p1; inversion IHe2p1;
          rewrite (interp_type_eq _ _ H5);
          rewrite (interp_type_eq _ _ H8);
          destruct b, b0;
            simpl;
            apply RBool';
            apply word.unsigned_inj;
            simpl Z.b2z;
            try rewrite word.unsigned_and_nowrap;
            try rewrite word.unsigned_or_nowrap;
            now try rewrite word.unsigned_of_Z_0;
            try rewrite word.unsigned_of_Z_1 ].
      1, 2:
        (* OWLessU, OWLessS *)
        split;
        [ simpl; now fwd
        | inversion IHe1p1; inversion IHe2p1;
          rewrite (interp_type_eq _ _ H5);
          rewrite (interp_type_eq _ _ H8);
          rewrite H6, H9;
          (destruct (word.ltu w0 w); apply RBool)
          || (destruct (word.lts w0 w); apply RBool) ].
      (* OEq *)
      + split.
        * simpl; now fwd.
        * destruct t; try easy; unfold eqb_values.
          -- (* TWord *)
             inversion IHe1p1. inversion IHe2p1.
             rewrite (interp_type_eq _ _ H5).
             rewrite (interp_type_eq _ _ H8).
             rewrite H6, H9.
             destruct (word.eqb w0 w); apply RBool.
          -- (* TBool *)
             inversion IHe1p1. inversion IHe2p1.
             rewrite (interp_type_eq _ _ H5).
             rewrite (interp_type_eq _ _ H8).
             rewrite H6, H9.
             destruct b, b0.
             all:
               destruct (word.eqb w0 w) eqn:Heq; try now apply RBool'.
             1, 4: rewrite <- H6, <- H9 in Heq; now apply word.eqb_false in Heq.
             all:
               rewrite <- H6, <- H9 in Heq; apply word.eqb_true in Heq;
               simpl in Heq; (rewrite Heq || rewrite <- Heq); apply RBool.
  Qed.

  Lemma compile'_correct : forall {t} (e : expr t) (c : Syntax.cmd) (e' : Syntax.expr),
    wf map.empty e ->
    compile_expr' e = Success (c, e') -> forall tr m l mc,
    exec (map.empty) c tr m l mc (fun tr' m' l' mc' => exists (w : word),
      eval_expr_old m' l' e' = Some w /\
      value_relation (interp_expr map.empty e) w
    ).
  Proof.
    intros t e c e' He He' tr m l mc.
    unfold compile_expr' in He'.
    fwd.
    apply exec.skip.
    assert (m = map.empty) as [= ->].
    { admit. }
    assert (l = map.empty) as [= ->].
    { admit. }
    now apply compile_correct.
  Admitted.

End WithMap.

Compute (compile_expr (EAtom (AWord 4))).
Compute (compile_expr (EAtom (ABool true))).
Compute (compile_expr (EAtom (ABool false))).
Compute (compile_expr (EBinop OOr (EAtom (ABool true)) (EAtom (ABool false)))).
Compute (compile_expr (EBinop OWPlus (EAtom (AWord 1)) (EAtom (AWord 1)))).
