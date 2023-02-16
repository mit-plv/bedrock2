Require Import PyLevelLang.Language.
Require Import PyLevelLang.Interpret.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Tactics.Tactics.
Require Import Coq.Lists.List.
From Coq Require Import FunctionalExtensionality.

Local Open Scope Z_scope.

Section WithMap.
  Context {locals: map.map string {t & interp_type t}} {locals_ok: map.ok locals}.

  Fixpoint listify {t : type} (l : list (expr t)) : expr (TList t) :=
    match l with
    | nil => EAtom (ANil t)
    | x :: xs => EBinop (OCons t) x (listify xs)
    end.

  Lemma listify_correct (t : type) (l : locals) (xs : list (expr t)) :
    interp_expr l (listify xs) = map (interp_expr l) xs.
  Proof.
    induction xs; try easy.
    simpl.
    rewrite IHxs.
    reflexivity.
  Qed.

  Fixpoint reify (t : type) : interp_type t -> expr t :=
    match t in type return interp_type t -> expr t with
    | TInt => fun n => EAtom (AInt n)
    | TBool => fun b => EAtom (ABool b)
    | TString => fun s => EAtom (AString s)
    | TPair s t1 t2 => fun p => EBinop (OPair s t1 t2) (reify t1 (fst p)) (reify t2 (snd p))
    | TEmpty => fun _ => EAtom AEmpty
    | TList t => fun l => listify (map (reify t) l)
    end.

  Lemma reify_correct (t : type) (l : locals) (c : interp_type t) : interp_expr l (reify t c) = c.
  Proof.
    induction t; intros; try easy.
    - destruct c. simpl. rewrite IHt1. rewrite IHt2. reflexivity.
    - destruct c. reflexivity.
    - induction c.
      + reflexivity.
      + simpl. rewrite IHt. simpl in IHc. rewrite IHc. reflexivity.
  Qed.

  Fixpoint as_const {t : type} (e : expr t) : option (interp_type t) :=
    match e with
    | EAtom a => Some (interp_atom a)
    | EUnop o e1 => match as_const e1 with
                    | Some c1 => Some (interp_unop o c1)
                    | _ => None
                    end
    | EBinop o e1 e2 => match as_const e1, as_const e2 with
                        | Some c1, Some c2 => Some (interp_binop o c1 c2)
                        | _, _ => None
                        end
    | _ => None
    end.

  Lemma as_const_correct {t : type} (l : locals) (e : expr t) :
    forall c, as_const e = Some c -> interp_expr l e = c.
  Proof.
    generalize dependent l.
    induction e; intros; try easy; simpl in H.
    - injection H as H. apply H.
    - destruct (as_const e); try easy.
      injection H as H. rewrite <- H. simpl. apply f_equal, IHe. reflexivity.
    - destruct (as_const e1); destruct (as_const e2); try easy.
      injection H as H. rewrite <- H. simpl. rewrite IHe1 with (c:=i), IHe2 with (c:=i0); easy.
  Qed.

  Fixpoint constant_folding' {t : type} (e : expr t) : expr t * option (interp_type t) :=
    match e with
    | EVar _ x => (EVar _ x, None)
    | ELoc _ x => (ELoc _ x, None)
    | EAtom a => (EAtom a, Some (interp_atom a))
    | EUnop o e1 =>
        let (e1', v) := constant_folding' e1 in
        match v with
        | Some v' => let r := interp_unop o v' in (reify _ r, Some r)
        | _ => (EUnop o e1', None)
        end
    | EBinop o e1 e2 =>
        let (e1', v1) := constant_folding' e1 in
        let (e2', v2) := constant_folding' e2 in
        match v1, v2 with
        | Some v1', Some v2' => let r := interp_binop o v1' v2' in (reify _ r, Some r)
        | _, _ => (EBinop o e1' e2', None)
        end
    | EFlatmap e1 x e2 => (EFlatmap (fst (constant_folding' e1)) x (fst (constant_folding' e2)), None)
    | EIf e1 e2 e3 => (EIf (fst (constant_folding' e1)) (fst (constant_folding' e2)) (fst (constant_folding' e3)), None)
    | ELet x e1 e2 => (ELet x (fst (constant_folding' e1)) (fst (constant_folding' e2)), None)
    end.

  Lemma constant_folding'_snd_correct {t : type} (l : locals) (e : expr t) :
    forall c, snd (constant_folding' e) = Some c -> interp_expr l e = c.
  Proof.
    generalize dependent l.
    induction e; intros; simpl; try easy.

    - inversion H. reflexivity.

    - simpl in H.
      destruct (constant_folding' e). destruct o0; inversion H.
      rewrite (IHe l i); easy.

    - simpl in H.
      destruct (constant_folding' e1). destruct (constant_folding' e2). destruct o0; destruct o1; inversion H.
      rewrite (IHe1 l i), (IHe2 l i0); easy.
  Qed.

  Definition constant_folding {t : type} (e : expr t) : expr t := fst (constant_folding' e).

  Lemma constant_folding_correct {t : type} (l : locals) (e : expr t) :
    interp_expr l (constant_folding e) = interp_expr l e.
  Proof.
    generalize dependent l.
    unfold constant_folding.
    induction e; intros; simpl; try easy.

    - destruct (constant_folding' e) eqn:E. destruct o0; simpl.
      + rewrite reify_correct.
        f_equal.
        simpl in IHe.
        rewrite (constant_folding'_snd_correct l e i); try easy.
        rewrite E. reflexivity.
      + simpl in IHe. rewrite IHe. reflexivity.

    - destruct (constant_folding' e1) eqn:E1. destruct (constant_folding' e2) eqn:E2. destruct o0; destruct o1; simpl.
      + rewrite reify_correct.
        f_equal.
        * simpl in IHe1.
          rewrite (constant_folding'_snd_correct l e1 i); try easy. rewrite E1. reflexivity.
        * simpl in IHe2.
          rewrite (constant_folding'_snd_correct l e2 i0); try easy. rewrite E2. reflexivity.

      + rewrite IHe1, IHe2. reflexivity.
      + rewrite IHe1, IHe2. reflexivity.
      + rewrite IHe1, IHe2. reflexivity.

    - rewrite IHe1.
      assert (H: (fun y : interp_type t => interp_expr (set_local l x y) (fst (constant_folding' e2)))
      = (fun y : interp_type t => interp_expr (set_local l x y) e2)).
      { apply functional_extensionality. intros. apply IHe2. }
      rewrite <- H.
      reflexivity.

    - rewrite IHe1, IHe2, IHe3. reflexivity.

    - rewrite IHe1, IHe2. reflexivity.
  Qed.

  Fixpoint branch_elim {t : type} (e : expr t) : expr t :=
    match e in expr t' return expr t' with
    | EVar _ x => EVar _ x
    | ELoc _ x => ELoc _ x
    | EAtom a => EAtom a
    | EUnop o e1 => EUnop o (branch_elim e1)
    | EBinop o e1 e2 => EBinop o (branch_elim e1) (branch_elim e2)
    | EIf e1 e2 e3 => 
        let e1' := branch_elim e1 in
        let e2' := branch_elim e2 in
        let e3' := branch_elim e3 in
        match as_const e1' with
        | Some true => e2'
        | Some false => e3'
        | _ => EIf e1' e2' e3'
        end
    | EFlatmap e1 x e2 => EFlatmap (branch_elim e1) x (branch_elim e2)
    | ELet x e1 e2 => ELet x (branch_elim e1) (branch_elim e2)
    end.

  Lemma branch_elim_correct {t : type} (l : locals) (e : expr t) 
    : interp_expr l (branch_elim e) = interp_expr l e.
  Proof.
    generalize dependent l.
    induction e; simpl; intros; 
    try rewrite <- IHe; try rewrite <- IHe1; try rewrite <- IHe2; try rewrite <- IHe3; 
    try reflexivity.

    - assert (H:(fun y : interp_type t => interp_expr (set_local l x y) (branch_elim e2)) 
              = (fun y => interp_expr (set_local l x y) e2)).
      { apply functional_extensionality. intros. rewrite IHe2. reflexivity. }
      rewrite H. reflexivity.

    - destruct (as_const (branch_elim e1)) eqn:H; try easy.
      destruct i; rewrite (as_const_correct l (branch_elim e1) _ H); reflexivity.
  Qed.

  Fixpoint is_name_used {t : type} (x : string) (e : expr t) : bool :=
    match e with
    | EVar _ x' => eqb x' x
    | ELoc _ x' => eqb x' x
    | EAtom _ => false
    | EUnop _ e1 => is_name_used x e1
    | EBinop _ e1 e2 => is_name_used x e1 || is_name_used x e2
    | EFlatmap e1 x' e2 => eqb x' x || is_name_used x e1 || is_name_used x e2
    | EIf e1 e2 e3 => is_name_used x e1 || is_name_used x e2 || is_name_used x e3
    | ELet x' e1 e2 => eqb x' x || is_name_used x e1 || is_name_used x e2
    end.

  Lemma set_local_comm_diff {tx ty : type} (x y : string) (vx : interp_type tx) (vy : interp_type ty) (l : locals)
    : x <> y -> set_local (set_local l y vy) x vx = set_local (set_local l x vx) y vy.
  Proof.
    unfold set_local.
    intros.
    apply map.map_ext.
    intros.
    rewrite 4 map.get_put_dec.
    repeat destruct_one_match; try rewrite map.get_put_diff; tauto.
  Qed.

  Lemma is_name_used_correct {t : type} {t' : type} (l : locals) (e : expr t) (x : string):
    forall y : interp_type t', is_name_used x e = false -> interp_expr l e = interp_expr (set_local l x y) e.
  Proof.
    generalize dependent l.
    induction e; intros; simpl in H; simpl.
    
    - unfold get_local, set_local.
      rewrite map.get_put_diff; try easy. 
      apply eqb_neq, H.

    - unfold get_local, set_local.
      rewrite map.get_put_diff; try easy.
      apply eqb_neq, H.

    - reflexivity.

    - rewrite <- IHe; easy.

    - rewrite <- IHe1, <- IHe2; destruct (is_name_used x e2); destruct (is_name_used x e1); try easy.

    - destruct (is_name_used x e1); destruct (is_name_used x e2); destruct (eqb x0 x) eqn:Hx; simpl in H; try easy.
      assert (Hf:(fun y0 : interp_type t => interp_expr (set_local l x0 y0) e2)
              = (fun y0 : interp_type t => interp_expr (set_local (set_local l x y) x0 y0) e2)).
              { apply functional_extensionality. intros. rewrite set_local_comm_diff.
                + apply IHe2. reflexivity.
                + apply eqb_neq, Hx.
              }
              rewrite Hf. rewrite <- IHe1; easy. 

    - rewrite <- IHe1, <- IHe2, <- IHe3;
      destruct (is_name_used x e1); 
      destruct (is_name_used x e2);
      destruct (is_name_used x e3);
      easy.

    - rewrite set_local_comm_diff;
      destruct (is_name_used x e1); 
      destruct (is_name_used x e2);
      destruct (eqb x0 x) eqn:Hx;
      try easy.
      + rewrite <- IHe1, <- IHe2; easy.
      + apply eqb_neq, Hx.
  Qed.

  Fixpoint unused_name_elim {t : type} (e : expr t) : expr t :=
    match e with
    | EVar _ x => EVar _ x
    | ELoc _ x => ELoc _ x
    | EAtom a => EAtom a
    | EUnop o e1 => EUnop o (unused_name_elim e1)
    | EBinop o e1 e2 => EBinop o (unused_name_elim e1) (unused_name_elim e2)
    | EFlatmap e1 x e2 => EFlatmap (unused_name_elim e1) x (unused_name_elim e2)
    | EIf e1 e2 e3 => EIf (unused_name_elim e1) (unused_name_elim e2) (unused_name_elim e3)
    | ELet x e1 e2 => if is_name_used x e2 then ELet x (unused_name_elim e1) (unused_name_elim e2) else unused_name_elim e2
    end.
  
  Lemma unused_name_elim_correct {t : type} (l : locals) (e : expr t) 
    : interp_expr l (unused_name_elim e) = interp_expr l e.
  Proof.
    generalize dependent l.
    induction e; try easy; intros; simpl.

    - rewrite IHe. reflexivity.

    - rewrite IHe1, IHe2. reflexivity.

    - assert (H:(fun y : interp_type t => interp_expr (set_local l x y) (unused_name_elim e2)) 
              = (fun y => interp_expr (set_local l x y) e2)).
      { apply functional_extensionality. intros. rewrite IHe2. reflexivity. }
      rewrite IHe1, H. reflexivity.

    - rewrite IHe1, IHe2, IHe3. reflexivity.

    - destruct (is_name_used x e2) eqn:E.
      + simpl. rewrite IHe1, IHe2. reflexivity.
      + rewrite <- is_name_used_correct; easy.
  Qed.
End WithMap.
