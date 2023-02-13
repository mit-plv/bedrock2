Require Import PyLevelLang.Language.
Require Import PyLevelLang.Interpret.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
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


  Fixpoint constant_folding {t : type} (e : expr t) : expr t :=
    match e with
    | EVar _ x => EVar _ x
    | ELoc _ x => ELoc _ x
    | EAtom a => EAtom a
    | EUnop o e1 => 
        let e1' := constant_folding e1 in 
        match as_const e1' with
        | Some c => reify _ (interp_unop o c)
        | _ => EUnop o e1'
        end
    | EBinop o e1 e2 => 
        let e1' := constant_folding e1 in
        let e2' := constant_folding e2 in
        match as_const e1', as_const e2' with
        | Some c1, Some c2 => reify _ (interp_binop o c1 c2)
        | _, _ => EBinop o e1' e2'
        end
    | EFlatmap e1 x e2 => EFlatmap (constant_folding e1) x (constant_folding e2)
    | EIf e1 e2 e3 =>  EIf (constant_folding e1) (constant_folding e2) (constant_folding e3)
    | ELet x e1 e2 => ELet x (constant_folding e1) (constant_folding e2)
    end.

  Lemma constant_folding_correct {t : type} (l : locals) (e : expr t) 
    :  interp_expr l (constant_folding e) = interp_expr l e.
  Proof.
    generalize dependent l.
    induction e; intros; simpl; try easy.

      Ltac transforms := repeat (rewrite reify_correct || rewrite listify_correct || reflexivity).

    - destruct o; simpl; destruct (as_const (constant_folding e)) eqn:H;
      rewrite <- IHe;
      try rewrite (as_const_correct l (constant_folding e) _ H);
      transforms.

    - destruct o; simpl; try easy;
      destruct (as_const (constant_folding e1)) eqn:H1;
      destruct (as_const (constant_folding e2)) eqn:H2;
      rewrite <- IHe1, <- IHe2;
      simpl;
      try rewrite (as_const_correct l (constant_folding e1) _ H1);
      try rewrite (as_const_correct l (constant_folding e2) _ H2);
      try transforms;
      try rewrite map_map;
      try rewrite (functional_extensionality (fun x => interp_expr l (reify t x)) (fun x => x) (reify_correct t l));
      try rewrite map_id;
      reflexivity.

    - assert (H : (fun y : interp_type t => interp_expr (set_local l x y) (constant_folding e2)) 
              = (fun y => interp_expr (set_local l x y) e2)).
      { apply functional_extensionality. intros. rewrite IHe2. reflexivity. }
      rewrite IHe1, H. reflexivity.

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

End WithMap.
