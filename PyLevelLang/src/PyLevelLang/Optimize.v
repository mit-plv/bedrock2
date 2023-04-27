Require Import Lia.
Require Import Coq.Program.Equality.
Require Import PyLevelLang.Language.
Require Import PyLevelLang.Interpret.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Tactics.Tactics.
Require Import Coq.Lists.List.
From Coq Require Import FunctionalExtensionality.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma length_eval_range : forall l s, length (eval_range s l) = l.
Proof.
  induction l; simpl; auto.
Qed.
  
Section WithMap.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {locals: map.map string {t & interp_type (width := width) t}} {locals_ok: map.ok locals}.

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
    | TWord => fun w => EAtom (AWord (word.unsigned w))
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
    - apply word.of_Z_unsigned.
    - destruct c. simpl. rewrite IHt1. rewrite IHt2. reflexivity.
    - destruct c. reflexivity.
    - induction c.
      + reflexivity.
      + simpl. rewrite IHt. simpl in IHc. rewrite IHc. reflexivity.
  Qed.

  Definition invert_atom {t : type} (e : expr t) : option (interp_type t) :=
    match e with
    | EAtom a => Some (interp_atom a)
    | _ => None
    end.

  Lemma invert_atom_correct {t : type} (l : locals) (e : expr t) :
    forall c, invert_atom e = Some c -> interp_expr l e = c.
  Proof.
    intros.
    destruct e; inversion H.
    simpl.
    reflexivity.
  Qed.

  Definition as_const {t : type} (e : expr t) : option (interp_type t) :=
    match e with
    | EAtom a => Some (interp_atom a)
    | EUnop o e1 => match invert_atom e1 with
                    | Some c1 => Some (interp_unop o c1)
                    | _ => None
                    end
    | EBinop o e1 e2 => match invert_atom e1, invert_atom e2 with
                        | Some c1, Some c2 => Some (interp_binop o c1 c2)
                        | _, _ => None
                        end
    | EIf a e1 e2 => match invert_atom a with
                     | Some c1 => if c1 then invert_atom e1 else invert_atom e2
                     | _ => None
                     end
    | _ => None
    end.

  Lemma as_const_correct {t : type} (l : locals) (e : expr t) :
    forall c, as_const e = Some c -> interp_expr l e = c.
  Proof.
    destruct e; simpl; intros; try solve [inversion H]; auto.
    - inversion H. reflexivity.
    - destruct e; try inversion H. reflexivity.
    - destruct e1; destruct e2; try inversion H. reflexivity.
    - dependent induction e1; simpl; simpl in *; try solve [inversion H];
      dependent induction a; simpl; simpl in *; try solve [inversion H]; 
      destruct b; simpl; apply invert_atom_correct; apply H.
  Qed.

  Definition constfold_head {t} (e : expr t) : expr t :=
    match t with
    | TInt | TBool | TString | TEmpty => match as_const e with
                                         | Some v => reify _ v
                                         | _ => e
                                         end
    | _ => e
    end.

  Lemma constfold_head_correct l {t} e :
    interp_expr l (@constfold_head t e) = interp_expr l e.
  Proof.
    cbv [constfold_head].
    repeat destruct_one_match; auto; try erewrite reify_correct, as_const_correct; auto.
  Qed.

  Fixpoint eLength {t : type} (e : expr (TList t)) : expr TInt :=
    match e with
    | EBinop (OCons t') eh et => EBinop OPlus (EAtom (AInt 1)) (eLength et)
    | EBinop ORange s e => constfold_head (EIf (constfold_head (EBinop OLess e s)) (EAtom (AInt 0)) (constfold_head (EBinop OMinus e s)))
    | _ => match invert_atom e with
           | Some nil => EAtom (AInt 0)
           | _ => EUnop (OLength _) e
           end
    end.

  Lemma eLength_correct {t : type} (l : locals) (e : expr (TList t)) :
    interp_expr l (eLength e) = interp_expr l (EUnop (OLength t) e).
  Proof.
    admit.
  Admitted.
    (* dependent induction e; cbn [eLength]; try reflexivity. *)
    (* - case invert_atom eqn:?; trivial. destruct i; trivial. *)
    (*   apply invert_atom_correct with (l:=l) in Heqo. *)
    (*   cbn in *. rewrite Heqo. reflexivity. *)
    (* - dependent induction o; cbn [invert_atom]; trivial. *)
    (*   + cbn [interp_expr interp_binop interp_unop interp_atom Datatypes.length]. *)
    (*     rewrite IHe2; trivial. *)
    (*     cbn [interp_expr interp_binop interp_unop interp_atom Datatypes.length]. *)
    (*     lia. *)
    (*   + repeat (rewrite constfold_head_correct; cbn [interp_expr interp_binop interp_unop interp_atom Datatypes.length]). *)
    (*     destruct_one_match; rewrite length_eval_range; lia. *)
  (* Qed. *)

  Definition invert_EPair {X A B} (e : expr (TPair X A B)) : option (expr A * expr B) :=
    match e in expr t
    return option match t with TPair _ A' B' => expr A' * expr B' | _ => Empty_set end
    with @EBinop _a _b _ab op e1 e2 =>
       match op in binop a b t
       return expr a -> expr b -> option match t with TPair _ A' B' => expr A' * expr B' | _ => Empty_set end
       with OPair s a b => fun e1' e2' => Some (e1', e2') | _ => fun _ _ => None
       end e1 e2
    | _ => None end.

  (* Partial evaluation happens before constant folding *)
  Definition eUnop {t1 t2 : type} (o : unop t1 t2) (e : expr t1) : expr t2 :=
    constfold_head (
    match o in unop t1 t2 return expr t1 -> expr t2 with
    | OLength t => eLength
    | OFst s t1 t2 as o => fun e => match invert_EPair e with Some (x, _) => x | _ => EUnop o e end
    | OSnd s t1 t2 as o => fun e => match invert_EPair e with Some (_, x) => x | _ => EUnop o e end
    | o => EUnop o
    end e).

  Lemma invert_EPair_correct {X A B} e e1 e2 :
    @invert_EPair X A B e = Some (e1, e2)
    <-> e = EBinop (OPair X A B) e1 e2.
  Proof.
    admit.
  Admitted.
    (* clear dependent locals. *)
    (* dependent induction e; cbn; intuition; try congruence; *)
    (* dependent induction o; inversion H; *) 
    (* try apply Eqdep.EqdepTheory.inj_pair2 in H1, H2; try exact type_eq_dec; *) 
    (* congruence. *)
  (* Qed. *)

  Lemma EUnop_correct {t1 t2 : type} (l : locals) (o : unop t1 t2) (e : expr t1)
    : interp_expr l (eUnop o e) = interp_expr l (EUnop o e).
  Proof.
    cbv [eUnop]; rewrite constfold_head_correct; case o in *; trivial.
    { apply eLength_correct. }
    { destruct invert_EPair as [[]|] eqn:H; try apply invert_EPair_correct in H; rewrite ?H; trivial. }
    { destruct invert_EPair as [[]|] eqn:H; try apply invert_EPair_correct in H; rewrite ?H; trivial. }
  Qed.

  Definition partial_head {t} (e : expr t) : expr t :=
    match e with
    | EUnop o e1 => eUnop o e1
    | e => e
    end.

  Section fold_expr.
    Context (f : forall {t}, expr t -> expr t). Local Arguments f {_}.
    Fixpoint fold_expr {t : type} (e : expr t) : expr t :=
      f
      match e in expr t return expr t with
      | EUnop o e1 => EUnop o (fold_expr e1)
      | EBinop o e1 e2 => EBinop o (fold_expr e1) (fold_expr e2)
      | EFlatmap e1 x e2 => EFlatmap (fold_expr e1) x (fold_expr e2)
      | EFold e1 e2 x y e3 => EFold (fold_expr e1) (fold_expr e2) x y (fold_expr e3)
      | EIf e1 e2 e3 => EIf (fold_expr e1) (fold_expr e2) (fold_expr e3)
      | ELet x e1 e2 => ELet x (fold_expr e1) (fold_expr e2)
      | (EVar _ _ | ELoc _ _ | EAtom _) as e => e
      end.
  End fold_expr.

  Definition partial {t : type} := @fold_expr (@partial_head) t.

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
    | EFold e1 e2 x y e3 => (EFold (fst(constant_folding' e1)) (fst(constant_folding' e2)) x y (fst(constant_folding' e3)), None)
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
      assert (H: (fun y : interp_type t1 => interp_expr (set_local l x y) (fst (constant_folding' e2)))
      = (fun y : interp_type t1 => interp_expr (set_local l x y) e2)).
      { apply functional_extensionality. intros. apply IHe2. }
      rewrite <- H.
      reflexivity.

    - rewrite IHe1.
      f_equal; eauto.
      apply functional_extensionality. intros.
      apply functional_extensionality. intros.
      easy.

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
    | EFold e1 e2 x y e3 => EFold (branch_elim e1) (branch_elim e2) x y (branch_elim e3)
    | ELet x e1 e2 => ELet x (branch_elim e1) (branch_elim e2)
    end.

  Lemma branch_elim_correct {t : type} (l : locals) (e : expr t) 
    : interp_expr l (branch_elim e) = interp_expr l e.
  Proof.
    generalize dependent l.
    induction e; simpl; intros; 
    try rewrite <- IHe; try rewrite <- IHe1; try rewrite <- IHe2; try rewrite <- IHe3; 
    try reflexivity.

    - assert (H:(fun y : interp_type t1 => interp_expr (set_local l x y) (branch_elim e2)) 
              = (fun y => interp_expr (set_local l x y) e2)).
      { apply functional_extensionality. intros. rewrite IHe2. reflexivity. }
      rewrite H. reflexivity.

    - f_equal. 
      do 2 (apply functional_extensionality; intros).
      easy.

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
    | EFold e1 e2 x' y' e3 => eqb x' x || eqb y' x || is_name_used x e1 || is_name_used x e2 || is_name_used x e3
    | EIf e1 e2 e3 => is_name_used x e1 || is_name_used x e2 || is_name_used x e3
    | ELet x' e1 e2 => eqb x' x || is_name_used x e1 || is_name_used x e2
    end.

  Lemma set_local_same {tx ty : type} (x : string) (vx : interp_type tx) (vy : interp_type ty) (l : locals)
    : set_local (set_local l x vx) x vy = set_local l x vy.
  Proof.
    unfold set_local.
    apply map.map_ext.
    intros.
    rewrite map.get_put_dec.
    destruct (eqb x k) eqn:E.
    - rewrite eqb_eq in E. rewrite E. rewrite map.get_put_same. reflexivity.
    - rewrite eqb_neq in E. rewrite map.get_put_diff; auto.
      rewrite map.get_put_diff; auto.
  Qed.

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
      assert (Hf:(fun y0 : interp_type t1 => interp_expr (set_local l x0 y0) e2)
              = (fun y0 : interp_type t1 => interp_expr (set_local (set_local l x y) x0 y0) e2)).
              { apply functional_extensionality. intros. rewrite set_local_comm_diff.
                + apply IHe2. reflexivity.
                + apply eqb_neq, Hx.
              }
              rewrite Hf. rewrite <- IHe1; easy.

    - destruct (eqb x0 x) eqn:H0x; 
      destruct (eqb y x) eqn:Hyx;
      destruct (is_name_used x e1) eqn:He1;
      destruct (is_name_used x e2) eqn:He2;
      destruct (is_name_used x e3) eqn:He3; 
      try discriminate H.
      f_equal; eauto.
      do 2 (apply functional_extensionality; intros).
      rewrite <- set_local_comm_diff with (x := x); cycle 1.
      { apply eqb_neq. rewrite eqb_sym. assumption. }
      rewrite <- set_local_comm_diff with (x := x); cycle 1.
      { apply eqb_neq. rewrite eqb_sym. assumption. }
      apply IHe3. reflexivity.

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
    | EFold e1 e2 x y e3 => EFold (unused_name_elim e1) (unused_name_elim e2) x y (unused_name_elim e3)
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

    - assert (H:(fun y : interp_type t1 => interp_expr (set_local l x y) (unused_name_elim e2)) 
              = (fun y => interp_expr (set_local l x y) e2)).
      { apply functional_extensionality. intros. rewrite IHe2. reflexivity. }
      rewrite IHe1, H. reflexivity.

    - f_equal; eauto.
      do 2 (apply functional_extensionality; intros).
      eauto.

    - rewrite IHe1, IHe2, IHe3. reflexivity.

    - destruct (is_name_used x e2) eqn:E.
      + simpl. rewrite IHe1, IHe2. reflexivity.
      + rewrite <- is_name_used_correct; easy.
  Qed.

  Definition flatmap_flatmap_head {t : type} (e : expr t) : expr t :=
    match e with
    | EFlatmap l x f => match l with
                        | EFlatmap l' y g => if orb (is_name_used y f) (eqb x y)
                                              then EFlatmap l x f 
                                              else EFlatmap l' y (EFlatmap g x f) 
                        | l' => EFlatmap l' x f
                        end
    | e' => e'
    end.

  Lemma flat_map_flat_map :
    forall {A B C} (l : list A) (f : B -> list C)  (g : A -> list B), 
    flat_map f (flat_map g l) = flat_map (fun x => flat_map f (g x)) l.
  Proof.
    induction l; auto.
    intros. simpl. rewrite flat_map_app. rewrite IHl. reflexivity.
  Qed.

  Lemma flatmap_flatmap_head_correct {t : type} (l : locals) (e : expr t)
    : interp_expr l (flatmap_flatmap_head e) = interp_expr l e.
  Proof.
    destruct e; auto.
    dependent induction e1; auto; simpl.
    destruct_one_match; auto; 
    simpl. rewrite flat_map_flat_map. f_equal. apply functional_extensionality.
    intros. f_equal. apply functional_extensionality.
    intros. symmetry. rewrite set_local_comm_diff.
    + apply is_name_used_correct. apply E.
    + apply E.
  Admitted.
  (* Qed. *)

  Definition flatmap_flatmap {t} : expr t -> expr t := fold_expr (@flatmap_flatmap_head).

  Goal forall s x, eUnop (OLength _) (eUnop (OFst s _ _)
    (EBinop (OPair s _ _)
      (EBinop ORange (EAtom (AInt 1)) (EAtom (AInt 5)))
      (EVar TInt x)))
  = EAtom (AInt 4).
  Proof. cbv. solve [trivial]. Abort.

  Lemma fold_flatmap : forall {A B C} (l : list A) (f : A -> list B) (g : B -> C -> C) (a : C),
    fold_right g a (flat_map f l) = fold_right (fun x y => fold_right g y (f x)) a l.
  Proof.
    induction l; eauto.
    intros. cbn. rewrite fold_right_app. f_equal. eauto.
  Qed.

  Definition fold_flatmap_head {t : type} (e : expr t) : expr t :=
    match e with
    | EFold l a x y f => match l with
                         | EFlatmap l' z g => 
                             if is_name_used z f || is_name_used y g || String.eqb x y || String.eqb x z || String.eqb y z
                             then EFold (EFlatmap l' z g) a x y f
                             else EFold l' a z y (EFold g (EVar _ y) x y f)
                         | l' => EFold l' a x y f
                         end
    | e' => e'
    end.

  (* Should be in Coqutil *)
  Lemma bool_dec_refl : forall b, Bool.bool_dec b b = left eq_refl.
  Proof.
    intros.
    destruct b; simpl; eauto.
  Qed.

  Lemma ascii_dec_refl : forall c, Ascii.ascii_dec c c = left eq_refl.
  Proof.
    intros.
    destruct c; eauto. 
    repeat (simpl; rewrite bool_dec_refl). simpl. f_equal.
  Qed.

  Lemma string_dec_refl : forall s, string_dec s s =  left eq_refl.
  Proof.
    intros.
    induction s; simpl; eauto.
    repeat (simpl; rewrite ascii_dec_refl). simpl. rewrite IHs. simpl. f_equal.
  Qed.

  Lemma type_eq_dec_refl : forall t, type_eq_dec t t = left eq_refl.
  Proof.
    induction t; eauto; simpl.
    - rewrite string_dec_refl. simpl. 
      rewrite IHt1. simpl.
      rewrite IHt2. simpl.
      f_equal.
    - rewrite IHt. simpl.
      f_equal.
  Qed.

  Lemma fold_flatmap_head_correct {t : type} (l : locals) (e : expr t)
    : interp_expr l (fold_flatmap_head e) = interp_expr l e.
  Proof.
    destruct e; eauto.
    dependent induction e1; eauto; simpl.
    destruct_one_match; eauto.
    simpl. rewrite fold_flatmap. f_equal. apply functional_extensionality.
    intros. f_equal. apply functional_extensionality.
    intros. f_equal.
    - apply functional_extensionality. intros.
      apply functional_extensionality. intros.
      repeat rewrite set_local_comm_diff with (y := x); try apply E.
      rewrite set_local_comm_diff with (x := x0); try apply E.
      rewrite set_local_same.
      symmetry. apply is_name_used_correct. apply E.
    - unfold get_local, set_local.
      rewrite map.get_put_same.
      unfold proj_expected. simpl.
      rewrite type_eq_dec_refl. reflexivity.
    - symmetry. apply is_name_used_correct. apply E.
  Admitted.

  Definition invert_singleton {t : type} (e : expr (TList t)) : option (expr t) :=
    match e in expr t' return option (expr t) with
    | EBinop (OCons t') h (EAtom (ANil _)) => match type_eq_dec t' t with
                               | left H => Some (cast H _ h)
                               | right _ => None
                               end
    | _ => None
    end.

  Definition fold_flatmap_singleton_head {t : type} (e : expr t) : expr t :=
    match e with
    | EFold l a x y f => match l with
                         | EFlatmap l' z g => 
                             if is_name_used z f || is_name_used y g || String.eqb x y || String.eqb x z || String.eqb y z
                             then EFold (EFlatmap l' z g) a x y f
                             else match invert_singleton g with
                                  | Some e => EFold l' a z y (ELet x e f)
                                  | None => EFold (EFlatmap l' z g) a x y f
                                  end
                         | l' => EFold l' a x y f
                         end
    | e' => e'
    end.

  Compute fold_flatmap_singleton_head 
    (EFold 
      (EFlatmap 
        (EBinop 
          (OCons TInt) 
          (EAtom (AInt 3))
          (EAtom (ANil TInt))
        )
        "z"
        (EBinop
          (OCons TInt)
          (EBinop 
            OTimes
            (EVar TInt "z")
            (EVar TInt "z")
          )
          (EAtom (ANil TInt))
        )
      )
      (EAtom (AInt 0))
      "x" "y" 
      (EBinop 
        OPlus 
        (EVar TInt "x")
        (EVar TInt "y")
      )
    ).

  Lemma fold_flatmap_singleton {A B C} (l : list A) (f : A -> B) (g : B -> C -> C) (a : C):
    
    fold_right g a (flat_map (fun x => f x :: nil) l) = fold_right (fun x y => g (f x) y) a l.
  Proof.
    induction l; eauto.
    intros. cbn. f_equal. eauto.
  Qed.

  Lemma fold_flatmap_singleton_head_correct {t : type} (l : locals) (e : expr t)
    : interp_expr l (fold_flatmap_singleton_head e) = interp_expr l e.
  Proof.
    destruct e; eauto.
    dependent induction e1; eauto; simpl.
    repeat (destruct_one_match; eauto).
    unfold invert_singleton in *.
    dependent induction e1_2; simpl in E0; try discriminate.
    dependent induction o; simpl in E0; try discriminate.
    dependent induction e1_2_2;  simpl in E0; try discriminate.
    dependent induction a.
    rewrite type_eq_dec_refl in E0. injection E0 as E0. subst.
    simpl.
    rewrite fold_flatmap_singleton.
    f_equal. repeat (apply functional_extensionality; intros).
    cbn [is_name_used] in E.
    rewrite! Bool.orb_false_r in E.
    repeat rewrite set_local_comm_diff with (y := x); try apply E.
    rewrite <- is_name_used_correct; try apply E.
    f_equal.
    rewrite set_local_comm_diff with (x := x0); try apply E.
    do 2 f_equal.
    rewrite set_local_comm_diff with (x := x).
    - rewrite <- is_name_used_correct; try apply E. reflexivity.
    - apply not_eq_sym. apply E.
  Admitted.
End WithMap.
