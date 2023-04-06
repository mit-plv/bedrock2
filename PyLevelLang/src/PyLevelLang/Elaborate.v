Require Import PyLevelLang.Language.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
Require Import coqutil.Datatypes.Result.
Import ResultMonadNotations.

(* Casts an expression `e` from `expr t2` to `expr t1`, if the two types are
   equal *)
Definition enforce_type (t1 : type) {t2 : type} (e : expr t2) : result (expr t1) :=
  match type_eq_dec t2 t1 with
  | left H => Success (cast H expr e)
  | _ => error:(e "has type" t2 "but expected" t1)
  end.

(* `enforce_type` preserves any predicate on expressions *)
Lemma enforce_type_pred {t t'} (e : expr t) (e' : expr t')
  (P : forall t, expr t -> Prop) :
  P t e
  -> enforce_type t' e = Success e' -> P t' e'.
Proof.
  intro H.
  cbv [enforce_type]; case type_eq_dec eqn:E; inversion_clear 1; subst; trivial.
Qed.

(* `enforce_type` preserves equality
 * (`existT` needs to be used for the statement to typecheck) *)
Lemma enforce_type_eq {t t'} (e : expr t) (e' : expr t') :
  enforce_type t' e = Success e' ->
  existT expr t e = existT expr t' e'.
Proof.
  intro H.
  now apply enforce_type_pred with (e := e) (e' := e').
Qed.

Section WithMap.
  (* abstract all functions in this section over the implementation of the map,
     and over its spec (map.ok) *)
  Context {tenv : map.map string (type * bool)} {tenv_ok : map.ok tenv}.

  (* Well-formedness judgement for `expr`s, stating that an `expr` has no free
   * variables and variables are used with correct types *)
  Inductive wf : tenv -> forall {t : type}, expr t -> Prop :=
    | wf_EVar G t (x : string) :
        map.get G x = Some (t, false) -> wf G (EVar t x)
    | wf_ELoc G t (x : string) :
        map.get G x = Some (t, true) -> wf G (ELoc t x)
    | wf_EAtom G {t} (a : atom t) : wf G (EAtom a)
    | wf_EUnop G {t1 t2} (o : unop t1 t2) (e : expr t1) :
        wf G e -> wf G (EUnop o e)
    | wf_EBinop G {t1 t2 t3} (o : binop t1 t2 t3)
        (e1 : expr t1) (e2 : expr t2) :
        wf G e1 -> wf G e2 -> wf G (EBinop o e1 e2)
    | wf_EFlatmap G {t1 t2} (e1 : expr (TList t1)) (x : string)
        (e2 : expr (TList t2)) :
        wf G e1 -> wf (map.put G x (t1, false)) e2 -> wf G (EFlatmap e1 x e2)
    | wf_EFold G {t1 t2} (e1 : expr (TList t1)) (e2 : expr t2) (x : string) 
        (y : string) (e3 : expr t2) :
        wf G e1 -> wf G e2 -> wf (map.put (map.put G x (t1, false)) y (t2, false)) e3 -> wf G (EFold e1 e2 x y e3)
    | wf_EIf G {t} (e1 : expr TBool) (e2 e3 : expr t) :
        wf G e1 -> wf G e2 -> wf G e3 -> wf G (EIf e1 e2 e3)
    | wf_ELet G {t1 t2} (x : string) (e1 : expr t1) (e2 : expr t2) :
        wf G e1 -> wf (map.put G x (t1, false)) e2 -> wf G (ELet x e1 e2).

  (* Same, but for commands *)
  Inductive wf_command : tenv -> command -> Prop :=
    | wf_CSkip G : wf_command G CSkip
    | wf_CSeq G (c1 c2 : command) :
        wf_command G c1 -> wf_command G c2 -> wf_command G (CSeq c1 c2)
    | wf_CLet G {t} (x : string) (e : expr t) (c : command) :
        wf G e -> wf_command (map.put G x (t, false)) c ->
        wf_command G (CLet x e c)
    | wf_CLetMut G {t} (x : string) (e : expr t) (c : command) :
        wf G e -> wf_command (map.put G x (t, true)) c ->
        wf_command G (CLetMut x e c)
    | wf_CGets G {t} (x : string) (e : expr t) :
        wf G e -> map.get G x = Some (t, true) -> wf_command G (CGets x e)
    | wf_CIf G (e : expr TBool) (c1 c2 : command) :
        wf G e -> wf_command G c1 -> wf_command G c2 ->
        wf_command G (CIf e c1 c2)
    | wf_CForeach G {t} (x : string) (e : expr (TList t)) (c : command) :
        wf G e -> wf_command (map.put G x (t, false)) c ->
        wf_command G (CForeach x e c).

  (* `enforce_type` preserves well-formedness *)
  Lemma enforce_type_wf {t t'} (e : expr t) (e' : expr t') : forall G,
    wf G e -> enforce_type t' e = Success e' -> wf G e'.
  Proof.
    intros G H He.
    now apply enforce_type_pred with (e := e).
  Qed.

  Definition elaborate_atom (pa : patom) : result {t & expr t} :=
    match pa with
    | PAWord z =>
        Success (existT _ _ (EAtom (AWord z)))
    | PAInt z =>
        Success (existT _ _ (EAtom (AInt z)))
    | PABool b =>
        Success (existT _ _ (EAtom (ABool b)))
    | PAString s =>
        Success (existT _ _ (EAtom (AString s)))
    | PANil t =>
        Success (existT _ _ (EAtom (ANil t)))
    end.

  Lemma elaborate_atom_wf (pa : patom) : forall G t e,
    elaborate_atom pa = Success (existT expr t e) -> wf G e.
  Proof.
    intros G t e H. destruct pa; unfold elaborate_atom in H.
    all:
      injection H as [= _ H];
      destruct t; try easy;
      repeat injection H as [= <-];
      apply Eqdep_dec.inj_pair2_eq_dec in H as [= <-]; try exact type_eq_dec;
      apply wf_EAtom.
  Qed.

  Definition elaborate_unop (po : punop) {t : type} (e : expr t) :
    result {t & expr t} :=
    match po with
    | PONeg =>
        match t as t' return expr t' -> _ with
        | TWord => fun e =>
            Success (existT _ _ (EUnop OWNeg e))
        | TInt => fun e =>
            Success (existT _ _ (EUnop ONeg e))
        | _ => fun _ =>
            error:(e "has type" t "but expected" TWord "or" TInt)
        end e
    | PONot =>
        e' <- enforce_type TBool e;;
        Success (existT _ _ (EUnop ONot e'))
    | POLength =>
        match t as t' return expr t' -> _ with
        | TList _ => fun e =>
            Success (existT _ _ (EUnop (OLength _) e))
        | TString => fun e =>
            Success (existT _ _ (EUnop OLengthString e))
        | _ => fun _ =>
            error:(e "has type" t "but expected" TList "or" TString)
        end e
    | POIntToString =>
        e' <- enforce_type TInt e;;
        Success (existT _ _ (EUnop OIntToString e'))
    end.

  Lemma elaborate_unop_wf (po : punop) {t : type} (e : expr t) : forall G t' e',
    wf G e -> elaborate_unop po e = Success (existT expr t' e') -> wf G e'.
  Proof.
    intros G t0 e0 He H.
    destruct po; unfold elaborate_unop in H.
    all: try (
      destruct (enforce_type _ e) as [e' |] eqn : H'; try easy;
      inversion H;
      apply wf_EUnop; now apply enforce_type_wf with (G := G) in H'
    ).
    all: try (
      destruct t; try easy; inversion H; now apply wf_EUnop
    ).
  Qed.

  (* Helper function to enforce `can_eq` in type system *)
  Definition construct_eq' {t : type} (e1 e2 : expr t) :
    if can_eq t then expr TBool else unit.
  Proof.
    refine (
        match t as t'
        return expr t' -> expr t' -> if can_eq t' then expr TBool else unit
        with
        | TWord | TInt | TBool | TString | TEmpty => fun e1 e2 =>
            EBinop (OEq _ _) e1 e2
        | _ => fun _ _ =>
            tt
        end e1 e2
      ); easy.
  Defined.

  Definition construct_eq {t: type} (e1 e2 : expr t) : result {t & expr t}.
  Proof.
    destruct (can_eq t) eqn : H.
    - pose (e := construct_eq' e1 e2).
      rewrite H in e.
      exact (Success (existT _ _ e)).
    - exact error:(e1 "has type" t "which does not support equality").
  Defined.

  Definition elaborate_binop (po : pbinop)
    {t1 t2 : type} (e1 : expr t1) (e2 : expr t2) :
    result {t & expr t} :=
    match po with
    | POPlus =>
        match t1 as t' return expr t' -> _ with
        | TWord => fun e1 =>
            e2' <- enforce_type TWord e2;;
            Success (existT _ _ (EBinop OWPlus e1 e2'))
        | TInt => fun e1 =>
            e2' <- enforce_type TInt e2;;
            Success (existT _ _ (EBinop OPlus e1 e2'))
        | _ => fun _ =>
            error:(e1 "has type" t1 "but expected" TWord "or" TInt)
        end e1
    | POMinus =>
        match t1 as t' return expr t' -> _ with
        | TWord => fun e1 =>
            e2' <- enforce_type TWord e2;;
            Success (existT _ _ (EBinop OWMinus e1 e2'))
        | TInt => fun e1 =>
            e2' <- enforce_type TInt e2;;
            Success (existT _ _ (EBinop OMinus e1 e2'))
        | _ => fun _ =>
            error:(e1 "has type" t1 "but expected" TWord "or" TInt)
        end e1
    | POTimes =>
        match t1 as t' return expr t' -> _ with
        | TWord => fun e1 =>
            e2' <- enforce_type TWord e2;;
            Success (existT _ _ (EBinop OWTimes e1 e2'))
        | TInt => fun e1 =>
            e2' <- enforce_type TInt e2;;
            Success (existT _ _ (EBinop OTimes e1 e2'))
        | _ => fun _ =>
            error:(e1 "has type" t1 "but expected" TWord "or" TInt)
        end e1
    | PODivU =>
        e1' <- enforce_type TWord e1;;
        e2' <- enforce_type TWord e2;;
        Success (existT _ _ (EBinop OWDivU e1' e2'))
    | PODiv =>
        match t1 as t' return expr t' -> _ with
        | TWord => fun e1 =>
            e2' <- enforce_type TWord e2;;
            Success (existT _ _ (EBinop OWDivS e1 e2'))
        | TInt => fun e1 =>
            e2' <- enforce_type TInt e2;;
            Success (existT _ _ (EBinop ODiv e1 e2'))
        | _ => fun _ =>
            error:(e1 "has type" t1 "but expected" TWord "or" TInt)
        end e1
    | POModU =>
        e1' <- enforce_type TWord e1;;
        e2' <- enforce_type TWord e2;;
        Success (existT _ _ (EBinop OWModU e1' e2'))
    | POMod =>
        match t1 as t' return expr t' -> _ with
        | TWord => fun e1 =>
            e2' <- enforce_type TWord e2;;
            Success (existT _ _ (EBinop OWModS e1 e2'))
        | TInt => fun e1 =>
            e2' <- enforce_type TInt e2;;
            Success (existT _ _ (EBinop OMod e1 e2'))
        | _ => fun _ =>
            error:(e1 "has type" t1 "but expected" TWord "or" TInt)
        end e1
    | POAnd =>
        e1' <- enforce_type TBool e1;;
        e2' <- enforce_type TBool e2;;
        Success (existT _ _ (EBinop OAnd e1' e2'))
    | POOr =>
        e1' <- enforce_type TBool e1;;
        e2' <- enforce_type TBool e2;;
        Success (existT _ _ (EBinop OOr e1' e2'))
    | POConcat =>
        match t1 as t' return expr t' -> _ with
        | TList t1 => fun e1 =>
            e2' <- enforce_type (TList t1) e2;;
            Success (existT _ _ (EBinop (OConcat _) e1 e2'))
        | TString => fun e1 =>
            e2' <- enforce_type TString e2;;
            Success (existT _ _ (EBinop OConcatString e1 e2'))
        | _ => fun _ =>
            error:(e1 "has type" t1 "but expected" TList "or" TString)
        end e1
    | POLessU =>
        e1' <- enforce_type TWord e1;;
        e2' <- enforce_type TWord e2;;
        Success (existT _ _ (EBinop OWLessU e1' e2'))
    | POLess =>
        match t1 as t' return expr t' -> _ with
        | TWord => fun e1 =>
            e2' <- enforce_type TWord e2;;
            Success (existT _ _ (EBinop OWLessU e1 e2'))
        | TInt => fun e1 =>
            e2' <- enforce_type TInt e2;;
            Success (existT _ _ (EBinop OLess e1 e2'))
        | _ => fun _ =>
            error:(e1 "has type" t1 "but expected" TWord "or" TInt)
        end e1
    | POEq =>
        e2' <- enforce_type t1 e2;;
        construct_eq e1 e2'
    | PORepeat =>
        match t1 as t' return expr t' -> _ with
        | TList t1 => fun e1 =>
            e2' <- enforce_type TInt e2;;
            Success (existT _ _ (EBinop (ORepeat _) e1 e2'))
        | _ => fun _ => error:(e1 "has type" t1 "but expected" TList)
        end e1
    | POPair =>
        Success (existT _ _
          (EBinop (OPair "0" _ _) e1
            (EBinop (OPair "1" _ _) e2
              (EAtom AEmpty))))
    | POCons =>
        e2' <- enforce_type (TList t1) e2;;
        Success (existT _ _ (EBinop (OCons _) e1 e2'))
    | PORange =>
        e1' <- enforce_type TInt e1;;
        e2' <- enforce_type TInt e2;;
        Success (existT _ _ (EBinop ORange e1' e2'))
    end.

  Lemma elaborate_binop_wf (po : pbinop)
    {t1 t2 : type} (e1 : expr t1) (e2 : expr t2) : forall G t' e',
    wf G e1 -> wf G e2 ->
    elaborate_binop po e1 e2 = Success (existT expr t' e') -> wf G e'.
  Proof.
    intros G t0 e0 H1 H2 H.
    destruct po; unfold elaborate_binop in H.
    all: try (
      destruct (enforce_type _ e1) as [e1' |] eqn : H1'; try easy;
      destruct (enforce_type _ e2) as [e2' |] eqn : H2'; try easy;
      inversion H;
      apply wf_EBinop; now apply enforce_type_wf with (G := G) in H1', H2'
    ).
    all: try (
      destruct t1; try easy;
      destruct (enforce_type _ e2) as [e2' |] eqn : H2'; try easy;
      inversion H;
      apply wf_EBinop; now apply enforce_type_wf with (G := G) in H2'
    ).
    - (* POPair *)
      inversion H.
      repeat apply wf_EBinop; now try apply wf_EAtom.
  Qed.

  Fixpoint elaborate_proj {t : type} (e : expr t) (s : string) :
    result {t & expr t} :=
    match t as t' return expr t' -> _ with
    | TPair s' _ _ => fun e =>
        if string_dec s s' then
        Success (existT _ _ (EUnop (OFst s' _ _) e))
        else
        elaborate_proj (EUnop (OSnd s' _ _) e) s
    | TEmpty => fun _ => error:("Field" s "not found in record")
    | _ => fun _ => error:(e "has type" t "but expected" TPair)
    end e.

  Lemma elaborate_proj_wf {t : type} (e : expr t) (s : string) : forall G t' e',
    wf G e -> elaborate_proj e s = Success (existT expr t' e') -> wf G e'.
  Proof.
    induction t; try easy.
    intros G t' e' He H.
    unfold elaborate_proj in H.
    destruct string_dec.
    - inversion H.
      now apply wf_EUnop.
    - fold @elaborate_proj in H.
      apply IHt2 with (G := G) in H.
      + exact H.
      + now apply wf_EUnop.
  Qed.

  Section ElaborateRecord.
    Context (elaborate : tenv -> pexpr -> result {t & expr t}).

    Fixpoint elaborate_record (G : tenv) (xs : list (string * pexpr)) :
      result {t & expr t} :=
      match xs with
      | nil =>
          Success (existT _ _ (EAtom AEmpty))
      | (s, p) :: xs =>
          '(existT _ _ e1) <- elaborate G p;;
          '(existT _ _ e2) <- elaborate_record G xs;;
          Success (existT _ _ (EBinop (OPair s _ _) e1 e2))
      end.
  End ElaborateRecord.

  (* Type checks a `pexpr` and possibly emits a typed expression
     Checks scoping for variables/locations *)
  Fixpoint elaborate (G : tenv) (p : pexpr) : result {t & expr t} :=
    match p with
    | PEVar x =>
        match map.get G x with
        | Some (t, false) =>
            Success (existT _ _ (EVar t x))
        | Some (t, true) =>
            Success (existT _ _ (ELoc t x))
        | None => error:("Undefined variable" x)
        end
    | PEAtom pa =>
        elaborate_atom pa
    | PESingleton p' =>
        '(existT _ t' e') <- elaborate G p';;
        Success (existT _ _ (EBinop (OCons _) e' (EAtom (ANil t'))))
    | PEUnop po p =>
        '(existT _ t e) <- elaborate G p;;
        elaborate_unop po e
    | PEBinop po p1 p2 =>
        '(existT _ t1 e1) <- elaborate G p1;;
        '(existT _ t2 e2) <- elaborate G p2;;
        elaborate_binop po e1 e2
    | PEFlatmap p1 x p2 =>
        '(existT _ t1 e1) <- elaborate G p1;;
        match t1 as t' return expr t' -> _ with
        | TList t1 => fun e1 =>
            let G' := map.put G x (t1, false) in
            '(existT _ t2 e2) <- elaborate G' p2;;
            match t2 as t' return expr t' -> _ with
            | TList t2 => fun e2 => Success (existT _ _ (EFlatmap e1 x e2))
            | _ => fun _ => error:(e2 "has type" t2 "but expected" TList)
            end e2
        | _ => fun _ => error:(e1 "has type" t1 "but expected" TList)
        end e1
    | PEFold p1 p2 x y p3 =>
        '(existT _ t1 e1) <- elaborate G p1;;
        match t1 as t' return expr t' -> _ with
        | TList t1 => fun e1 => 
            '(existT _ t2 e2) <- elaborate G p2;;
            let G' := map.put (map.put G x (t1, false)) y (t2, false) in
            '(existT _ t3 e3) <- elaborate G' p3;;
            e3' <- enforce_type t2 e3;;
            Success (existT _ _ (EFold e1 e2 x y e3'))
        | _ => fun _ => error:(e1 "has type" t1 "but expected" TList)
        end e1
    | PEIf p1 p2 p3 =>
        '(existT _ t1 e1) <- elaborate G p1;;
        '(existT _ t2 e2) <- elaborate G p2;;
        '(existT _ t3 e3) <- elaborate G p3;;
        e1' <- enforce_type TBool e1;;
        e3' <- enforce_type t2 e3;;
        Success (existT _ _ (EIf e1' e2 e3'))
    | PELet x p1 p2 =>
        '(existT _ t1 e1) <- elaborate G p1;;
        let G' := map.put G x (t1, false) in
        '(existT _ t2 e2) <- elaborate G' p2;;
        Success (existT _ _ (ELet x e1 e2))
    | PERecord ps =>
        elaborate_record elaborate G ps
    | PEProj p s =>
      '(existT _ t e) <- elaborate G p;;
        elaborate_proj e s
    end.

  Fixpoint elaborate_wf (p : pexpr) : forall G t e,
    elaborate G p = Success (existT expr t e) -> wf G e.
  Proof.
    induction p; intros G t e H; unfold elaborate in H; fold elaborate in H.
    - (* PEVar x *)
      destruct (map.get G x) as [[t' [|]] |] eqn : Hmap.
      + (* Some (t', true) *)
        injection H as [= H' H]. rewrite H' in H.
        injection H as H.
        apply Eqdep_dec.inj_pair2_eq_dec in H as [= <-]; try exact type_eq_dec.
        apply wf_ELoc. now rewrite Hmap, H'.
      + (* Some (t', false) *)
        injection H as [= H' H]. rewrite H' in H.
        apply Eqdep_dec.inj_pair2_eq_dec in H as [= <-]; try exact type_eq_dec.
        apply wf_EVar. now rewrite Hmap, H'.
      + (* None *)
        discriminate H.
    - (* PEAtom pa *)
      now apply elaborate_atom_wf with (pa := pa).
    - (* PESingleton p *)
      destruct (elaborate G p) as [[t' e'] |] eqn : H'; try easy.
      inversion H.
      apply wf_EBinop.
      * now apply IHp.
      * apply wf_EAtom.
    - (* PEUnop po p *)
      destruct (elaborate G p) as [[t' e'] |] eqn : H'; try easy.
      apply elaborate_unop_wf with (po := po) (e := e').
      + now apply IHp.
      + easy.
    - (* PEBinop po p1 p2 *)
      destruct (elaborate G p1) as [[t1 e1] |] eqn : H1; try easy.
      destruct (elaborate G p2) as [[t2 e2] |] eqn : H2; try easy.
      apply elaborate_binop_wf with (po := po) (e1 := e1) (e2 := e2).
      + now apply IHp1.
      + now apply IHp2.
      + easy.
    - (* PEFlatmap p1 x p2 *)
      destruct (elaborate G p1) as [[t1 e1] |] eqn : H1; try easy.
      destruct t1; try easy.
      destruct (elaborate (map.put G x (t1, false)) p2) as [[t2 e2] |] eqn : H2;
          try easy.
      destruct t2; try easy.
      inversion H.
      apply wf_EFlatmap.
      + now apply IHp1.
      + now apply IHp2.
    - (* PEFold p1 p2 x y p3 *)
      destruct (elaborate G p1) as [[t1 e1] |] eqn : H1; try easy.
      destruct t1; try easy.
      destruct (elaborate G p2) as [[t2 e2] |] eqn : H2; try easy.
      destruct (elaborate (map.put (map.put G x (t1, false)) y (t2, false)) p3) as [[t3 e3] |] eqn : H3; try easy.
      destruct (enforce_type t2 e3) as [e3' |] eqn : H3'; try easy.
      inversion H.
      apply wf_EFold.
      + now apply IHp1.
      + now apply IHp2.
      + apply IHp3. rewrite H3.
        enough (existT expr t3 e3 = existT expr t2 e3').
        { now rewrite <- H0. }
        apply enforce_type_eq.
        exact H3'.
    - (* PEIf p1 p2 p3 *)
      destruct (elaborate G p1) as [[t1 e1] |] eqn : H1; try easy.
      destruct (elaborate G p2) as [[t2 e2] |] eqn : H2; try easy.
      destruct (elaborate G p3) as [[t3 e3] |] eqn : H3; try easy.
      destruct (enforce_type TBool e1) as [e1' |] eqn : H1'; try easy.
      destruct (enforce_type t2 e3) as [e3' |] eqn : H3'; try easy.
      inversion H.
      apply wf_EIf.
      + apply IHp1.
        rewrite H1.
        enough (existT expr t1 e1 = existT expr TBool e1').
        { now rewrite <- H0. }
        apply enforce_type_eq.
        exact H1'.
      + apply IHp2, H2.
      + apply IHp3.
        rewrite H3.
        enough (existT expr t3 e3 = existT expr t2 e3').
        { now rewrite <- H0. }
        apply enforce_type_eq.
        exact H3'.
    - (* PELet x p1 p2 *)
      destruct (elaborate G p1) as [[t1 e1] |] eqn : H1; try easy.
      destruct (elaborate (map.put G x (t1, false)) p2) as [[t2 e2] |] eqn : H2;
          try easy.
      inversion H.
      apply wf_ELet.
      + now apply IHp1.
      + apply IHp2, H2.
    - (* PERecord xs *)
      revert G t e H.
      induction xs as [| [s p]]; intros G t e H.
      + (* nil *)
        inversion H. apply wf_EAtom.
      + (* (s, p) :: xs *)
        unfold elaborate_record in H.
        destruct (elaborate G p) as [[t1 e1] |] eqn : H1; try easy.
        assert (elaborate_record elaborate G xs =
          (fix elaborate_record
             (G0 : tenv) (xs0 : list (string * pexpr)) {struct xs0} :
               result {t0 : type & expr t0} :=
             match xs0 with
             | nil =>
                 Success (existT (fun t0 : type => expr t0) TEmpty (EAtom AEmpty))
             | (s0, p1) :: xs1 =>
                 ' (existT _ x e0) <- elaborate G0 p1;;
                 ' (existT _ x0 e2) <- elaborate_record G0 xs1;;
                 Success
                   (existT (fun t0 : type => expr t0) (TPair s0 x x0)
                      (EBinop (OPair s0 x x0) e0 e2))
             end) G xs
        ).
        { easy. }
        rewrite <- H0 in H. clear H0.
        destruct (elaborate_record elaborate G xs) as [[t2 e2] |] eqn : H2; try easy.
        inversion H.
        apply wf_EBinop.
        * apply elaborate_wf in H1. exact H1.
        * apply IHxs. exact H2.
    - (* PEProj p s *)
      unfold elaborate_proj in H.
      destruct (elaborate G p) as [[t0 e0] |] eqn : H0; try easy.
      apply elaborate_proj_wf with (e := e0) (s := s).
      + now apply IHp.
      + exact H.
  Qed.

  Fixpoint elaborate_command (G : tenv) (pc : pcommand) : result command :=
    match pc with
    | PCSkip =>
        Success CSkip
    | PCSeq pc1 pc2 =>
        c1 <- elaborate_command G pc1;;
        c2 <- elaborate_command G pc2;;
        Success (CSeq c1 c2)
    | PCLet x p pc =>
        '(existT _ t e) <- elaborate G p;;
        match map.get G x with
        | Some (_, true) =>
            error:("Variable" x "already defined as mutable")
        | Some (_, false) | None =>
            (* If already defined as immutable, shadow that variable *)
            let G' := map.put G x (t, false) in
            c <- elaborate_command G' pc;;
            Success (CLet x e c)
        end
    | PCLetMut x p pc =>
        '(existT _ t e) <- elaborate G p;;
        match map.get G x with
        | Some (_, true) =>
            error:("Mutable variable" x "already defined")
        | Some (_, false) =>
            error:("Variable" x "already defined as immutable")
        | None =>
            let G' := map.put G x (t, true) in
            c <- elaborate_command G' pc;;
            Success (CLetMut x e c)
        end
    | PCGets x p =>
        '(existT _ t e) <- elaborate G p;;
        match map.get G x with
        | Some (t', true) =>
            e' <- enforce_type t' e;;
            Success (CGets x e')
        | Some (_, false) =>
            error:("Variable" x "is not mutable")
        | None =>
            error:("Undefined variable" x)
        end
    | PCIf p pc1 pc2 =>
        '(existT _ _ e) <- elaborate G p;;
        e' <- enforce_type TBool e;;
        c1 <- elaborate_command G pc1;;
        c2 <- elaborate_command G pc2;;
        Success (CIf e' c1 c2)
    | PCForeach x p pc =>
        '(existT _ t e) <- elaborate G p;;
        match t as t' return expr t' -> _ with
        | TList t => fun e =>
            let G' := map.put G x (t, false) in
            c <- elaborate_command G' pc;;
            Success (CForeach x e c)
        | _ => fun _ => error:(e "has type" t "but expected" TList)
        end e
    end.

  Lemma elaborate_command_wf (pc : pcommand) : forall G c,
    elaborate_command G pc = Success c -> wf_command G c.
  Proof.
    induction pc; intros G c H;
    unfold elaborate_command in H; fold elaborate_command in H.
    - (* PCSkip *)
      inversion H.
      apply wf_CSkip.
    - (* PCSeq pc1 pc2 *)
      destruct (elaborate_command G pc1) as [c1 |] eqn:H1; try easy.
      destruct (elaborate_command G pc2) as [c2 |] eqn:H2; try easy.
      inversion H.
      now apply wf_CSeq; [apply IHpc1 | apply IHpc2].
    - (* PCLet x p pc *)
      destruct (elaborate G p) as [[t e] |] eqn:He; try easy.
      destruct (map.get G x) as [[t' [|]] |] eqn : Hmap; try easy;
      destruct (elaborate_command _ pc) as [c' |] eqn:H'; try easy;
      inversion H;
      apply wf_CLet;
      eapply elaborate_wf, He || now apply IHpc.
    - (* PCLetMut x p pc *)
      destruct (elaborate G p) as [[t e] |] eqn:He; try easy.
      destruct (map.get G x) as [[t' [|]] |] eqn : Hmap; try easy;
      destruct (elaborate_command _ pc) as [c' |] eqn:H'; try easy;
      inversion H;
      apply wf_CLetMut;
      eapply elaborate_wf, He || now apply IHpc.
    - (* PCGets x p *)
      destruct (elaborate G p) as [[t e] |] eqn:He; try easy.
      destruct (map.get G x) as [[t' [|]] |] eqn : Hmap; try easy.
      destruct (enforce_type t' e) as [e' |] eqn : He'; try easy.
      inversion H.
      apply wf_CGets.
      + eapply enforce_type_pred, He'.
        eapply elaborate_wf, He.
      + easy.
    - (* PCIf p pc1 pc2 *)
      destruct (elaborate G p) as [[t e] |] eqn:He; try easy.
      destruct (enforce_type TBool e) as [e' |] eqn : He'; try easy.
      destruct (elaborate_command G pc1) as [c1 |] eqn:H1; try easy.
      destruct (elaborate_command G pc2) as [c2 |] eqn:H2; try easy.
      inversion H.
      apply wf_CIf.
      + eapply enforce_type_pred, He'.
        eapply elaborate_wf, He.
      + now apply IHpc1.
      + now apply IHpc2.
    - (* PCForeach x p pc *)
      destruct (elaborate G p) as [[t e] |] eqn:He; try easy.
      destruct t; try easy.
      destruct (elaborate_command _ pc) as [c' |] eqn:H'; try easy.
      inversion H.
      apply wf_CForeach.
      + eapply elaborate_wf, He.
      + now apply IHpc.
  Qed.
End WithMap.
