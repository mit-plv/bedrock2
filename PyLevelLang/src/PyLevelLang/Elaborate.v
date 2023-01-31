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

(* `enforce_type` preserves equality
 * (`existT` needs to be used for the statement to typecheck) *)
Lemma enforce_type_eq {t t'} (e : expr t) (e' : expr t') :
  enforce_type t' e = Success e' ->
  existT expr t e = existT expr t' e'.
Proof.
  cbv [enforce_type]; case type_eq_dec eqn:E; inversion_clear 1; subst; trivial.
Qed.

Section WithMap.
  (* abstract all functions in this section over the implementation of the map,
     and over its spec (map.ok) *)
  Context {tenv : map.map string (type * bool)} {tenv_ok : map.ok tenv}.

  Section ElaborateHelpers.
    Context (elaborate : tenv -> pexpr -> result {t & expr t}).

    Definition elaborate_const (G : tenv) (pc : pconst) : result {t & expr t} :=
      match pc with
      | PCInt z =>
          Success (existT _ _ (EConst (CInt z)))
      | PCBool b =>
          Success (existT _ _ (EConst (CBool b)))
      | PCString s =>
          Success (existT _ _ (EConst (CString s)))
      | PCNil t =>
          Success (existT _ _ (EConst (CNil t)))
      end.

    Definition elaborate_unop (G : tenv) (po : punop) (p1 : pexpr) :
      result {t & expr t} :=
      '(existT _ t1 e1) <- elaborate G p1;;
      match po with
      | PONeg =>
          e1' <- enforce_type TInt e1;;
          Success (existT _ _ (EUnop ONeg e1'))
      | PONot =>
          e1' <- enforce_type TBool e1;;
          Success (existT _ _ (EUnop ONot e1'))
      | POLength =>
          match t1 as t' return expr t' -> _ with
          | TList _ => fun e1 =>
              Success (existT _ _ (EUnop (OLength _) e1))
          | TString => fun e1 =>
              Success (existT _ _ (EUnop OLengthString e1))
          | _ => fun _ => error:(e1 "has type" t1 "but expected" TList "or" TString)
          end e1
      end.

    (* Helper function to enforce `can_eq` in type system *)
    Definition construct_eq' {t : type} (e1 e2 : expr t) :
      if can_eq t then expr TBool else unit.
    Proof.
      refine (
          match t as t'
          return expr t' -> expr t' -> if can_eq t' then expr TBool else unit
          with
          | TInt | TBool | TString | TEmpty => fun e1 e2 =>
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

    Definition elaborate_binop (G : tenv) (po : pbinop) (p1 p2 : pexpr) :
      result {t & expr t} :=
      '(existT _ t1 e1) <- elaborate G p1;;
      '(existT _ t2 e2) <- elaborate G p2;;
      match po with
      | POPlus =>
          e1' <- enforce_type TInt e1;;
          e2' <- enforce_type TInt e2;;
          Success (existT _ _ (EBinop OPlus e1' e2'))
      | POMinus =>
          e1' <- enforce_type TInt e1;;
          e2' <- enforce_type TInt e2;;
          Success (existT _ _ (EBinop OMinus e1' e2'))
      | POTimes =>
          e1' <- enforce_type TInt e1;;
          e2' <- enforce_type TInt e2;;
          Success (existT _ _ (EBinop OTimes e1' e2'))
      | PODiv =>
          e1' <- enforce_type TInt e1;;
          e2' <- enforce_type TInt e2;;
          Success (existT _ _ (EBinop ODiv e1' e2'))
      | POMod =>
          e1' <- enforce_type TInt e1;;
          e2' <- enforce_type TInt e2;;
          Success (existT _ _ (EBinop OMod e1' e2'))
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
          | _ => fun _ => error:(e1 "has type" t1 "but expected" TList "or" TString)
          end e1
      | POLess =>
          e1' <- enforce_type TInt e1;;
          e2' <- enforce_type TInt e2;;
          Success (existT _ _ (EBinop OLess e1' e2'))
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
                (EConst CEmpty))))
      | POCons =>
          e2' <- enforce_type (TList t1) e2;;
          Success (existT _ _ (EBinop (OCons _) e1 e2'))
      | PORange =>
          e1' <- enforce_type TInt e1;;
          e2' <- enforce_type TInt e2;;
          Success (existT _ _ (EBinop ORange e1' e2'))
      end.

    Fixpoint elaborate_record (G : tenv) (xs : list (string * pexpr)) :
      result {t & expr t} :=
      match xs with
      | nil =>
          Success (existT _ _ (EConst CEmpty))
      | (s, p) :: xs =>
          '(existT _ _ e1) <- elaborate G p;;
          '(existT _ _ e2) <- elaborate_record G xs;;
          Success (existT _ _ (EBinop (OPair s _ _) e1 e2))
      end.

    Fixpoint project (t : type) (e : expr t) (s : string) :
      result {t & expr t} :=
      match t as t' return expr t' -> _ with
      | TPair s' _ _ => fun e =>
          if string_dec s s' then
          Success (existT _ _ (EUnop (OFst s' _ _) e))
          else
          project _ (EUnop (OSnd s' _ _) e) s
      | TEmpty => fun _ => error:("Field" s "not found in record")
      | _ => fun _ => error:(e "has type" t "but expected" TPair)
      end e.

    Definition elaborate_proj (G : tenv) (p : pexpr) (s : string) :
      result {t & expr t} :=
      '(existT _ t e) <- elaborate G p;;
      project t e s.
  End ElaborateHelpers.

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
    | PEConst pc =>
        elaborate_const G pc
    | PESingleton p' =>
        '(existT _ t' e') <- elaborate G p';;
        Success (existT _ _ (EBinop (OCons _) e' (EConst (CNil t'))))
    | PEUnop po p1 =>
        elaborate_unop elaborate G po p1
    | PEBinop po p1 p2 =>
        elaborate_binop elaborate G po p1 p2
    | PEFlatmap p1 x p2 =>
        '(existT _ t1 e1) <- elaborate G p1;;
        match t1 as t' return expr t' -> _ with
        | TList t1 => fun e1 =>
            let G' := map.put G x (t1, false) in
            '(existT _ t2 e2) <- elaborate G' p2;;
            e2' <- enforce_type (TList t1) e2;;
            Success (existT _ _ (EFlatmap e1 x e2'))
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
        elaborate_proj elaborate G p s
    end.

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
            c <- elaborate_command G pc;;
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
            c <- elaborate_command G pc;;
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

  (* Well-formedness judgement for `expr`s, stating that an `expr` has no free
   * variables and variables are used with correct types *)
  Inductive wf : tenv -> forall {t : type}, expr t -> Prop :=
    | wf_EVar G t (x : string) :
        map.get G x = Some (t, false) -> wf G (EVar t x)
    | wf_ELoc G t (x : string) :
        map.get G x = Some (t, true) -> wf G (ELoc t x)
    | wf_EConst G {t} (c : const t) : wf G (EConst c)
    | wf_EUnop G {t1 t2} (o : unop t1 t2) (e : expr t1) :
        wf G e -> wf G (EUnop o e)
    | wf_EBinop G {t1 t2 t3} (o : binop t1 t2 t3)
        (e1 : expr t1) (e2 : expr t2) :
        wf G e1 -> wf G e2 -> wf G (EBinop o e1 e2)
    | wf_EFlatmap G {t} (e1 : expr (TList t)) (x : string)
        (e2 : expr (TList t)) :
        wf G e1 -> wf (map.put G x (t, false)) e2 -> wf G (EFlatmap e1 x e2)
    | wf_EIf G {t} (e1 : expr TBool) (e2 e3 : expr t) :
        wf G e1 -> wf G e2 -> wf G e3 -> wf G (EIf e1 e2 e3)
    | wf_ELet G {t1 t2} (x : string) (e1 : expr t1) (e2 : expr t2) :
        wf G e1 -> wf (map.put G x (t1, false)) e2 -> wf G (ELet x e1 e2).

  Fixpoint elaborate_wf (p : pexpr) : forall G t e,
    elaborate G p = Success (existT expr t e) -> wf G e.
  Proof.
    induction p; intros G t e H; unfold elaborate in H; fold elaborate in H.
    - (* PEVar x *)
      destruct (map.get G x) as [[t' [|]] |] eqn : Hmap.
      + (* Some (t', true) *)
        injection H as [= H' H]. rewrite H' in H.
        injection H as H. rewrite <- H.
        apply wf_ELoc. now rewrite Hmap, H'.
      + (* Some (t', false) *)
        injection H as [= H' H]. rewrite H' in H.
        injection H as [= <-].
        apply wf_EVar. now rewrite Hmap, H'.
      + (* None *)
        discriminate H.
    - (* PEConst pc *)
      destruct pc; unfold elaborate_const in H.
      all: injection H as [= _ H].
      all: destruct t; try easy.
      all: repeat injection H as [= <-].
      all: apply wf_EConst.
    - (* PESingleton p *)
      destruct (elaborate G p) as [[t' e'] |] eqn : H'; try easy.
      inversion H.
      apply wf_EBinop.
      * now apply IHp.
      * apply wf_EConst.
    - (* PEUnop po p *)
      destruct po; unfold elaborate_unop in H.
      all: destruct (elaborate G p) as [[t1 e1] |] eqn : H1; try easy.
      all: try (
        destruct (enforce_type _ e1) as [e1' |] eqn : H1'; try easy;
        inversion H;
        apply wf_EUnop;
        apply IHp; rewrite H1;
        enough (existT expr _ e1 = existT expr _ e1');
        now rewrite <- H0 || apply enforce_type_eq;
        destruct t1 || exact H1'
      ).
      + (* POLength *)
        destruct t1; try easy; inversion H; apply wf_EUnop, IHp, H1.
    - (* PEBinop po p1 p2 *)
      destruct po; unfold elaborate_binop in H.
      all: destruct (elaborate G p1) as [[t1 e1] |] eqn : H1; try easy.
      all: destruct (elaborate G p2) as [[t2 e2] |] eqn : H2; try easy.
      all: try (
        destruct (enforce_type _ e1) as [e1' |] eqn : H1'; try easy;
        destruct (enforce_type _ e2) as [e2' |] eqn : H2'; try easy;
        inversion H;
        apply wf_EBinop; (
          apply IHp1; rewrite H1;
          enough (existT expr _ e1 = existT expr _ e1');
          now rewrite <- H0 || apply enforce_type_eq;
          destruct t1 || exact H1'
        ) || (
          apply IHp2; rewrite H2;
          enough (existT expr _ e2 = existT expr _ e2');
          now rewrite <- H0 || apply enforce_type_eq;
          destruct t2 || exact H2'
        )
      ).
      + (* POConcat *)
        destruct t1; try easy;
        destruct t2; try easy.
        * inversion H.
          apply wf_EBinop.
          -- now apply IHp1.
          -- now apply IHp2.
        * destruct (enforce_type _ e2) as [e2' |] eqn : H2'; try easy.
          inversion_clear H.
          apply wf_EBinop.
          -- now apply IHp1.
          -- apply IHp2. rewrite H2.
             f_equal.
             apply enforce_type_eq; auto.
      + (* POEq *)
        destruct (enforce_type _ e2) as [e2' |] eqn : H2'; try easy.
        unfold construct_eq in H.
        destruct t1; try easy.
        all:
          inversion H;
          apply wf_EBinop; (
            now apply IHp1
          ) || (
            apply IHp2; rewrite H2;
            enough (existT expr _ e2 = existT expr _ e2');
            now rewrite <- H0 || apply enforce_type_eq;
            destruct t2 || exact H2'
          ).
      + (* PORepeat *)
        destruct t1; try easy.
        destruct (enforce_type _ e2) as [e2' |] eqn : H2'; try easy.
        inversion H.
        apply wf_EBinop.
        * now apply IHp1.
        * apply IHp2. rewrite H2.
          enough (existT expr _ e2 = existT expr _ e2').
          { now rewrite <- H0. }
          apply enforce_type_eq.
          now destruct t2.
      + (* POPair *)
        inversion H.
        apply wf_EBinop.
        * now apply IHp1.
        * apply wf_EBinop.
          -- now apply IHp2.
          -- apply wf_EConst.
      + (* POCons *)
        destruct (enforce_type _ e2) as [e2' |] eqn : H2'; try easy.
        inversion H.
        apply wf_EBinop.
        * now apply IHp1.
        * apply IHp2. rewrite H2.
          enough (existT expr _ e2 = existT expr _ e2').
          { now rewrite <- H0. }
          apply enforce_type_eq.
          exact H2'.
    - (* PEFlatmap p1 x p2 *)
      destruct (elaborate G p1) as [[t1 e1] |] eqn : H1; try easy.
      destruct t1; try easy.
      destruct (elaborate (map.put G x (t1, false)) p2) as [[t2 e2] |] eqn : H2;
          try easy.
      destruct (enforce_type (TList t1) e2) as [e2' |] eqn : H2'; try easy.
      inversion H.
      apply wf_EFlatmap.
      + now apply IHp1.
      + apply IHp2. rewrite H2.
        enough (existT expr t2 e2 = existT expr (TList t1) e2').
        { now rewrite <- H0. }
        apply enforce_type_eq.
        exact H2'.
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
        inversion H. apply wf_EConst.
      + (* (s, p) :: xs *)
        unfold elaborate_record in H.
        destruct (elaborate G p) as [[t1 e1] |] eqn : H1; try easy.
        assert (elaborate_record elaborate G xs =
          (fix elaborate_record
             (G0 : tenv) (xs0 : list (string * pexpr)) {struct xs0} :
               result {t0 : type & expr t0} :=
             match xs0 with
             | nil =>
                 Success (existT (fun t0 : type => expr t0) TEmpty (EConst CEmpty))
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
      destruct (elaborate G p) as [[t0 e0] |] eqn: H0; try easy.
      unfold project in H.
      induction t0; try easy.
      destruct (string_dec s s0).
      + inversion H.
        apply wf_EUnop.
        apply IHp, H0.
      + admit.
  Admitted.
End WithMap.
