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

    Definition elaborate_proj (G : tenv) (p : pexpr) (s : string) :
      result {t & expr t} :=
      '(existT _ t e) <- elaborate G p;;
      let fix project {t : type} (e : expr t) (s : string) : result {t & expr t} :=
        match t as t' return expr t' -> _ with
        | TPair s' _ _ => fun e =>
            if string_dec s s' then
                Success (existT _ _ (EUnop (OFst s' _ _) e))
            else
                project (EUnop (OSnd s' _ _) e) s
        | TEmpty => fun _ => error:("Field" s "not found in record")
        | _ => fun _ => error:(e "has type" t "but expected" TPair)
        end e
      in
      project e s.
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
End WithMap.
