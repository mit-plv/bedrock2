Require Import PyLevelLang.Language.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
Require Import coqutil.Datatypes.Result.
Import ResultMonadNotations.

Definition elaborate_unop (po : punop) (t1 : type) : result {t2 & unop t1 t2} :=
  match po with
  | PONeg =>
      match t1 with
      | TInt =>
          Success (existT _ _ ONeg)
      | _ => error:("PONeg with wrong type")
      end
  | PONot =>
      match t1 with
      | TBool =>
          Success (existT _ _ ONot)
      | _ => error:("PONot with wrong type")
      end
  | POLength =>
      match t1 with
      | TList t =>
          Success (existT _ _ (OLength t))
      | _ => error:("POLength with wrong type")
      end
  | POLengthString =>
      match t1 with
      | TString =>
          Success (existT _ _ OLengthString)
      | _ => error:("POLengthString with wrong type")
      end
  | POFst =>
      match t1 with
      | TPair t1' t2' =>
          Success (existT _ _ (OFst t1' t2'))
      | _ => error:("POFst with wrong type")
      end
  | POSnd =>
      match t1 with
      | TPair t1' t2' =>
          Success (existT _ _ (OSnd t1' t2'))
      | _ => error:("POSnd with wrong type")
      end
  end.

Definition elaborate_binop (po : pbinop) (t1 : type) (t2 : type) :
  result {t3 & binop t1 t2 t3} :=
  match po with
  | POPlus =>
      match t1, t2 with
      | TInt, TInt =>
          Success (existT _ _ OPlus)
      | _, _ => error:("POPlus with wrong types")
      end
  | POMinus =>
      match t1, t2 with
      | TInt, TInt =>
          Success (existT _ _ OMinus)
      | _, _ => error:("POMinus with wrong types")
      end
  | POTimes =>
      match t1, t2 with
      | TInt, TInt =>
          Success (existT _ _ OTimes)
      | _, _ => error:("POTimes with wrong types")
      end
  | PODiv =>
      match t1, t2 with
      | TInt, TInt =>
          Success (existT _ _ ODiv)
      | _, _ => error:("PODiv with wrong types")
      end
  | POMod =>
      match t1, t2 with
      | TInt, TInt =>
          Success (existT _ _ OMod)
      | _, _ => error:("POMod with wrong types")
      end
  | POAnd =>
      match t1, t2 with
      | TBool, TBool =>
          Success (existT _ _ OAnd)
      | _, _ => error:("POAnd with wrong types")
      end
  | POOr =>
      match t1, t2 with
      | TBool, TBool =>
          Success (existT _ _ OOr)
      | _, _ => error:("POOr with wrong types")
      end
  | POConcat =>
      match t1, t2 with
      | TList t1, TList t2 =>
          match type_eq_dec t1 t2 with
          | left H =>
              let o : binop (TList t1) (TList t2) _ :=
                cast H (fun t => binop _ (TList t) _) (OConcat t1) in
              Success (existT _ _ o)
          | _ => error:("POConcat with mismatched types")
          end
      | _, _ => error:("POConcat with wrong types")
      end
  | POConcatString =>
      match t1, t2 with
      | TString, TString =>
          Success (existT _ _ OConcatString)
      | _, _ => error:("POConcatString with wrong types")
      end
  | POLess =>
      match t1, t2 with
      | TInt, TInt =>
          Success (existT _ _ OLess)
      | _, _ => error:("POLess with wrong types")
      end
  | POEq =>
      match type_eq_dec t1 t2 with
      | left H =>
          let o : binop t1 t2 _ :=
            cast H (fun t => binop _ t _) (OEq t1) in
          Success (existT _ _ o)
      | _ => error:("POEq with wrong types")
      end
  | PORepeat =>
      match t1 with
      | TInt =>
          Success (existT _ _ (ORepeat t2))
      | _ => error:("PORepeat with wrong type")
      end
  | POPair =>
      Success (existT _ _ (OPair t1 t2))
  | POCons =>
      match t2 with
      | TList t2 =>
          match type_eq_dec t1 t2 with
          | left H =>
              let o : binop t1 (TList t2) _ :=
                cast H (fun t => binop _ (TList t) _) (OCons t1) in
              Success (existT _ _ o)
          | _ => error:("POCons with mismatched types")
          end
      | _ => error:("POCons with wrong types")
      end
  | PORange =>
      match t1, t2 with
      | TInt, TInt =>
          Success (existT _ _ ORange)
      | _, _ => error:("PORange with wrong types")
      end
  end.

Section WithMap.
  (* abstract all functions in this section over the implementation of the map,
     and over its spec (map.ok) *)
  Context {tenv: map.map string (type * bool)} {tenv_ok: map.ok tenv}.

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
        | None => error:("PEVar with undefined variable")
        end
    | PEConst c =>
        Success (existT _ _ (EConst c))
    | PESingleton p' =>
        '(existT _ t' e') <- elaborate G p' ;;
        Success (existT _ _ (EBinop (OCons _) e' (EConst (CNil t'))))
    | PEUnop po p1 =>
        '(existT _ t1 e1) <- elaborate G p1 ;;
        '(existT _ t2 o) <- elaborate_unop po t1 ;;
        Success (existT _ _ (EUnop o e1))
    | PEBinop po p1 p2 =>
        '(existT _ t1 e1) <- elaborate G p1 ;;
        '(existT _ t2 e2) <- elaborate G p2 ;;
        '(existT _ t3 o) <- elaborate_binop po t1 t2 ;;
        Success (existT _ _ (EBinop o e1 e2))
    | PEFlatmap p1 x p2 =>
        '(existT _ t1 e1) <- elaborate G p1 ;;
        let G' := map.put G x (t1, false) in
        '(existT _ t2 e2) <- elaborate G' p2 ;;
        match t1 as t1' return expr t1' -> _ with
        | TList t' => fun e1 =>
            match type_eq_dec t2 (TList t') with
            | left H2 =>
                Success (existT _ _ (EFlatmap e1 x (cast H2 _ e2)))
            | _ => error:("PEFlatmap with mismatched types")
            end
        | _ => fun _ => error:("PEFlatmap with non-list")
        end e1
    | PEIf p1 p2 p3 =>
        '(existT _ t1 e1) <- elaborate G p1 ;;
        '(existT _ t2 e2) <- elaborate G p2 ;;
        '(existT _ t3 e3) <- elaborate G p3 ;;
        match t1 as t' return expr t' -> _ with
        | TBool => fun e1 =>
            match type_eq_dec t3 t2 with
            | left H =>
                Success (existT _ _ (EIf e1 e2 (cast H _ e3)))
            | _ => error:("PEIf with mismatched types")
            end
        | _ => fun _ => error:("PEIf with non-boolean condition")
        end e1
    | PELet x p1 p2 =>
        '(existT _ t1 e1) <- elaborate G p1 ;;
        let G' := map.put G x (t1, false) in
        '(existT _ t2 e2) <- elaborate G' p2 ;;
        Success (existT _ _ (ELet x e1 e2))
    end.
End WithMap.
