Require Import PyLevelLang.Language.
Require Import coqutil.Map.Interface.
Require Import PyLevelLang.Elaborate.

Local Open Scope Z_scope.

Fixpoint interp_type (t : type) :=
  match t with
  | TInt => Z
  | TBool => bool
  | TString => string
  | TPair t1 t2 => prod (interp_type t1) (interp_type t2)
  | TList t' => list (interp_type t')
  | TEmpty => unit
  end.

Fixpoint default_val (t : type) : interp_type t :=
  match t as t' return interp_type t' with
  | TInt => 0
  | TBool => false
  | TString => EmptyString
  | TPair t1 t2 => (default_val t1, default_val t2)
  | TList t' => nil
  | TEmpty => tt
  end.

Fixpoint eval_range (lo : Z) (len : nat) : list Z :=
  match len with
  | 0%nat => nil
  | S n => lo :: eval_range (lo + 1) n
  end.

Definition proj_expected (t_expected : type) (v : {t_actual & interp_type t_actual}) : 
  interp_type t_expected :=
  match type_eq_dec (projT1 v) t_expected with
  | left H => cast H _ (projT2 v)
  | _ => default_val t_expected
  end.

Definition compare_values {t : type} : interp_type t -> interp_type t -> bool :=
  match t with
  | TInt => Z.eqb
  | TString => String.eqb
  | TBool => Bool.eqb
  | _ => fun _ _ => false
  end.

Section WithMap.
  Context {locals: map.map string {t & interp_type t}} {locals_ok: map.ok locals}.

  Fixpoint interp_expr (l : locals) {t : type} (e : expr t) : interp_type t :=
    match e in (expr t0) return (interp_type t0) with
    | EVar _ x => match map.get l x with
                  | None => default_val _
                  | Some v => proj_expected _ v
                  end
    | ELoc _ x => match map.get l x with
                  | None => default_val _
                  | Some v => proj_expected _ v
                  end
    | EConst c => match c with
                  | CInt n => n
                  | CBool b => b
                  | CString s => s
                  | CNil t => nil
                  end
    | EUnop o e1 => match o in unop t1 t2 return expr t1 -> interp_type t2 with
                    | ONeg => fun e1 => - (interp_expr l e1)
                    | ONot => fun e1 => negb (interp_expr l e1)
                    | OLength _ => fun e1 => Z.of_nat (length (interp_expr l e1))
                    | OLengthString => fun e1 => Z.of_nat (String.length (interp_expr l e1))
                    | OFst _ _ => fun e1 => fst (interp_expr l e1)
                    | OSnd _ _ => fun e1 => snd (interp_expr l e1)
                    end e1
    | EBinop o e1 e2 => match o in binop t1 t2 t3 return expr t1 -> expr t2 -> interp_type t3 with
                        | OPlus => fun e1 e2 => interp_expr l e1 + interp_expr l e2
                        | OMinus => fun e1 e2 => interp_expr l e1 - interp_expr l e2
                        | OTimes => fun e1 e2 => interp_expr l e1 * interp_expr l e2
                        | ODiv => fun e1 e2 => interp_expr l e1 / interp_expr l e2
                        | OMod => fun e1 e2 => Zmod (interp_expr l e1) (interp_expr l e2)
                        | OAnd => fun e1 e2 => andb (interp_expr l e1) (interp_expr l e2)
                        | OOr => fun e1 e2 => orb (interp_expr l e1) (interp_expr l e2)
                        | OConcat _ => fun e1 e2 => app (interp_expr l e1) (interp_expr l e2)
                        | OConcatString => fun e1 e2 => String.append (interp_expr l e1) (interp_expr l e2)
                        | OLess => fun e1 e2 => (interp_expr l e1) <? (interp_expr l e2)
                        | OEq _ => fun e1 e2 => compare_values (interp_expr l e1) (interp_expr l e2)
                        | ORepeat _ => fun e1 e2 => repeat (interp_expr l e2) (Z.to_nat (interp_expr l e1))
                        | OPair _ _ => fun e1 e2 => (interp_expr l e1, interp_expr l e2)
                        | OCons _ => fun e1 e2 => interp_expr l e1 :: interp_expr l e2
                        | ORange => fun e1 e2 => 
                            let lo := interp_expr l e1 in 
                            let hi := interp_expr l e2 in 
                            eval_range lo (Z.to_nat (hi - lo))
                        end e1 e2
    | EFlatmap e1 x e2 => 
        flat_map (fun y => interp_expr (map.put l x (existT _ _ y)) e1) 
        (interp_expr l e2)
    | EIf e1 e2 e3 => match interp_expr l e1 with
                      | true => interp_expr l e2
                      | false => interp_expr l e3
                      end
    | ELet x e1 e2 => 
        interp_expr (map.put l x (existT _ _ (interp_expr l e1))) e2
    end.

End WithMap.

Section Examples.
  Instance locals : map.map string {t & interp_type t} := SortedListString.map _.
  Instance locals_ok : map.ok locals := SortedListString.ok _.

  Definition ex1 : expr (TList TInt) :=
      (EBinop (OCons _) (EConst (CInt 1))
        (EBinop (OCons _) (EConst (CInt 2))
          (EBinop (OCons _) (EConst (CInt 3))
            (EBinop (OCons _) (EConst (CInt 4))
              (EConst (CNil _)))))).
  Goal interp_expr map.empty ex1 = 1 :: 2 :: 3 :: 4 :: nil.
  reflexivity. Qed.

  Definition ex2 : expr TInt:= 
      (EUnop (OFst _ _) (ELet "x"
        (EConst (CInt 42)) (EBinop (OPair _ _) (EVar TInt "x") (EVar TInt "x")))).
  Goal interp_expr map.empty ex2 = 42.
  reflexivity. Qed.

  Local Open Scope string_scope.
  Definition ex3 : expr (TPair TInt (TPair TBool TString)) :=
      (EBinop (OPair _ _) (EConst (CInt 42))
        (EBinop (OPair _ _) (EConst (CBool true)) (EConst (CString "hello")))).
  Goal interp_expr map.empty ex3 = (42, (true, "hello")).
  reflexivity. Qed.
End Examples.
