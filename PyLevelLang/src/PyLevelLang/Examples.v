Require Import PyLevelLang.Language.
Require Import PyLevelLang.Elaborate.
Require Import PyLevelLang.Interpret.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString.
Require Import coqutil.Datatypes.Result.
Import ResultMonadNotations.

Section Examples.
  Instance tenv : map.map string (type * bool) := SortedListString.map _.
  Instance tenv_ok : map.ok tenv := SortedListString.ok _.
  
  Instance locals : map.map string {t & interp_type t} := SortedListString.map _.
  Instance locals_ok : map.ok locals := SortedListString.ok _.

  Definition elaborate_interpret (p : pexpr) : result {t & interp_type t} :=
    match elaborate map.empty p with
    | Success v => Success (existT _ _ (interp_expr map.empty (projT2 v)))
    | Failure e => Failure e
    end.

  Local Open Scope Z_scope.
  Local Open Scope string_scope.

  Definition ex1 : pexpr :=
    PEBinop POCons (PEConst (CInt 1))
      (PEBinop POCons (PEConst (CInt 2))
        (PEBinop POCons (PEConst (CInt 3))
          (PESingleton (PEConst (CInt 4))))).
  Goal elaborate map.empty ex1 =
    Success (existT _ _
      (EBinop (OCons _) (EConst (CInt 1))
        (EBinop (OCons _) (EConst (CInt 2))
          (EBinop (OCons _) (EConst (CInt 3))
            (EBinop (OCons _) (EConst (CInt 4))
              (EConst (CNil _))))))).
  reflexivity. Qed.
  Goal elaborate_interpret ex1 = Success (existT _ (TList TInt) (1 ::  2 :: 3 :: 4 :: nil)).
  reflexivity. Qed.

  Definition ex2 : pexpr :=
    PEBinop POCons (PEConst (CString "a")) (
      PEBinop POCons (PEConst (CInt 2)) (
        PEBinop POCons (PEConst (CInt 3)) (
          PESingleton (PEConst (CInt 4))))).
  Goal elaborate map.empty ex2 = error:("POCons with mismatched types").
  reflexivity. Qed.
  Goal elaborate_interpret ex2 = error:("POCons with mismatched types").
  reflexivity. Qed.

  Definition ex3 : pexpr :=
    PEUnop POFst (PELet "x"
      (PEConst (CInt 42)) (PEBinop POPair (PEVar "x") (PEVar "x"))).
  Goal elaborate map.empty ex3 =
    Success (existT _ _
      (EUnop (OFst _ _) (ELet "x"
        (EConst (CInt 42)) (EBinop (OPair _ _) (EVar TInt "x") (EVar TInt "x"))))).
  reflexivity. Qed.
  Goal elaborate_interpret ex3 = Success (existT _ TInt 42).
  reflexivity. Qed.

  Definition ex4 : pexpr :=
    PEUnop POFst (PELet "x"
      (PEConst (CInt 42)) (PEBinop POPair (PEVar "x") (PEVar "y"))).
  Goal elaborate map.empty ex4 = error:("PEVar with undefined variable").
  reflexivity. Qed.
  Goal elaborate_interpret ex4 = error:("PEVar with undefined variable").
  reflexivity. Qed.

  Definition ex5 : pexpr :=
    PEBinop POPair (PEConst (CInt 42))
      (PEBinop POPair (PEConst (CBool true)) (PEConst (CString "hello"))).
  Goal elaborate map.empty ex5 =
    Success (existT _ _
      (EBinop (OPair _ _) (EConst (CInt 42))
        (EBinop (OPair _ _) (EConst (CBool true)) (EConst (CString "hello"))))).
  reflexivity. Qed.
  Goal elaborate_interpret ex5 = Success (existT _ (TPair TInt (TPair TBool TString)) (42, (true, "hello"))).
  reflexivity. Qed.
End Examples.
