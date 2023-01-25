Require Import PyLevelLang.Language.
Require Import PyLevelLang.Elaborate.
Require Import PyLevelLang.Interpret.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Map.Properties.
Require Import coqutil.Datatypes.Result.
Import ResultMonadNotations.

Section Examples.
  Instance tenv : map.map string (type * bool) := SortedListString.map _.
  Instance tenv_ok : map.ok tenv := SortedListString.ok _.
  
  Instance locals : map.map string {t & interp_type t} := SortedListString.map _.
  Instance locals_ok : map.ok locals := SortedListString.ok _.

  Definition elaborate_interpret (l : locals) (p : pexpr) : result {t & interp_type t} :=
    e <- elaborate (map.map_values (fun x => (projT1 x, true)) l) p;;
    Success (existT _ _ (interp_expr l (projT2 e))).

  Local Open Scope Z_scope.
  Local Open Scope string_scope.

  Definition ex1 : pexpr :=
    PEBinop POCons (PEConst (PCInt 1))
      (PEBinop POCons (PEConst (PCInt 2))
        (PEBinop POCons (PEConst (PCInt 3))
          (PESingleton (PEConst (PCInt 4))))).
  Goal elaborate map.empty ex1 =
    Success (existT _ _
      (EBinop (OCons _) (EConst (CInt 1))
        (EBinop (OCons _) (EConst (CInt 2))
          (EBinop (OCons _) (EConst (CInt 3))
            (EBinop (OCons _) (EConst (CInt 4))
              (EConst (CNil _))))))).
  reflexivity. Qed.
  Goal elaborate_interpret map.empty ex1 =
    Success (existT _ (TList TInt) (1 ::  2 :: 3 :: 4 :: nil)).
  reflexivity. Qed.

  Definition ex2 : pexpr :=
    PEBinop POCons (PEConst (PCString "a")) (
      PEBinop POCons (PEConst (PCInt 2)) (
        PEBinop POCons (PEConst (PCInt 3)) (
          PESingleton (PEConst (PCInt 4))))).
  Goal elaborate map.empty ex2 = error:(
    (EBinop (OCons TInt) (EConst (CInt 2))
      (EBinop (OCons TInt) (EConst (CInt 3))
        (EBinop (OCons TInt) (EConst (CInt 4))
          (EConst (CNil TInt)))))
    "has type" 
    (TList TInt)
    "but expected"
    (TList TString)).
  reflexivity. Qed.
  Goal elaborate_interpret map.empty ex2 = error:(
    (EBinop (OCons TInt) (EConst (CInt 2))
      (EBinop (OCons TInt) (EConst (CInt 3))
        (EBinop (OCons TInt) (EConst (CInt 4))
          (EConst (CNil TInt)))))
    "has type" 
    (TList TInt)
    "but expected"
    (TList TString)).
  reflexivity. Qed.

  Definition ex3 : pexpr :=
    PEProj (PELet "x" (PEConst (PCInt 42))
      (PEBinop POPair (PEVar "x") (PEVar "x"))) "0".
  Goal elaborate map.empty ex3 =
    Success (existT _ _
      (EUnop (OFst _ _ _) (ELet "x" (EConst (CInt 42))
        (EBinop (OPair "0" _ _) (EVar TInt "x")
          (EBinop (OPair "1" _ _) (EVar TInt "x")
            (EConst CEmpty)))))).
  reflexivity. Qed.
  Goal elaborate_interpret map.empty ex3 = Success (existT _ TInt 42).
  reflexivity. Qed.

  Definition ex4 : pexpr :=
    PEProj (PELet "x" (PEConst (PCInt 42))
      (PEBinop POPair (PEVar "x") (PEVar "y"))) "0".
  Goal elaborate map.empty ex4 = error:("Undefined variable" "y").
  reflexivity. Qed.
  Goal elaborate_interpret map.empty ex4 = error:("Undefined variable" "y").
  reflexivity. Qed.

  Definition ex5 : pexpr :=
    PEBinop POPair (PEConst (PCInt 42))
      (PEBinop POPair (PEConst (PCBool true)) (PEConst (PCString "hello"))).
  Goal elaborate map.empty ex5 =
    Success (existT _ _
      (EBinop (OPair "0" _ _) (EConst (CInt 42))
        (EBinop (OPair "1" _ _)
          (EBinop (OPair "0" _ _) (EConst (CBool true))
            (EBinop (OPair "1" _ _) (EConst (CString "hello"))
              (EConst CEmpty)))
          (EConst CEmpty)))).
  reflexivity. Qed.
  Goal elaborate_interpret map.empty ex5 =
    Success (existT _
      (TPair "0" TInt
        (TPair "1"
          (TPair "0" TBool
            (TPair "1" TString
              TEmpty))
          TEmpty))
      (42, ((true, ("hello", tt)), tt))).
  reflexivity. Qed.

  Definition ex6 : pexpr :=
    PERecord
      (("bool", PEConst (PCBool false))
      :: ("string", PEConst (PCString "abc"))
      :: ("int", PEConst (PCInt (-2)))
      :: nil).
  Goal elaborate map.empty ex6 =
    Success (existT _ _
      (EBinop (OPair "bool" _ _) (EConst (CBool false))
        (EBinop (OPair "string" _ _) (EConst (CString "abc"))
          (EBinop (OPair "int" _ _) (EConst (CInt (-2)))
            (EConst CEmpty))))).
  reflexivity. Qed.
  Goal elaborate_interpret map.empty ex6 =
    Success (existT _
      (TPair "bool" TBool
        (TPair "string" TString
          (TPair "int" TInt TEmpty)))
      (false, ("abc", (-2, tt)))).
  reflexivity. Qed.

  Definition ex7 : pexpr :=
    PEProj (PERecord
      (("a", PEConst (PCBool true))
      :: ("b", PEConst (PCInt 50))
      :: nil))
    "b".
  Goal elaborate map.empty ex7 =
    Success (existT _ _
      (EUnop (OFst _ _ _)
        (EUnop (OSnd _ _ _)
          (EBinop (OPair "a" _ _) (EConst (CBool true))
            (EBinop (OPair "b" _ _) (EConst (CInt 50))
              (EConst CEmpty)))))).
  reflexivity. Qed.
  Goal elaborate_interpret map.empty ex7 =
    Success (existT _ TInt 50).
  reflexivity. Qed.

  Definition ex8 : pexpr :=
    PEBinop POEq (PEConst (PCBool true)) (PEConst (PCInt 5)).
  Goal elaborate map.empty ex8 =
    error:((EConst (CInt 5)) "has type" TInt "but expected" TBool).
  reflexivity. Qed.

  Definition ex9 : pexpr :=
    PEBinop POEq (PEConst (PCBool true)) (PEConst (PCBool false)).
  Goal elaborate map.empty ex9 =
    Success (existT _ _
      (EBinop (OEq TBool eq_refl)
        (EConst (CBool true)) (EConst (CBool false)))).
  reflexivity. Qed.
End Examples.
