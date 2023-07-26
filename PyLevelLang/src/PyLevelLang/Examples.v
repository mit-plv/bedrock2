Require Import PyLevelLang.Language.
Require Import PyLevelLang.Elaborate.
Require Import PyLevelLang.Interpret.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Map.Properties.
Require Import coqutil.Datatypes.Result.
Require Import compiler.NameGen compiler.StringNameGen.
Import ResultMonadNotations.

Section Examples.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Instance tenv : map.map string (type * bool) := SortedListString.map _.
  Instance tenv_ok : map.ok tenv := SortedListString.ok _.
  
  Instance locals : map.map string {t & interp_type t} := SortedListString.map _.
  Instance locals_ok : map.ok locals := SortedListString.ok _.

  Instance namemap : map.map string string := SortedListString.map _.
  Instance namemap_ok : map.ok namemap := SortedListString.ok _.
  Instance NG : NameGen string N := StringNameGen.

  Definition elaborate_interpret (l : locals) (p : pexpr) : result {t & interp_type t} :=
    let G : tenv := map.map_values (fun x => (projT1 x, true)) l in
    let vars := map.keys l in
    let nm : namemap := map.of_list (List.zip pair vars vars) in
    e <- elaborate nm G p;;
    Success (existT _ _ (interp_expr l (projT2 e))).

  Local Open Scope Z_scope.
  Local Open Scope string_scope.

  Definition ex1 : pexpr :=
    PEBinop POCons (PEAtom (PAInt 1))
      (PEBinop POCons (PEAtom (PAInt 2))
        (PEBinop POCons (PEAtom (PAInt 3))
          (PESingleton (PEAtom (PAInt 4))))).
  Goal elaborate map.empty map.empty ex1 =
    Success (existT _ _
      (EBinop (OCons _) (EAtom (AInt 1))
        (EBinop (OCons _) (EAtom (AInt 2))
          (EBinop (OCons _) (EAtom (AInt 3))
            (EBinop (OCons _) (EAtom (AInt 4))
              (EAtom (ANil _))))))).
  reflexivity. Qed.
  Goal elaborate_interpret map.empty ex1 =
    Success (existT _ (TList TInt) (1 ::  2 :: 3 :: 4 :: nil)).
  reflexivity. Qed.

  Definition ex2 : pexpr :=
    PEBinop POCons (PEAtom (PAString "a")) (
      PEBinop POCons (PEAtom (PAInt 2)) (
        PEBinop POCons (PEAtom (PAInt 3)) (
          PESingleton (PEAtom (PAInt 4))))).
  Goal elaborate map.empty map.empty ex2 = error:(
    (EBinop (OCons TInt) (EAtom (AInt 2))
      (EBinop (OCons TInt) (EAtom (AInt 3))
        (EBinop (OCons TInt) (EAtom (AInt 4))
          (EAtom (ANil TInt)))))
    "has type" 
    (TList TInt)
    "but expected"
    (TList TString)).
  reflexivity. Qed.
  Goal elaborate_interpret map.empty ex2 = error:(
    (EBinop (OCons TInt) (EAtom (AInt 2))
      (EBinop (OCons TInt) (EAtom (AInt 3))
        (EBinop (OCons TInt) (EAtom (AInt 4))
          (EAtom (ANil TInt)))))
    "has type" 
    (TList TInt)
    "but expected"
    (TList TString)).
  reflexivity. Qed.

  Definition ex3 : pexpr :=
    PEProj (PELet "x" (PEAtom (PAInt 42))
      (PEBinop POPair (PEVar "x") (PEVar "x"))) "0".
  Goal exists x, elaborate map.empty map.empty ex3 =
    Success (existT _ _
      (EUnop (OFst _ _ _) (ELet x (EAtom (AInt 42))
        (EBinop (OPair "0" _ _) (EVar TInt x)
          (EBinop (OPair "1" _ _) (EVar TInt x)
            (EAtom AEmpty)))))).
  eexists. reflexivity. Qed.
  Goal elaborate_interpret map.empty ex3 = Success (existT _ TInt 42).
  reflexivity. Qed.

  Definition ex4 : pexpr :=
    PEProj (PELet "x" (PEAtom (PAInt 42))
      (PEBinop POPair (PEVar "x") (PEVar "y"))) "0".
  Goal elaborate map.empty map.empty ex4 = error:("Undefined variable" "y").
  reflexivity. Qed.
  Goal elaborate_interpret map.empty ex4 = error:("Undefined variable" "y").
  reflexivity. Qed.

  Definition ex5 : pexpr :=
    PEBinop POPair (PEAtom (PAInt 42))
      (PEBinop POPair (PEAtom (PABool true)) (PEAtom (PAString "hello"))).
  Goal elaborate map.empty map.empty ex5 =
    Success (existT _ _
      (EBinop (OPair "0" _ _) (EAtom (AInt 42))
        (EBinop (OPair "1" _ _)
          (EBinop (OPair "0" _ _) (EAtom (ABool true))
            (EBinop (OPair "1" _ _) (EAtom (AString "hello"))
              (EAtom AEmpty)))
          (EAtom AEmpty)))).
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
      (("bool", PEAtom (PABool false))
      :: ("string", PEAtom (PAString "abc"))
      :: ("int", PEAtom (PAInt (-2)))
      :: nil).
  Goal elaborate map.empty map.empty ex6 =
    Success (existT _ _
      (EBinop (OPair "bool" _ _) (EAtom (ABool false))
        (EBinop (OPair "string" _ _) (EAtom (AString "abc"))
          (EBinop (OPair "int" _ _) (EAtom (AInt (-2)))
            (EAtom AEmpty))))).
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
      (("a", PEAtom (PABool true))
      :: ("b", PEAtom (PAInt 50))
      :: nil))
    "b".
  Goal elaborate map.empty map.empty ex7 =
    Success (existT _ _
      (EUnop (OFst _ _ _)
        (EUnop (OSnd _ _ _)
          (EBinop (OPair "a" _ _) (EAtom (ABool true))
            (EBinop (OPair "b" _ _) (EAtom (AInt 50))
              (EAtom AEmpty)))))).
  reflexivity. Qed.
  Goal elaborate_interpret map.empty ex7 =
    Success (existT _ TInt 50).
  reflexivity. Qed.

  Definition ex8 : pexpr :=
    PEBinop POEq (PEAtom (PABool true)) (PEAtom (PAInt 5)).
  Goal elaborate map.empty map.empty ex8 =
    error:((EAtom (AInt 5)) "has type" TInt "but expected" TBool).
  reflexivity. Qed.

  Definition ex9 : pexpr :=
    PEBinop POEq (PEAtom (PABool true)) (PEAtom (PABool false)).
  Goal elaborate map.empty map.empty ex9 =
    Success (existT _ _
      (EBinop (OEq TBool eq_refl)
        (EAtom (ABool true)) (EAtom (ABool false)))).
  reflexivity. Qed.

  Definition ex10 : expr _ :=
    EFold (EBinop (OCons _) (EAtom (AInt 2)) (EBinop (OCons _) (EAtom (AInt 5)) (EAtom (ANil _)))) (EAtom (AInt 3)) "x" "y" (EBinop OPlus (EVar _ "x") (EVar _ "y")).
  Compute interp_expr map.empty ex10.
End Examples.
