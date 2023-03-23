Require Import PyLevelLang.Language.
Require Import PyLevelLang.Elaborate.
Require Import PyLevelLang.Notations.
Require Import PyLevelLang.Interpret.
Require Import PyLevelLang.SamplePrograms.
Require Import PyLevelLang.Optimize.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Map.Properties.
Require Import coqutil.Datatypes.Result.
Require Import Coq.Lists.List.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.


Section Queries_Section.
  Instance tenv : map.map string (type * bool) := SortedListString.map _.
  Instance tenv_ok : map.ok tenv := SortedListString.ok _.
  Instance locals : map.map string {t & interp_type t} := SortedListString.map _.
  Instance locals_ok : map.ok locals := SortedListString.ok _.

  Fixpoint record (l : list (string * type)) : type :=
    match l with
    | nil => TEmpty
    | (s, t) :: xs => TPair s t (record xs)
    end.

  Compute interp_type (record (("a", TString) :: ("b", TInt) :: nil)).

  Fixpoint from_tuple {l : list (string * type)} (tp : interp_type (record l)) : expr (record l) :=
    match l return interp_type (record l) -> expr (record l) with
    | nil => fun _ => EAtom AEmpty
    | (s, t) :: xs => fun tp => let (a, b) := tp in EBinop (OPair s _ _) (reify t a) (from_tuple (snd tp))
    end tp.

  Definition artist := record (("id", TInt) :: ("name", TString) :: nil).

  Definition artist_1 := from_tuple ((1, ("AC/DC", tt)) : interp_type artist).
  Definition artist_2 := from_tuple ((2, ("Accept", tt)) : interp_type artist).
  Definition artist_3 := from_tuple ((3, ("Aerosmith", tt)) : interp_type artist).
  Definition artist_4 := from_tuple ((4, ("Alanis Morisette", tt)) : interp_type artist).

  Definition artists := listify (artist_1 :: artist_2 :: artist_3 :: artist_4 :: nil).

  Compute interp_expr map.empty artists.
  
  Definition artists_filter_q := 
    EFlatmap artists "x" (
      EIf (EBinop OLess (EUnop (OFst _ _ _) (ELoc artist "x")) (EAtom (AInt 3)))
        (EBinop (OCons artist) (ELoc artist "x") (EAtom (ANil _)))
        (EAtom (ANil _))
    ).
  
  Compute artists_filter_q.

  Definition artists_filter_q' := 
    EFlatmap artists "x" (EBinop (OCons _) (EUnop (OFst "id" _ (TPair "name" TString TEmpty)) (EVar _ "x")) (EAtom (ANil TInt))).

  Compute interp_expr map.empty artists_filter_q.

  Definition test := PEProj (PERecord (("a", PEAtom (PAInt 1)) :: ("b", PEAtom (PAInt 2)) :: nil)) "a".

  Fixpoint pexpr_list (t : type) (l : list (pexpr)) : pexpr :=
    match l with
    | nil => PEAtom (PANil t)
    | x :: xs => PEBinop POCons x (pexpr_list t xs)
    end.

  Fixpoint as_pexpr {t : type} (v : interp_type t) : pexpr := 
    match t return interp_type t -> pexpr with
    | TInt => fun v => PEAtom (PAInt v)
    | TBool => fun v => PEAtom (PABool v)
    | TString => fun v => PEAtom (PAString v)
    | TPair _ _ _  => fun v => PEBinop POPair (as_pexpr (fst v)) (as_pexpr (snd v))
    | TEmpty => fun v => PERecord nil
    | TList t => fun v => pexpr_list t (map as_pexpr v)
    end v.

  Fixpoint zip {A B} (l1 : list A) (l2 : list B) : list (A * B) :=
    match l1, l2 with
    | x :: xs, y :: ys => (x, y) :: zip xs ys
    | _, _ => nil
    end.

  Fixpoint pexperify {l : list (string * type)} (tp : interp_type (record l)) : list pexpr :=
    match l return interp_type (record l) -> list pexpr  with
    | nil => fun _ => nil
    | (s, t) :: xs => fun tp => as_pexpr (fst tp) :: (pexperify (snd tp))
    end tp.
    
  Definition from_tuple' {l : list (string * type)} (tp : interp_type (record l)) : pexpr :=
    PERecord (zip (map fst l) (pexperify tp)).

  Definition artist_1' := from_tuple' ((1, ("AC/DC", tt)) : interp_type artist).
  Definition artist_2' := from_tuple' ((2, ("Accept", tt)) : interp_type artist).
  Definition artist_3' := from_tuple' ((3, ("Aerosmith", tt)) : interp_type artist).
  Definition artist_4' := from_tuple' ((4, ("Alanis Morisette", tt)) : interp_type artist).

  Definition artists' := pexpr_list artist (artist_1' :: artist_2' :: artist_3' :: artist_4' :: nil).

  Compute artists'.

  Local Open Scope pylevel_scope.

  Definition filter_test := <{
    "ans" <- flatmap artists' "x" (if "x"["id"] < 3 then ["x"] else nil[artist])
    }>.

  Local Close Scope pylevel_scope.

  Compute filter_test.
  Compute run_program ((("ans", (TList artist, true)) :: nil)) filter_test.

End Queries_Section.
