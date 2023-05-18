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

  (* SELECT * FROM artists WHERE id < 3 *)
  Definition filter_test := <{
    "ans" <- flatmap artists' "x" (if "x"["id"] < 3 then ["x"] else nil[artist])
    }>.
  Compute run_program ((("ans", (TList artist, true)) :: nil)) filter_test.

  (* SELECT SUM(id) FROM artists *)
  Definition fold_test := <{
    "ans" <- fold artists' 0 "x" "y" ("x"["id"] + "y")
  }>.
  Compute run_program ((("ans", (TInt, true)) :: nil)) fold_test.

  (* SELECT name FROM artists WHERE id < 3 *)
  Definition select_test := <{
    "ans" <- flatmap (flatmap artists' "x" (if "x"["id"] < 3 then ["x"] else nil[artist])) "y" ["y"["name"]]
  }>.
  Compute run_program ((("ans", (TList TString, true)) :: nil)) select_test.

  Definition select_test_elaborated' : command := 
    Eval cbv in match elaborate_command (map.of_list (("ans", (TList TString, true))::nil)) select_test with
    | Success x => x
    | _ => _
    end.
  
  Definition select_test_elaborated := Eval cbv in match select_test_elaborated' with
                                                    | CGets _ e => e
                                                    | _ => _
                                                    end.
  Compute select_test_elaborated.
  Compute flatmap_flatmap select_test_elaborated.
  Compute interp_expr map.empty select_test_elaborated.

  Definition album := record (("album_id", TInt) :: ("title", TString) :: ("artist_id", TInt) :: nil).
  Definition albums := pexpr_list album (map from_tuple'
    ((1, ("For Those About To Rock We Salute You", (1, tt)))
      :: (2, ("Balls to the Wall", (2, tt)))
      :: (3, ("Restless and Wild", (2, tt)))
      :: (4, ("Let There Be Rock", (1, tt)))
      :: (5, ("Big Ones", (3, tt)))
      :: (6, ("Jaggged Little Pill", (4, tt)))
      :: (7, ("Facelift", (5, tt)))
      :: nil
      : list (interp_type album)
           )).

  Definition t := TPair "0" album (TPair "1" artist Unit).

  (* SELECT * FROM albums JOIN artists WHERE album_id = id *)
  Definition join_test := <{
    "ans" <- flatmap (flatmap albums "y" (flatmap artists' "z" [("y", "z")])) "x" 
    (if fst("x")["artist_id"] == snd("x")["id"] then ["x"] else nil[t])
  }>.
  Compute run_program ((("ans", (TList (t), true))) :: nil) join_test.

  Definition tmp' : command := 
    Eval cbv in match elaborate_command (map.of_list (("ans", (TList t, true))::nil)) join_test with
    | Success x => x
    | _ => _
    end.
  
  Definition tmp := Eval cbv in match tmp' with
                                | CGets _ e => e
                                | _ => _
                                end.
  Compute tmp.
  Compute flatmap_flatmap tmp.
  Compute interp_expr map.empty tmp.

  Local Close Scope pylevel_scope.

  Declare Scope query_sugar_scope.
  Notation "'join' ( a : x ) ( b : y )" := 
    (PEFlatmap a x%string (PEFlatmap b y%string (PEBinop POPair (PEVar x%string) (PEVar y%string))))
    (at level 0, left associativity) : query_sugar_scope.

  Declare Scope pretty_expr_scope.
  Notation "[ e | x <- l ]" := (EFlatmap l x%string (EBinop (OCons _) e (EAtom (ANil _))))
   (at level 10, only printing, left associativity) : pretty_expr_scope.

  Notation "'nil'" := (EAtom (ANil _))
    (at level 0, only printing) : pretty_expr_scope.

  Notation "[ z ]" := (EBinop (OCons _) z (EAtom (ANil _)))
   (at level 0, only printing) : pretty_expr_scope.

  Notation "[ x , .. , y , z ]" := 
    (EBinop (OCons _) x .. (EBinop (OCons _) y (EBinop (OCons _) z (EAtom (ANil _)))) ..)
   (at level 110, only printing) : pretty_expr_scope.

  Notation "{ x , .. , y , z }" := 
    (EBinop (OPair _ _ _) x .. (EBinop (OPair _ _ _) y (EBinop (OPair _ _ _) z (EAtom AEmpty))) ..)
   (at level 110, only printing) : pretty_expr_scope.

  Declare Custom Entry pretty_record_fields.

  Notation "{{ x }}" := x
    (x custom pretty_record_fields at level 100, only printing) : pretty_expr_scope.

  Notation "x : t , rest" := (TPair x t rest)
    (in custom pretty_record_fields at level 100, x constr at level 0, t constr at level 0, right associativity, only printing) : pretty_expr_scope.

  Notation "x : t" := (TPair x t TEmpty)
    (in custom pretty_record_fields at level 100, x constr at level 0, t constr at level 0, only printing) : pretty_expr_scope.

  Notation "{{}}" := TEmpty : pretty_expr_scope.

  Notation "'<' x '>'" := (EAtom (_ x))
   (at level 10, only printing, format "< x >") : pretty_expr_scope.

  Notation "()" := (EAtom AEmpty)
   (at level 10, only printing) : pretty_expr_scope.

  Notation "$ x" := (EVar _ x%string)
    (at level 10, only printing, format "$ x") : pretty_expr_scope.

  Notation "'if' x 'then' y 'else' z" := (EIf x y z)
    (at level 0, only printing) : pretty_expr_scope.

  Notation "x == y" := (EBinop (OEq _ _) x y)
    (at level 80, only printing) : pretty_expr_scope.

  Notation "x [ k ]" := (EUnop (OFst k _ _) x)
    (at level 10, only printing, left associativity) : pretty_expr_scope.

  Notation "x" := (EUnop (OSnd _ _ _) x)
    (at level 10, only printing, right associativity) : pretty_expr_scope.

  Notation "[ x | x <- l , e ]" := 
    (EFlatmap l x%string (EIf e (EBinop (OCons _) (EVar _ x%string) (EAtom (ANil _))) (EAtom (ANil _))))
    (at level 10, only printing, l at level 9, x at level 0, e at level 10, left associativity) : pretty_expr_scope.

  Local Open Scope pretty_expr_scope.
  Compute tmp.
  Compute partial (flatmap_singleton (flatmap_flatmap (flatmap_flatmap tmp))).
  Local Close Scope pretty_expr_scope.

End Queries_Section.
