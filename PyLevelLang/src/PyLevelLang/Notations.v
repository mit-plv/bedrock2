Require Import PyLevelLang.Language.
Require Import PyLevelLang.Elaborate.
Require Import PyLevelLang.Interpret.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Map.Properties.
Require Import coqutil.Datatypes.Result.
Require Import Coq.Lists.List.
Import ListNotations.
Import ResultMonadNotations.

Declare Scope pylevel_scope.
Declare Custom Entry py_expr.
Declare Custom Entry py_comm.
Declare Custom Entry py_type.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Local Open Scope pylevel_scope.

Coercion PEVar : string >-> pexpr.

Coercion PAInt : Z >-> patom.
Coercion PABool : bool >-> patom.
Coercion PEAtom : patom >-> pexpr.

Notation "<{ e }>"       := (e : pcommand) (at level 0, e custom py_comm at level 99, only parsing) : pylevel_scope.
Notation "<{ e }>"       := e (at level 0, e custom py_comm at level 99, only printing) : pylevel_scope.
Notation "<[ e ]>"       := e (in custom py_expr at level 0, e constr at level 200) : pylevel_scope.
Notation "<[ e ]>"       := e (in custom py_comm at level 0, e constr at level 200) : pylevel_scope.
Notation "<[ e ]>"       := e (in custom py_type at level 0, e constr at level 200) : pylevel_scope.
Notation "( x )"         := x (in custom py_expr at level 0, x custom py_expr at level 99) : pylevel_scope.
Notation "( x )"         := x (in custom py_comm at level 0, x custom py_comm at level 99) : pylevel_scope.
Notation "( x )"         := x (in custom py_type at level 0, x custom py_type at level 99) : pylevel_scope.
Notation "x"             := x (in custom py_expr at level 0, x constr at level 0) : pylevel_scope.
Notation "x"             := x (in custom py_comm at level 0, x constr at level 0) : pylevel_scope.
Notation "x"             := x (in custom py_type at level 0, x constr at level 0) : pylevel_scope.

(* TODO Allow string constants (which are different from vars) *)

(* Command parsing *)
Notation "'skip'"                     := (PCSkip)
   (in custom py_comm at level 0) : pylevel_scope.
Notation "c1 ; c2"                    := (PCSeq c1 c2)
   (in custom py_comm at level 90, right associativity, c1 custom py_comm, c2 custom py_comm) : pylevel_scope.
Notation "'let' x := p 'in' c"        := (PCLet x p c)
   (in custom py_comm at level 100, p custom py_expr, c custom py_comm) : pylevel_scope.
Notation "'let' 'mut' x := p 'in' c"    := (PCLetMut x%string p c)
   (in custom py_comm at level 100, p custom py_expr, c custom py_comm) : pylevel_scope.
Notation "x <- p"                     := (PCGets x p)
   (in custom py_comm at level 50, p custom py_expr) : pylevel_scope.
Notation "'if' p 'then' c1 'else' c2 'end'" := (PCIf p c1 c2)
   (in custom py_comm at level 80, p custom py_expr, c1 custom py_comm, c2 custom py_comm) : pylevel_scope.
Notation "'for' x 'in' p : c 'end'"  := (PCForeach x p c)
   (in custom py_comm at level 80, p custom py_expr, c custom py_comm) : pylevel_scope.

(* Type parsing (Types are prefixed with @ so they do not become keywords and pollute the namespace *)
Notation Int    := TInt.
Notation Bool   := TBool.
Notation String := TString.
Notation Pair   := TPair.
Notation Unit   := TEmpty.
Notation List   := TList.


(* Expression parsing *)

(* Unary operations (PEUnop) *)
Notation "- x"         := (PEUnop PONeg x)
   (in custom py_expr at level 10) : pylevel_scope.
Notation "! x"         := (PEUnop PONot x)
   (in custom py_expr at level 10) : pylevel_scope.
Notation "'length(' x ')'"   := (PEUnop POLength x)
   (in custom py_expr at level 10) : pylevel_scope.


(* not a unary operator, move *)
Notation "x [ field ]"        := (PEProj x field%string) (in custom py_expr at level 10) : pylevel_scope.
(* syntactic sugar *)
Notation "'fst(' x ')'" := (PEProj x "0")
   (in custom py_expr at level 10, format "fst( x )") : pylevel_scope.
Notation "'snd(' x ')'" := (PEProj x "1")
   (in custom py_expr at level 10) : pylevel_scope.


(* Binary operators (PEBinop) *)
Notation "x + y"              := (PEBinop POPlus x y)
   (in custom py_expr at level 50, left associativity) : pylevel_scope.
Notation "x - y"              := (PEBinop POMinus x y)
   (in custom py_expr at level 50, left associativity) : pylevel_scope.
Notation "x * y"              := (PEBinop POTimes x y)
   (in custom py_expr at level 40, left associativity) : pylevel_scope.
Notation "x / y"              := (PEBinop PODiv x y)
   (in custom py_expr at level 40, left associativity) : pylevel_scope.
Notation "x % y"              := (PEBinop POMod x y)
   (in custom py_expr at level 40, left associativity) : pylevel_scope.
Notation "x && y"             := (PEBinop POAnd x y)
   (in custom py_expr at level 40, left associativity) : pylevel_scope.
Notation "x || y"             := (PEBinop POOr x y)
   (in custom py_expr at level 50, left associativity) : pylevel_scope.
Notation "x ++ y"             := (PEBinop POConcat x y)
   (in custom py_expr at level 60, left associativity) : pylevel_scope.
Notation "x < y"              := (PEBinop POLess x y)
   (in custom py_expr at level 70, left associativity) : pylevel_scope.
Notation "x == y"             := (PEBinop POEq x y)
   (in custom py_expr at level 70, left associativity) : pylevel_scope.
Notation "'repeat(' list ',' cnt ')'"       := (PEBinop PORepeat list cnt)
   (in custom py_expr at level 10, left associativity) : pylevel_scope.
Notation "( x , y )"          := (PEBinop POPair x y)
   (in custom py_expr at level 0, x custom py_expr at level 99,
    y custom py_expr at level 99, left associativity) : pylevel_scope.
Notation "x :: y"             := (PEBinop POCons x y)
   (in custom py_expr at level 55, right associativity) : pylevel_scope.
Notation "'range(' x ',' y ')'"  := (PEBinop PORange x y)
   (in custom py_expr at level 10, left associativity) : pylevel_scope.

Notation "[ x , .. , y , z ]"   := (PEBinop POCons x .. (PEBinop POCons y (PESingleton z)) ..)
   (in custom py_expr at level 0, left associativity) : pylevel_scope.
Notation "[ x ]"                := (PESingleton x)
   (in custom py_expr at level 0) : pylevel_scope.
Notation "'nil(' t ')'"        := (PANil t)
   (in custom py_expr at level 10, t custom py_type) : pylevel_scope.


(* Other pexpr *)
Notation "'flatmap' e1 x e2"           := (PEFlatmap e1 x%string e2)
   (in custom py_expr at level 99, x constr at level 0) : pylevel_scope.
Notation "'if' p1 'then' p2 'else' p3" := (PEIf p1 p2 p3)
   (in custom py_expr at level 99) : pylevel_scope.
Notation "'let' x := p1 'in' p2"       := (PELet x p1 p2)
   (in custom py_expr at level 99) : pylevel_scope.
(* TODO PERecord *)

Section Tests.
   Goal <{ skip }> = PCSkip. reflexivity. Abort.
   Goal <{ skip; skip }> = PCSeq PCSkip PCSkip. reflexivity. Abort.

   Goal <{ "x" <- 0 }> = PCGets "x" (PEAtom 0). reflexivity. Abort.

   Goal <{ "_" <- -3 }> = PCGets "_" (PEUnop PONeg 3). reflexivity. Abort.
   Goal <{ "_" <- -(3) }> = PCGets "_" (PEUnop PONeg 3). reflexivity. Abort.

   Goal <{ "_" <- !true }> = PCGets "_" (PEUnop PONot true). reflexivity. Abort.
   Goal <{ "_" <- !(true) }> = PCGets "_" (PEUnop PONot true). reflexivity. Abort.

   Goal <{ "_" <- length([ 1, 2, 3]) }> = PCGets "_"
     (PEUnop POLength (PEBinop POCons 1 (PEBinop POCons 2 (PESingleton 3)))).
   reflexivity. Abort.

   Goal <{ "_" <- fst(0) }> = PCGets "_" (PEProj 0 "0"). reflexivity. Abort.
   Goal forall x, <{ "_" <- x["0"] }> = PCGets "_" (PEProj x "0"). reflexivity. Abort.

   Goal <{ "_" <- ((1 + 3)*4, 2) }> = PCGets "_" ((PEBinop POPair (PEBinop POTimes (PEBinop POPlus 1 3) 4) 2)).
   reflexivity. Abort.

   Goal <{ "_" <- [1, 2, 3] }> = PCGets "_" (PEBinop POCons 1 (PEBinop POCons 2 (PESingleton 3))).
   reflexivity. Abort.

   Goal <{ "_" <- [1, 2] }> = PCGets "_" (PEBinop POCons 1 (PESingleton 2)).
   reflexivity. Abort.

   Goal <{ "_" <- true }> = PCGets "_" (PEAtom (PABool true)).
   reflexivity. Abort.

   Goal <{ "_" <- [ 1 ] }> = PCGets "_" (PESingleton 1).
   reflexivity. Abort.

   Goal <{ "_" <- true }> = PCGets "_" (PEAtom (PABool true)).
   reflexivity. Abort.

   Goal <{ "_" <- 1 :: 2 :: [3, 4] }> = PCGets "_"
      (PEBinop POCons 1 (PEBinop POCons 2 (PEBinop POCons 3 (PESingleton 4)))).
   reflexivity. Abort.

   Goal <{ "_" <- 3 :: 4 :: nil(@int) }> = PCGets "_"
      (PEBinop POCons 3 (PEBinop POCons 4 (PANil TInt))).
   reflexivity. Abort.
   Goal <{ "_" <- true :: false :: nil(@bool) }> = PCGets "_"
      (PEBinop POCons true (PEBinop POCons false (PANil TBool))).
   reflexivity. Abort.
   Goal <{ "_" <- [2,4] :: nil(@list @int) }> = PCGets "_"
      (PEBinop POCons (PEBinop POCons 2 (PESingleton 4)) (PANil (TList TInt))).
   reflexivity. Abort.

   Goal <{ let "x" := 3 + 4 in "y" <- "x"+1; "z" <- 5+"x" }> =
      (PCLet "x" (PEBinop POPlus 3 4)
         (PCSeq (PCGets "y" (PEBinop POPlus "x" 1))
                (PCGets "z" (PEBinop POPlus 5 "x")))).
   reflexivity. Abort.

   Goal <{ let "x" := 3 + 4 in
               let "y" := "x" + 1 in
                  "z" <- "x" + "y" - 1 }> =
      (PCLet "x" (PEBinop POPlus 3 4)
         (PCLet "y" (PEBinop POPlus "x" 1)
                (PCGets "z" (PEBinop POMinus (PEBinop POPlus "x" "y") 1)))).
   reflexivity. Abort.

   Goal <{ (let mut "x" := 3 in "y" <- "x" + 1);
           "x" <- "y" * 2;
           skip }> =
           PCSeq
               (PCLetMut "x" 3 (PCGets "y" (PEBinop POPlus "x" 1)))
               (PCSeq
                  (PCGets "x" (PEBinop POTimes "y" 2))
                  PCSkip).
   reflexivity. Abort.

   Goal <{ if 3 == 3 then "y" <- 0+1 else "y" <- 0+10; "a" <- 0 end }> =
      PCIf (PEBinop POEq 3 3)
           (PCGets "y" (PEBinop POPlus 0 1))
           (PCSeq (PCGets "y" (PEBinop POPlus 0 10))
                  (PCGets "a" 0)).
   reflexivity. Abort.

   Goal <{ for "x" in [1,2]++[3]:
             "a" <- "x"*2;
             "b" <- "x"+1
           end;
           "z" <- 123 }> =
         PCSeq (PCForeach "x" (PEBinop POConcat (PEBinop POCons 1 (PESingleton 2)) (PESingleton 3))
                  (PCSeq (PCGets "a" (PEBinop POTimes "x" 2))
                         (PCGets "b" (PEBinop POPlus "x" 1))))
               (PCGets "z" 123).
   reflexivity. Abort.

End Tests.

Unset Printing All.

Section Examples.
  Instance tenv : map.map string (type * bool) := SortedListString.map _.
  Instance tenv_ok : map.ok tenv := SortedListString.ok _.

  Instance locals : map.map string {t & interp_type t} := SortedListString.map _.
  Instance locals_ok : map.ok locals := SortedListString.ok _.

  Definition elaborate_interpret (l : locals) (pc : pcommand) : result locals :=
    c <- elaborate_command (map.map_values (fun x => (projT1 x, true)) l) pc;;
    Success (interp_command l c).

  Definition set_local (l : locals) {t : type} (x : string) (v : interp_type t) :
    locals := map.put l x (existT _ _ v).

  Fixpoint init_locals (vars : list string) :=
     match vars with
     | [] => map.empty
     | x :: xs => @set_local (init_locals xs) TInt x(0)
     end.

  Definition run_program (init : locals) (pc : pcommand) :=
   match elaborate_interpret init pc with
       | Success x => Success x.(SortedList.value)
       | Failure e => Failure e
       end.

  Goal run_program (init_locals ["a"]) <{ "a" <- 5 }> = Success [("a", existT interp_type TInt 5)].
  reflexivity.  Abort.

  Goal run_program (init_locals ["a"]) <{
     let "b" := 100 in
     "a" <- 5 + "b";
     "a" <- "a" + 1
  }> = Success [("a", existT interp_type TInt 106)].
  reflexivity.  Abort.

  Goal run_program (init_locals ["y"]) <{
     let mut "a" := 2 in
     "a" <- (let "x" := 5 in "x"*"a");
     "y" <- "a"
  }> = Success [("y", existT interp_type TInt 10)].
  reflexivity. Abort.

  Goal run_program (init_locals ["x"]) <{
     "x" <- 5;
     (let "y" := ("x" - 2) in
         "x" <- "y" * 100
     )
  }> = Success [("x", existT interp_type TInt 300)].
  reflexivity. Abort.

  Goal run_program (init_locals ["o"]) <{
     "o" <- let "x" := 2 in "x"
  }> = Success [("o", existT _ TInt 2)].
  Proof. reflexivity. Abort.

  Goal run_program (init_locals ["o"]) <{
     "o" <- let "x" := 2 in "x"+3*100
  }> = Success [("o", existT _ TInt 302)].
  Proof. reflexivity. Abort.

  Goal run_program (@set_local map.empty TBool "o" false) <{
     "o" <- ! (1 == 1)
  }> = Success [("o", existT _ TBool false)].
  Proof. reflexivity. Abort.

  Goal run_program (init_locals ["o"]) <{
     "o" <- if !(1 == 2) then 5 else 98+1
  }> = Success [("o", existT _ TInt 5)].
  Proof. reflexivity. Abort.

  Goal run_program (@set_local map.empty (TList TInt) "o" []) <{
     "o" <- range(3, 5)
  }> = Success [("o", existT _ (TList TInt) (3 :: 4 :: nil))].
  Proof. reflexivity. Abort.

  Goal run_program (@set_local map.empty (TList TInt) "o" []) <{
     "o" <- flatmap [1, 2] "x" ["x"]
  }> = Success [("o", existT _ (TList TInt) (1 :: 2 :: nil))].
  reflexivity. Abort.

  Goal run_program (@set_local map.empty (TList TInt) "o" []) <{
     "o" <- flatmap [1] "x" ["x"]
  }> = Success [("o", existT _ (TList TInt) (1 :: nil))].
  reflexivity.  Abort.

  Goal run_program (@set_local map.empty (TList TInt) "o" []) <{
     "o" <- flatmap range(1, 10) "x" ["x"*"x"] }>
     = Success [("o", existT interp_type (TList TInt) [1; 4; 9; 16; 25; 36; 49; 64; 81])].
  Proof. reflexivity. Abort.

  (* Program which test whether a number is square or not *)

  Definition isSquare (n : Z) : pcommand := <{
     let "n" := n in
     for "x" in range(0, "n"+1):
         if "x"*"x" == "n"
           then "ans" <- true
           else skip
           end
     end
     }>.

   Goal run_program (@set_local map.empty TBool "ans" false)
      (isSquare 4) = Success [("ans", existT interp_type TBool true)].
   Proof. reflexivity. Abort.

   Goal run_program (@set_local map.empty TBool "ans" false)
      (isSquare 25) = Success [("ans", existT interp_type TBool true)].
   Proof. reflexivity. Abort.

   Goal run_program (@set_local map.empty TBool "ans" false)
      (isSquare (11*11 )) = Success [("ans", existT interp_type TBool true)].
   Proof. reflexivity. Abort.

   Goal run_program (@set_local map.empty TBool "ans" false)
      (isSquare 0) = Success [("ans", existT interp_type TBool true)].
   Proof. reflexivity. Abort.

   Goal run_program (@set_local map.empty TBool "ans" false)
      (isSquare 2) = Success [("ans", existT interp_type TBool false)].
   Proof. reflexivity. Abort.

   Goal run_program (@set_local map.empty TBool "ans" false)
      (isSquare 13) = Success [("ans", existT interp_type TBool false)].
   Proof. reflexivity. Abort.

   Goal run_program (@set_local map.empty TBool "ans" false)
      (isSquare (-2)) = Success [("ans", existT interp_type TBool false)].
   Proof. reflexivity. Abort.

End Examples.

