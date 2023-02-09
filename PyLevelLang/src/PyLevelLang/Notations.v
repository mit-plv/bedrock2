Require Import PyLevelLang.Language.
Require Import PyLevelLang.Elaborate.
Require Import PyLevelLang.Interpret.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Map.Properties.
Require Import coqutil.Datatypes.Result.
Require Import Coq.Lists.List.
Import ListNotations.
Import ResultMonadNotations.

(* Set Printing All. *)

Declare Custom Entry pylevel.
Declare Scope pylevel_scope.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Local Open Scope pylevel_scope.

Coercion PEVar : string >-> pexpr.

Coercion PAInt : Z >-> patom.
Coercion PABool : bool >-> patom.
Coercion PEAtom : patom >-> pexpr.

Notation "<{ e }>"       := (e : pexpr) (at level 0, e custom pylevel at level 99, only parsing) : pylevel_scope.
Notation "<{ e }>"       := e (at level 0, e custom pylevel at level 99, only printing) : pylevel_scope.
Notation "<[ e ]>"       := e (in custom pylevel at level 0, e constr at level 200) : pylevel_scope.
Notation "( x )"         := x (in custom pylevel at level 0, x custom pylevel at level 99) : pylevel_scope.
Notation "x"             := x (in custom pylevel at level 0, x constr at level 0) : pylevel_scope.

(* TODO Allow string constants (which are different from vars) *)

(* Unary operations (PEUnop) *)
Notation "- x"         := (PEUnop PONeg x)
   (in custom pylevel at level 10) : pylevel_scope.
Notation "! x"         := (PEUnop PONot x)
   (in custom pylevel at level 10) : pylevel_scope.
Notation "'length(' x ')'"   := (PEUnop POLength x)
   (in custom pylevel at level 10) : pylevel_scope.


(* not a unary operator, move *)
Notation "x [ field ]"        := (PEProj x field%string) (in custom pylevel at level 10) : pylevel_scope.
(* syntactic sugar *)
Notation "'fst(' x ')'" := <{ x["0"] }>
   (in custom pylevel at level 10, format "fst( x )") : pylevel_scope.
Notation "'snd(' x ')'" := <{ x["1"] }>
   (in custom pylevel at level 10) : pylevel_scope.


(* Binary operators (PEBinop) *)
Notation "x + y"              := (PEBinop POPlus x y)
   (in custom pylevel at level 50, left associativity) : pylevel_scope.
Notation "x - y"              := (PEBinop POMinus x y)
   (in custom pylevel at level 50, left associativity) : pylevel_scope.
Notation "x * y"              := (PEBinop POTimes x y)
   (in custom pylevel at level 40, left associativity) : pylevel_scope.
Notation "x / y"              := (PEBinop PODiv x y)
   (in custom pylevel at level 40, left associativity) : pylevel_scope.
Notation "x % y"              := (PEBinop POMod x y)
   (in custom pylevel at level 40, left associativity) : pylevel_scope.
Notation "x && y"             := (PEBinop POAnd x y)
   (in custom pylevel at level 40, left associativity) : pylevel_scope.
Notation "x || y"             := (PEBinop POOr x y)
   (in custom pylevel at level 50, left associativity) : pylevel_scope.
Notation "x ++ y"             := (PEBinop POConcat x y)
   (in custom pylevel at level 60, left associativity) : pylevel_scope.
Notation "x < y"              := (PEBinop POLess x y)
   (in custom pylevel at level 70, left associativity) : pylevel_scope.
Notation "x == y"             := (PEBinop POEq x y)
   (in custom pylevel at level 70, left associativity) : pylevel_scope.
Notation "'repeat(' list ',' cnt ')'"       := (PEBinop PORepeat list cnt)
   (in custom pylevel at level 10, left associativity) : pylevel_scope.
Notation "( x , y )"          := (PEBinop POPair x y)
   (in custom pylevel at level 0, x custom pylevel at level 99,
    y custom pylevel at level 99, left associativity) : pylevel_scope.
Notation "x :: y"             := (PEBinop POCons x y)
   (in custom pylevel at level 55, right associativity) : pylevel_scope.
Notation "'range(' x ',' y ')'"  := (PEBinop PORange x y)
   (in custom pylevel at level 10, left associativity) : pylevel_scope.

Notation "[ x , .. , y , z ]"   := (PEBinop POCons x .. (PEBinop POCons y (PESingleton z)) ..)
   (in custom pylevel at level 0, left associativity) : pylevel_scope.
Notation "[ x ]"                := (PESingleton x)
   (in custom pylevel at level 0) : pylevel_scope.
Notation "'nil(' t ')'"        := (PANil t)
   (in custom pylevel at level 10) : pylevel_scope.


(* Other pexpr *)
Notation "'flatmap' e1 x e2"           := (PEFlatmap e1 x%string e2)
   (in custom pylevel at level 99, x constr at level 0) : pylevel_scope.
Notation "'if' p1 'then' p2 'else' p3" := (PEIf p1 p2 p3)
   (in custom pylevel at level 99) : pylevel_scope.
Notation "'let' x := p1 'in' p2"       := (PELet x p1 p2)
   (in custom pylevel at level 99) : pylevel_scope.
(* TODO PERecord *)

Section Tests.
   Goal <{ -3 }> = PEUnop PONeg 3. reflexivity. Abort.
   Goal <{ -(3) }> = PEUnop PONeg 3. reflexivity. Abort.

   Goal <{ !true }> = PEUnop PONot true. reflexivity. Abort.
   Goal <{ !(true) }> = PEUnop PONot true. reflexivity. Abort.

   Goal <{ fst(0) }> = PEProj 0 "0". reflexivity. Abort.
   Goal forall x, <{ x["0"] }> = PEProj x "0". reflexivity. Abort.

   Goal <{ ((1 + 3)*4, 2) }> = (PEBinop POPair (PEBinop POTimes (PEBinop POPlus 1 3) 4) 2).
   reflexivity. Abort.

   Goal <{ [1, 2, 3] }> = PEBinop POCons 1 (PEBinop POCons 2 (PESingleton 3)).
   reflexivity. Abort.

   Goal <{ [1, 2] }> = PEBinop POCons 1 (PESingleton 2).
   reflexivity. Abort.

   Goal <{ [ 1 ] }> = PESingleton 1.
   reflexivity. Abort.

   Goal <{ true }> = PEAtom (PABool true).
   reflexivity. Abort.

   Goal <{ 1 :: 2 :: [3, 4] }> = PEBinop POCons 1 (PEBinop POCons 2 (PEBinop POCons 3 (PESingleton 4))).
   reflexivity. Abort.
End Tests.




(* pcommand *)
(*
Notation "'done'"                     := (PCSkip) (in custom pylevel at level 99) : pylevel_scope.
Notation "c1 ; c2"                    := (PCSeq c1 c2) (in custom pylevel at level 99) : pylevel_scope.
Notation "'let' x := p 'in' c"        := (PCLet x p c) (in custom pylevel at level 99) : pylevel_scope.
Notation "'let mut' x := p 'in' c"    := (PCLetMut x p c) (in custom pylevel at level 99) : pylevel_scope.
Notation "x <- p"          := (PCGets x p) (in custom pylevel at level 99) : pylevel_scope.
Notation "'if' p 'then' c1 'else' c2" := (PCIf p c1 c2) (in custom pylevel at level 99) : pylevel_scope.
Notation "'for' 'each' x 'in' p : c"  := (PCForeach x p c) (in custom pylevel at level 99) : pylevel_scope.
*)



Unset Printing All.

Section Examples.
  Instance tenv : map.map string (type * bool) := SortedListString.map _.
  Instance tenv_ok : map.ok tenv := SortedListString.ok _.

  Instance locals : map.map string {t & interp_type t} := SortedListString.map _.
  Instance locals_ok : map.ok locals := SortedListString.ok _.

  Definition elaborate_interpret (l : locals) (p : pexpr) : result {t & interp_type t} :=
    e <- elaborate (map.map_values (fun x => (projT1 x, true)) l) p;;
    Success (existT _ _ (interp_expr l (projT2 e))).

  (*
  Set Printing All.
  Definition c1 := <{ let "a" := (1) in (if (1 > 1) then 3 else 4) }>.
  Print c1.
   *)

  Goal elaborate_interpret map.empty <{ 1 + 2 }> = Success (existT _ (TInt) (3)).
  Proof. reflexivity. Abort.

  Goal elaborate_interpret map.empty <{ let "x" := 2 in "x" }> = Success (existT _ (TInt) (2)).
  Proof. reflexivity. Abort.

  Goal elaborate_interpret map.empty <{ let "x" := 2 in "x"+3*100 }> = Success (existT _ (TInt) (302)).
  Proof. reflexivity. Abort.

  Goal elaborate_interpret map.empty <{ ! (1 == 1)  }> = Success (existT _ (TBool) (false)).
  Proof. reflexivity. Abort.

  Goal elaborate_interpret map.empty <{ if !(1 == 2) then 5 else 98+1 }> = Success (existT _ (TInt) (5)).
  Proof. reflexivity. Abort.

  Goal elaborate_interpret map.empty <{ range(3, 5) }> = Success (existT _ (TList TInt) (3 :: 4 :: nil)).
  Proof. reflexivity. Abort.

  Goal elaborate_interpret map.empty <{ flatmap [1, 2] "x" ["x"]}> = Success (existT _ (TList TInt) (1 :: 2 :: nil)).
  reflexivity. Abort.

  Goal elaborate_interpret map.empty <{ flatmap [1] "x" ["x"] }> = Success (existT _ (TList TInt) (1 :: nil)).
  reflexivity.  Abort.

  Goal elaborate_interpret map.empty <{ flatmap range(1, 10) "x" ["x"*"x"] }>
     = Success (existT interp_type (TList TInt) [1; 4; 9; 16; 25; 36; 49; 64; 81]).
  Proof. reflexivity. Abort.

End Examples.

