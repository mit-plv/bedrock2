Require Import PyLevelLang.Language.
Require Import PyLevelLang.Elaborate.
Require Import PyLevelLang.Interpret.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Map.Properties.
Require Import coqutil.Datatypes.Result.
Import ResultMonadNotations.

Set Printing All.

Declare Custom Entry pylevel.
Declare Scope pylevel_scope.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Local Open Scope pylevel_scope.

Coercion PEVar : string >-> pexpr.

Coercion PCInt : Z >-> pconst.
Coercion PEConst : pconst >-> pexpr.

Notation "<{ e }>"       := e (at level 0, e custom pylevel at level 99) : pylevel_scope.
Notation "<[ e ]>"       := e (in custom pylevel at level 0, e constr at level 200) : pylevel_scope.
Notation "( x )"         := x (in custom pylevel at level 99) : pylevel_scope.
Notation "x"             := x (in custom pylevel at level 0, x constr at level 0) : pylevel_scope.


(* Consts (PEConst) *)
(* TODO Maybe use Coercion PCBool : bool >-> pconst. *)
(* TODO What level? *)
Notation "'btrue'"   := (PEConst (PCBool true)) (in custom pylevel at level 5) : pylevel_scope.
Notation "'bfalse'"   := (PEConst (PCBool false)) (in custom pylevel at level 5) : pylevel_scope.
(* TODO Allow string constants (which are different from vars) *)

(* Unary operations (PEUnop) *)
Notation "- x"      := (PEUnop PONeg x) (in custom pylevel at level 10) : pylevel_scope.
Notation "~ x"      := (PEUnop PONot x) (in custom pylevel at level 10) : pylevel_scope.
Notation "~( x )"      := (PEUnop PONot x) (in custom pylevel at level 10) : pylevel_scope.
(* TODO Get length to work for both *)
Notation "'length' x" := (PEUnop POLength x) (in custom pylevel at level 10) : pylevel_scope.
Notation "'lengthS' x" := (PEUnop POLengthString x) (in custom pylevel at level 10) : pylevel_scope.
(* TODO fst, snd? Need PFst *)

(* Binary operators (PEBinop) *)
Notation "x + y"              := (PEBinop POPlus x y) (in custom pylevel at level 50, left associativity) : pylevel_scope.
Notation "x - y"              := (PEBinop POMinus x y) (in custom pylevel at level 50, left associativity) : pylevel_scope.
Notation "x * y"              := (PEBinop POTimes x y) (in custom pylevel at level 40, left associativity) : pylevel_scope.
Notation "x / y"              := (PEBinop PODiv x y) (in custom pylevel at level 40, left associativity) : pylevel_scope.
Notation "x % y"              := (PEBinop POMod x y) (in custom pylevel at level 40, left associativity) : pylevel_scope.
Notation "x && y"             := (PEBinop POAnd x y) (in custom pylevel at level 40, left associativity) : pylevel_scope.
Notation "x || y"             := (PEBinop POOr x y) (in custom pylevel at level 50, left associativity) : pylevel_scope.
(* TODO Make ++ work for both *)
Notation "x '++l' y"          := (PEBinop POConcat x y) (in custom pylevel at level 60, left associativity) : pylevel_scope.
Notation "x '++s' y"          := (PEBinop POConcatString x y) (in custom pylevel at level 60, left associativity) : pylevel_scope.
Notation "x < y"              := (PEBinop POLess x y) (in custom pylevel at level 70, left associativity) : pylevel_scope.
Notation "x =? y"             := (PEBinop POEq x y) (in custom pylevel at level 70, left associativity) : pylevel_scope.
(* TODO What should the precedence of repeat be? *)
Notation "'repeat' x y"       := (PEBinop PORepeat x y) (in custom pylevel at level 50, left associativity) : pylevel_scope.
(* TODO Pairs? It conflicts with the parenthesis notation *)
(* Notation "( x , y )"       := (PEBinop POPair x y) (in custom pylevel at level 50, left associativity) : pylevel_scope. *)
Notation "x :: y"             := (PEBinop POCons x y) (in custom pylevel at level 60, left associativity) : pylevel_scope.
(* TODO range precedence? *)
 Notation "'range' x 'to' y"  := (PEBinop PORange x y) (in custom pylevel at level 99, left associativity) : pylevel_scope. 


(* TODO Get list notation to use PESingleton *)
(* TODO List notation doesn't print properly *)
Notation "[ x ; .. ; y ]"   := (PEBinop POCons x .. (PEBinop POCons y (PCNil TInt)) ..)
   (in custom pylevel at level 65, left associativity) : pylevel_scope.
(* Notation "[ x ; .. ; y ; .. ; z ]"   := (PEBinop POCons x .. PEBinop POCons y .. (PESingleton z) .. ) (in custom pylevel at level 55, left associativity) : pylevel_scope. *)
(* Check (PEBinop POCons (PEConst (PCInt 3)) (PEConst (PCNil TInt))). *)



(* Other pexpr *)
Notation "'flatmap' e1 x e2" := (PEFlatmap e1 x e2) (in custom pylevel at level 99) : pylevel_scope.
Notation "'if' p1 'then' p2 'else' p3" := (PEIf p1 p2 p3) (in custom pylevel at level 99) : pylevel_scope.
Notation "'let' x := p1 'in' p2" := (PELet x p1 p2) (in custom pylevel at level 99) : pylevel_scope.
(* TODO PERecord *)
(* TODO PEProj *)


Unset Printing All.

Section Examples.
  Instance tenv : map.map string (type * bool) := SortedListString.map _.
  Instance tenv_ok : map.ok tenv := SortedListString.ok _.

  Instance locals : map.map string {t & interp_type t} := SortedListString.map _.
  Instance locals_ok : map.ok locals := SortedListString.ok _.

  Definition elaborate_interpret (l : locals) (p : pexpr) : result {t & interp_type t} :=
    e <- elaborate (map.map_values (fun x => (projT1 x, true)) l) p;;
    Success (existT _ _ (interp_expr l (projT2 e))).

  Definition ex1 := elaborate_interpret map.empty <{ 1 + 2 }>.
  Goal ex1 = Success (existT _ (TInt) (3)).
  Proof. reflexivity. Qed.

  Definition ex2 := elaborate_interpret map.empty <{ let "x" := 2 in "x" }>.
  Goal ex2 = Success (existT _ (TInt) (2)).
  Proof. reflexivity. Qed.

  Definition ex3 := elaborate_interpret map.empty <{ let "x" := 2 in "x"+3*100 }>.
  Goal ex3 = Success (existT _ (TInt) (302)).
  Proof. reflexivity. Qed.

  Definition ex4 := elaborate_interpret map.empty <{ if ~(1 =? 2) then 5 else 98+1 }>.
  Goal ex4 = Success (existT _ (TInt) (5)).
  Proof. reflexivity. Qed.

  Definition ex5 := elaborate_interpret map.empty <{ range 3 to 5 }>.
  Goal ex5 = Success (existT _ (TList TInt) (3 :: 4 :: nil)).
  Proof. reflexivity. Qed.

  Definition ex0' := elaborate_interpret map.empty <{ flatmap (["x"]) "x" [1; 2] }>.
  Goal ex0' = Success (existT _ (TList TInt) (1 :: 2 :: nil)).
     unfold ex0', elaborate_interpret.
     simpl.
     (* Error: Undefined variable "x" *)
  Abort.

End Examples.

