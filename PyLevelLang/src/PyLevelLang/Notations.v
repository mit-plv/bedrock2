Require Import PyLevelLang.Language.
Require Import PyLevelLang.Elaborate.
Require Import PyLevelLang.Interpret.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Map.Properties.
Require Import coqutil.Datatypes.Result.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Import ResultMonadNotations.

Declare Scope pylevel_scope.
Declare Custom Entry py_expr.
Declare Custom Entry py_comm.


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
Notation "( x )"         := x (in custom py_expr at level 0, x custom py_expr at level 99) : pylevel_scope.
Notation "( x )"         := x (in custom py_comm at level 0, x custom py_comm at level 99) : pylevel_scope.
Notation "x"             := x (in custom py_expr at level 0, x constr at level 0) : pylevel_scope.
Notation "x"             := x (in custom py_comm at level 0, x constr at level 0) : pylevel_scope.

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
Notation "'nil[' t ']'"        := (PANil t)
   (in custom py_expr at level 10, t constr) : pylevel_scope.


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

   Goal <{ "_" <- 3 :: 4 :: nil[Int] }> = PCGets "_"
      (PEBinop POCons 3 (PEBinop POCons 4 (PANil TInt))).
   reflexivity. Abort.
   Goal <{ "_" <- true :: false :: nil[Bool] }> = PCGets "_"
      (PEBinop POCons true (PEBinop POCons false (PANil TBool))).
   reflexivity. Abort.

   Goal <{ "_" <- [2,4] :: nil[List Int] }> = PCGets "_"
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



Section Square_Section.
  Instance tenv : map.map string (type * bool) := SortedListString.map _.
  Instance tenv_ok : map.ok tenv := SortedListString.ok _.

  Definition isSquare (n : Z) : pcommand := <{
     let "n" := n in
     let "ans" := true in
     for "x" in range(0, "n"+1):
         if "x"*"x" == "n"
           then "ans" <- true
           else skip
           end
     end
     }>.

  Definition isSquare_elaborated (n : Z) : command :=
     Eval cbv in (match (elaborate_command map.empty (isSquare n)) with
                    | Success x => x
                    | _ => _
                    end
        ).
End Square_Section.



Section WithMap.
  Context {locals: map.map string {t & interp_type t}} {locals_ok: map.ok locals}.
  Context { tenv : map.map string (type * bool) }
          { tenv_ok : map.ok tenv }.

  Goal interp_command map.empty (isSquare_elaborated 0)
     = (map.put map.empty "ans" (existT interp_type Bool true)).
  Proof.
     unfold isSquare_elaborated.
     simpl.

     unfold get_local, set_local.
     repeat rewrite map.get_put_same.
     rewrite map.get_put_diff by congruence.

     simpl.
     rewrite !map.get_put_same.
     rewrite !map.get_put_diff by congruence.

     simpl.
     rewrite !map.get_put_same.
     repeat rewrite map.get_empty.
     simpl.

     rewrite map.remove_put_diff by congruence.
     rewrite map.remove_put_diff by congruence.
     rewrite map.remove_put_same.

     rewrite map.remove_put_diff by congruence.
     rewrite map.remove_empty.
     rewrite map.remove_put_same.
     rewrite map.remove_empty.
     reflexivity.
  Abort.


   Lemma last_range : forall (x : Z) (n : nat),
      eval_range x (S n) = (eval_range x n) ++ [x + Z.of_nat n].
   Proof.
      intros. generalize dependent x.
      induction n.
      - intros. rewrite Z.add_0_r. reflexivity.
      - intros.
        assert (forall (n : nat),
           eval_range x (S n) = x :: eval_range (x + 1) n).
        { easy.  }
        rewrite H. rewrite IHn.  simpl.
        repeat (try lia; f_equal).
   Qed.

   Lemma first_range : forall (x : Z) (n : nat),
      eval_range x (S n) = x :: eval_range (x + 1) n.
   Proof.
      easy.
   Qed.

   Lemma split_range : forall (x : nat) (n : nat),
      (x <= n)%nat ->
      eval_range 0 n =
      eval_range 0 x ++
      eval_range (Z.of_nat x) (n - x).
   Proof.
      intros. induction n.
      - simpl. destruct x; try easy.
      - destruct (x =? S n)%nat eqn:x_Sn.
        + rewrite Nat.eqb_eq in x_Sn. subst.
          rewrite Nat.sub_diag. simpl.
          rewrite app_nil_r. reflexivity.
        + rewrite last_range.
          rewrite Nat.eqb_neq in x_Sn.
          assert (NotEq : forall (a b : nat),
            (a <= S b)%nat -> a <> S b -> (a <= b)%nat).
            { lia. }

         apply (NotEq _ _ H) in x_Sn.
         apply IHn in x_Sn as IH.
         rewrite IH.
         rewrite <- app_assoc.
         repeat f_equal.

         rewrite Nat.sub_succ_l; try lia.
         rewrite last_range.
         f_equal. f_equal. lia.
   Qed.

   Lemma Sx_Sq_le : forall (x n : nat),
      (S x * S x)%nat = n -> (x*x < n)%nat.
   Proof.
      intros. induction x; try lia.
   Qed.

   Lemma x_Sq_pred_neq : forall (x n : nat),
      (S x * S x)%nat = n -> (x*x)%nat <> n.
   Proof.
      intros. induction x; try lia.
   Qed.

   Lemma cnt_exists : forall x n,
      (x < n)%nat -> (exists k : nat, n = (x + S k)%nat).
   Proof.
      intros. induction n; try easy.
      destruct (x =? n)%nat eqn:x_eq_n.
      - apply Nat.eqb_eq in x_eq_n. subst.
        exists 0%nat. lia.
      - apply Nat.eqb_neq in x_eq_n.
        assert (x <> n -> (x < S n)%nat -> (x < n)%nat).
        { lia. }
        specialize (IHn (H0 x_eq_n H)).
        destruct IHn as [k IHk].
        exists (S k). lia.
   Qed.

   Lemma small_loop_false : forall x n, (S x * S x = n)%nat ->
      fold_left (fun (l' : locals) (v : Z) =>
      if
       (match
          map.get (map.put l' "x" (existT interp_type Int v)) "x"
        with
        | Some v0 => proj_expected Int v0
        | None => 0
        end *
        match
          map.get (map.put l' "x" (existT interp_type Int v)) "x"
        with
        | Some v0 => proj_expected Int v0
        | None => 0
        end =?
        match
          map.get (map.put l' "x" (existT interp_type Int v)) "n"
        with
        | Some v0 => proj_expected Int v0
        | None => 0
        end)%Z
      then
       map.put (map.put l' "x" (existT interp_type Int v)) "ans"
         (existT interp_type Bool true)
      else map.put l' "x" (existT interp_type Int v))
     (eval_range 0 (S x))
     (@map.put string (sigT (fun t : type => interp_type t)) locals
                 (@map.empty string (@sigT type (fun t : type => interp_type t))
                     locals)
                 "n" (existT interp_type TInt (Z.of_nat n)))
     = map.put (map.put map.empty "n" (existT interp_type Int (Z.of_nat n))) "x" (existT interp_type Int (Z.of_nat x)).
   Proof.
      intros x n x_Sq. apply Sx_Sq_le in x_Sq.
      induction x.
      - intros. simpl in x_Sq. subst. cbn.
        rewrite map.get_put_same.
        rewrite map.get_put_diff by congruence.
        rewrite map.get_put_same .
        destruct n; try easy.
      - intros.
        rewrite last_range. rewrite fold_left_app.

        destruct ((x * x =? n)%nat) eqn:x_Sq_eq.
        * rewrite Nat.eqb_eq in x_Sq_eq.
          subst.
          assert ((S x * S x < x * x)%nat -> False).
          { lia. }
          easy.
        * assert ((S x * S x < n)%nat -> (x * x =? n) % nat = false
                     -> (x * x < n)%nat).
          { lia. }
          specialize (H x_Sq x_Sq_eq).
          specialize (IHx H).

          rewrite IHx. clear IHx.
          cbn.

          rewrite !map.get_put_same.
          rewrite !map.get_put_diff by congruence.
          rewrite !map.get_put_same.
          cbn.

          destruct n; try easy.
          + cbn.
            assert ((S x * S x < S n)%nat ->
                    ((Pos.of_succ_nat x * Pos.of_succ_nat x
                    =? Pos.of_succ_nat n)%positive = false)).
           { destruct (Pos.of_succ_nat x * Pos.of_succ_nat x =?
                        Pos.of_succ_nat n)%positive eqn:S_x_sq.
             - rewrite Pos.eqb_eq in S_x_sq. lia.
             - lia.
           }
           specialize (H0 x_Sq).
           rewrite H0.

           rewrite map.put_put_same.
           reflexivity.
   Qed.

   Lemma large_loop_true : forall x k,
      (fold_left
        (fun (l' : locals) (v : Z) =>
         if
          (match map.get (map.put l' "x" (existT interp_type Int v)) "x" with
           | Some v0 => proj_expected Int v0
           | None => 0
           end *
           match map.get (map.put l' "x" (existT interp_type Int v)) "x" with
           | Some v0 => proj_expected Int v0
           | None => 0
           end =?
           match map.get (map.put l' "x" (existT interp_type Int v)) "n" with
           | Some v0 => proj_expected Int v0
           | None => 0
           end)%Z
         then
          map.put (map.put l' "x" (existT interp_type Int v)) "ans"
            (existT interp_type Bool true)
         else map.put l' "x" (existT interp_type Int v))
        (eval_range (Z.pos (Pos.of_succ_nat x + 1)) (S k))
        (map.put
           (map.put
              (map.put map.empty "n"
                 (existT interp_type Int (Z.pos (Pos.of_nat (S x * S x)))))
              "ans" (existT interp_type Bool true)) "x"
           (existT interp_type Int (Z.pos (Pos.of_succ_nat x))))
      = map.put (map.put (map.put map.empty "ans" (existT interp_type Bool true)) "x"
        (existT interp_type Int
           match Z.of_nat k with
           | 0 => Z.pos (Pos.of_succ_nat x + 1)
           | Z.pos y' => Z.pos (Pos.of_succ_nat x + 1 + y')
           | Z.neg y' => Z.pos_sub (Pos.of_succ_nat x + 1) y'
           end)) "n"
        (existT interp_type Int
           (Z.pos
              match (x + x * S x)%nat with
              | 0%nat => 1
              | S _ => Pos.succ (Pos.of_nat (x + x * S x))
              end))).
   Proof.
      intros. induction k.
      - simpl eval_range.
        simpl fold_left.
        rewrite map.put_put_same.
        rewrite map.get_put_same.
        rewrite (map.put_put_diff _ "n" "ans") by congruence.
        rewrite (map.put_put_diff _ "n" "x") by congruence.
        rewrite map.get_put_same.

        simpl.
        destruct (
           ((Pos.of_succ_nat x + 1) * (Pos.of_succ_nat x + 1) =?
            match (x + x * S x)%nat with
            | 0%nat => 1
            | S _ => Pos.succ (Pos.of_nat (x + x * S x))
            end)%positive); try reflexivity.
         rewrite (map.put_put_diff _ "ans" "x") by congruence.
         rewrite map.put_put_diff by congruence.
         rewrite map.put_put_same.
         rewrite (map.put_put_diff _ "ans" "x") by congruence.
         reflexivity.
      - rewrite last_range. rewrite fold_left_app.
        rewrite IHk. clear IHk.
        simpl.

        rewrite map.get_put_same.
        rewrite (map.put_put_diff _ "n" "x") by congruence.
        rewrite map.get_put_same.
        cbn.

        destruct (
           ((Pos.of_succ_nat x + 1 + Pos.of_succ_nat k) *
            (Pos.of_succ_nat x + 1 + Pos.of_succ_nat k) =?
            match (x + x * S x)%nat with
            | 0%nat => 1
            | S _ => Pos.succ (Pos.of_nat (x + x * S x))
            end)%positive).

        * rewrite map.put_put_diff by congruence.
          rewrite map.put_put_same.
          rewrite (map.put_put_diff _ "x" "ans") by congruence.
          rewrite map.put_put_same.
          reflexivity.
        * rewrite map.put_put_diff by congruence.

          rewrite (map.put_put_diff _ "x" "n") by congruence.
          rewrite map.put_put_same.
          rewrite (map.put_put_diff _ "x" "n") by congruence.
          reflexivity.
    Qed.


   Theorem is_square_exists : forall (n : nat),
      (exists (x : nat), (x*x)%nat = n) ->
      interp_command map.empty (isSquare_elaborated (Z.of_nat n))
      = (map.put map.empty "ans" (existT interp_type Bool true)).
   Proof.
      intros n [x xSq].

      simpl.

      unfold set_local.
      rewrite map.get_put_diff by congruence.
      rewrite !map.get_empty.

      unfold get_local.
      rewrite map.get_put_same.
      simpl.

      assert (x_leq_Sn : (x <= Z.to_nat (Z.of_nat n + 1 - 0))%nat).
      { replace (Z.of_nat n + 1 - 0) with (Z.of_nat (S n)) by lia.
         rewrite <- xSq.
         rewrite Nat2Z.id.
         induction x; try lia.
      }

      rewrite (split_range x); try assumption.
      rewrite fold_left_app.
      generalize dependent n.
      destruct x.
      - intros. subst. simpl.
        rewrite map.get_put_same.
        rewrite map.get_put_diff by congruence.
        rewrite map.get_put_same.
        cbn.
        rewrite map.remove_put_diff by congruence.
        rewrite map.remove_put_same.
        rewrite !map.remove_put_diff by congruence.
        rewrite !map.remove_put_same.
        rewrite map.remove_empty.
        rewrite map.remove_empty.
        reflexivity.
      - intros.
        specialize (small_loop_false _ _ xSq) as IH.
        rewrite IH. clear IH.

         cbn.
         replace ((Z.to_nat (Z.of_nat n + 1 - 0) - S x)%nat) with (n - x)%nat by lia.
         assert (first_range : forall x n, eval_range x (S n) = x :: eval_range (x + 1) n).
            { easy. }

         assert (x_le_n : (S x * S x)%nat = n -> (x < n)%nat).
         { lia. }

         destruct (cnt_exists _ _ (x_le_n xSq)) as [k x_plus_k].
         rewrite x_plus_k.

         assert ((x + S k - x)%nat = (S k)).
         { lia. } rewrite H. clear H.

         rewrite first_range.

         simpl.
         rewrite map.get_put_same.
         rewrite map.get_put_diff by congruence.
         rewrite map.get_put_diff by congruence.
         rewrite map.get_put_same.
         cbn.

         rewrite <- x_plus_k.
         destruct n; try lia.
         simpl.

         assert (((Pos.of_succ_nat x * Pos.of_succ_nat x)%positive
                  = Pos.of_nat (S x * S x)%nat)).
         { lia. }
         rewrite H. clear H.

         rewrite (Pos.of_nat_succ n).
         rewrite <- xSq.

         assert((Pos.of_nat (S x * S x) =? Pos.of_nat (S x * S x))%positive
               = true).
         { rewrite Pos.eqb_eq. lia. }

         rewrite H. clear H.
         rewrite map.put_put_same.
         rewrite map.put_put_diff by congruence.

         destruct k.
         * simpl.
           rewrite !map.remove_put_same.
           rewrite !map.remove_put_diff by congruence.
           rewrite map.remove_put_same by congruence.
           rewrite !map.remove_empty.
           reflexivity.
         * rewrite large_loop_true.
           rewrite map.put_put_diff by congruence.
           rewrite map.remove_put_same.
           rewrite (map.remove_put_diff) by congruence.
           rewrite map.remove_put_same.
           rewrite map.remove_put_diff by congruence.
           rewrite map.remove_empty.
           rewrite map.remove_put_diff by congruence.
           rewrite map.remove_empty.
           reflexivity.
   Qed.

End WithMap.



Section Examples.
  Instance locals : map.map string {t & interp_type t} := SortedListString.map _.
  Instance locals_ok : map.ok locals := SortedListString.ok _.

  Fixpoint init_locals (vars : list (string * type)) : locals :=
     match vars with
     | [] => map.empty
     | (x, t) :: xs => set_local (init_locals xs) x (default_val t)
     end.

  Definition run_program (init : list (string * (type * bool))) (pc : pcommand)
     := let locals_map := init_locals (map (fun x => match x with
                                                    | (x, (t, _)) => (x, t)
                                                    end) init)
     in c <- @elaborate_command tenv (map.of_list init) pc;;
        Success (SortedList.value (interp_command locals_map c)).


  Goal run_program [("a", (TInt, true))] <{ "a" <- 5 }> = Success [("a", existT interp_type TInt 5)].
  reflexivity.  Abort.

  Goal run_program [("a", (TInt, true))] <{
     let "b" := 100 in
     "a" <- 5 + "b";
     "a" <- "a" + 1
  }> = Success [("a", existT interp_type TInt 106)].
  reflexivity.  Abort.

  Goal run_program [("y", (TInt, true))] <{
     let mut "a" := 2 in
     "a" <- (let "x" := 5 in "x"*"a");
     "y" <- "a"
  }> = Success [("y", existT interp_type TInt 10)].
  reflexivity. Abort.

  Goal run_program [("x", (TInt, true))] <{
     "x" <- 5;
     (let "y" := ("x" - 2) in
         "x" <- "y" * 100
     )
  }> = Success [("x", existT interp_type TInt 300)].
  reflexivity. Abort.

  Goal run_program [("o", (TInt, true))] <{
     "o" <- let "x" := 2 in "x"
  }> = Success [("o", existT _ TInt 2)].
  Proof. reflexivity. Abort.

  Goal run_program [("o", (TInt, true))] <{
     "o" <- let "x" := 2 in "x"+3*100
  }> = Success [("o", existT _ TInt 302)].
  Proof. reflexivity. Abort.

  Goal run_program [("o", (TBool, true))] <{
     "o" <- ! (1 == 1)
  }> = Success [("o", existT _ TBool false)].
  Proof. reflexivity. Abort.

  Goal run_program [("o", (TInt, true))] <{
     "o" <- if !(1 == 2) then 5 else 98+1
  }> = Success [("o", existT _ TInt 5)].
  Proof. reflexivity. Abort.

  Goal run_program [("o", (TList TInt, true))] <{
     "o" <- range(3, 5)
  }> = Success [("o", existT _ (TList TInt) (3 :: 4 :: nil))].
  Proof. reflexivity. Abort.

  Goal run_program [("o", (TList TInt, true))] <{
     "o" <- flatmap [1, 2] "x" ["x"]
  }> = Success [("o", existT _ (TList TInt) (1 :: 2 :: nil))].
  reflexivity. Abort.

  Goal run_program [("o", (TList TInt, true))] <{
     "o" <- flatmap [1] "x" ["x"]
  }> = Success [("o", existT _ (TList TInt) (1 :: nil))].
  reflexivity.  Abort.

  Goal run_program [("o", (TList TInt, true))] <{
     "o" <- flatmap range(1, 10) "x" ["x"*"x"] }>
     = Success [("o", existT interp_type (TList TInt) [1; 4; 9; 16; 25; 36; 49; 64; 81])].
  Proof. reflexivity. Abort.

   Definition isEven (n : Z) : pcommand := <{
      let "n" := n in
      if "n" % 2 == 0
         then "ans" <- true
         else skip
      end
      }>.

   Goal run_program [("ans", (TBool, true))]
      (isEven 4) = Success [("ans", existT interp_type TBool true)].
   Proof. reflexivity. Abort.

   Goal run_program [("ans", (TBool, true))]
      (isEven 3) = Success [("ans", existT interp_type TBool false)].
   Proof. reflexivity. Abort.
End Examples.

