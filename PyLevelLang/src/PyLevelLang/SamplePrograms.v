Require Import PyLevelLang.Language.
Require Import PyLevelLang.Elaborate.
Require Import PyLevelLang.Interpret.
Require Import PyLevelLang.Notations.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Map.Properties.
Require Import coqutil.Datatypes.Result.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Numbers.DecimalString.
Import ListNotations.
Import ResultMonadNotations.

Require Import Coq.Program.Tactics.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Local Open Scope pylevel_scope.

Section WithWord.
Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

(*
   JSON Values can be
   * A list of other values (TList)
   * An object of key value pairs, represented as TPair key value rest,
     where rest is more nested pairs (until Tempty)
   * A TInt, TBool, or TString
*)

Definition to_json_field_list_body to_json to_json_field_list t : interp_type t -> string :=
   match t as t return (interp_type t -> string) with
   | TPair key t1 t2 => fun s =>
       match s with
       | (a, rest) =>
           match t2 with
           | TEmpty => append (append key ": ") (to_json t1 a)
           | _ => append (append (append (append
                   key ": ") (to_json t1 a)) ", ") (to_json_field_list t2 rest)
           end
         end
   | TEmpty => fun i => ""
   | _ => fun s => "Error this type cannot be conerted to a json object"
   end.
Fixpoint to_json t : interp_type t -> string :=
   match t as t return (interp_type t -> string) with
   | TWord => fun w => ""
   | TInt => fun n => DecimalString.NilZero.string_of_int (BinInt.Z.to_int n)
   | TBool => fun i => match i with
                      | true => "true"
                      | false => "false"
                       end
   | TString => fun s => append (append """" s) """"
   | TList t => fun s => append (append "[" (String.concat ", " (map (to_json _) s))) "]"
   | TPair key t1 t2 => fun s =>
         append (append "{" (to_json_field_list_body to_json to_json_field_list (TPair key t1 t2) s)) "}"
   | TEmpty => fun i => ""
   end
with to_json_field_list t : interp_type t -> string := to_json_field_list_body to_json to_json_field_list t.


Definition generate_json_field_list_body generate_json generate_json_field_list (t : type) (field : expr t) : expr String :=
  match t as t return (expr t -> expr String) with
  | TPair key t1 t2 => fun f =>
      EBinop OConcatString (EBinop OConcatString (EBinop OConcatString
          (EAtom (AString key))
          (EAtom (AString ": ")))
          (generate_json t1 (EUnop (OFst _ _ _) f)))
          (EIf (EBinop (OEq TString eq_refl) (generate_json_field_list t2 (EUnop (OSnd _ _ _) f)) (EAtom (AString "")))
          (EAtom (AString ""))
          (EBinop OConcatString (EAtom (AString ", "))
            (generate_json_field_list t2 (EUnop (OSnd _ _ _) f))))
  | TEmpty => fun f => EAtom (AString "")
  | _ => fun f => EAtom (AString "Error this type cannot be conerted to a json object")
  end field.
Fixpoint generate_json (t : type) (field : expr t) : expr String :=
  match t as t return (expr t -> expr String) with
  | TWord => fun f => EAtom (AString "")
  | TInt => fun f => EUnop OIntToString f
  | TBool => fun f =>
      EIf (EBinop (OEq TBool eq_refl) f (EAtom (ABool true)))
          (EAtom (AString "true")) (EAtom (AString "false"))
  | TString => fun f => EBinop OConcatString (EBinop OConcatString (EAtom (AString """")) f) (EAtom (AString """"))
  | TList t => fun f => EBinop OConcatString
      (EAtom (AString "["))
      (EFold f (EAtom (AString "]")) "v" "acc"
             (EBinop OConcatString (EBinop OConcatString
             (generate_json t (EVar t "v"))
             (EIf (EBinop (OEq TString eq_refl) (EVar String "acc") (EAtom (AString "]")))
                  (EAtom (AString "")) (EAtom (AString ", "))))
             (EVar String "acc")))
  | TPair key t1 t2 => fun f =>
      EBinop OConcatString (EBinop OConcatString
          (EAtom (AString "{"))
          (generate_json_field_list_body generate_json generate_json_field_list (TPair key t1 t2) f))
          (EAtom (AString "}"))
  | TEmpty => fun f => EAtom (AString "")
  end field
with
  generate_json_field_list t : expr t -> expr String
    := generate_json_field_list_body generate_json generate_json_field_list t.

Section Generate_Json_Tests_Section.
  Instance locals : map.map string {t & interp_type t} := SortedListString.map _.
  Instance locals_ok : map.ok locals := SortedListString.ok _.

  Goal to_json (TList (TList TInt)) [[1]; [3; 33]; [5; 55; 555]]
    = "[[1], [3, 33], [5, 55, 555]]".
  reflexivity. Abort.

  Goal to_json (TPair "foo" TString (TPair "bar" TInt TEmpty)) ("hi", (7, tt))
  = "{foo: ""hi"", bar: 7}".
  reflexivity. Abort.

  Goal interp_expr (map.put map.empty "x" (existT interp_type Bool true))
        (generate_json TBool (EVar TBool "x")) = "true".
  reflexivity. Abort.

  Goal interp_expr (map.put map.empty "x" (existT interp_type Bool true))
        (generate_json TBool (EVar TBool "x")) = "true".
  reflexivity. Abort.

  Goal interp_expr (map.put map.empty "x" (existT interp_type String "str"))
        (generate_json TString (EVar TString "x")) = """str""".
  reflexivity. Abort.

  Goal interp_expr (map.put map.empty "x" (existT interp_type (TList Bool) [true; false; false]))
        (generate_json (TList Bool) (EVar (TList Bool) "x")) = "[true, false, false]".
  reflexivity. Abort.

  Goal interp_expr (map.put map.empty "x" (existT interp_type (TPair "foo" TString (TPair "bar" TInt TEmpty))
        ("hi", (7, tt))))
        (generate_json (TPair "foo" TString (TPair "bar" TInt TEmpty)) (EVar (TPair "foo" TString (TPair "bar" TInt TEmpty)) "x"))
        = "{foo: ""hi"", bar: 7}".
  reflexivity. Abort.

  Goal interp_expr (map.put map.empty "x"
      (existT interp_type (TPair "foo" TString (TPair "bar" (TPair "baz" TString TEmpty) TEmpty))
                          ("a", (("b", tt), tt))))
        (generate_json (TPair "foo" TString (TPair "bar" (TPair "baz" TString TEmpty) TEmpty)) (EVar _ "x"))
        = "{foo: ""a"", bar: {baz: ""b""}}".
  reflexivity. Abort.

  Goal interp_expr (map.put map.empty "x"
      (existT interp_type (TPair "foo" (TPair "bar" (TPair "baz" TString TEmpty) TEmpty) (TPair "bar" (TPair "baz" TString TEmpty) TEmpty))
                          ((("a", tt), tt), (("b", tt), tt))))
        (generate_json (TPair "foo" (TPair "bar" (TPair "baz" TString TEmpty) TEmpty) (TPair "bar" (TPair "baz" TString TEmpty) TEmpty)) (EVar _ "x"))
        = "{foo: {bar: {baz: ""a""}}, bar: {baz: ""b""}}".
  reflexivity. Abort.

  Goal interp_expr (map.put map.empty "x"
      (existT interp_type (TList (TList TString))
                          [["a"; "b"]; ["c"; "d"]]))
        (generate_json (TList (TList TString)) (EVar _ "x"))
        = "[[""a"", ""b""], [""c"", ""d""]]".
  reflexivity. Abort.

  Goal interp_expr (map.put map.empty "x"
      (existT interp_type (TList (TList TString))
                          [[]; ["a"; ""]]))
        (generate_json (TList (TList TString)) (EVar _ "x"))
        = "[[], [""a"", """"]]".
  reflexivity. Abort.
End Generate_Json_Tests_Section.


Section Square_Section.
  Instance tenv : map.map string (type * bool) := SortedListString.map _.
  Instance tenv_ok : map.ok tenv := SortedListString.ok _.

  Definition isSquare (n : Z) : pcommand := <{
     let "n" := n in
     for "x" in range(0, "n"+1):
         if "x"*"x" == "n"
           then "ans" <- true
           else skip
           end
     end
     }>.

  Definition isSquare_elaborated (n : Z) : command :=
     Eval cbv in (match (elaborate_command (map.of_list [("ans", (TBool, true))]) (isSquare n)) with
                    | Success x => x
                    | _ => _
                    end
        ).
End Square_Section.

Section Examples.
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

  Goal run_program [("o", (TInt, true))] <{
    "o" <- fold range(1, 10) 0 "x" "y" ("x" + "y") }>
    = Success [("o", existT interp_type TInt 45)].
  reflexivity. Abort.

  Goal run_program [("o", (TInt, true))] <{
    "o" <- fold range(1, 10) 0 "x" "y" ("x" * "x" + "y") }>
    = Success [("o", existT interp_type TInt 285)].
  reflexivity. Abort.

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

End WithWord.

