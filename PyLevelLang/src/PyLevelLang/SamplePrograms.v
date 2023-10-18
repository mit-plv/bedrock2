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
   | TEmpty => fun i => "tt"
   | _ => fun s => "Error this type cannot be conerted to a json object"
   end.
Fixpoint to_json t : interp_type t -> string :=
  match t as t return (interp_type t -> string) with
    (*TODO: properly implement for words*)
   | TWord => fun w => "TODO"
   | TInt => fun n => DecimalString.NilZero.string_of_int (BinInt.Z.to_int n)
   | TBool => fun i => match i with
                      | true => "true"
                      | false => "false"
                       end
   | TString => fun s => append (append """" s) """"
   | TList t => fun s => append (append "[" (String.concat ", " (map (to_json _) s))) "]"
   | TPair key t1 t2 => fun s =>
         append (append "{" (to_json_field_list_body to_json to_json_field_list (TPair key t1 t2) s)) "}"
   | TEmpty => fun i => "tt"
   end
with to_json_field_list t : interp_type t -> string := to_json_field_list_body to_json to_json_field_list t.


Definition generate_json_field_list_body generate_json generate_json_field_list (t : type) (var : expr t) : expr String :=
  match t as t return (expr t -> expr String) with
  | TPair key t1 t2 => match t2 with
       | TEmpty => fun f =>
          EBinop OConcatString (EBinop OConcatString (EBinop OConcatString
              (EAtom (AString key))
              (EAtom (AString ": ")))
              (generate_json t1 (EUnop (OFst _ _ _) f)))
              (EAtom (AString ""))
       | t2 => fun f =>
        EBinop OConcatString (EBinop OConcatString (EBinop OConcatString
            (EAtom (AString key))
            (EAtom (AString ": ")))
            (generate_json t1 (EUnop (OFst _ _ _) f)))
            (EBinop OConcatString (EAtom (AString ", "))
              (generate_json_field_list t2 (EUnop (OSnd _ _ t2) f)))
                       end
  | TEmpty => fun f => EAtom (AString "tt")
  | _ => fun f => EAtom (AString "Error this type cannot be conerted to a json object")
  end var.
Fixpoint generate_json (t : type) (var : expr t) { struct t }: expr String :=
  match t as t return (expr t -> expr String) with
  (*TODO: properly implement for words*)
  | TWord => fun f => EAtom (AString "TODO")
  | TInt => fun f => EUnop OIntToString f
  | TBool => fun f =>
      EIf (EBinop (OEq TBool eq_refl) f (EAtom (ABool true)))
          (EAtom (AString "true")) (EAtom (AString "false"))
  | TString => fun f => EBinop OConcatString (EBinop OConcatString (EAtom (AString """")) f) (EAtom (AString """"))
  | TList t => fun f => EBinop OConcatString (EBinop OConcatString
      (EAtom (AString "["))
      (EFold f (EAtom (AString "")) "v" "acc"
             (EBinop OConcatString (EBinop OConcatString
             (generate_json t (EVar t "v"))
             (EIf (EBinop (OEq TString eq_refl) (EVar String "acc") (EAtom (AString "")))
                  (EAtom (AString "")) (EAtom (AString ", "))))
             (EVar String "acc")))) (EAtom (AString "]"))
  | TPair key t1 t2 => fun f =>
      EBinop OConcatString (EBinop OConcatString
          (EAtom (AString "{"))
          (generate_json_field_list_body generate_json generate_json_field_list (TPair key t1 t2) f))
          (EAtom (AString "}"))
  | TEmpty => fun f => EAtom (AString "tt")
  end var
with
  generate_json_field_list t {struct t}: expr t -> expr String
    := generate_json_field_list_body generate_json generate_json_field_list t.

Lemma string_app_nil (s : string) :
  (s ++ "")%string = s.
Proof.
  induction s.
  - reflexivity.
  - replace (String.String a s ++ "")%string
       with (String.String a (s ++ "")%string) by reflexivity.
    rewrite IHs.
    reflexivity.
Qed.

(* TODO Move this to some other file *)
Lemma string_app_assoc (s1 s2 s3 : string) :
  ((s1 ++ s2)%string ++ s3)%string = (s1 ++ (s2 ++ s3)%string)%string.
Proof.
  induction s1.
  - reflexivity.
  - assert (forall x y,
      (String.String a x ++ y)%string = String.String a (x ++ y)%string).
    { reflexivity. }
    repeat rewrite H.
    rewrite IHs1.
    reflexivity.
Qed.

Section Generate_Json_Equal_Section.
  Context {locals: map.map string {t & interp_type t}} {locals_ok: map.ok locals}.
  Context { tenv : map.map string (type * bool) }
          { tenv_ok : map.ok tenv }.

  Lemma string_move c1 c2 s :
    String.String c1 (String.String c2 s) =
          ((String.String c1 (String.String c2 "")) ++ s)%string.
  Proof. reflexivity. Qed.

  Lemma string_app_nonempty (s1 s2 : string) :
    ((s1 ++ ": " ++ s2)%string =? "")%string = false.
  Proof. destruct s1, s2; easy. Qed.

  Lemma str_pre_eq a s1 s2:
    String.String a s1 = String.String a s2 ->
    s1 = s2.
  Proof. intros. injection H. easy. Qed.

  Lemma str_app_eq_left p s t:
    (p ++ s)%string = (p ++ t)%string ->
    s = t.
  Proof.
    induction p; try easy.
      cbn.
      intros.
      apply str_pre_eq in H.
      apply IHp. apply H.
  Qed.

  Lemma str_len_app s t :
    String.length (s ++ t) = (String.length s + String.length t)%nat.
  Proof.
    induction s; simpl; congruence.
  Qed.

  Lemma str_len_eq s t :
    s = t -> String.length s = String.length t.
  Proof.
    congruence.
  Qed.


  Lemma str_app_eq_right p s t:
    (s ++ p)%string = (t ++ p)%string ->
    s = t.
  Proof.
    revert p t.
    induction s; destruct t; cbn; eauto.
    - intros. apply str_len_eq in H. simpl in H.
      rewrite str_len_app in H. lia.
    - intros. apply str_len_eq in H. simpl in H.
      rewrite str_len_app in H. lia.
    - intros. inversion H. f_equal.
      eauto.
  Qed.

  Lemma fold_right_map A B C (f : B -> C -> C) (g : A -> B) (l : list A) x :
    fold_right f x (map g l) = fold_right (fun y => f (g y)) x l.
  Proof.
    induction l; cbn; try congruence.
  Qed.


  Lemma concat_fold_right s l:
    ~(In "" l) ->
    String.concat s l = fold_right (fun v acc =>
    (v ++ (if (acc =? "")%string then "" else s) ++ acc)%string) "" l.
  Proof.
    induction l; try reflexivity.
    cbn. intros. rewrite <- IHl.
    - destruct l.
      * cbn. rewrite string_app_nil. reflexivity.
      * f_equal. f_equal.
        cbn. destruct l.
        ** cbn in H. destruct (String.eqb_spec s0 ""); intuition.
        ** destruct (String.eqb_spec (s0 ++ s ++ String.concat s (s1 :: l))%string "").
           + destruct s; try reflexivity.
             apply str_len_eq in H0.
             repeat rewrite str_len_app in H0.
             simpl in H0.
             lia.
           + reflexivity.
    - intuition.
  Qed.

  Check map_ext.
  Lemma fold_right_ext A B (f : A -> B -> B) g l x :
    (forall a b, f a b = g a b) ->
    fold_right f x l = fold_right g x l.
  Proof.
    intros.
    induction l; cbn; congruence.
  Qed.

  Lemma proj_expected_refl t a :
    proj_expected t (existT interp_type t a) = a.
  Proof. Admitted.

  Lemma not_in_any (A : Type) x (l : list A) :
      (forall v, In v l -> v <> x) -> ~ In x l.
  Proof.
    intros. induction l; try easy.
    rewrite not_in_cons. split.
    - apply not_eq_sym. apply H. apply in_eq.
    - apply IHl. intros.
      apply H. apply in_cons. apply H0.
  Qed.

  Lemma not_in_any2 (A B : Type) (x : B) (f : A -> B) (l : list A) :
    (forall y, f y <> x) ->
    ~ In x (map f l).
  Proof.
    intros. induction l; try easy.
    apply not_in_cons. split.
    - apply not_eq_sym. apply H.
    - apply IHl.
  Qed.


  Fixpoint is_record_type (t : type) : Prop :=
    match t with
    | Unit => True
    | Pair s t1 t2 => is_json_type t1 /\ is_record_type t2
    | _ => False
    end
  with is_json_type (t : type) : Prop :=
  match t with
  | Pair s t1 t2 => is_json_type t1 /\ is_record_type t2
  | List t => is_json_type t
  | _ => True
  end.

  Fixpoint type_size (t : type) : nat :=
    match t with
    | Pair s t1 t2 => 2 + (type_size t1 + type_size t2)
    | List t => S (type_size t)
    | _ => 0
    end.

  Lemma generate_json_full_eq (l : locals) (n : nat) (t : type) :
    (type_size t < n)%nat ->
    (forall (t1 : type) (i2 : interp_type t) (i1 : interp_type t1) s (e : expr (Pair s t1 t)),
    is_json_type t1 ->
    is_record_type t ->
    (S (type_size t1) < n)%nat ->
    interp_expr l e = (i1, i2) ->
    to_json_field_list (Pair s t1 t) (i1, i2) = interp_expr l (generate_json_field_list (Pair s t1 t) e))
    /\
    (forall (v : interp_type t) (e : expr t),
    interp_expr l e = v ->
    is_json_type t ->
    to_json t v = interp_expr l (generate_json t e)).
  Proof.
    revert l t. induction n; try lia; destruct t; split; intros; cbn -[append] in *;
      try tauto. 
    - cbn. congruence.
    - intros. try (cbn; try rewrite H; reflexivity); cbn.
      * (* Bool *) destruct v; rewrite H0; reflexivity.
    - intros. cbn; try rewrite H0; reflexivity; cbn.
    - cbn -[append]. destruct i2.
      repeat rewrite string_app_assoc. repeat f_equal.
      * apply IHn; try lia; auto.
        ** cbn. rewrite H3. reflexivity.
      * repeat rewrite <- string_app_assoc.
        apply IHn; try lia; intuition auto.
        cbn. rewrite H3. reflexivity.
    - destruct v. repeat f_equal. apply IHn; try lia; intuition auto.
    - intros. cbn. repeat rewrite string_app_assoc. repeat f_equal.
      rewrite string_app_nil.
      apply IHn; try lia; intuition auto. cbn. rewrite H3. reflexivity.
    - repeat rewrite string_app_assoc. f_equal. f_equal.
      rewrite H0.

      rewrite concat_fold_right.
      * rewrite fold_right_map. apply fold_right_ext.
        intros. unfold set_local, get_local.
        rewrite map.get_put_same.
        cbn -[append].
        repeat rewrite string_app_assoc. f_equal.
        specialize (IHn (map.put (map.put l "v" (existT interp_type t a)) "acc"
                     (existT interp_type String b)) t).
        destruct IHn as [field_list to_json_eq]; try lia.
        rewrite (to_json_eq a (EVar t "v")).
        ** reflexivity.
        ** cbn. unfold get_local.
           rewrite map.put_put_diff by congruence. 
           rewrite map.get_put_same.
           apply proj_expected_refl.
        ** intuition auto.
      * apply not_in_any2. intros. destruct t; try easy.
        ** cbn.
           destruct Z.to_int; try easy.
           destruct Decimal.Pos; try easy.
           cbn. destruct d0; try easy.
        ** destruct y; easy.
  Qed.

  Theorem generate_json_eq : (forall l t (v : interp_type t) (e : expr t),
    interp_expr l e = v ->
    is_json_type t ->
    to_json t v = interp_expr l (generate_json t e)).
  Proof. intros. eapply generate_json_full_eq; auto. Qed.
End Generate_Json_Equal_Section.


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




  Compute (interp_expr (map.put map.empty "x" (existT interp_type (TPair "foo" TString TInt)
        ("hi", 7)))
        (generate_json (TPair "foo" TString TInt) (EVar _ "x")) =? 
  to_json (TPair "foo" TString TInt) ("hi", 7))%string.






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
  Definition map_to_locals (init : list (string * (type * bool))) : locals :=
    init_locals (map (fun x => match x with
                               | (x, (t, _)) => (x, t)
                               end) init).

  Definition run_program (init : list (string * (type * bool))) (pc : pcommand)
     := c <- @elaborate_command tenv (map.of_list init) pc;;
        Success (SortedList.value (interp_command (map_to_locals init) c)).


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



Section WithMap.
  Context {locals: map.map string {t & interp_type t}} {locals_ok: map.ok locals}.
  Context { tenv : map.map string (type * bool) }
          { tenv_ok : map.ok tenv }.


  Lemma fold_left_loop (A : Type) (Q : locals -> Prop) (P : locals -> Prop) (lcls : locals) f (l : list A)
   : Q lcls ->
        (forall lcls' e,
            In e l ->
            Q lcls' ->
            Q (f lcls' e)) ->
        (forall lcls', Q lcls' -> P lcls') ->
        P (fold_left f l lcls).
  Proof.
  Admitted.

  (* TODO This should be in Coqutil *)
  Lemma fold_left_ext (A B : Type) P (Q : B -> Prop) l (f g : A -> B -> A):
    (forall x y, P x -> P (f x y)) ->
    (forall x y, P x -> P (g x y)) ->
    (forall x y,
      P x -> Q y ->
      f x y = g x y) ->
    (forall a,
      P a -> Forall Q l ->
      fold_left f l a = fold_left g l a).
  Proof.
    intros H0 H1 H2.
    induction l; try easy.
    simpl.
    intros.
    inversion H; subst.
    rewrite H2; try easy.
    eapply IHl; eauto.
  Qed.

  Lemma fold_left_no_ans (l : list Z) m :
    map.get m "ans" = None ->
    map.get
      (fold_left
         (fun (x1 : locals) (x2 : interp_type Int) =>
          map.put x1 "x" (existT interp_type Int x2))
          l m) "ans" =
    None.
  Proof.
    generalize dependent m. induction l; try easy.
    intros.
    cbn.
    apply IHl.
    rewrite map.get_put_diff by congruence.
    apply H.
  Qed.

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
