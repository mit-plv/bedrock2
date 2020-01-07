Require Coq.Lists.List.
Require Coq.Arith.PeanoNat.
Require Coq.Arith.Compare_dec.
Require Coq.ZArith.BinInt.
Require Coq.NArith.NArith.
Require Coq.Strings.String.
Require Coq.ZArith.ZArith.
Require Coq.micromega.Lia.
Require Coq.omega.Omega.
Require Coq.Program.Tactics.
Require Coq.btauto.Btauto.
Require Coq.setoid_ring.Ring_theory.
Require Coq.ZArith.BinIntDef.
Require Coq.Numbers.BinNums.
Require Coq.Classes.Morphisms.
Module coqutil_DOT_Macros_DOT_subst.
Module coqutil.
Module Macros.
Module subst.
Notation "'subst!' y 'for' x 'in' f" := (match y with x => f end) (at level 10).

End subst.

End Macros.

End coqutil.

End coqutil_DOT_Macros_DOT_subst.

Module coqutil_DOT_Macros_DOT_unique.
Module coqutil.
Module Macros.
Module unique.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Notation "'unique!' cls" := (ltac:(
  match constr:(Set) with
  | _ => let __ := constr:(_:cls) in fail 1 "unique!: already have an instance of" cls
  | _ => exact cls%type
  end))
  (at level 10, only parsing).

End unique.

End Macros.

End coqutil.

End coqutil_DOT_Macros_DOT_unique.

Module coqutil_DOT_sanity.
Module coqutil.
Module sanity.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Global Unset Refine Instance Mode.
Global Unset Universe Minimization ToSet.
Global Set Default Goal Selector "!".

(** Work around some counter-intuitive defaults. *)

(** [intuition] means [intuition auto with *].  This is very wrong and
    fragile and slow.  We make [intuition] mean [intuition auto]. *)
Tactic Notation "intuition" tactic3(tactic) := intuition tactic.
Tactic Notation "intuition" := intuition auto.

(** [firstorder] means [firstorder auto with *].  This is very wrong
    and fragile and slow.  We make [firstorder] mean [firstorder
    auto]. *)
Global Set Firstorder Solver auto.

(** A version of [intuition] that allows you to see how the old
    [intuition] tactic solves the proof. *)
Ltac debug_intuition := idtac "<infomsg>Warning: debug_intuition should not be used in production code.</infomsg>"; intuition debug auto with *.

(** [assert_fails] and [assert_succeeds] should never solve the goal.
    This redefinition fixes both of them, and the notations of the standard library can
    be reused.
    https://github.com/coq/coq/issues/9114 *)
Ltac assert_fails tac ::=
  tryif (cut True; [ intros _; tac | ]) then fail 0 tac "succeeds" else idtac.

Goal 1 = 1.
  assert_succeeds reflexivity.
  assert_fails (exact I).
  Fail assert_succeeds (exact I).
  Fail assert_fails reflexivity.
  idtac.
Abort.

End sanity.

End coqutil.

End coqutil_DOT_sanity.

Module coqutil_DOT_Datatypes_DOT_PrimitivePair.
Module coqutil.
Module Datatypes.
Module PrimitivePair.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Module pair.
  Local Set Universe Polymorphism.
  Local Set Primitive Projections.
  Record pair {A B} := mk { _1 : A; _2 : B _1 }.
  Arguments pair : clear implicits.
  Arguments mk {A B} _ _.

  (* TODO: make * right-associative like /\ *)
  Notation "A * B" := (pair A%type (fun _ => B%type)) : type_scope.

  Notation "{ x  &  P }" := (pair _ (fun x => P)) : type_scope.
  Notation "{ ' pat  &  P }" := (pair _ (fun pat => P)) : type_scope.

  Notation "{ x : A  &  P }" := (pair A (fun x => P)) : type_scope.
  Notation "{ ' pat : A  &  P }" := (pair A (fun pat => P)) : type_scope.

  Notation "( x , y , .. , z )" := (mk .. (mk x y) .. z) : core_scope.

  Notation "x '.(1)'" := (_1 x) (at level 1, left associativity) : core_scope.
  Notation "x '.(2)'" := (_2 x) (at level 1, left associativity) : core_scope.
End pair. Notation pair := pair.pair.

End PrimitivePair.

End Datatypes.

End coqutil.

End coqutil_DOT_Datatypes_DOT_PrimitivePair.

Module coqutil_DOT_Datatypes_DOT_HList.
Module coqutil.
Module Datatypes.
Module HList.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import Coq.Lists.List.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.PrimitivePair. Import pair.
Local Set Universe Polymorphism.

Module Import polymorphic_list.
  Inductive list {A : Type} : Type := nil | cons (_:A) (_:list).
  Arguments list : clear implicits.

  Section WithA.
    Context {A : Type}.
    Fixpoint length (l : list A) : nat :=
      match l with
      | nil => 0
      | cons _ l' => S (length l')
      end.
  End WithA.

  Section WithElement.
    Context {A} (x : A).
    Fixpoint repeat (x : A) (n : nat) {struct n} : list A :=
      match n with
      | 0 => nil
      | S k => cons x (repeat x k)
      end.
  End WithElement.
End polymorphic_list.

Fixpoint arrows (argts : list Type) : Type -> Type :=
  match argts with
  | nil => fun ret => ret
  | cons T argts' => fun ret => T -> arrows argts' ret
  end.

Fixpoint hlist@{i j} (argts : list@{j} Type@{i}) : Type@{j} :=
  match argts with
  | nil => unit
  | cons T argts' => T * hlist argts'
  end.

Module hlist.
  Fixpoint apply {argts : list Type} : forall {P} (f : arrows argts P) (args : hlist argts), P :=
    match argts return forall {P} (f : arrows argts P) (args : hlist argts), P with
    | nil => fun P f _ => f
    | cons T argts' => fun P f '(x, args') => apply (f x) args'
    end.

  Fixpoint binds {argts : list Type} : forall {P} (f : hlist argts -> P), arrows argts P :=
    match argts return forall {P} (f : hlist argts -> P), arrows argts P with
    | nil => fun P f => f tt
    | cons T argts' => fun P f x => binds (fun xs' => f (x, xs'))
    end.

  Fixpoint foralls {argts : list Type} : forall (P : hlist argts -> Prop), Prop :=
    match argts with
    | nil => fun P => P tt
    | cons T argts' => fun P => forall x:T, foralls (fun xs' => P (x, xs'))
    end.

  Fixpoint existss {argts : list Type} : forall (P : hlist argts -> Prop), Prop :=
    match argts with
    | nil => fun P => P tt
    | cons T argts' => fun P => exists x:T, existss (fun xs' => P (x, xs'))
    end.

  Lemma foralls_forall {argts} {P} : @foralls argts P -> forall x, P x.
  Proof.
    revert P; induction argts as [|A argts']; intros P.
    { destruct x; eauto. }
    { cbn. intros H xs.
      refine (IHargts' (fun xs' => P (xs.(1), xs')) _ _); eauto. }
  Qed.

  Lemma existss_exists {argts} {P} : @existss argts P -> exists x, P x.
  Proof.
    revert P; induction argts as [|A argts']; intros P.
    { intro. exists tt. eauto. }
    { cbn. intros [x xs'].
      destruct (IHargts' (fun xs' => P (x, xs'))); eauto. }
  Qed.
End hlist.

Definition tuple A n := hlist (repeat A n).
Definition ufunc A n := arrows (repeat A n).
Module tuple.
  Notation apply := hlist.apply.
  Definition binds {A n} := hlist.existss (argts:=repeat A n).
  Definition foralls {A n} := hlist.foralls (argts:=repeat A n).
  Definition existss {A n} := hlist.existss (argts:=repeat A n).

  Import Datatypes.
  Section WithA.
    Context {A : Type}.
    Fixpoint to_list {n : nat} : tuple A n -> list A :=
      match n return tuple A n -> list A with
      | O => fun _ => nil
      | S n => fun '(pair.mk x xs') => cons x (to_list xs')
      end.

    Fixpoint of_list (xs : list A) : tuple A (length xs) :=
      match xs with
      | nil => tt
      | cons x xs => pair.mk x (of_list xs)
      end.

    Fixpoint option_all {sz : nat} : tuple (option A) sz -> option (tuple A sz) :=
      match sz with
      | O => fun _ => Some tt
      | S sz' => fun '(pair.mk ox xs) =>
                   match ox, option_all xs with
                   | Some x, Some ys => Some (pair.mk x ys)
                   | _ , _ => None
                   end
      end.

    Section WithF.
      Context {B: Type}.
      Context (f: A -> B).
      Fixpoint map{sz: nat}: tuple A sz -> tuple B sz :=
        match sz with
        | O => fun _ => tt
        | S sz' => fun '(pair.mk x xs) => pair.mk (f x) (map xs)
        end.
    End WithF.

    Section WithStep.
      Context (step : A -> A).
      Fixpoint unfoldn (n : nat) (start : A) : tuple A n :=
        match n with
        | O => tt
        | S n => pair.mk start (unfoldn n (step start))
        end.
    End WithStep.
  End WithA.
End tuple.

End HList.

End Datatypes.

End coqutil.

End coqutil_DOT_Datatypes_DOT_HList.

Module coqutil_DOT_Tactics_DOT_autoforward.
Module coqutil.
Module Tactics.
Module autoforward.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Definition autoforward (A B : Prop) := A -> B.

Ltac autoforward_in db H :=
  let tmp := fresh H in
  rename H into tmp;
  let A := type of tmp in
  pose proof ((ltac:(typeclasses eauto with db) : autoforward A _) tmp) as H;
  clear tmp.

Tactic Notation "autoforward" "with" ident(db) "in" hyp(H) :=
  autoforward_in db H.

End autoforward.

End Tactics.

End coqutil.

End coqutil_DOT_Tactics_DOT_autoforward.

Module coqutil_DOT_Decidable.
Module coqutil.
Module Decidable.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import coqutil_DOT_sanity.coqutil.sanity coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.autoforward.
Import Coq.Arith.PeanoNat.
Import Coq.Arith.Compare_dec.
Import Coq.ZArith.BinInt.
Import Coq.NArith.NArith.

(* needed because it unfolds to Nat.leb and then typeclass search picks Nat.leb_spec
   instead of Nat.ltb_spec *)
Hint Opaque Nat.ltb : typeclass_instances.

Existing Class BoolSpec.

Lemma BoolSpec_true P Q x (H : BoolSpec P Q x) : autoforward (x = true) P.
Proof. intro; subst. inversion H; auto. Qed.

Lemma BoolSpec_false P Q x (H : BoolSpec P Q x) : autoforward (x = false) Q.
Proof. intro; subst. inversion H; auto. Qed.

Hint Resolve BoolSpec_true BoolSpec_false : typeclass_instances.

Notation EqDecider f := (forall x y, BoolSpec (x = y) (x <> y) (f x y)).

Module Nat.
  Lemma eqb_spec: EqDecider Nat.eqb.
  Proof.
    intros. destruct (x =? y) eqn: E; constructor.
    - apply Nat.eqb_eq. assumption.
    - apply Nat.eqb_neq. assumption.
  Qed.
End Nat.

Module N.
  Lemma eqb_spec: EqDecider N.eqb.
  Proof.
    intros. destruct (x =? y)%N eqn: E; constructor.
    - apply N.eqb_eq. assumption.
    - apply N.eqb_neq. assumption.
  Qed.
End N.

Module Z.
  Lemma eqb_spec: EqDecider Z.eqb.
  Proof.
    intros. destruct (x =? y)%Z eqn: E; constructor.
    - apply Z.eqb_eq. assumption.
    - apply Z.eqb_neq. assumption.
  Qed.
End Z.

Module String.
  Lemma eqb_spec: EqDecider String.eqb.
  Proof.
    intros. destruct (String.eqb x y) eqn: E; constructor.
    - apply String.eqb_eq. assumption.
    - apply String.eqb_neq. assumption.
  Qed.
End String.

Hint Resolve
     Nat.eqb_spec
     Nat.leb_spec
     Nat.ltb_spec
     N.eqb_spec
     N.leb_spec
     N.ltb_spec
     Z.eqb_spec
     Z.gtb_spec
     Z.geb_spec
     Z.leb_spec
     Z.ltb_spec
     String.eqb_spec
: typeclass_instances.


Goal forall x y, Nat.ltb x y = true -> x < y.
  intros.
  autoforward with typeclass_instances in H.
  assumption.
  all: fail "goals remaining".
Abort.

End Decidable.

End coqutil.

End coqutil_DOT_Decidable.

Module coqutil_DOT_Tactics_DOT_destr.
Module coqutil.
Module Tactics.
Module destr.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.autoforward.
Import coqutil_DOT_Decidable.coqutil.Decidable. (* adds hints to typeclass_instances needed by autoforward *)

Ltac destr d :=
  match type of d with
  | _ => is_var d; destruct d
  | sumbool _ _ => destruct d
  | _ => let E := fresh "E" in destruct d eqn: E;
         try autoforward with typeclass_instances in E
  end.

End destr.

End Tactics.

End coqutil.

End coqutil_DOT_Tactics_DOT_destr.

Module coqutil_DOT_Tactics_DOT_forward.
Module coqutil.
Module Tactics.
Module forward.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
(* Tactics for forward-reasoning *)

Ltac ensure_new H :=
  let t := type of H in
  assert_fails (clear H; match goal with
                | A: t |- _ => idtac
                end).

(** [pose proof defn], but only if no hypothesis of the same type exists.
    most useful for proofs of a proposition *)
Tactic Notation "unique" "pose" "proof" constr(defn) "as" ident(H) :=
  let T := type of defn in
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => pose proof defn as H
  end.

Tactic Notation "unique" "pose" "proof" constr(defn) :=
  let T := type of defn in
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => pose proof defn
  end.

Ltac hard_assert_is_sort E :=
  let T := type of E in
  lazymatch T with
  | Set => idtac
  | Prop => idtac
  | Type => idtac
  | _ =>
  (* this error is almost certainly a bug, so we let it bubble up with level 10000, instead
     of being swallowed by try, repeat, ||, etc *)
    fail 10000 "type of" E "is" T "but should be Set, Prop or Type"
  end.

Ltac specialize_with E :=
  (* Catch errors such as E is something like "@name: NameWithEq -> Set" instead of "name: Set" *)
  hard_assert_is_sort E;
  repeat match goal with
  | H: forall (x: E), _, y: E |- _ =>
    match type of H with
    | forall x y, BoolSpec _ _ _ => fail 1
    | _ => let H' := fresh H y in unique pose proof (H y) as H'
    end
  end.

Tactic Notation "unique" "eapply" constr(p) "in" "copy" "of" ident(H) :=
  let H' := fresh H "_uac" in
  pose proof H as H';
  unshelve eapply p in H';
  [ ensure_new H' | assumption .. ].

Ltac ret_type P :=
  lazymatch P with
  | forall x, @?Q x => let Q' := open_constr:(Q _) in
                       let Q'' := eval cbv beta in Q' in
                           ret_type Q''
  | _ -> ?Q => ret_type Q
  | ?Q => open_constr:(Q)
  end.

Ltac especialize_as P H :=
  let T := type of P in
  let R := ret_type T in
  assert R as H; [eapply P|].

Ltac especialize H :=
  let T := type of H in
  let R := ret_type T in
  let N := fresh in
  rename H into N;
  assert R as H; [eapply N|]; clear N.

Ltac auto_specialize :=
  repeat match goal with
         | H: ?P -> _, H': _ |- _ => match type of P with
                                     | Prop => specialize (H H')
                                     end
         end.

Ltac apply_in_hyps t :=
  repeat match goal with
         | H: _ |- _ => unique eapply t in copy of H
         end.

Ltac specialize_first_num P Q :=
  first [ specialize P with (1 := Q)
        | specialize P with (2 := Q)
        | specialize P with (3 := Q)
        | specialize P with (4 := Q)
        | specialize P with (5 := Q)
        | specialize P with (6 := Q)
        | specialize P with (7 := Q)
        | specialize P with (8 := Q)
        | specialize P with (9 := Q)
        | fail 1 "no match found for" Q "within the first few hypotheses of" P ].

Ltac specialize_first_ident P a :=
  match type of P with
  | forall                                           (x: _), _ => specialize P with (x := a)
  | forall                                         _ (x: _), _ => specialize P with (x := a)
  | forall                                       _ _ (x: _), _ => specialize P with (x := a)
  | forall                                     _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                                   _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                                 _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                               _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                             _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                           _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                         _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                       _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                     _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                   _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                 _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall               _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall           _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall         _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall       _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | _ => fail 1 "no match found for" a "within the first few arguments of" P
  end.

Ltac specialize_first P Q := specialize_first_num P Q || specialize_first_ident P Q.

End forward.

End Tactics.

End coqutil.

End coqutil_DOT_Tactics_DOT_forward.

Module coqutil_DOT_Tactics_DOT_Tactics.
Module coqutil.
Module Tactics.
Module Tactics.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import Coq.ZArith.ZArith.
Export coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.forward.
Export coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.destr.

Tactic Notation "forget" constr(X) "as" ident(y) := set (y:=X) in *; clearbody y.

Ltac destruct_one_match :=
  match goal with
  | [ |- context[match ?e with _ => _ end] ] => destr e
  end.

Ltac destruct_one_match_hyp_test type_test :=
  match goal with
  | H: context[match ?e with _ => _ end] |- _ => let T := type of e in type_test T; destr e
  | H: context[if ?e then _ else _]      |- _ => let T := type of e in type_test T; destr e
  end.

Ltac destruct_one_match_hyp_of_type T :=
  destruct_one_match_hyp_test ltac:(fun t => unify t T).

Ltac destruct_one_match_hyp :=
  destruct_one_match_hyp_test ltac:(fun t => idtac).

Ltac repeat_at_least_once tac := tac; repeat tac.
Tactic Notation "repeatplus" tactic(t) := (repeat_at_least_once t).

Ltac destruct_products :=
  repeat match goal with
  | p: _ * _  |- _ => destruct p
  | H: _ /\ _ |- _ => let Hl := fresh H "l" in let Hr := fresh H "r" in destruct H as [Hl Hr]
  | E: exists y, _ |- _ => let yf := fresh y in destruct E as [yf E]
  end.

Ltac deep_destruct H :=
  lazymatch type of H with
  | exists x, _ => let x' := fresh x in destruct H as [x' H]; deep_destruct H
  | _ /\ _ => let H' := fresh H in destruct H as [H' H]; deep_destruct H'; deep_destruct H
  | _ \/ _ => destruct H as [H | H]; deep_destruct H
  | _ => idtac
  end.

(* simplify an "if then else" where only one branch is possible *)
Ltac simpl_if :=
  match goal with
  | |- context[if ?e then _ else _]      => destr e; [contradiction|]
  | |- context[if ?e then _ else _]      => destr e; [|contradiction]
  | _: context[if ?e then _ else _] |- _ => destr e; [contradiction|]
  | _: context[if ?e then _ else _] |- _ => destr e; [|contradiction]
  end.

Ltac rewrite_match :=
  repeat match goal with
  | E: ?A = _ |- context[match ?A with | _ => _ end] => rewrite E
  end.

Tactic Notation "so" tactic(f) :=
  match goal with
  | _: ?A |- _  => f A
  |       |- ?A => f A
  end.

Ltac exists_to_forall H :=
  match type of H with
  | (exists k: ?A, @?P k) -> ?Q =>
    let Horig := fresh in
    rename H into Horig;
    assert (forall k: A, P k -> Q) as H by eauto;
    clear Horig;
    cbv beta in H
  end.

Ltac destruct_one_match_hyporgoal_test check cleanup :=
  match goal with
  | |- context[match ?d with _ => _ end]      => check d; destr d; subst
  | H: context[match ?d with _ => _ end] |- _ => check d; destr d; subst; cleanup H
  end.

Ltac specialize_hyp H :=
    repeat match type of H with
           | ?P -> ?Q => let F := fresh in assert P as F; [clear H|specialize (H F); clear F]
           end.

(* What "split" really should be: does not unfold definitions to discover more
   conjunctions, but does split multiple conjunctions *)
Ltac ssplit :=
  repeat match goal with
         | |- _ /\ _ => split
         end.

(* needed because of https://github.com/coq/coq/issues/10848 *)
Ltac prewrite lhs lem :=
  pattern lhs;
  eapply eq_rect; [|symmetry; eapply lem].

End Tactics.

End Tactics.

End coqutil.

End coqutil_DOT_Tactics_DOT_Tactics.

Module coqutil_DOT_Z_DOT_Lia.
Module coqutil.
Module Z.
Module Lia.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import Coq.micromega.Lia.
Import Coq.omega.Omega.

(* Note: running is_lia before lia is not always what you want, because lia can also
   solve contradictory goals where the conclusion is not LIA,
   and it can also deal with conjunctions and disjunctions *)
Ltac is_lia P :=
  lazymatch P with
  | @eq Z _ _ => idtac
  | not (@eq Z _ _) => idtac
  | (_ < _)%Z => idtac
  | (_ <= _)%Z => idtac
  | (_ <= _ < _)%Z => idtac
  | @eq nat _ _ => idtac
  | not (@eq nat _ _) => idtac
  | (_ < _)%nat => idtac
  | (_ <= _)%nat => idtac
  | (_ <= _ < _)%nat => idtac
  | _ => fail "The term" P "is not LIA"
  end.

(* We have encountered cases where lia is insanely slower than omega,
   (https://github.com/coq/coq/issues/9848), but not the other way. *)
Ltac compare_tacs omegatac liatac :=
  idtac; (* <-- needed to prevent invocations such as [intuition blia] from
                applying blia right away instead of passing it to [intuition] *)
  lazymatch goal with
  | |- ?G =>
    let Ho := fresh in let Hl := fresh in
    tryif (assert G as Ho by omegatac) then (
      tryif (assert G as Hl by liatac) then (
        (* both succeed *)
        exact Ho
      ) else (
        (* lia failed on a goal omega solved *)
        idtac "BAD_LIA";
        exact Ho
      )
    ) else (
      tryif (assert G as Hl by liatac) then (
        (* omega failed on a goal lia solved *)
        idtac "BAD_OMEGA";
        exact Hl
      ) else (
        (* both failed (this can be intended) *)
        fail
      )
    )
  end.

(* Tests:

Ltac loop_forever := idtac; loop_forever.

Ltac wait z :=
  match eval cbv in (Z.to_nat z) with
  | S ?n => wait (Z.of_nat n); wait (Z.of_nat n)
  | O => idtac
  end.

Goal True. compare_tacs ltac:(wait 10%Z; exact I) ltac:(wait 10%Z; fail). Abort.
Goal True. compare_tacs ltac:(wait 10%Z; fail) ltac:(wait 10%Z; exact I). Abort.
Goal True. compare_tacs ltac:(wait 10%Z; exact I) ltac:(wait 10%Z; exact I). Abort.
Goal True. compare_tacs ltac:(wait 10%Z; fail) ltac:(wait 10%Z; fail). Abort.
Goal True. compare_tacs ltac:(wait 10%Z; exact I) ltac:(loop_forever). Abort.

*)

Ltac compare_omega_lia_timed :=
  compare_tacs ltac:(time "omega" omega) ltac:(time "lia" lia).

Ltac compare_omega_lia :=
  compare_tacs ltac:(omega) ltac:(lia).

Ltac default_lia := omega || lia.

(* bench-lia to be used by all code, unless lia doesn't work *)
Ltac blia := lia.

(* bench-omega: to be used if we fear that using lia would be slow or fail.
   But we still use the bomega alias instead of plain omega, so that we can experiment
   with swapping it by lia. *)
Ltac bomega := omega.

End Lia.

End Z.

End coqutil.

End coqutil_DOT_Z_DOT_Lia.

Module coqutil_DOT_Datatypes_DOT_List.
Module coqutil.
Module Datatypes.
Module List.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import coqutil_DOT_sanity.coqutil.sanity.
Import coqutil_DOT_Decidable.coqutil.Decidable.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.destr coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.Tactics.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.Lia.
Import Coq.Lists.List. Import ListNotations.


Section WithA.
  Context {A : Type}.
  Fixpoint option_all (xs : list (option A)) {struct xs} : option (list A) :=
    match xs with
    | nil => Some nil
    | cons ox xs =>
      match ox, option_all xs with
      | Some x, Some ys => Some (cons x ys)
      | _ , _ => None
      end
    end.

  Definition removeb(aeq: A -> A -> bool){aeq_spec: EqDecider aeq}(e: A)(l: list A): list A :=
    filter (fun e' => negb (aeq e e')) l.

  Lemma removeb_not_In{aeqb : A -> A -> bool}{aeqb_dec: EqDecider aeqb}:
    forall (l : list A) (a: A), ~ In a l -> removeb aeqb a l = l.
  Proof.
    induction l; intros; simpl; try reflexivity.
    destr (aeqb a0 a); simpl in *; subst.
    + exfalso. auto.
    + f_equal. eauto.
  Qed.

  Lemma In_removeb_In{aeqb : A -> A -> bool}{aeqb_dec: EqDecider aeqb}:
    forall (a1 a2: A) (l: list A), In a1 (removeb aeqb a2 l) -> In a1 l.
  Proof.
    induction l; intros; simpl in *; try contradiction.
    destr (aeqb a2 a); simpl in *; intuition idtac.
  Qed.

  Lemma In_removeb_diff{aeqb : A -> A -> bool}{aeqb_dec: EqDecider aeqb}:
    forall (a1 a2: A) (l: list A), a1 <> a2 -> In a1 l -> In a1 (removeb aeqb a2 l).
  Proof.
    induction l; intros; simpl in *; try contradiction.
    destr (aeqb a2 a); simpl in *; subst; intuition congruence.
  Qed.

  Lemma NoDup_removeb{aeqb : A -> A -> bool}{aeqb_dec: EqDecider aeqb}:
    forall (a: A) (l: list A),
      NoDup l ->
      NoDup (removeb aeqb a l).
  Proof.
    induction l; intros; simpl in *; try assumption.
    destr (aeqb a a0); simpl in *; inversion H; auto.
    constructor; auto. intro C. apply H2. eapply In_removeb_In. eassumption.
  Qed.

  Lemma length_NoDup_removeb{aeqb: A -> A -> bool}{aeqb_sepc: EqDecider aeqb}:
    forall (s: list A) (a: A),
      In a s ->
      NoDup s ->
      Datatypes.length (removeb aeqb a s) = pred (Datatypes.length s).
  Proof.
    induction s; intros.
    - simpl in H. contradiction.
    - simpl in *. inversion H0. subst. destr (aeqb a0 a).
      + simpl. subst. rewrite removeb_not_In by assumption. reflexivity.
      + simpl. destruct H; [congruence|].
        rewrite IHs by assumption.
        destruct s.
        * simpl in *. contradiction.
        * reflexivity.
  Qed.

  Section WithStep.
    Context (step : A -> A).
    Fixpoint unfoldn (n : nat) (start : A) :=
      match n with
      | 0%nat => nil
      | S n => cons start (unfoldn n (step start))
      end.
  End WithStep.

  Lemma length_nil : length (@nil A) = 0. Proof. reflexivity. Qed.
  Lemma length_cons x xs : length (@cons A x xs) = S (length xs).
  Proof. exact eq_refl. Qed.

  Lemma tl_skipn n (xs : list A) : tl (skipn n xs) = skipn (S n) xs.
  Proof. revert xs; induction n, xs; auto; []; eapply IHn. Qed.
  Lemma tl_is_skipn1 (xs : list A) : tl xs = skipn 1 xs.
  Proof. destruct xs; reflexivity. Qed.
  Lemma skipn_all_exact (xs : list A) : skipn (length xs) xs = nil.
  Proof. induction xs; eauto. Qed.
  Lemma skipn_0_l (xs : list A) : skipn 0 xs = xs.
  Proof. exact eq_refl. Qed.
  Lemma skipn_nil_r n : @skipn A n nil = nil.
  Proof. induction n; auto. Qed.
  Lemma skipn_all n (xs : list A) (H : le (length xs) n) : skipn n xs = nil.
  Proof.
    revert dependent xs; induction n, xs; cbn; auto; try blia; [].
    intros; rewrite IHn; trivial; blia.
  Qed.

  Lemma length_firstn_inbounds n (xs : list A) (H : le n (length xs))
    : length (firstn n xs) = n.
  Proof.
    rewrite firstn_length, PeanoNat.Nat.min_comm.
    destruct (Min.min_spec (length xs) n); blia.
  Qed.
  Lemma length_tl_inbounds (xs : list A) : length (tl xs) = (length xs - 1)%nat.
  Proof.
    destruct xs; cbn [length tl]; Lia.lia.
  Qed.
  Lemma length_skipn n (xs : list A) :
    length (skipn n xs) = (length xs - n)%nat.
  Proof.
    pose proof firstn_skipn n xs as HH; eapply (f_equal (@length _)) in HH; rewrite <-HH.
    destruct (Compare_dec.le_lt_dec n (length xs)).
    { rewrite app_length, length_firstn_inbounds; Lia.lia. }
    { rewrite skipn_all, app_nil_r, firstn_all2, length_nil; Lia.lia. }
  Qed.

  Lemma skipn_nil n: skipn n (@nil A) = nil.
  Proof. destruct n; reflexivity. Qed.

  Lemma skipn_app n (xs ys : list A) : skipn n (xs ++ ys) = skipn n xs ++ skipn (n - length xs) ys.
  Proof.
    revert n ys.
    induction xs; intros.
    - simpl. rewrite skipn_nil. simpl. rewrite PeanoNat.Nat.sub_0_r. reflexivity.
    - simpl. destruct n.
      + simpl. reflexivity.
      + simpl. apply IHxs.
  Qed.

  Lemma skipn_skipn n m (xs : list A) : skipn n (skipn m xs) = skipn (n + m) xs.
  Proof.
    revert m xs.
    induction n; intros.
    - simpl. reflexivity.
    - change (S n + m) with (S (n + m)).
      destruct xs as [|x xs].
      + simpl. rewrite skipn_nil. reflexivity.
      + destruct m as [|m].
        * simpl. rewrite PeanoNat.Nat.add_0_r. reflexivity.
        * change (skipn (S m) (x :: xs)) with (skipn m xs).
          change (skipn (S (n + S m)) (x :: xs)) with (skipn (n + S m) xs).
          rewrite <- IHn.
          clear IHn x.
          revert n m.
          induction xs; intros.
          { simpl. rewrite !skipn_nil. reflexivity. }
          { destruct m as [|m].
            - simpl. reflexivity.
            - change (skipn (S m) (a :: xs)) with (skipn m xs).
              change (skipn (S (S m)) (a :: xs)) with (skipn (S m) xs).
              apply IHxs. }
  Qed.

  Lemma nth_error_nil_Some: forall i (a: A), nth_error nil i = Some a -> False.
  Proof.
    intros. destruct i; simpl in *; discriminate.
  Qed.

  Lemma nth_error_single_Some: forall (a1 a2: A) i,
      nth_error (a1 :: nil) i = Some a2 ->
      i = O /\ a1 = a2.
  Proof.
    intros. destruct i; inversion H; auto. simpl in *.
    exfalso. eapply nth_error_nil_Some. eassumption.
  Qed.

  Lemma nth_error_cons_Some: forall (a1 a2: A) (l: list A) i,
      nth_error (a1 :: l) i = Some a2 ->
      i = O /\ a1 = a2 \/ exists j, i = S j /\ nth_error l j = Some a2.
  Proof.
    intros. destruct i; simpl in *.
    - inversion H. auto.
    - eauto.
  Qed.

  Lemma nth_error_app_Some: forall (a: A) (l1 l2: list A) i,
      nth_error (l1 ++ l2) i = Some a ->
      nth_error l1 i = Some a \/ nth_error l2 (i - length l1) = Some a.
  Proof.
    intros.
    destr (Nat.ltb i (length l1)).
    - left. rewrite nth_error_app1 in H; assumption.
    - right. rewrite nth_error_app2 in H; assumption.
  Qed.

  Definition endswith (xs : list A) (suffix : list A) :=
    exists prefix, xs = prefix ++ suffix.
  Lemma endswith_refl (xs : list A) : endswith xs xs.
  Proof. exists nil; trivial. Qed.
  Lemma endswith_cons_l (x : A) xs ys :
    endswith ys xs -> endswith (cons x ys) xs.
  Proof. inversion 1; subst. eexists (cons x _). exact eq_refl. Qed.

End WithA.


Lemma remove_In_ne{A: Type}{aeqb: A -> A -> bool}{aeqb_spec: EqDecider aeqb}:
  forall (l: list A) (f1 f2: A),
      In f1 l ->
      f1 <> f2 ->
      In f1 (removeb aeqb f2 l).
Proof.
  induction l; intros.
  - inversion H.
  - simpl in *. destruct H.
    + subst a.
      destr (aeqb f2 f1); try congruence. simpl. auto.
    + destr (aeqb f2 a); simpl.
      * subst a. eauto.
      * simpl. eauto.
Qed.

Lemma firstn_skipn_reassemble: forall (T: Type) (l l1 l2: list T) (n: nat),
    List.firstn n l = l1 ->
    List.skipn n l = l2 ->
    l = l1 ++ l2.
Proof.
  intros. subst. symmetry. apply firstn_skipn.
Qed.

Lemma firstn_skipn_nth: forall (T: Type) (i: nat) (L: list T) (d: T),
    (i < length L)%nat ->
    List.firstn 1 (List.skipn i L) = [List.nth i L d].
Proof.
  induction i; intros.
  - simpl. destruct L; simpl in *; try (exfalso; blia). reflexivity.
  - simpl. destruct L; try (simpl in *; exfalso; blia). simpl.
    rewrite <- IHi; [reflexivity|]. simpl in *. blia.
Qed.

Definition listUpdate{E: Type}(l: list E)(i: nat)(e: E): list E :=
  firstn i l ++ [e] ++ skipn (S i) l.

Lemma listUpdate_length: forall E i l (e: E),
  i < length l ->
  length (listUpdate l i e) = length l.
Proof.
  induction i; intros.
  - destruct l; simpl in *; [bomega|reflexivity].
  - destruct l; simpl in *; [bomega|].
    f_equal.
    apply IHi.
    bomega.
Qed.

Definition listUpdate_error{E: Type}(l: list E)(i: nat)(e: E): option (list E) :=
  if Nat.ltb i (length l) then Some (listUpdate l i e) else None.

Lemma listUpdate_error_length: forall E i l l' (e: E),
  listUpdate_error l i e = Some l' ->
  length l' = length l.
Proof.
  intros. unfold listUpdate_error in H. destruct_one_match_hyp; [|discriminate].
  inversion H. apply listUpdate_length. assumption.
Qed.

Lemma nth_error_listUpdate_error_same: forall i E l l' (e e': E),
  listUpdate_error l i e = Some l' ->
  nth_error l' i = Some e' ->
  e' = e.
Proof.
  induction i; intros.
  - unfold listUpdate_error in H.
    destruct_one_match_hyp; [|discriminate].
    destruct l.
    + simpl in *; bomega.
    + unfold listUpdate in H. simpl in *. inversion H. rewrite <- H2 in H0.
      inversion H0. reflexivity.
  - unfold listUpdate_error in H.
    destruct_one_match_hyp; [|discriminate].
    destruct l.
    + simpl in *; bomega.
    + unfold listUpdate in H. simpl in *. inversion H. rewrite <- H2 in H0.
      eapply IHi with (l := l).
      2: eassumption.
      unfold listUpdate_error.
      destr (Nat.ltb i (length l)); [reflexivity|bomega].
Qed.

Lemma nth_error_firstn: forall E i (l: list E) j,
  j < i ->
  nth_error (firstn i l) j = nth_error l j.
Proof.
  induction i; intros.
  - bomega.
  - simpl. destruct l; [reflexivity|].
    destruct j; [reflexivity|].
    simpl.
    apply IHi.
    bomega.
Qed.

Lemma nth_error_skipn: forall E i j (l: list E),
  i <= j ->
  nth_error (skipn i l) (j - i) = nth_error l j.
Proof.
  induction i; intros.
  - replace (j - 0) with j by bomega. reflexivity.
  - simpl. destruct l.
    * destruct j; simpl; [reflexivity|].
      destruct (j - i); reflexivity.
    * simpl. destruct j; [bomega|].
      replace (S j - S i) with (j - i) by bomega.
      rewrite IHi by bomega.
      reflexivity.
Qed.

Lemma nth_error_listUpdate_error_diff: forall E l l' i j (e: E),
  listUpdate_error l i e = Some l' ->
  j <> i ->
  nth_error l' j = nth_error l j.
Proof.
  intros. unfold listUpdate_error in H.
  destruct_one_match_hyp; [|discriminate].
  assert (j < i \/ i < j < length l \/ length l <= j) as C by bomega.
  destruct C as [C|[C|C]].
  - inversion H. clear H. subst l'. unfold listUpdate.
    rewrite nth_error_app1.
    + apply nth_error_firstn. assumption.
    + pose proof (@firstn_length_le _ l i). bomega.
  - inversion H. subst l'. unfold listUpdate.
    pose proof (firstn_le_length i l).
    rewrite nth_error_app2 by bomega.
    rewrite nth_error_app2 by (simpl; bomega).
    rewrite firstn_length_le by bomega.
    change (length [e]) with 1.
    replace (j - i -1) with (j - (S i)) by bomega.
    apply nth_error_skipn.
    bomega.
  - inversion H.
    pose proof (nth_error_None l j) as P.
    destruct P as [_ P]. rewrite P by assumption.
    apply nth_error_None.
    rewrite listUpdate_length; assumption.
Qed.

End List.

End Datatypes.

End coqutil.

End coqutil_DOT_Datatypes_DOT_List.

Module coqutil_DOT_Datatypes_DOT_PropSet.
Module coqutil.
Module Datatypes.
Module PropSet.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import Coq.Lists.List. Import ListNotations.

Definition set(A: Type) := A -> Prop.

Definition elem_of{K: Type}(k: K)(ks: K -> Prop): Prop := ks k.

Notation "x '\in' s" := (elem_of x s) (at level 70, no associativity).

Section PropSet.
  Context {E: Type}.

  (* basic definitions (which require knowing that set E = E -> Prop *)
  Definition empty_set: set E := fun _ => False.
  Definition singleton_set: E -> set E := eq.
  Definition union: set E -> set E -> set E :=
    fun s1 s2 x => x \in s1 \/ x \in s2.
  Definition intersect: set E -> set E -> set E :=
    fun s1 s2 x => x \in s1 /\ x \in s2.
  Definition diff: set E -> set E -> set E :=
    fun s1 s2 x => x \in s1 /\ ~ x \in s2.
  Definition of_list(l: list E): set E := fun e => List.In e l.

  (* derived definitions (based on basic definitions, without knowing that set E = E -> Prop) *)
  Definition add(s: set E)(e: E) := union (singleton_set e) s.
  Definition remove(s: set E)(e: E) := diff s (singleton_set e).
  Definition subset(s1 s2: set E) := forall x, x \in s1 -> x \in s2.
  Definition sameset(s1 s2: set E) := subset s1 s2 /\ subset s2 s1.
  Definition disjoint(s1 s2: set E) := forall x, (~ x \in s1) \/ (~ x \in s2).
  Definition of_option(o: option E) := match o with
                                       | Some e => singleton_set e
                                       | None => empty_set
                                       end.

End PropSet.

Hint Unfold
     elem_of
     empty_set
     singleton_set
     union
     intersect
     diff
     of_list
  : unf_basic_set_defs.

Hint Unfold
     add
     remove
     subset
     sameset
     disjoint
     of_option
  : unf_derived_set_defs.

Section PropSetLemmas.
  Context {E: Type}.

  Lemma of_list_cons: forall (e: E) (l: list E),
      sameset (of_list (e :: l)) (add (of_list l) e).
  Proof.
    intros. repeat autounfold with unf_derived_set_defs. simpl. auto.
  Qed.

  Lemma of_list_app: forall (l1 l2: list E),
      sameset (of_list (l1 ++ l2)) (union (of_list l1) (of_list l2)).
  Proof.
    induction l1; repeat autounfold with unf_basic_set_defs unf_derived_set_defs in *;
      intros; simpl; [intuition idtac|].
    setoid_rewrite in_app_iff in IHl1.
    setoid_rewrite in_app_iff.
    intuition idtac.
  Qed.

  Lemma disjoint_diff_l: forall (A B C: set E),
      disjoint A C ->
      disjoint (diff A B) C.
  Proof.
    intros. unfold set, disjoint, diff in *. firstorder idtac.
  Qed.

  Lemma disjoint_diff_r: forall (A B C: set E),
      disjoint C A ->
      disjoint C (diff A B).
  Proof.
    intros. unfold set, disjoint, diff in *. firstorder idtac.
  Qed.

End PropSetLemmas.
Import Coq.Program.Tactics.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.Tactics.

Ltac set_solver_generic E :=
  repeat (so fun hyporgoal => match hyporgoal with
  | context [of_list (?l1 ++ ?l2)] => unique pose proof (of_list_app l1 l2)
  | context [of_list (?h :: ?t)] => unique pose proof (of_list_cons h t)
  end);
  repeat autounfold with unf_basic_set_defs unf_derived_set_defs in *;
  unfold elem_of in *;
  destruct_products;
  intros;
  specialize_with E;
  intuition (subst *; auto).

Goal forall T (l1 l2: list T) (e: T),
    subset (of_list (l2 ++ l1)) (union (of_list (e :: l1)) (of_list l2)).
Proof. intros. set_solver_generic T. Qed.

End PropSet.

End Datatypes.

End coqutil.

End coqutil_DOT_Datatypes_DOT_PropSet.

Module coqutil_DOT_Map_DOT_Interface.
Module coqutil.
Module Map.
Module Interface.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_PropSet.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import coqutil_DOT_sanity.coqutil.sanity.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.HList.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.PropSet.

Module map.
  Class map {key value} := mk {
    rep : Type;

    (* fundamental operation, all others are axiomatized in terms of this one *)
    get: rep -> key -> option value;

    empty : rep;
    put : rep -> key -> value -> rep;
    remove : rep -> key -> rep;
    putmany : rep -> rep -> rep;
  }.
  Arguments map : clear implicits.
  Global Coercion rep : map >-> Sortclass.

  Class ok {key value : Type} {map : map key value}: Prop := {
    map_ext : forall m1 m2, (forall k, get m1 k = get m2 k) -> m1 = m2;
    get_empty : forall k, get empty k = None;
    get_put_same : forall m k v, get (put m k v) k = Some v;
    get_put_diff : forall m k v k', k <> k' -> get (put m k' v) k = get m k;
    get_remove_same : forall m k, get (remove m k) k = None;
    get_remove_diff : forall m k k', k <> k' -> get (remove m k') k = get m k;
    get_putmany_left : forall m1 m2 k, get m2 k = None -> get (putmany m1 m2) k = get m1 k;
    get_putmany_right : forall m1 m2 k v, get m2 k = Some v -> get (putmany m1 m2) k = Some v;
  }.
  Arguments ok {_ _} _.

  Section WithMap.
    Context {key value : Type} {map : map key value} {map_ok : ok map}.

    Definition extends (m1 m2 : map) := forall x w, get m2 x = Some w -> get m1 x = Some w.
    Definition agree_on (P : set key) m1 m2 := forall k, elem_of k P -> get m1 k = get m2 k.
    Definition only_differ(m1: map)(ks: set key)(s2: map) :=
      forall x, elem_of x ks \/ get m1 x = get s2 x.
    Definition undef_on m P := agree_on P m empty.
    Definition disjoint (a b : map) :=
      forall k v1 v2, get a k = Some v1 -> get b k = Some v2 -> False.
    Definition sub_domain(m1 m2: map): Prop :=
      forall k v1, map.get m1 k = Some v1 -> exists v2, map.get m2 k = Some v2.
    Definition same_domain(m1 m2: map): Prop := sub_domain m1 m2 /\ sub_domain m2 m1.
    Definition split m m1 m2 := m = (putmany m1 m2) /\ disjoint m1 m2.

    Definition getmany_of_list (m : map) (keys : list key) : option (list value) :=
      List.option_all (List.map (get m) keys).

    Fixpoint putmany_of_list (l : list (key*value)) (init : rep) {struct l} : map :=
      match l with
      | nil => init
      | cons (k,v) l =>
        putmany_of_list l (put init k v)
      end.
    Fixpoint of_list (l : list (key * value)) : rep :=
      match l with
      | nil => map.empty
      | cons (k,v) l => put (of_list l) k v
      end.

    Fixpoint putmany_of_list_zip (keys : list key) (values : list value) (init : rep) {struct keys} : option map :=
      match keys, values with
      | nil, nil => Some init
      | cons k keys, cons v values =>
        putmany_of_list_zip keys values (put init k v)
      | _, _ => None
      end.
    Definition of_list_zip keys values := putmany_of_list_zip keys values empty.

    Import PrimitivePair.

    Definition getmany_of_tuple(m: map){sz: nat}(keys: tuple key sz): option (tuple value sz) :=
      tuple.option_all (tuple.map (get m) keys).

    Fixpoint putmany_of_tuple {sz : nat} : tuple key sz -> tuple value sz -> map -> map :=
      match sz with
      | O => fun keys values init => init
      | S sz' => fun '(pair.mk k ks) '(pair.mk v vs) init =>
                   put (putmany_of_tuple ks vs init) k v
      end.
    Definition of_tuple {sz : nat} (keys: tuple key sz) (values: tuple value sz) :=
      putmany_of_tuple keys values empty.
  End WithMap.
End map. Local Notation map := map.map.
Global Coercion map.rep : map >-> Sortclass.

End Interface.

End Map.

End coqutil.

End coqutil_DOT_Map_DOT_Interface.

Module coqutil_DOT_Z_DOT_div_mod_to_equations.
Module coqutil.
Module Z.
Module div_mod_to_equations.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_PropSet.
Import coqutil_DOT_Map_DOT_Interface.
Import coqutil_DOT_Map_DOT_Interface.coqutil.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Map_DOT_Interface.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.

(* This will hopefully eventually become a part of coq COQBUG(8062) *)

(** These tactic use the complete specification of [Z.div] and
    [Z.modulo] to remove these functions from the goal without losing
    information. The [Z.euclidean_division_equations_cleanup] tactic
    removes needless hypotheses, which makes tactics like [nia] run
    faster. *)

Module Z.
  Lemma mod_0_r_ext x y : y = 0 -> x mod y = 0.
  Proof. intro; subst; destruct x; reflexivity. Qed.
  Lemma div_0_r_ext x y : y = 0 -> x / y = 0.
  Proof. intro; subst; destruct x; reflexivity. Qed.

  Ltac div_mod_to_equations_generalize x y :=
    pose proof (Z.div_mod x y);
    pose proof (Z.mod_pos_bound x y);
    pose proof (Z.mod_neg_bound x y);
    pose proof (div_0_r_ext x y);
    pose proof (mod_0_r_ext x y);
    let q := fresh "q" in
    let r := fresh "r" in
    set (q := x / y) in *;
    set (r := x mod y) in *;
    clearbody q r.

  Ltac div_mod_to_equations_step :=
    match goal with
    | [ |- context[?x / ?y] ] => div_mod_to_equations_generalize x y
    | [ |- context[?x mod ?y] ] => div_mod_to_equations_generalize x y
    | [ H : context[?x / ?y] |- _ ] => div_mod_to_equations_generalize x y
    | [ H : context[?x mod ?y] |- _ ] => div_mod_to_equations_generalize x y
    end.
  Ltac div_mod_to_equations' := repeat div_mod_to_equations_step.
  Ltac euclidean_division_equations_cleanup :=
    repeat match goal with
           | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
           | [ H : ?x <> ?x -> _ |- _ ] => clear H
           | [ H : ?x < ?x -> _ |- _ ] => clear H
           | [ H : ?T -> _, H' : ?T |- _ ] => specialize (H H')
           | [ H : ?T -> _, H' : ~?T |- _ ] => clear H
           | [ H : ~?T -> _, H' : ?T |- _ ] => clear H
           | [ H : ?A -> ?x = ?x -> _ |- _ ] => specialize (fun a => H a eq_refl)
           | [ H : ?A -> ?x <> ?x -> _ |- _ ] => clear H
           | [ H : ?A -> ?x < ?x -> _ |- _ ] => clear H
           | [ H : ?A -> ?B -> _, H' : ?B |- _ ] => specialize (fun a => H a H')
           | [ H : ?A -> ?B -> _, H' : ~?B |- _ ] => clear H
           | [ H : ?A -> ~?B -> _, H' : ?B |- _ ] => clear H
           | [ H : 0 < ?x -> _, H' : ?x < 0 |- _ ] => clear H
           | [ H : ?x < 0 -> _, H' : 0 < ?x |- _ ] => clear H
           | [ H : ?A -> 0 < ?x -> _, H' : ?x < 0 |- _ ] => clear H
           | [ H : ?A -> ?x < 0 -> _, H' : 0 < ?x |- _ ] => clear H
           | [ H : 0 <= ?x -> _, H' : ?x < 0 |- _ ] => clear H
           | [ H : ?x <= 0 -> _, H' : 0 < ?x |- _ ] => clear H
           | [ H : ?A -> 0 <= ?x -> _, H' : ?x < 0 |- _ ] => clear H
           | [ H : ?A -> ?x <= 0 -> _, H' : 0 < ?x |- _ ] => clear H
           | [ H : 0 < ?x -> _, H' : ?x <= 0 |- _ ] => clear H
           | [ H : ?x < 0 -> _, H' : 0 <= ?x |- _ ] => clear H
           | [ H : ?A -> 0 < ?x -> _, H' : ?x <= 0 |- _ ] => clear H
           | [ H : ?A -> ?x < 0 -> _, H' : 0 <= ?x |- _ ] => clear H
           | [ H : 0 <= ?x -> _, H' : ?x <= 0 |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x (eq_sym pf)))
           | [ H : ?A -> 0 <= ?x -> _, H' : ?x <= 0 |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl 0 x (eq_sym pf)))
           | [ H : ?x <= 0 -> _, H' : 0 <= ?x |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x pf))
           | [ H : ?A -> ?x <= 0 -> _, H' : 0 <= ?x |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl x 0 pf))
           | [ H : ?x < ?y -> _, H' : ?x = ?y |- _ ] => clear H
           | [ H : ?x < ?y -> _, H' : ?y = ?x |- _ ] => clear H
           | [ H : ?A -> ?x < ?y -> _, H' : ?x = ?y |- _ ] => clear H
           | [ H : ?A -> ?x < ?y -> _, H' : ?y = ?x |- _ ] => clear H
           | [ H : ?x = ?y -> _, H' : ?x < ?y |- _ ] => clear H
           | [ H : ?x = ?y -> _, H' : ?y < ?x |- _ ] => clear H
           | [ H : ?A -> ?x = ?y -> _, H' : ?x < ?y |- _ ] => clear H
           | [ H : ?A -> ?x = ?y -> _, H' : ?y < ?x |- _ ] => clear H
           end.
  Ltac div_mod_to_equations := div_mod_to_equations'; euclidean_division_equations_cleanup.
End Z.

End div_mod_to_equations.

End Z.

End coqutil.

End coqutil_DOT_Z_DOT_div_mod_to_equations.

Module coqutil_DOT_Z_DOT_PushPullMod.
Module coqutil.
Module Z.
Module PushPullMod.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_PropSet.
Import coqutil_DOT_Map_DOT_Interface.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.
Import coqutil_DOT_Map_DOT_Interface.coqutil.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.Z.
Import coqutil_DOT_Map_DOT_Interface.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.

Module Z.

  Ltac push_mod_step :=
    match goal with
    | |- context [ (?op ?a ?b) mod ?m ] =>
      lazymatch a with
      | _ mod m =>
        lazymatch b with
        | _ mod m => fail
        | _ => idtac
        end
      | _ => idtac
      end;
      match op with
      | Z.add => rewrite (Zplus_mod a b m)
      | Z.sub => rewrite (Zminus_mod a b m)
      | Z.mul => rewrite (Zmult_mod a b m)
      end
    end.

  Ltac push_mod := repeat push_mod_step.

  Ltac mod_free t :=
    lazymatch t with
    | Z.modulo ?a ?b => fail "contains" a "mod" b
    | Z.add ?a ?b => mod_free a; mod_free b
    | Z.sub ?a ?b => mod_free a; mod_free b
    | Z.mul ?a ?b => mod_free a; mod_free b
    | _ => idtac
    end.

  Ltac pull_mod_step :=
    match goal with
    | |- context [ (?op (?a mod ?m) (?b mod ?m)) mod ?m ] =>
      mod_free a;
      mod_free b;
      match op with
      | Z.add => rewrite <- (Zplus_mod a b m)
      | Z.sub => rewrite <- (Zminus_mod a b m)
      | Z.mul => rewrite <- (Zmult_mod a b m)
      end
    end.

  Ltac pull_mod := repeat pull_mod_step.

  Ltac unary_to_binary_minus :=
    repeat match goal with
           | |- context [(- ?x)] => rewrite <- (Z.sub_0_l x)
           end.

  Ltac push_pull_mod :=
    unary_to_binary_minus;
    push_mod;
    rewrite? Zmod_mod;
    pull_mod.

  Ltac mod_equality :=
    push_pull_mod;
    solve [repeat (ring || f_equal)].

End Z.

(* Useful for debugging parenthesis around mod:
Notation "[ a ]_ m" := (a mod m) (at level 20, format "[ a ]_ m").
*)

Goal forall v B M lo, (v + B) mod M =
  ((((v + B) mod M - B - lo + B) mod M - B + B) mod M - B + ((lo + B) mod M - B) + B) mod M.
Proof.
  intros.
  Z.mod_equality.
Qed.

End PushPullMod.

End Z.

End coqutil.

End coqutil_DOT_Z_DOT_PushPullMod.

Module coqutil_DOT_Z_DOT_bitblast.
Module coqutil.
Module Z.
Module bitblast.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_PropSet.
Import coqutil_DOT_Map_DOT_Interface.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.
Import coqutil_DOT_Z_DOT_PushPullMod.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.
Import coqutil_DOT_Map_DOT_Interface.coqutil.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.Z.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.Z.
Import coqutil_DOT_Map_DOT_Interface.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import Coq.ZArith.ZArith.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.Lia.
Import Coq.btauto.Btauto.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Module Z.

  Lemma testbit_minus1 i (H:0<=i) :
    Z.testbit (-1) i = true.
  Proof.
    destruct i; try blia; exact eq_refl.
  Qed.

  Lemma testbit_mod_pow2 a n i (H:0<=n) :
    Z.testbit (a mod 2 ^ n) i = (i <? n) && Z.testbit a i.
  Proof.
    destruct (Z.ltb_spec i n); rewrite
      ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high by auto; auto.
  Qed.

  Lemma testbit_ones n i (H : 0 <= n) :
    Z.testbit (Z.ones n) i = (0 <=? i) && (i <? n).
  Proof.
    destruct (Z.leb_spec 0 i), (Z.ltb_spec i n); cbn;
      rewrite ?Z.testbit_neg_r, ?Z.ones_spec_low, ?Z.ones_spec_high by blia; trivial.
  Qed.

  Lemma testbit_ones_nonneg n i (Hn : 0 <= n) (Hi: 0 <= i) :
    Z.testbit (Z.ones n) i = (i <? n).
  Proof.
    rewrite testbit_ones by blia.
    destruct (Z.leb_spec 0 i); cbn; solve [trivial | blia].
  Qed.

  Lemma shiftl_spec': forall a n m : Z,
      Z.testbit (Z.shiftl a n) m = negb (m <? 0) && Z.testbit a (m - n).
  Proof.
    intros.
    destruct (Z.ltb_spec m 0).
    - rewrite Z.testbit_neg_r; trivial.
    - apply Z.shiftl_spec. assumption.
  Qed.

  Lemma shiftr_spec': forall a n m : Z,
      Z.testbit (Z.shiftr a n) m = negb (m <? 0) && Z.testbit a (m + n).
  Proof.
    intros.
    destruct (Z.ltb_spec m 0).
    - rewrite Z.testbit_neg_r; trivial.
    - apply Z.shiftr_spec. assumption.
  Qed.

  Lemma lnot_spec' : forall a n : Z,
      Z.testbit (Z.lnot a) n = negb (n <? 0) && negb (Z.testbit a n).
  Proof.
    intros.
    destruct (Z.ltb_spec n 0).
    - rewrite Z.testbit_neg_r; trivial.
    - apply Z.lnot_spec. assumption.
  Qed.

  Lemma div_pow2_bits' : forall a n m : Z,
      0 <= n ->
      Z.testbit (a / 2 ^ n) m = negb (m <? 0) && Z.testbit a (m + n).
  Proof.
    intros.
    destruct (Z.ltb_spec m 0).
    - rewrite Z.testbit_neg_r; trivial.
    - apply Z.div_pow2_bits; trivial.
  Qed.

  Lemma bits_opp' : forall a n : Z,
      Z.testbit (- a) n = negb (n <? 0) && negb (Z.testbit (Z.pred a) n).
  Proof.
    intros.
    destruct (Z.ltb_spec n 0).
    - rewrite Z.testbit_neg_r; trivial.
    - apply Z.bits_opp; trivial.
  Qed.

  Lemma testbit_ones_nonneg' : forall n i : Z,
      0 <= n ->
      Z.testbit (Z.ones n) i = negb (i <? 0) && (i <? n).
  Proof.
    intros.
    destruct (Z.ltb_spec i 0).
    - rewrite Z.testbit_neg_r; trivial.
    - apply testbit_ones_nonneg; trivial.
  Qed.

  Lemma testbit_minus1' : forall i : Z,
      Z.testbit (-1) i = negb (i <? 0).
  Proof.
    intros.
    destruct (Z.ltb_spec i 0).
    - rewrite Z.testbit_neg_r; trivial.
    - apply testbit_minus1; trivial.
  Qed.

  Lemma or_to_plus: forall a b,
      Z.land a b = 0 ->
      Z.lor a b = a + b.
  Proof.
    intros.
    rewrite <- Z.lxor_lor by assumption.
    symmetry. apply Z.add_nocarry_lxor. assumption.
  Qed.

  (* 3 kinds of rewrite lemmas to turn (Z.testbit (Z.some_op ...)) into a boolean expression: *)

  (* 1) lemmas without any hypotheses (these are our favorites) *)
  Hint Rewrite
       Z.lor_spec
       Z.lxor_spec
       Z.land_spec
       Z.ldiff_spec
       Z.testbit_0_l
    : z_bitwise_no_hyps.
  Hint Rewrite <-Z.ones_equiv : z_bitwise_no_hyps.

  (* 2) lemmas which have linear arithmetic hypotheses (good if we can solve the hypotheses) *)
  Hint Rewrite
       Z.shiftl_spec_low
       Z.shiftl_spec_alt
       Z.shiftl_spec
       Z.shiftr_spec_aux
       Z.lnot_spec
       Z.shiftr_spec
       Z.ones_spec_high
       Z.ones_spec_low
       Z.div_pow2_bits
       Z.pow2_bits_eqb
       Z.bits_opp
       Z.testbit_mod_pow2
       Z.testbit_ones_nonneg
       Z.testbit_minus1
       using solve [auto with zarith]
    : z_bitwise_with_hyps.

  (* 3) lemmas where we move some or all linear algebra preconditions into the conclusion
     by turning them into a boolean test
     (used as a fallback to make sure the bitblaster knows that it's worth case-destructing) *)
  Hint Rewrite
       Z.shiftl_spec'
       Z.shiftr_spec'
       Z.lnot_spec'
       Z.div_pow2_bits'
       Z.bits_opp'
       Z.testbit_ones_nonneg'
       Z.testbit_minus1'
       using solve [auto with zarith]
    : z_bitwise_forced_no_hyps.

  Ltac rewrite_bitwise :=
    repeat (autorewrite with z_bitwise_no_hyps;
            autorewrite with z_bitwise_with_hyps);
    autorewrite with z_bitwise_forced_no_hyps.

  Ltac destruct_ltbs :=
    repeat match goal with
           | |- context [ ?a <? ?b ] => destruct (Z.ltb_spec a b)
           end.

  Ltac discover_equal_testbit_indices :=
    repeat match goal with
           | |- context [Z.testbit _ ?i] =>
             assert_fails (is_var i);
             let l := fresh "l" in remember i as l
           end;
    repeat match goal with
           | i: Z, j: Z |- _ => replace i with j in * by blia; clear i
           end.

  Ltac bitblast_core :=
    rewrite_bitwise;
    discover_equal_testbit_indices;
    destruct_ltbs;
    try (exfalso; blia);
    try btauto.

  (* Note: The Coq Standard library already provides a tactic called "Z.bitwise", but
     it's less powerful because it does no splitting *)
  Ltac bitblast := eapply Z.bits_inj'; intros ?i ?Hi; bitblast_core.

End Z.

Goal forall v i j k,
    0 <= i ->
    i <= j ->
    j <= k ->
    Z.land (Z.shiftl (v / 2 ^ i) i) (Z.ones j) +
    Z.land (Z.shiftl (v / 2 ^ j) j) (Z.ones k) =
    Z.land (Z.shiftl (v / 2 ^ i) i) (Z.ones k).
Proof.
  intros. rewrite <- Z.or_to_plus; Z.bitblast.
Qed.

End bitblast.

End Z.

End coqutil.

End coqutil_DOT_Z_DOT_bitblast.

Module coqutil_DOT_Word_DOT_Interface.
Module coqutil.
Module Word.
Module Interface.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_PropSet.
Import coqutil_DOT_Map_DOT_Interface.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.
Import coqutil_DOT_Z_DOT_PushPullMod.
Import coqutil_DOT_Z_DOT_bitblast.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.
Import coqutil_DOT_Map_DOT_Interface.coqutil.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.Z.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.Z.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.Z.
Import coqutil_DOT_Map_DOT_Interface.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
(* Specification of two's complement machine words wrt Z *)
Import Coq.ZArith.BinIntDef Coq.ZArith.BinInt.
Local Open Scope Z_scope.

Module word.
  Class word {width : Z} := {
    rep : Type;

    (* defining relations *)
    unsigned : rep -> Z;
    signed : rep -> Z;
    of_Z : Z -> rep;

    (* operations *)
    add : rep -> rep -> rep;
    sub : rep -> rep -> rep;
    opp : rep -> rep;

    or : rep -> rep -> rep;
    and : rep -> rep -> rep;
    xor : rep -> rep -> rep;
    not : rep -> rep;
    ndn : rep -> rep -> rep;

    mul : rep -> rep -> rep;
    mulhss : rep -> rep -> rep;
    mulhsu : rep -> rep -> rep;
    mulhuu : rep -> rep -> rep;

    divu : rep -> rep -> rep;
    divs : rep -> rep -> rep; (* Z.quot *)
    modu : rep -> rep -> rep;
    mods : rep -> rep -> rep; (* Z.rem *)

    slu : rep -> rep -> rep;
    sru : rep -> rep -> rep;
    srs : rep -> rep -> rep;

    eqb : rep -> rep -> bool;
    ltu : rep -> rep -> bool;
    lts : rep -> rep -> bool;

    gtu x y := ltu y x;
    gts x y := lts y x;

    swrap z := (z + 2^(width-1)) mod 2^width - 2^(width-1);

    sextend: Z -> rep -> rep; (* Z is bitwidth of input *)
  }.
  Arguments word : clear implicits.

  Class ok {width} {word : word width}: Prop := {
    wrap z := z mod 2^width;

    width_pos: 0 < width;

    unsigned_of_Z : forall z, unsigned (of_Z z) = wrap z;
    signed_of_Z : forall z, signed (of_Z z) = swrap z;
    of_Z_unsigned : forall x, of_Z (unsigned x) = x;

    unsigned_add : forall x y, unsigned (add x y) = wrap (Z.add (unsigned x) (unsigned y));
    unsigned_sub : forall x y, unsigned (sub x y) = wrap (Z.sub (unsigned x) (unsigned y));
    unsigned_opp : forall x, unsigned (opp x) = wrap (Z.opp (unsigned x));

    unsigned_or : forall x y, unsigned (or x y) = wrap (Z.lor (unsigned x) (unsigned y));
    unsigned_and : forall x y, unsigned (and x y) = wrap (Z.land (unsigned x) (unsigned y));
    unsigned_xor : forall x y, unsigned (xor x y) = wrap (Z.lxor (unsigned x) (unsigned y));
    unsigned_not : forall x, unsigned (not x) = wrap (Z.lnot (unsigned x));
    unsigned_ndn : forall x y, unsigned (ndn x y) = wrap (Z.ldiff (unsigned x) (unsigned y));

    unsigned_mul : forall x y, unsigned (mul x y) = wrap (Z.mul (unsigned x) (unsigned y));
    signed_mulhss : forall x y, signed (mulhss x y) = swrap (Z.mul (signed x) (signed y) / 2^width);
    signed_mulhsu : forall x y, signed (mulhsu x y) = swrap (Z.mul (signed x) (unsigned y) / 2^width);
    unsigned_mulhuu : forall x y, unsigned (mulhuu x y) = wrap (Z.mul (unsigned x) (unsigned y) / 2^width);

    unsigned_divu : forall x y, unsigned y <> 0 -> unsigned (divu x y) = wrap (Z.div (unsigned x) (unsigned y));
    signed_divs : forall x y, signed y <> 0 -> signed x <> -2^(width-1) \/ signed y <> -1 -> signed (divs x y) = swrap (Z.quot (signed x) (signed y));
    unsigned_modu : forall x y, unsigned y <> 0 -> unsigned (modu x y) = wrap (Z.modulo (unsigned x) (unsigned y));
    signed_mods : forall x y, signed y <> 0 -> signed (mods x y) = swrap (Z.rem (signed x) (signed y));

    unsigned_slu : forall x y, Z.lt (unsigned y) width -> unsigned (slu x y) = wrap (Z.shiftl (unsigned x) (unsigned y));
    unsigned_sru : forall x y, Z.lt (unsigned y) width -> unsigned (sru x y) = wrap (Z.shiftr (unsigned x) (unsigned y));
    signed_srs : forall x y, Z.lt (unsigned y) width -> signed (srs x y) = swrap (Z.shiftr (signed x) (unsigned y));

    unsigned_eqb : forall x y, eqb x y = Z.eqb (unsigned x) (unsigned y);
    unsigned_ltu : forall x y, ltu x y = Z.ltb (unsigned x) (unsigned y);
    signed_lts : forall x y, lts x y = Z.ltb (signed x) (signed y);
  }.
  Arguments ok {_} _.
End word. Notation word := word.word.
Global Coercion word.rep : word >-> Sortclass.

End Interface.

End Word.

End coqutil.

End coqutil_DOT_Word_DOT_Interface.

Module coqutil_DOT_Word_DOT_Properties.
Module coqutil.
Module Word.
Module Properties.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_PropSet.
Import coqutil_DOT_Map_DOT_Interface.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.
Import coqutil_DOT_Z_DOT_PushPullMod.
Import coqutil_DOT_Z_DOT_bitblast.
Import coqutil_DOT_Word_DOT_Interface.
Import coqutil_DOT_Word_DOT_Interface.coqutil.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.
Import coqutil_DOT_Map_DOT_Interface.coqutil.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.Z.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.Z.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.Z.
Import coqutil_DOT_Map_DOT_Interface.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import Coq.ZArith.ZArith.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.Z.div_mod_to_equations.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.Lia Coq.btauto.Btauto.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.Z.PushPullMod.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.Z.bitblast.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.Interface. Import word.

Local Open Scope Z_scope.

Local Ltac mia := Z.div_mod_to_equations; Lia.nia.

Module word.
  Section WithWord.
    Context {width} {word : word width} {word_ok : word.ok word}.

    (* Create HintDb word_laws discriminated. *) (* DON'T do this, COQBUG(5381) *)
    Hint Rewrite
       unsigned_of_Z signed_of_Z of_Z_unsigned unsigned_add unsigned_sub unsigned_opp unsigned_or unsigned_and unsigned_xor unsigned_not unsigned_ndn unsigned_mul signed_mulhss signed_mulhsu unsigned_mulhuu unsigned_divu signed_divs unsigned_modu signed_mods unsigned_slu unsigned_sru signed_srs unsigned_eqb unsigned_ltu signed_lts
       using trivial
  : word_laws.

    Lemma wrap_unsigned x : (unsigned x) mod (2^width) = unsigned x.
    Proof.
      pose proof unsigned_of_Z (unsigned x) as H.
      rewrite of_Z_unsigned in H. unfold wrap in *. congruence.
    Qed.

    Lemma unsigned_of_Z_0 : word.unsigned (word.of_Z 0) = 0.
    Proof.
      rewrite word.unsigned_of_Z; cbv [wrap]; rewrite Z.mod_small; trivial; [].
      split; try blia.
      epose proof proj1 (Z.pow_gt_1 2 width ltac:(blia)) word.width_pos; blia.
    Qed.

    Lemma unsigned_inj x y (H : unsigned x = unsigned y) : x = y.
    Proof. rewrite <-(of_Z_unsigned x), <-(of_Z_unsigned y). apply f_equal, H. Qed.

    Lemma signed_eq_swrap_unsigned x : signed x = swrap (unsigned x).
    Proof. cbv [wrap]; rewrite <-signed_of_Z, of_Z_unsigned; trivial. Qed.

    Lemma width_nonneg : 0 <= width. pose proof width_pos. blia. Qed.
    Let width_nonneg_context : 0 <= width. apply width_nonneg. Qed.
    Lemma modulus_pos : 0 < 2^width. apply Z.pow_pos_nonneg; firstorder idtac. Qed.
    Let modulus_pos_section_context := modulus_pos.

    Lemma unsigned_range x : 0 <= unsigned x < 2^width.
    Proof. rewrite <-wrap_unsigned. mia. Qed.

    Lemma ring_theory : Ring_theory.ring_theory (of_Z 0) (of_Z 1) add mul sub opp Logic.eq.
    Proof.
     split; intros; apply unsigned_inj; repeat (rewrite ?wrap_unsigned,
         ?unsigned_add, ?unsigned_sub, ?unsigned_opp, ?unsigned_mul, ?unsigned_of_Z,
         ?Z.add_mod_idemp_l, ?Z.add_mod_idemp_r, ?Z.mul_mod_idemp_l, ?Z.mul_mod_idemp_r,
         ?Z.add_0_l, ?(Z.mod_small 1), ?Z.mul_1_l || unfold wrap);
       f_equal; auto with zarith.
    Qed.

    Ltac prove_ring_morph :=
      intros; apply unsigned_inj; repeat ((rewrite ?wrap_unsigned,
         ?unsigned_add, ?unsigned_sub, ?unsigned_opp, ?unsigned_mul, ?unsigned_of_Z,
         ?Z.add_mod_idemp_l, ?Z.add_mod_idemp_r, ?Z.mul_mod_idemp_l, ?Z.mul_mod_idemp_r,
         ?Zdiv.Zminus_mod_idemp_l, ?Zdiv.Zminus_mod_idemp_r,
         ?Z.sub_0_l, ?Z.add_0_l, ?(Z.mod_small 1), ?Z.mul_1_l by auto with zarith) || unfold wrap);
       try solve [f_equal; auto with zarith].
    Lemma ring_morph_add : forall x y : Z, of_Z (x + y) = add (of_Z x) (of_Z y).
    Proof. prove_ring_morph. Qed.
    Lemma ring_morph_sub : forall x y : Z, of_Z (x - y) = sub (of_Z x) (of_Z y).
    Proof. prove_ring_morph. Qed.
    Lemma ring_morph_mul : forall x y : Z, of_Z (x * y) = mul (of_Z x) (of_Z y).
    Proof. prove_ring_morph. Qed.
    Lemma ring_morph_opp : forall x : Z, of_Z (- x) = opp (of_Z x).
    Proof.
      prove_ring_morph.
      rewrite <-Z.sub_0_l; symmetry; rewrite <-Z.sub_0_l, Zdiv.Zminus_mod_idemp_r. auto.
    Qed.
    Lemma ring_morph_eqb : forall x y : Z, Zbool.Zeq_bool x y = true -> of_Z x = of_Z y.
    Proof. intros. f_equal. apply Zbool.Zeq_is_eq_bool. assumption. Qed.
    Lemma ring_morph :
      Ring_theory.ring_morph (of_Z 0) (of_Z 1) add   mul   sub   opp   Logic.eq
                             0        1        Z.add Z.mul Z.sub Z.opp Zbool.Zeq_bool of_Z.
    Proof.
      split; auto using ring_morph_add, ring_morph_sub, ring_morph_mul,
                        ring_morph_opp, ring_morph_eqb.
    Qed.

    Ltac generalize_wrap_unsigned :=
      repeat match goal with
             | x : @word.rep ?a ?b |- _ =>
               rewrite <-(wrap_unsigned x);
               let x' := fresh in
               set (unsigned x) as x' in *; clearbody x'; clear x; rename x' into x
             end.

    Lemma unsigned_mulhuu_nowrap x y : unsigned (mulhuu x y) = Z.mul (unsigned x) (unsigned y) / 2^width.
    Proof. autorewrite with word_laws; unfold wrap; generalize_wrap_unsigned; rewrite Z.mod_small; mia. Qed.
    Lemma unsigned_divu_nowrap x y (H:unsigned y <> 0) : unsigned (divu x y) = Z.div (unsigned x) (unsigned y).
    Proof. autorewrite with word_laws; unfold wrap; generalize_wrap_unsigned; rewrite Z.mod_small; mia. Qed.
    Lemma unsigned_modu_nowrap x y (H:unsigned y <> 0) : unsigned (modu x y) = Z.modulo (unsigned x) (unsigned y).
    Proof. autorewrite with word_laws; unfold wrap; generalize_wrap_unsigned; rewrite Z.mod_small; mia. Qed.

    Ltac bitwise :=
      autorewrite with word_laws;
      unfold wrap;
      generalize_wrap_unsigned;
      Z.bitblast.

    Lemma unsigned_or_nowrap x y : unsigned (or x y) = Z.lor (unsigned x) (unsigned y).
    Proof. bitwise. Qed.
    Lemma unsigned_and_nowrap x y : unsigned (and x y) = Z.land (unsigned x) (unsigned y).
    Proof. bitwise. Qed.
    Lemma unsigned_xor_nowrap x y : unsigned (xor x y) = Z.lxor (unsigned x) (unsigned y).
    Proof. bitwise. Qed.
    Lemma unsigned_ndn_nowrap x y : unsigned (ndn x y) = Z.ldiff (unsigned x) (unsigned y).
    Proof. bitwise. Qed.
    Lemma unsigned_sru_nowrap x y (H:unsigned y < width) : unsigned (sru x y) = Z.shiftr (unsigned x) (unsigned y).
    Proof.
      pose proof unsigned_range y.
      rewrite unsigned_sru by blia.
      unfold wrap.
      rewrite <-(wrap_unsigned x).
      Z.bitblast.
    Qed.

    Lemma testbit_wrap z i : Z.testbit (wrap z) i = ((i <? width) && Z.testbit z i)%bool.
    Proof. cbv [wrap]. Z.rewrite_bitwise; trivial. Qed.

    Lemma eqb_true: forall (a b: word), word.eqb a b = true -> a = b.
    Proof.
      intros.
      rewrite word.unsigned_eqb in H. rewrite Z.eqb_eq in H. apply unsigned_inj in H.
      assumption.
    Qed.

    Lemma eqb_eq: forall (a b: word), a = b -> word.eqb a b = true.
    Proof.
      intros. subst. rewrite unsigned_eqb. apply Z.eqb_refl.
    Qed.

    Lemma eqb_false: forall (a b: word), word.eqb a b = false -> a <> b.
    Proof.
      intros. intro. rewrite eqb_eq in H; congruence.
    Qed.

    Lemma eqb_ne: forall (a b: word), a <> b -> word.eqb a b = false.
    Proof.
      intros. destruct (word.eqb a b) eqn: E; try congruence.
      exfalso. apply H. apply eqb_true in E. assumption.
    Qed.

    Lemma eqb_spec(a b: word): BoolSpec (a = b) (a <> b) (word.eqb a b).
    Proof.
      destruct (eqb a b) eqn: E; constructor.
      - eauto using eqb_true.
      - eauto using eqb_false.
    Qed.

    Lemma eq_or_neq (k1 k2 : word) : k1 = k2 \/ k1 <> k2.
    Proof. destruct (word.eqb k1 k2) eqn:H; [eapply eqb_true in H | eapply eqb_false in H]; auto. Qed.

    Let width_nonzero : 0 < width. apply width_pos. Qed.
    Lemma half_modulus_pos : 0 < 2^(width-1). apply Z.pow_pos_nonneg; auto with zarith. Qed.
    Let half_modulus_pos_section_context := half_modulus_pos.
    Let twice_halfm : 2^(width-1) * 2 = 2^width.
    Proof. rewrite Z.mul_comm, <-Z.pow_succ_r by blia; f_equal; blia. Qed.

    Lemma unsigned_of_Z_1 : word.unsigned (word.of_Z 1) = 1.
    Proof.
      rewrite word.unsigned_of_Z; cbv [wrap]; rewrite Z.mod_small; trivial; []; blia.
    Qed.

    Lemma unsigned_of_Z_minus1 : word.unsigned (word.of_Z (-1)) = Z.ones width.
    Proof.
      rewrite word.unsigned_of_Z; cbv [wrap].
      change (-1) with (Z.opp 1).
      rewrite Z.mod_opp_l_nz; rewrite ?Z.mod_small; try Lia.lia; [].
      rewrite Z.ones_equiv.
      eapply Z.sub_1_r.
    Qed.

    Lemma signed_range x : -2^(width-1) <= signed x < 2^(width-1).
    Proof.
      rewrite signed_eq_swrap_unsigned. cbv [swrap].
      rewrite <-twice_halfm. mia.
    Qed.

    Lemma swrap_inrange z (H : -2^(width-1) <= z < 2^(width-1)) : swrap z = z.
    Proof. cbv [swrap]; rewrite Z.mod_small; blia. Qed.

    Lemma swrap_as_div_mod z : swrap z = z mod 2^(width-1) - 2^(width-1) * (z / (2^(width - 1)) mod 2).
    Proof.
      symmetry; cbv [swrap wrap].
      replace (2^width) with ((2 ^ (width - 1) * 2))
        by (rewrite Z.mul_comm, <-Z.pow_succ_r by blia; f_equal; blia).
      replace (z + 2^(width-1)) with (z + 1*2^(width-1)) by blia.
      rewrite Z.rem_mul_r, ?Z.div_add, ?Z.mod_add, (Z.add_mod _ 1 2), Zdiv.Zmod_odd by blia.
      destruct (Z.odd _); cbn; blia.
    Qed.

    Lemma pow2_width_minus1: 2 ^ width = 2 * 2 ^ (width - 1).
    Proof. rewrite <-Z.pow_succ_r, Z.sub_1_r, Z.succ_pred; blia. Qed.

    Ltac prove_signed_op :=
      rewrite !signed_eq_swrap_unsigned;
      autorewrite with word_laws;
      cbv [wrap swrap];
      rewrite pow2_width_minus1;
      Z.mod_equality.

    Lemma signed_add x y : signed (add x y) = swrap (Z.add (signed x) (signed y)).
    Proof. prove_signed_op. Qed.

    Lemma signed_sub x y : signed (sub x y) = swrap (Z.sub (signed x) (signed y)).
    Proof. prove_signed_op. Qed.

    Lemma signed_opp x : signed (opp x) = swrap (Z.opp (signed x)).
    Proof. prove_signed_op. Qed.

    Lemma signed_mul x y : signed (mul x y) = swrap (Z.mul (signed x) (signed y)).
    Proof. prove_signed_op. Qed.

    Lemma testbit_swrap z i : Z.testbit (swrap z) i
                              = if i <? width
                                then Z.testbit (wrap z) i
                                else Z.testbit (wrap z) (width -1).
    Proof.
      destruct (ZArith_dec.Z_lt_le_dec i 0).
      { destruct (Z.ltb_spec i width); rewrite ?Z.testbit_neg_r by blia; trivial. }
      rewrite swrap_as_div_mod. cbv [wrap].
      rewrite <-Z.testbit_spec' by blia.
      rewrite <-Z.add_opp_r.
      rewrite Z.add_nocarry_lxor; cycle 1.
      { destruct (Z.testbit z (width - 1)) eqn:Hw1; cbn [Z.b2z];
          rewrite ?Z.mul_1_r, ?Z.mul_0_r, ?Z.opp_0, ?Z.add_0_r, ?Z.land_0_r;
          [|solve[trivial]].
        Z.bitblast. }
      autorewrite with z_bitwise_no_hyps z_bitwise_with_hyps;
      destruct (Z.testbit z (width - 1)) eqn:Hw1; cbn [Z.b2z];
        rewrite ?Z.mul_1_r, ?Z.mul_0_r, ?Z.opp_0, ?Z.add_0_r, ?Z.land_0_r;
        autorewrite with z_bitwise_no_hyps z_bitwise_with_hyps; cbn [Z.pred];
        destruct (Z.ltb_spec i (width-1)), (Z.ltb_spec i width) ,(Z.ltb_spec (width-1) width) ; cbn; blia || btauto || trivial.
      { assert (i = width-1) by blia; congruence. }
      { assert (i = width-1) by blia; congruence. }
    Qed.

    Lemma testbit_signed x i : Z.testbit (signed x) i
                               = if i <? width
                                 then Z.testbit (unsigned x) i
                                 else Z.testbit (unsigned x) (width -1).
    Proof.
      rewrite <-wrap_unsigned, signed_eq_swrap_unsigned.
      eapply testbit_swrap; assumption.
    Qed.

    Hint Rewrite testbit_signed testbit_wrap testbit_swrap
         using solve [auto with zarith] : z_bitwise_signed.

    Ltac sbitwise :=
      eapply Z.bits_inj'; intros ?i ?Hi;
      autorewrite with word_laws z_bitwise_signed z_bitwise_no_hyps z_bitwise_with_hyps;
      repeat match goal with |- context [?a <? ?b] =>
        destruct (Z.ltb_spec a b); trivial; try blia
      end.

    Lemma swrap_signed x : swrap (signed x) = signed x.
    Proof. rewrite signed_eq_swrap_unsigned. sbitwise. Qed.

    Lemma signed_or x y (H : Z.lt (unsigned y) width) : signed (or x y) = swrap (Z.lor (signed x) (signed y)).
    Proof. sbitwise. Qed.
    Lemma signed_and x y : signed (and x y) = swrap (Z.land (signed x) (signed y)).
    Proof. sbitwise. Qed.
    Lemma signed_xor x y : signed (xor x y) = swrap (Z.lxor (signed x) (signed y)).
    Proof. sbitwise. Qed.
    Lemma signed_not x : signed (not x) = swrap (Z.lnot (signed x)).
    Proof. sbitwise. Qed.
    Lemma signed_ndn x y : signed (ndn x y) = swrap (Z.ldiff (signed x) (signed y)).
    Proof. sbitwise. Qed.

    Lemma signed_or_nowrap x y (H : Z.lt (unsigned y) width) : signed (or x y) = Z.lor (signed x) (signed y).
    Proof. sbitwise. Qed.
    Lemma signed_and_nowrap x y : signed (and x y) = Z.land (signed x) (signed y).
    Proof. sbitwise. Qed.
    Lemma signed_xor_nowrap x y : signed (xor x y) = Z.lxor (signed x) (signed y).
    Proof. sbitwise. Qed.
    Lemma signed_not_nowrap x : signed (not x) = Z.lnot (signed x).
    Proof. sbitwise. Qed.
    Lemma signed_ndn_nowrap x y : signed (ndn x y) = Z.ldiff (signed x) (signed y).
    Proof. sbitwise. Qed.

    Lemma signed_srs_nowrap x y (H:unsigned y < width) : signed (srs x y) = Z.shiftr (signed x) (unsigned y).
    Proof.
      pose proof unsigned_range y; sbitwise.
      replace (unsigned y) with 0 by blia; rewrite Z.add_0_r; trivial.
    Qed.

    Lemma signed_mulhss_nowrap x y : signed (mulhss x y) = Z.mul (signed x) (signed y) / 2^width.
    Proof. rewrite signed_mulhss. apply swrap_inrange. pose (signed_range x); pose (signed_range y). mia. Qed.
    Lemma signed_mulhsu_nowrap x y : signed (mulhsu x y) = Z.mul (signed x) (unsigned y) / 2^width.
    Proof. rewrite signed_mulhsu. apply swrap_inrange. pose (signed_range x); pose proof (unsigned_range y). mia. Qed.
    Lemma signed_divs_nowrap x y (H:signed y <> 0) (H0:signed x <> -2^(width-1) \/ signed y <> -1) : signed (divs x y) = Z.quot (signed x) (signed y).
    Proof.
      rewrite signed_divs by assumption. apply swrap_inrange.
      rewrite Z.quot_div by assumption. pose proof (signed_range x).
      destruct (Z.sgn_spec (signed x)) as [[? X]|[[? X]|[? X]]];
      destruct (Z.sgn_spec (signed y)) as [[? Y]|[[? Y]|[? Y]]];
      rewrite ?X, ?Y; rewrite ?Z.abs_eq, ?Z.abs_neq by blia; mia.
    Qed.
    Lemma signed_mods_nowrap x y (H:signed y <> 0) : signed (mods x y) = Z.rem (signed x) (signed y).
    Proof.
      rewrite signed_mods by assumption. apply swrap_inrange.
      rewrite Z.rem_mod by assumption.
      pose (signed_range x); pose (signed_range y).
      destruct (Z.sgn_spec (signed x)) as [[? X]|[[? X]|[? X]]];
      destruct (Z.sgn_spec (signed y)) as [[? Y]|[[? Y]|[? Y]]];
      rewrite ?X, ?Y; repeat rewrite ?Z.abs_eq, ?Z.abs_neq by blia; mia.
    Qed.

    Lemma signed_inj x y (H : signed x = signed y) : x = y.
    Proof.
      eapply unsigned_inj, Z.bits_inj'; intros i Hi.
      eapply (f_equal (fun z => Z.testbit z i)) in H.
      rewrite 2testbit_signed in H. rewrite <-(wrap_unsigned x), <-(wrap_unsigned y).
      autorewrite with word_laws z_bitwise_signed z_bitwise_no_hyps z_bitwise_with_hyps.
      destruct (Z.ltb_spec i width); auto.
    Qed.

    Lemma signed_eqb x y : eqb x y = Z.eqb (signed x) (signed y).
    Proof.
      rewrite unsigned_eqb.
      destruct (Z.eqb_spec (unsigned x) (unsigned y)) as [?e|?];
        destruct (Z.eqb_spec (  signed x) (  signed y)) as [?e|?];
        try (apply unsigned_inj in e || apply signed_inj in e); congruence.
    Qed.
  End WithWord.

  Section WordConvenienceKitchenSink.
    Context {width} {word : word width} {word_ok : word.ok word}.
    Lemma word_sub_add_l_same_l x y : word.sub (word.add x y) x = y.
    Proof.
      eapply word.unsigned_inj.
      rewrite <- (wrap_unsigned y), unsigned_sub, unsigned_add;
        cbv [wrap]; rewrite Zdiv.Zminus_mod_idemp_l. f_equal; blia.
    Qed.
    Lemma word_sub_add_l_same_r x y : word.sub (word.add y x) x = y.
    Proof.
      eapply word.unsigned_inj.
      rewrite <- (wrap_unsigned y), unsigned_sub, unsigned_add;
        cbv [wrap]; rewrite Zdiv.Zminus_mod_idemp_l; f_equal; blia.
    Qed.

    Lemma decrement_nonzero_lt x (H : word.unsigned x <> 0) :
      word.unsigned (word.sub x (word.of_Z 1)) < word.unsigned x.
    Proof.
      pose proof word.unsigned_range x; pose proof modulus_pos.
      rewrite word.unsigned_sub, word.unsigned_of_Z_1.
      unfold word.wrap. Z.div_mod_to_equations.
      enough (0 <= q); Lia.nia.
    Qed.

    Lemma if_zero (t:bool) (H : unsigned (if t then of_Z 1 else of_Z 0) = 0) : t = false.
    Proof. destruct t; trivial; []. rewrite unsigned_of_Z_1 in H; inversion H. Qed.
    Lemma if_nonzero (t:bool) (H : unsigned (if t then of_Z 1 else of_Z 0) <> 0) : t = true.
    Proof. destruct t; trivial; []. rewrite unsigned_of_Z_0 in H. case (H eq_refl). Qed.

    Add Ring wring: (@word.ring_theory width word word_ok).

    Lemma add_assoc: forall (x y z: word), word.add x (word.add y z) = word.add (word.add x y) z.
    Proof. intros. ring. Qed.
    Lemma mul_assoc: forall (x y z: word), word.mul x (word.mul y z) = word.mul (word.mul x y) z.
    Proof. intros. ring. Qed.

    Lemma of_Z_inj_mod: forall x y,
        x mod 2 ^ width = y mod 2 ^ width ->
        word.of_Z x = word.of_Z y.
    Proof.
      intros.
      apply word.unsigned_inj.
      rewrite ?word.unsigned_of_Z.
      unfold word.wrap.
      assumption.
    Qed.

    Lemma of_Z_eq_by_moddiff0: forall x y,
        (x - y) mod 2 ^ width = 0 ->
        word.of_Z x = word.of_Z y.
    Proof.
      intros. apply of_Z_inj_mod.
      apply Z.mod_divide in H; cycle 1. {
        pose proof word.width_pos.
        apply Z.pow_nonzero; blia.
      }
      unfold Z.divide in H.
      destruct H as [k H].
      apply Z.sub_move_r in H.
      subst x.
      rewrite <- Zplus_mod_idemp_l.
      rewrite Z_mod_mult.
      rewrite Z.add_0_l.
      reflexivity.
    Qed.

  End WordConvenienceKitchenSink.
End word.
Import coqutil_DOT_Decidable.coqutil.Decidable.

Existing Instance word.eqb_spec.


(* Ring Helpers: *)

Ltac word_cst w :=
  match w with
  | word.of_Z ?x => let b := isZcst x in
                    match b with
                    | true => x
                    | _ => constr:(NotConstant)
                    end
  | _ => constr:(NotConstant)
  end.

Hint Rewrite
  @word.ring_morph_add
  @word.ring_morph_sub
  @word.ring_morph_mul
  @word.ring_morph_opp
  using typeclasses eauto
  : rew_word_morphism.


Section RingDemoAndTest.

  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  (* These test cases show that the above extra options for "Add Ring" are indeed needed:
     Remove any of them and something below will break. *)
  Goal False.
    assert (forall (w1 w2: word), word.add w1 w2 = word.add w2 w1) as A.
    { intros. ring. } clear A.

    assert (forall (z: Z) (w: word),
               word.add w (word.mul (word.of_Z 4)
                                    (word.sub (word.of_Z (1 + z + 1)) (word.of_Z z))) =
               word.add (word.add w (word.of_Z 4)) (word.of_Z 4)) as A.
    { intros. ring. } clear A.

    assert (forall (L : Z) (w : word),
               word.add w (word.of_Z ((L + 2) * 4)) =
               word.add (word.add (word.add w (word.of_Z 4))
                                  (word.mul (word.of_Z 4) (word.of_Z L)))
                        (word.of_Z 4)) as A.
    { intros. ring. } clear A.
  Abort.

  (* This test case illustrates why it's better to use Zbool.Zeq_bool instead of Z.eqb
     when defining word.ring_morph.
     "Add Ring" adds the option "sign get_signZ_th" by default, but get_signZ_th uses
     Zbool.Zeq_bool instead of Z.eqb, so if we use Z.eqb, the sign option fails and is
     ignored, and ring_simplify creates terms like "add x (mul (of_Z (-1)) y)"
     instead of just "sub x y". *)
  Goal False.
    assert (forall (w1 w2 w3: word),
               word.sub (word.add w1 w2) (word.add w2 w3) =
               word.sub w1 w3) as A.
    { intros. ring_simplify (sub (add w1 w2) (add w2 w3)). reflexivity. } clear A.
  Abort.

End RingDemoAndTest.

End Properties.

End Word.

End coqutil.

End coqutil_DOT_Word_DOT_Properties.

Module bedrock2_DOT_Notations.
Module bedrock2.
Module Notations.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_PropSet.
Import coqutil_DOT_Map_DOT_Interface.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.
Import coqutil_DOT_Z_DOT_PushPullMod.
Import coqutil_DOT_Z_DOT_bitblast.
Import coqutil_DOT_Word_DOT_Interface.
Import coqutil_DOT_Word_DOT_Properties.
Import coqutil_DOT_Word_DOT_Properties.coqutil.
Import coqutil_DOT_Word_DOT_Interface.coqutil.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.
Import coqutil_DOT_Map_DOT_Interface.coqutil.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Word_DOT_Properties.coqutil.Word.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.Z.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.Z.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.Z.
Import coqutil_DOT_Map_DOT_Interface.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.subst coqutil_DOT_Macros_DOT_unique.coqutil.Macros.unique.

Notation "' x <- a | y ; f" :=
  (match a with
   | x => f
   | _ => y
   end)
  (right associativity, at level 70, x pattern).

Notation "'bind_ex' x <- a ; f" :=
  (subst! a for a' in exists x, a' x /\ f)
  (only parsing, right associativity, at level 60, f at level 200).
Notation "'bind_ex_Some' x <- a ; f" :=
  (subst! a for a' in exists x, a' = Some x /\ f)
  (only parsing, right associativity, at level 60, f at level 200).
Notation "'bind_eq' x <- a ; f" :=
  (subst! a for a' in forall x, x = a' -> f)
  (only parsing, right associativity, at level 60, f at level 200).

End Notations.

End bedrock2.

End bedrock2_DOT_Notations.

Module coqutil_DOT_dlet.
Module coqutil.
Module dlet.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_PropSet.
Import coqutil_DOT_Map_DOT_Interface.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.
Import coqutil_DOT_Z_DOT_PushPullMod.
Import coqutil_DOT_Z_DOT_bitblast.
Import coqutil_DOT_Word_DOT_Interface.
Import coqutil_DOT_Word_DOT_Properties.
Import bedrock2_DOT_Notations.
Import coqutil_DOT_Word_DOT_Properties.coqutil.
Import coqutil_DOT_Word_DOT_Interface.coqutil.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.
Import coqutil_DOT_Map_DOT_Interface.coqutil.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import bedrock2_DOT_Notations.bedrock2.
Import coqutil_DOT_Word_DOT_Properties.coqutil.Word.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.Z.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.Z.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.Z.
Import coqutil_DOT_Map_DOT_Interface.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Definition dlet {A P} (x : A) (f : forall a : A, P a) : P x
  := let y := x in f y.
Notation "'dlet!' x .. y := v 'in' f" :=
  (dlet v (fun x => .. (fun y => f) .. ))
    (at level 200, x binder, y binder, f at level 200,
     format "'dlet!'  x .. y  :=  v  'in' '//' f").

End dlet.

End coqutil.

End coqutil_DOT_dlet.

Module bedrock2_DOT_Syntax.
Module bedrock2.
Module Syntax.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_PropSet.
Import coqutil_DOT_Map_DOT_Interface.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.
Import coqutil_DOT_Z_DOT_PushPullMod.
Import coqutil_DOT_Z_DOT_bitblast.
Import coqutil_DOT_Word_DOT_Interface.
Import coqutil_DOT_Word_DOT_Properties.
Import bedrock2_DOT_Notations.
Import coqutil_DOT_dlet.
Import coqutil_DOT_Word_DOT_Properties.coqutil.
Import coqutil_DOT_Word_DOT_Interface.coqutil.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.
Import coqutil_DOT_Map_DOT_Interface.coqutil.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_dlet.coqutil.
Import bedrock2_DOT_Notations.bedrock2.
Import coqutil_DOT_Word_DOT_Properties.coqutil.Word.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.Z.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.Z.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.Z.
Import coqutil_DOT_Map_DOT_Interface.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import coqutil_DOT_sanity.coqutil.sanity coqutil_DOT_Macros_DOT_subst.coqutil.Macros.subst coqutil_DOT_Macros_DOT_unique.coqutil.Macros.unique.
Import Coq.Numbers.BinNums.

Module Import bopname.
  Inductive bopname := add | sub | mul | mulhuu | divu | remu | and | or | xor | sru | slu | srs | lts | ltu | eq.
End bopname.
Notation bopname := bopname.bopname.

Class parameters := {
  varname : Type;
  funname : Type;
  actname : Type;
}.

Module access_size.
  Variant access_size := one | two | four | word.
  Scheme Equality for access_size.
End access_size. Notation access_size := access_size.access_size.

Module expr. Section expr.
  Context {p : unique! parameters}.
  Inductive expr  : Type :=
  | literal (v: Z)
  | var (x: varname)
  | load (_ : access_size) (addr:expr)
  | op (op: bopname) (e1 e2: expr).
End expr. End expr. Notation expr := expr.expr.

Module cmd. Section cmd.
  Context {p : unique! parameters}.
  Inductive cmd :=
  | skip
  | set (lhs : varname) (rhs : expr)
  | unset (lhs : varname)
  | store (_ : access_size) (address : expr) (value : expr)
  | cond (condition : expr) (nonzero_branch zero_branch : cmd)
  | seq (s1 s2: cmd)
  | while (test : expr) (body : cmd)
  | call (binds : list varname) (function : funname) (args: list expr)
  | interact (binds : list varname) (action : actname) (args: list expr).
End cmd. End cmd. Notation cmd := cmd.cmd.

End Syntax.

End bedrock2.

End bedrock2_DOT_Syntax.

Module coqutil_DOT_Word_DOT_LittleEndian.
Module coqutil.
Module Word.
Module LittleEndian.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_PropSet.
Import coqutil_DOT_Map_DOT_Interface.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.
Import coqutil_DOT_Z_DOT_PushPullMod.
Import coqutil_DOT_Z_DOT_bitblast.
Import coqutil_DOT_Word_DOT_Interface.
Import coqutil_DOT_Word_DOT_Properties.
Import bedrock2_DOT_Notations.
Import coqutil_DOT_dlet.
Import bedrock2_DOT_Syntax.
Import coqutil_DOT_Word_DOT_Properties.coqutil.
Import coqutil_DOT_Word_DOT_Interface.coqutil.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.
Import coqutil_DOT_Map_DOT_Interface.coqutil.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import bedrock2_DOT_Syntax.bedrock2.
Import coqutil_DOT_dlet.coqutil.
Import bedrock2_DOT_Notations.bedrock2.
Import coqutil_DOT_Word_DOT_Properties.coqutil.Word.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.Z.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.Z.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.Z.
Import coqutil_DOT_Map_DOT_Interface.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import Coq.ZArith.ZArith.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.Lia.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.Interface coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.HList coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.PrimitivePair.
Import coqutil_DOT_Word_DOT_Properties.coqutil.Word.Properties.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.Z.bitblast.
Local Set Universe Polymorphism.

Local Open Scope Z_scope.

Section LittleEndian.
  Context {byte: word 8}.

  Fixpoint combine (n : nat) : forall (bs : tuple byte n), Z :=
    match n with
    | O => fun _ => 0
    | S n => fun bs => Z.lor (word.unsigned (pair._1 bs))
                             (Z.shiftl (combine n (pair._2 bs)) 8)
    end.

  Fixpoint split (n : nat) (w : Z) : tuple byte n :=
    match n with
    | O => tt
    | S n => pair.mk (word.of_Z w) (split n (Z.shiftr w 8))
    end.

  Lemma combine_split {ok : word.ok byte} (n : nat) (z : Z) :
    combine n (split n z) = z mod 2 ^ (Z.of_nat n * 8).
  Proof.
    revert z; induction n.
    - cbn. intros. rewrite Z.mod_1_r. trivial.
    - cbn [split combine PrimitivePair.pair._1 PrimitivePair.pair._2]; intros.
      erewrite IHn; clear IHn.
      rewrite word.unsigned_of_Z, Nat2Z.inj_succ, Z.mul_succ_l by blia.
      unfold word.wrap.
      rewrite <-! Z.land_ones by blia.
      Z.bitblast.
  Qed.

  Lemma split_combine {ok : word.ok byte} (n: nat) bs :
    split n (combine n bs) = bs.
  Proof.
    revert bs; induction n.
    - destruct bs. reflexivity.
    - destruct bs; cbn [split combine PrimitivePair.pair._1 PrimitivePair.pair._2]; intros.
      specialize (IHn _2).
      f_equal.
      { eapply Properties.word.unsigned_inj.
        rewrite word.unsigned_of_Z, <-Properties.word.wrap_unsigned; cbv [word.wrap].
        Z.bitblast; cbn; subst.
        rewrite (Z.testbit_neg_r _ (i-8)) by bomega.
        Z.bitblast_core. }
      { rewrite <-IHn.
        rewrite combine_split.
        f_equal.
        rewrite <-word.wrap_unsigned.
        Z.bitblast; subst; cbn.
        rewrite <-IHn.
        rewrite combine_split.
        Z.bitblast_core. }
  Qed.

End LittleEndian.

Arguments combine: simpl never.
Arguments split: simpl never.

End LittleEndian.

End Word.

End coqutil.

End coqutil_DOT_Word_DOT_LittleEndian.

Module bedrock2_DOT_MetricLogging.
Module bedrock2.
Module MetricLogging.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_PropSet.
Import coqutil_DOT_Map_DOT_Interface.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.
Import coqutil_DOT_Z_DOT_PushPullMod.
Import coqutil_DOT_Z_DOT_bitblast.
Import coqutil_DOT_Word_DOT_Interface.
Import coqutil_DOT_Word_DOT_Properties.
Import bedrock2_DOT_Notations.
Import coqutil_DOT_dlet.
Import bedrock2_DOT_Syntax.
Import coqutil_DOT_Word_DOT_LittleEndian.
Import coqutil_DOT_Word_DOT_LittleEndian.coqutil.
Import coqutil_DOT_Word_DOT_Properties.coqutil.
Import coqutil_DOT_Word_DOT_Interface.coqutil.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.
Import coqutil_DOT_Map_DOT_Interface.coqutil.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Word_DOT_LittleEndian.coqutil.Word.
Import bedrock2_DOT_Syntax.bedrock2.
Import coqutil_DOT_dlet.coqutil.
Import bedrock2_DOT_Notations.bedrock2.
Import coqutil_DOT_Word_DOT_Properties.coqutil.Word.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.Z.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.Z.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.Z.
Import coqutil_DOT_Map_DOT_Interface.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import Coq.ZArith.BinInt.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.Lia.

Section Riscv.

  Open Scope Z_scope.

  Record MetricLog := mkMetricLog {
    instructions: Z;
    stores: Z;
    loads: Z; (* Note that this also includes loads of the PC *)
    jumps: Z;
  }.

  Definition EmptyMetricLog := mkMetricLog 0 0 0 0.

  Definition withInstructions i log := mkMetricLog i (stores log) (loads log) (jumps log).
  Definition withStores s log := mkMetricLog (instructions log) s (loads log) (jumps log).
  Definition withLoads l log := mkMetricLog (instructions log) (stores log) l (jumps log).
  Definition withJumps j log := mkMetricLog (instructions log) (stores log) (loads log) j.

  Definition addMetricInstructions n log := withInstructions (instructions log + n) log.
  Definition addMetricStores n log := withStores (stores log + n) log.
  Definition addMetricLoads n log := withLoads (loads log + n) log.
  Definition addMetricJumps n log := withJumps (jumps log + n) log.

  Definition subMetricInstructions n log := withInstructions (instructions log - n) log.
  Definition subMetricStores n log := withStores (stores log - n) log.
  Definition subMetricLoads n log := withLoads (loads log - n) log.
  Definition subMetricJumps n log := withJumps (jumps log - n) log.

  Definition metricSub(metric: MetricLog -> Z) finalM initialM : Z :=
    Z.sub (metric finalM) (metric initialM).

  Definition metricsOp op : MetricLog -> MetricLog -> MetricLog :=
    fun initialM finalM =>
      mkMetricLog
        (op instructions initialM finalM)
        (op stores initialM finalM)
        (op loads initialM finalM)
        (op jumps initialM finalM).

  Definition metricsSub := metricsOp metricSub.

  Definition metricLeq(metric: MetricLog -> Z) m1 m2: Prop :=
    (metric m1) <= (metric m2).

  Definition metricsLeq(m1: MetricLog)(m2: MetricLog): Prop :=
    metricLeq instructions m1 m2 /\
    metricLeq stores m1 m2 /\
    metricLeq loads m1 m2 /\
    metricLeq jumps m1 m2.

End Riscv.

Bind Scope MetricH_scope with MetricLog.
Delimit Scope MetricH_scope with metricsH.

Infix "<=" := metricsLeq : MetricH_scope.
Infix "-" := metricsSub : MetricH_scope.

Hint Unfold
     withInstructions
     withLoads
     withStores
     withJumps
     addMetricInstructions
     addMetricLoads
     addMetricStores
     addMetricJumps
     subMetricInstructions
     subMetricLoads
     subMetricStores
     subMetricJumps
     metricsOp
     metricSub
     metricsSub
     metricLeq
     metricsLeq
  : unf_metric_log.

Ltac unfold_MetricLog := autounfold with unf_metric_log in *.

Lemma MetricLog_eq: forall m,
    {|
      instructions := instructions m;
      stores := stores m;
      loads := loads m;
      jumps := jumps m;
    |} = m.
Proof.
  destruct m; reflexivity.
Qed.

Ltac fold_MetricLog :=
  rewrite MetricLog_eq in *.

Ltac simpl_MetricLog :=
  cbn [instructions loads stores jumps] in *.

Ltac solve_MetricLog :=
  repeat unfold_MetricLog;
  repeat simpl_MetricLog;
  bomega.

End MetricLogging.

End bedrock2.

End bedrock2_DOT_MetricLogging.

Module coqutil_DOT_Datatypes_DOT_Option.
Module coqutil.
Module Datatypes.
Module Option.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_PropSet.
Import coqutil_DOT_Map_DOT_Interface.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.
Import coqutil_DOT_Z_DOT_PushPullMod.
Import coqutil_DOT_Z_DOT_bitblast.
Import coqutil_DOT_Word_DOT_Interface.
Import coqutil_DOT_Word_DOT_Properties.
Import bedrock2_DOT_Notations.
Import coqutil_DOT_dlet.
Import bedrock2_DOT_Syntax.
Import coqutil_DOT_Word_DOT_LittleEndian.
Import bedrock2_DOT_MetricLogging.
Import coqutil_DOT_Word_DOT_LittleEndian.coqutil.
Import coqutil_DOT_Word_DOT_Properties.coqutil.
Import coqutil_DOT_Word_DOT_Interface.coqutil.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.
Import coqutil_DOT_Map_DOT_Interface.coqutil.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import bedrock2_DOT_MetricLogging.bedrock2.
Import coqutil_DOT_Word_DOT_LittleEndian.coqutil.Word.
Import bedrock2_DOT_Syntax.bedrock2.
Import coqutil_DOT_dlet.coqutil.
Import bedrock2_DOT_Notations.bedrock2.
Import coqutil_DOT_Word_DOT_Properties.coqutil.Word.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.Z.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.Z.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.Z.
Import coqutil_DOT_Map_DOT_Interface.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Scheme Equality for option.
Arguments option_beq {_} _ _ _.

Definition option_relation {A B} R (x : option A) (y : option B) :=
  match x with
  | None    => y = None
  | Some ax => match y with
               | None => False
               | Some ay => R ax ay
               end
  end.

Definition invert_Some {A} (x : option A) : match x with
                                            | Some _ => A
                                            | None => unit
                                            end
  := match x with
     | Some x' => x'
     | None => tt
     end.

Definition invert_Some_not_None {A} (x : option A) {pf : x <> None} : A
  := match x return x <> None -> A with
     | Some v => fun _ => v
     | None => fun pf => False_rect _ (pf eq_refl)
     end pf.

Lemma eq_of_eq_Some {A} (x y : A) (H: Some x = Some y) : x = y.
Proof. congruence. Qed.

Section ProofsOfEquality.
  Definition option_relation_eq {A} (x y : option A) : x = y -> option_relation eq x y.
  Proof. destruct x; intro; subst; simpl; reflexivity. Defined.
  Definition eq_option_relation {A} (x y : option A) : option_relation eq x y -> x = y.
  Proof. destruct x, y; cbn; try solve [ intros [] | apply f_equal | reflexivity | apply eq_sym ]. Defined.

  Local Lemma option_leq_to_eq_to_leq {A x y} v : @eq_option_relation A x y (@option_relation_eq A x y v) = v.
  Proof. destruct x; subst; simpl; reflexivity. Qed.
  Local Lemma option_eq_to_leq_to_eq {A x y} v : @option_relation_eq A x y (@eq_option_relation A x y v) = v.
  Proof. cbv in *. (destruct x; subst; trivial); (destruct y; subst; trivial); destruct v. Qed.

  Lemma UIP_None {A} (p q : @None A = @None A) : p = q.
  Proof. rewrite <-(option_leq_to_eq_to_leq p), <-(option_leq_to_eq_to_leq q); cbn; reflexivity. Qed.
  Lemma invert_eq_Some {A x y} (p : Some x = Some y) : { pf : x = y | @eq_option_relation A (Some x) (Some y) pf = p }.
  Proof. refine (exist _ _ (option_leq_to_eq_to_leq _)). Qed.
End ProofsOfEquality.

Ltac inversion_option :=
  match goal with
  | [ H : None = None |- _ ] => clear H
  | [ H : Some _ = Some _ |- _ ] => apply eq_of_eq_Some in H
  | [ H : None = Some _ |- _ ] => solve [ inversion H ]
  | [ H : Some _ = None |- _ ] => solve [ inversion H ]
  (* dependent elimination *)
  | [ H : None = None |- _ ]
    => assert (eq_refl = H) by apply UIP_None; subst H
  | [ H : Some _ = Some _ |- _ ]
    => let H' := fresh in
       rename H into H';
       destruct (invert_eq_Some H') as [H ?]; subst H'
  end.

End Option.

End Datatypes.

End coqutil.

End coqutil_DOT_Datatypes_DOT_Option.

Module coqutil_DOT_Map_DOT_Properties.
Module coqutil.
Module Map.
Module Properties.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_PropSet.
Import coqutil_DOT_Map_DOT_Interface.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.
Import coqutil_DOT_Z_DOT_PushPullMod.
Import coqutil_DOT_Z_DOT_bitblast.
Import coqutil_DOT_Word_DOT_Interface.
Import coqutil_DOT_Word_DOT_Properties.
Import bedrock2_DOT_Notations.
Import coqutil_DOT_dlet.
Import bedrock2_DOT_Syntax.
Import coqutil_DOT_Word_DOT_LittleEndian.
Import bedrock2_DOT_MetricLogging.
Import coqutil_DOT_Datatypes_DOT_Option.
Import coqutil_DOT_Datatypes_DOT_Option.coqutil.
Import coqutil_DOT_Word_DOT_LittleEndian.coqutil.
Import coqutil_DOT_Word_DOT_Properties.coqutil.
Import coqutil_DOT_Word_DOT_Interface.coqutil.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.
Import coqutil_DOT_Map_DOT_Interface.coqutil.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Datatypes_DOT_Option.coqutil.Datatypes.
Import bedrock2_DOT_MetricLogging.bedrock2.
Import coqutil_DOT_Word_DOT_LittleEndian.coqutil.Word.
Import bedrock2_DOT_Syntax.bedrock2.
Import coqutil_DOT_dlet.coqutil.
Import bedrock2_DOT_Notations.bedrock2.
Import coqutil_DOT_Word_DOT_Properties.coqutil.Word.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.Z.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.Z.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.Z.
Import coqutil_DOT_Map_DOT_Interface.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.autoforward coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.destr coqutil_DOT_Decidable.coqutil.Decidable coqutil_DOT_Map_DOT_Interface.coqutil.Map.Interface. Import map.
Import coqutil_DOT_Datatypes_DOT_Option.coqutil.Datatypes.Option.

Module map.
  Section WithMap.
    Context {key value} {map : map key value} {ok : map.ok map}.
    Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.
    Hint Resolve
         get_empty
         get_remove_same
         get_remove_diff
         get_put_same
         get_put_diff
         get_putmany_left
         get_putmany_right
      : map_spec_hints_separate.

    Ltac prover :=
      intros;
      repeat match goal with
             | |- context[match ?d with _ => _ end] => destr d
             end;
      subst;
      eauto with map_spec_hints_separate.

    Lemma get_remove_dec m x y : get (remove m x) y = if key_eqb x y then None else get m y.
    Proof. prover. Qed.
    Lemma get_put_dec m x y v : get (put m x v) y = if key_eqb x y then Some v else get m y.
    Proof. prover. Qed.
    Lemma get_putmany_dec m1 m2 k : get (putmany m1 m2) k =
      match get m2 k with Some v => Some v | None => get m1 k end.
    Proof. prover. Qed.

    Lemma put_put_same: forall k v1 v2 m, put (put m k v1) k v2 = put m k v2.
    Proof.
      intros. apply map_ext. intros. rewrite get_put_dec. destr (key_eqb k k0).
      - subst k0. rewrite get_put_same. reflexivity.
      - rewrite !get_put_diff; congruence.
    Qed.

    Lemma putmany_spec m1 m2 k :
      (exists v, get m2 k = Some v /\ get (putmany m1 m2) k = Some v) \/
      (get m2 k = None /\ get (putmany m1 m2) k = get m1 k).
    Proof.
      destruct (get m2 k) eqn:?HH; [left | right ].
      { exists v. split; [ reflexivity | ]. erewrite get_putmany_right; eauto. }
      { split; [ reflexivity | ]. rewrite get_putmany_left; eauto. }
    Qed.

    Lemma putmany_comm x y : disjoint x y -> putmany x y = putmany y x.
    Proof.
      cbv [disjoint]; intros; eapply map_ext; intros.
      destruct (get x k) eqn:Hl, (get y k) eqn:Hr;
        repeat ((erewrite get_putmany_left by eauto)
                || (erewrite get_putmany_right by eauto));
        firstorder congruence.
    Qed.

    Lemma putmany_assoc x y z
      : disjoint x y -> disjoint y z -> disjoint x z ->
        putmany x (putmany y z) = putmany (putmany x y) z.
    Proof.
      cbv [disjoint]; intros; eapply map_ext; intros.
      destruct (putmany_spec x (putmany y z) k);
        destruct (putmany_spec (putmany x y) z k);
        destruct (putmany_spec y z k);
        destruct (putmany_spec x y k);
        destruct (get x k) as [?vx|] eqn:?Hx;
        destruct (get y k) as [?vy|] eqn:?Hy;
        destruct (get z k) as [?vz|] eqn:?Hz;
        firstorder congruence.
    Qed.

    Lemma putmany_empty_r x : putmany x empty = x.
    Proof. eapply map_ext; intros; rewrite get_putmany_left; eauto using get_empty. Qed.
    Lemma putmany_empty_l x : putmany empty x = x.
    Proof.
      rewrite (putmany_comm empty x).
      - eapply putmany_empty_r.
      - intros k. pose proof get_empty k. congruence.
    Qed.
    Lemma empty_putmany m1 m2 : putmany m1 m2 = empty <-> (m1 = empty /\ m2 = empty).
    Proof.
      split; [|intros (?&?); subst; eauto using putmany_empty_r]; intros H.
      pose proof get_empty as HH; rewrite <-H in HH.
      split; eapply map_ext; intros k; specialize (HH k);
        destruct (putmany_spec m1 m2 k); firstorder congruence.
    Qed.

    Lemma disjoint_empty_l x : disjoint empty x. intros k **; pose proof get_empty k; congruence. Qed.
    Lemma disjoint_empty_r x : disjoint x empty. intros k **; pose proof get_empty k; congruence. Qed.
    Lemma disjoint_comm m1 m2 : disjoint m1 m2 <-> disjoint m2 m1.
    Proof. cbv [disjoint]. firstorder idtac. Qed.
    Lemma disjoint_putmany_r x y z : disjoint x (putmany y z) <-> (disjoint x y /\ disjoint x z).
    Proof.
      cbv [disjoint]; repeat (split || intros);
        destruct (putmany_spec y z k);
        destruct (get x k) as [?vx|] eqn:?Hx;
        destruct (get y k) as [?vy|] eqn:?Hy;
        destruct (get z k) as [?vz|] eqn:?Hz;
        firstorder congruence.
    Qed.
    Lemma disjoint_putmany_l x y z : disjoint (putmany x y) z <-> (disjoint x z /\ disjoint y z).
    Proof. rewrite disjoint_comm. rewrite disjoint_putmany_r. rewrite 2(disjoint_comm z). reflexivity. Qed.
    Lemma split_comm m m1 m2 : split m m1 m2 <-> split m m2 m1.
    Proof. cbv [split]. pose proof disjoint_comm m1 m2. intuition idtac. all:rewrite putmany_comm; eauto. Qed.

    Lemma split_disjoint_putmany : forall x y, disjoint x y -> split (putmany x y) x y.
    Proof. cbv [split]; intuition eauto. Qed.

    Lemma split_empty_r m1 m2 : split m1 m2 empty <-> m1 = m2.
    Proof. cbv [split]. erewrite putmany_empty_r. intuition eauto using disjoint_empty_r. Qed.
    Lemma split_empty_l m1 m2 : split m1 empty m2 <-> m1 = m2.
    Proof. rewrite split_comm. eapply split_empty_r. Qed.
    Lemma split_empty m1 m2 : split empty m1 m2 <-> (m1 = empty /\ m2 = empty).
    Proof.
      cbv [split].
      unshelve erewrite (_:forall a b, a=b<->b=a); [intuition congruence|].
      rewrite empty_putmany.
      intuition idtac. subst. eapply disjoint_empty_l.
    Qed.

    Lemma get_split k m m1 m2 (H : split m m1 m2) :
      (get m k = get m1 k /\ get m2 k = None) \/ (get m k = get m2 k /\ get m1 k = None).
    Proof.
      destruct H as [?Hm H]; subst m.
      destruct (get m1 k) eqn:?; [ left | right ];
        destruct (get m2 k) eqn:?; [ solve[edestruct H; eauto] | | | ];
        erewrite ?get_putmany_left, ?get_putmany_right by eauto; eauto.
    Qed.

    Lemma split_undef_put: forall m k v,
        get m k = None ->
        split (put m k v) (put empty k v) m.
    Proof.
      intros.
      repeat split.
      - apply map_ext. intros.
        rewrite get_put_dec.
        destr (key_eqb k k0).
        + subst. rewrite get_putmany_left by assumption.
          rewrite get_put_same. reflexivity.
        + rewrite get_putmany_dec.
          destruct (get m k0); [reflexivity|].
          rewrite get_put_diff by congruence.
          rewrite get_empty.
          reflexivity.
      - unfold disjoint.
        intros.
        rewrite get_put_dec in H0.
        destr (key_eqb k k0).
        + subst. congruence.
        + rewrite get_empty in H0. congruence.
    Qed.

    Lemma split_diff: forall {m m1 m2 m3 m4: map},
        map.same_domain m2 m4 ->
        map.split m m1 m2 ->
        map.split m m3 m4 ->
        m1 = m3 /\ m2 = m4.
    Proof.
      intros.
      unfold split, same_domain, disjoint, sub_domain in *.
      destruct H as [S24 S42].
      destruct H0 as [? S12].
      destruct H1 as [? S34].
      subst.
      assert (forall k, get (putmany m1 m2) k = get (putmany m3 m4) k) as G. {
        intro. rewrite H0. reflexivity.
      }
      split;
        apply map.map_ext;
        intro k; specialize (G k); do 2 rewrite get_putmany_dec in G;
        destr (get m1 k);
        destr (get m2 k);
        destr (get m3 k);
        destr (get m4 k);
        repeat match goal with
               | H: _, A: get _ _ = Some _ |- _ => specialize H with (1 := A)
               | H: exists _, _ |- _ => destruct H
               end;
        try contradiction;
        try congruence.
    Qed.

    Lemma split_det: forall {m m' m1 m2: map},
        map.split m  m1 m2 ->
        map.split m' m1 m2 ->
        m = m'.
    Proof.
      unfold map.split.
      intros *. intros [? ?] [? ?].
      subst.
      reflexivity.
    Qed.

    Lemma extends_get: forall {m1 m2} {k: key} {v: value},
        map.get m1 k = Some v ->
        map.extends m2 m1 ->
        map.get m2 k = Some v.
    Proof. unfold map.extends. intros. eauto. Qed.

    Lemma put_extends: forall k v m1 m2,
        extends m2 m1 ->
        extends (put m2 k v) (put m1 k v).
    Proof.
      unfold extends. intros.
      rewrite get_put_dec.
      destr (key_eqb k x).
      + subst. rewrite get_put_same in H0. exact H0.
      + rewrite get_put_diff in H0; try congruence.
        eapply H. assumption.
    Qed.

    Lemma putmany_of_list_zip_extends_exists: forall ks vs m1 m1' m2,
        putmany_of_list_zip ks vs m1 = Some m1' ->
        extends m2 m1 ->
        exists m2', putmany_of_list_zip ks vs m2 = Some m2' /\ extends m2' m1'.
    Proof.
      induction ks; intros.
      - destruct vs; simpl in H; [|discriminate].
        inversion H. subst m1'. exists m2. simpl. auto.
      - simpl in *. destruct vs; try discriminate.
        specialize IHks with (1 := H).
        edestruct IHks as (m2' & IH1 & IH2); cycle 1.
        + rewrite IH1. eexists; split; [reflexivity|assumption].
        + auto using put_extends.
    Qed.

    Lemma putmany_of_list_zip_extends: forall ks vs m1 m1' m2 m2',
        putmany_of_list_zip ks vs m1 = Some m1' ->
        putmany_of_list_zip ks vs m2 = Some m2' ->
        extends m2 m1 ->
        extends m2' m1'.
    Proof.
      induction ks; intros.
      - destruct vs; simpl in *; [|discriminate].
        inversion H. inversion H0. subst. assumption.
      - simpl in *. destruct vs; try discriminate.
        eauto using put_extends.
    Qed.

    Lemma getmany_of_list_extends: forall ks vs m1 m2,
        extends m2 m1 ->
        getmany_of_list m1 ks = Some vs ->
        getmany_of_list m2 ks = Some vs.
    Proof.
      induction ks; intros.
      - inversion H0. subst. reflexivity.
      - cbn in *.
        destruct (get m1 a) eqn: E1; try discriminate.
        destruct (List.option_all (List.map (get m1) ks)) eqn: E2; try discriminate.
        destruct vs as [|v0 vs]; try discriminate.
        inversion H0. subst l v0.
        unfold getmany_of_list in *.
        erewrite IHks by eassumption.
        unfold extends in H. erewrite H by eassumption. reflexivity.
    Qed.

    Lemma getmany_of_list_length: forall ks vs m,
        map.getmany_of_list m ks = Some vs ->
        length ks = length vs.
    Proof.
      induction ks; intros vs m E.
      - inversion E. reflexivity.
      - cbn in E. destruct (map.get m a) eqn: F; try discriminate.
        destruct (List.option_all (List.map (get m) ks)) eqn: G; try discriminate.
        inversion E.
        simpl.
        f_equal.
        eapply IHks.
        eassumption.
    Qed.

    Lemma getmany_of_list_exists_elem: forall m ks k vs,
        List.In k ks ->
        map.getmany_of_list m ks = Some vs ->
        exists v, map.get m k = Some v.
    Proof.
      induction ks; intros.
      - cbv in H. contradiction.
      - destruct H as [A | A].
        + subst a. unfold map.getmany_of_list in H0. simpl in H0.
          destruct (get m k); try discriminate.
          destruct (List.option_all (List.map (get m) ks)); try discriminate.
          inversion H0. eauto.
        + unfold map.getmany_of_list in H0. simpl in H0.
          destruct (get m a); try discriminate.
          destruct (List.option_all (List.map (get m) ks)) eqn: E; try discriminate.
          eauto.
    Qed.

    Lemma getmany_of_list_exists: forall m (P: key -> Prop) (ks: list key),
        List.Forall P ks ->
        (forall k, P k -> exists v, map.get m k = Some v) ->
        exists vs, map.getmany_of_list m ks = Some vs.
    Proof.
      induction ks; intros.
      - exists nil. reflexivity.
      - inversion H. subst. clear H.
        edestruct IHks as [vs IH]; [assumption..|].
        edestruct H0 as [v ?]; [eassumption|].
        exists (cons v vs). cbn. rewrite H. unfold map.getmany_of_list in IH.
        rewrite IH. reflexivity.
    Qed.

    Lemma putmany_of_list_zip_sameLength : forall bs vs st st',
        map.putmany_of_list_zip bs vs st = Some st' ->
        length bs = length vs.
    Proof.
      induction bs, vs; cbn; try discriminate; trivial; [].
      intros; destruct (map.putmany_of_list_zip bs vs st) eqn:?; eauto using f_equal.
    Qed.

    Lemma sameLength_putmany_of_list : forall bs vs st,
        length bs = length vs ->
        exists st', map.putmany_of_list_zip bs vs st = Some st'.
    Proof.
      induction bs, vs; cbn; try discriminate; intros; eauto.
    Qed.

    Lemma putmany_of_list_zip_find_index: forall keys vals (m1 m2: map) k v,
        putmany_of_list_zip keys vals m1 = Some m2 ->
        get m2 k = Some v ->
        (exists n, List.nth_error keys n = Some k /\ List.nth_error vals n = Some v) \/
        (get m1 k = Some v).
    Proof.
      induction keys; intros.
      - simpl in H. destruct vals; try discriminate. replace m2 with m1 in * by congruence. eauto.
      - simpl in H.
        destruct vals; try discriminate. specialize IHkeys with (1 := H) (2 := H0).
        destruct IHkeys as [IH | IH].
        + destruct IH as (n & IH).
          left. exists (S n). simpl. exact IH.
        + rewrite get_put_dec in IH. destr (key_eqb a k).
          * subst. left. exists O. simpl. auto.
          * right. assumption.
    Qed.

    Lemma getmany_of_list_get: forall keys n (m: map) vals k v,
        getmany_of_list m keys = Some vals ->
        List.nth_error keys n = Some k ->
        List.nth_error vals n = Some v ->
        get m k = Some v.
    Proof.
      induction keys; intros.
      - apply List.nth_error_nil_Some in H0. contradiction.
      - unfold getmany_of_list in *. simpl in *.
        destr (get m a); try discriminate.
        destr (List.option_all (List.map (get m) keys)); try discriminate.
        destruct n.
        + simpl in *. destr vals; congruence.
        + simpl in *. destr vals; try discriminate. inversion H. subst. eauto.
    Qed.

    Lemma extends_putmany_of_list_empty: forall argnames argvals (lL lH: map),
        putmany_of_list_zip argnames argvals empty = Some lH ->
        getmany_of_list lL argnames = Some argvals ->
        extends lL lH.
    Proof.
      unfold extends. intros.
      pose proof putmany_of_list_zip_find_index as P.
      specialize P with (1 := H) (2 := H1). destruct P as [P | P]; cycle 1. {
        rewrite get_empty in P. discriminate.
      }
      destruct P as (n & P1 & P2).
      eapply getmany_of_list_get; eassumption.
    Qed.

    Lemma only_differ_putmany : forall (bs : list key) (vs : list value) st st',
        map.putmany_of_list_zip bs vs st = Some st' ->
        map.only_differ st (PropSet.of_list bs) st'.
    Proof.
      induction bs, vs; cbn; try discriminate.
      - inversion 1; subst. cbv; eauto.
      - intros ? ? H x.
        simpl.
        destruct (map.putmany_of_list_zip bs vs st) eqn:Heqo.
        + specialize IHbs with (1 := H). specialize (IHbs x).
          destruct IHbs as [IHbs | IHbs]; unfold PropSet.elem_of in *; simpl; auto.
          rewrite get_put_dec in IHbs.
          destr (key_eqb a x); auto.
        + apply putmany_of_list_zip_sameLength in H.
          apply (sameLength_putmany_of_list _ _ st) in H.
          destruct H. rewrite H in Heqo. discriminate.
    Qed.

    Lemma putmany_of_list_zip_get_oldval: forall keys values (m1 m2: map) k v,
        map.putmany_of_list_zip keys values m1 = Some m2 ->
        ~ List.In k keys ->
        map.get m1 k = Some v ->
        map.get m2 k = Some v.
    Proof.
      induction keys; intros.
      - simpl in H. destruct values; try discriminate.
        replace m2 with m1 in * by congruence. assumption.
      - simpl in H.
        destruct values; try discriminate.
        simpl in H0.
        eapply IHkeys.
        + eassumption.
        + intro C. apply H0. auto.
        + rewrite get_put_dec. destr (key_eqb a k).
          * exfalso. apply H0. auto.
          * assumption.
    Qed.

    Lemma putmany_of_list_zip_get_newval:
      forall (keys : list key) (values : list value) m1 m2 k i v,
        map.putmany_of_list_zip keys values m1 = Some m2 ->
        List.NoDup keys ->
        List.nth_error keys i = Some k ->
        List.nth_error values i = Some v ->
        map.get m2 k = Some v.
    Proof.
      induction keys; intros.
      - simpl in H. destruct values; try discriminate.
        replace m2 with m1 in * by congruence. apply List.nth_error_nil_Some in H1. contradiction.
      - simpl in H.
        destruct values; try discriminate.
        inversion H0. subst. clear H0.
        apply List.nth_error_cons_Some in H1.
        apply List.nth_error_cons_Some in H2.
        destruct H1 as [ [? ?] | [i1 [ ? ? ] ] ];
          destruct H2 as [ [? ?] | [i2 [ ? ? ] ] ].
        + subst.
          eapply putmany_of_list_zip_get_oldval; try eassumption.
          apply map.get_put_same.
        + subst. discriminate.
        + subst. discriminate.
        + subst. replace i2 with i1 in * by congruence. clear i2.
          eauto.
    Qed.

    Lemma put_putmany_commute k v m1 m2 : put (putmany m1 m2) k v = putmany m1 (put m2 k v).
    Proof.
      apply map_ext. intro k'.
      destr (key_eqb k k').
      - subst k'. rewrite get_put_same. erewrite get_putmany_right; [reflexivity|].
        apply get_put_same.
      - rewrite get_put_diff by congruence.
        pose proof (putmany_spec m1 m2 k') as P.
        destruct P as [(v' & G1 & G2) | (G1 & G2)]; rewrite G2.
        + erewrite get_putmany_right; [reflexivity|].
          rewrite get_put_diff by congruence. assumption.
        + rewrite get_putmany_left; [reflexivity|].
          rewrite get_put_diff by congruence. assumption.
    Qed.

    Lemma putmany_of_list_zip_to_putmany_aux:
      forall (ks: list key) (vs: list value)(m m2 r: map),
        putmany_of_list_zip ks vs (putmany m m2) = Some r ->
        exists r', putmany_of_list_zip ks vs m2 = Some r' /\ r = putmany m r'.
    Proof.
      induction ks; intros.
      - destruct vs; try discriminate. simpl in H. inversion H. subst.
        eexists. simpl. eauto.
      - destruct vs as [|v vs]; try discriminate. simpl in *.
        eapply IHks.
        rewrite <- put_putmany_commute.
        assumption.
    Qed.

    Lemma putmany_of_list_zip_to_putmany: forall (ks: list key) (vs: list value) (m r: map),
        map.putmany_of_list_zip ks vs m = Some r ->
        exists r', map.putmany_of_list_zip ks vs map.empty = Some r' /\
                   r = map.putmany m r'.
    Proof.
      intros.
      apply putmany_of_list_zip_to_putmany_aux.
      rewrite putmany_empty_r. assumption.
    Qed.

    Lemma putmany_of_list_zip_empty_find_value: forall keys values (m: map) i k,
        map.putmany_of_list_zip keys values map.empty = Some m ->
        List.nth_error keys i = Some k ->
        exists v, List.nth_error values i = Some v.
    Proof.
      induction keys; intros.
      - apply List.nth_error_nil_Some in H0. contradiction.
      - simpl in *. destruct values; try discriminate.
        destruct i.
        + simpl in *. eexists. reflexivity.
        + simpl in *.
          apply putmany_of_list_zip_sameLength in H.
          pose proof sameLength_putmany_of_list as Q.
          specialize Q with (1 := H). specialize (Q map.empty).
          destruct Q as [m' Q].
          eapply IHkeys. 2: eassumption. exact Q.
    Qed.

    Lemma invert_getmany_of_tuple_Some: forall n ks (vs: HList.tuple value (S n)) m,
        getmany_of_tuple m ks = Some vs ->
        get m (PrimitivePair.pair._1 ks) = Some (PrimitivePair.pair._1 vs) /\
        getmany_of_tuple m (PrimitivePair.pair._2 ks) = Some (PrimitivePair.pair._2 vs).
    Proof.
      intros. destruct ks as [k ks]. destruct vs as [v vs].
      simpl in *.
      unfold getmany_of_tuple, HList.tuple.map, HList.tuple.option_all in H.
      destruct (get m k); [|discriminate].
      change (
          match (getmany_of_tuple m ks) with
          | Some ys => Some {| PrimitivePair.pair._1 := v0; PrimitivePair.pair._2 := ys |}
          | None => None
          end = Some {| PrimitivePair.pair._1 := v; PrimitivePair.pair._2 := vs |}
        ) in H.
      destruct (getmany_of_tuple m ks); [|discriminate].
      inversion H. auto.
    Qed.

    Lemma build_getmany_of_tuple_Some
        (n: nat) (ks : HList.tuple key (S n)) (vs : HList.tuple value (S n)) (m : map)
        (G1: map.get m (PrimitivePair.pair._1 ks) = Some (PrimitivePair.pair._1 vs))
        (G2: map.getmany_of_tuple m (PrimitivePair.pair._2 ks) = Some (PrimitivePair.pair._2 vs)):
        map.getmany_of_tuple m ks = Some vs.
    Proof.
      unfold map.getmany_of_tuple, HList.tuple.option_all, HList.tuple.map.
      match goal with
      | |- match ?e with _ => _ end = _ =>
        replace e with (Some (PrimitivePair.pair._1 vs)) by exact G1
      end.
      match goal with
      | |- match ?e with _ => _ end = _ =>
        replace e with (map.getmany_of_tuple m (PrimitivePair.pair._2 ks)) by reflexivity
      end.
      match goal with
      | |- match ?e with _ => _ end = _ =>
        replace e with (Some (PrimitivePair.pair._2 vs)) by exact G2
      end.
      reflexivity.
    Qed.

    Lemma put_preserves_getmany_of_tuple_success: forall k v n m (ks: HList.tuple key n),
        getmany_of_tuple m ks <> None ->
        getmany_of_tuple (put m k v) ks <> None.
    Proof.
      induction n; intros.
      - destruct ks. cbv. congruence.
      - destruct (getmany_of_tuple m ks) eqn: E; [|exfalso; congruence].
        destruct ks as [k1 ks].
        apply invert_getmany_of_tuple_Some in E.
        simpl in E. destruct E as [E1 E2].
        unfold getmany_of_tuple, HList.tuple.map, HList.tuple.option_all.
        let t := constr:(getmany_of_tuple (put m k v) ks) in
        let t' := eval unfold getmany_of_tuple, HList.tuple.map, HList.tuple.option_all in t in
        assert (t' = t) as F by reflexivity.
        rewrite F; clear F.
        assert (getmany_of_tuple m ks <> None) as G. {
          rewrite E2. congruence.
        }
        specialize IHn with (1 := G). clear G.
        destruct (getmany_of_tuple (put m k v) ks) eqn: E; [|exfalso; congruence].
        destruct (key_eq_dec k k1).
        + subst k1.
          rewrite get_put_same.
          congruence.
        + rewrite get_put_diff by congruence.
          rewrite E1. congruence.
    Qed.

    Lemma get_in_disjoint_putmany (m1 m2: map) (k: key) (v: value)
        (G: map.get m1 k = Some v)
        (D: map.disjoint m1 m2):
        map.get (map.putmany m1 m2) k = Some v.
    Proof.
      pose proof (putmany_spec m1 m2 k) as P.
      destruct P as [(v2 & G2 & G3) | (G2 & G3)].
      - exfalso. unfold disjoint in D. eauto.
      - rewrite G3. assumption.
    Qed.

    Lemma getmany_of_tuple_in_disjoint_putmany
        (n: nat) (m1 m2: map) (ks: HList.tuple key n) (vs: HList.tuple value n)
        (G: map.getmany_of_tuple m1 ks = Some vs)
        (D: map.disjoint m1 m2):
        map.getmany_of_tuple (map.putmany m1 m2) ks = Some vs.
    Proof.
      revert n ks vs G. induction n as [|n]; intros ks vs G.
      - destruct ks. destruct vs. reflexivity.
      - apply invert_getmany_of_tuple_Some in G. destruct G as [G1 G2].
        destruct ks as [k ks]. destruct vs as [v vs]. simpl in *.
        apply build_getmany_of_tuple_Some; simpl.
        + apply get_in_disjoint_putmany; assumption.
        + apply IHn. assumption.
    Qed.

    Lemma putmany_of_tuple_to_putmany_aux
          (m: map) (n: nat) (m2: map) (ks: HList.tuple key n) (vs: HList.tuple value n):
        putmany_of_tuple ks vs (putmany m m2) = putmany m (putmany_of_tuple ks vs m2).
    Proof.
      revert n ks vs m2. induction n; intros ks vs m2.
      - destruct ks. destruct vs. simpl. reflexivity.
      - destruct ks as [k ks]. destruct vs as [v vs]. simpl.
        specialize (IHn ks vs m2). rewrite IHn.
        rewrite put_putmany_commute.
        reflexivity.
    Qed.

    Lemma putmany_of_tuple_to_putmany
          (n: nat) (m: map) (ks: HList.tuple key n) (vs: HList.tuple value n):
        map.putmany_of_tuple ks vs m = map.putmany m (map.putmany_of_tuple ks vs map.empty).
    Proof.
      pose proof (putmany_of_tuple_to_putmany_aux m n empty ks vs) as P.
      rewrite putmany_empty_r in P. exact P.
    Qed.

    Lemma disjoint_putmany_commutes(m1 m2 m3: map)
        (D: map.disjoint m2 m3):
        map.putmany (map.putmany m1 m2) m3 = map.putmany (map.putmany m1 m3) m2.
    Proof.
      unfold disjoint in D.
      apply map_ext. intro k.
      destruct (get m3 k) eqn: E3; destruct (get m2 k) eqn: E2; [ solve [exfalso; eauto] | .. ].
      all: repeat (first [erewrite get_putmany_left by eassumption |
                          erewrite get_putmany_right by eassumption]).
      all: reflexivity.
    Qed.

    Lemma sub_domain_refl(m: map): sub_domain m m.
    Proof. unfold sub_domain. eauto. Qed.

    Lemma same_domain_refl(m: map): same_domain m m.
    Proof. unfold same_domain. eauto using sub_domain_refl. Qed.

    Lemma sub_domain_trans(m1 m2 m3: map)
      (S1: sub_domain m1 m2)
      (S2: sub_domain m2 m3):
      sub_domain m1 m3.
    Proof.
      unfold sub_domain in *. intros k v1 G1.
      specialize S1 with (1 := G1). destruct S1 as [v2 S1].
      specialize S2 with (1 := S1). exact S2.
    Qed.

    Lemma same_domain_trans(m1 m2 m3: map)
      (S1: same_domain m1 m2)
      (S2: same_domain m2 m3):
      same_domain m1 m3.
    Proof.
      unfold same_domain in *. intuition (eauto using sub_domain_trans).
    Qed.

    Lemma same_domain_sym(m1 m2: map)(S: same_domain m1 m2): same_domain m2 m1.
    Proof. unfold same_domain in *. tauto. Qed.

    Lemma sub_domain_put(m1 m2: map)(k: key)(v1 v2: value)
        (S: sub_domain m1 m2):
        sub_domain (put m1 k v1) (put m2 k v2).
    Proof.
      unfold sub_domain in *. intros k' v' G.
      destr (key_eqb k' k).
      - subst k'. rewrite get_put_same in G. inversion_option. subst v'.
        exists v2. apply get_put_same.
      - rewrite get_put_diff in G by assumption.
        specialize S with (1 := G).
        rewrite get_put_diff by assumption.
        exact S.
    Qed.

    Lemma sub_domain_put_l(m1 m2: map)(k: key)(v v1: value)
        (S: sub_domain m1 m2)
        (G: map.get m1 k = Some v):
        sub_domain (put m1 k v1) m2.
    Proof.
      unfold sub_domain in *. intros k' v' G'.
      destr (key_eqb k' k).
      - subst k'. rewrite get_put_same in G'. inversion_option. subst v'.
        eapply S. eassumption.
      - rewrite get_put_diff in G' by assumption.
        eapply S. eassumption.
    Qed.

    Lemma sub_domain_put_r(m1 m2: map)(k: key)(v: value)
        (S: sub_domain m1 m2):
        sub_domain m1 (map.put m2 k v).
    Proof.
      unfold sub_domain in *. intros k' v' G.
      destr (key_eqb k' k).
      - subst k'. exists v. rewrite get_put_same. reflexivity.
      - rewrite get_put_diff by assumption.
        eapply S. eassumption.
    Qed.

    Lemma same_domain_put_l(m1 m2: map)(k: key)(v v1: value)
        (S: same_domain m1 m2)
        (G: map.get m1 k = Some v):
        same_domain (put m1 k v1) m2.
    Proof.
      unfold same_domain in *. intuition (eauto using sub_domain_put_l, sub_domain_put_r).
    Qed.

    Lemma same_domain_put_r(m1 m2: map)(k: key)(v v2: value)
        (S: same_domain m1 m2)
        (G: map.get m2 k = Some v):
        same_domain m1 (put m2 k v2).
    Proof.
      unfold same_domain in *. intuition (eauto using sub_domain_put_l, sub_domain_put_r).
    Qed.

    Lemma sub_domain_putmany_r(m1 m2 m: map)
        (S: sub_domain m1 m2):
        sub_domain m1 (putmany m2 m).
    Proof.
      unfold sub_domain in *. intros k v1 G.
      specialize S with (1 := G). destruct S as [v2 S].
      pose proof (putmany_spec m2 m k) as P.
      destruct P as [(v & G1 & G2) | (G1 & G2)]; rewrite G2; eauto.
    Qed.

    Lemma same_domain_put(m1 m2: map)(k: key)(v1 v2: value)
        (S: same_domain m1 m2):
        same_domain (put m1 k v1) (put m2 k v2).
    Proof.
      unfold same_domain in *. destruct S as [S1 S2]. eauto using sub_domain_put.
    Qed.

    Lemma getmany_of_tuple_to_sub_domain
        (n: nat) (m: map) (ks: HList.tuple key n) (vs: HList.tuple value n)
        (G: map.getmany_of_tuple m ks = Some vs):
        sub_domain (putmany_of_tuple ks vs map.empty) m.
    Proof.
      revert n m ks vs G. induction n; intros m ks vs G k v1 GP.
      - destruct ks. destruct vs. simpl in *. rewrite get_empty in GP. discriminate.
      - apply invert_getmany_of_tuple_Some in G. destruct G as [G1 G2].
        destruct ks as [ki ks]. destruct vs as [vi vs]. simpl in *.
        destr (key_eqb ki k).
        + subst ki. eexists. exact G1.
        + rewrite get_put_diff in GP by congruence.
          specialize IHn with (1 := G2). unfold sub_domain in IHn.
          eapply IHn.
          eassumption.
    Qed.

    Lemma putmany_of_tuple_same_domain
        (n: nat) (m1 m2: map) (ks: HList.tuple key n) (vs1 vs2: HList.tuple value n)
        (S: same_domain m1 m2):
        same_domain (map.putmany_of_tuple ks vs1 m1)
                       (map.putmany_of_tuple ks vs2 m2).
    Proof.
      revert m1 m2 ks vs1 vs2 S. induction n; intros m1 m2 ks vs1 vs2 S.
      - destruct ks. destruct vs1. destruct vs2. simpl. assumption.
      - destruct vs1 as [v1 vs1]. destruct vs2 as [v2 vs2]. destruct ks as [k ks].
        simpl in *.
        specialize IHn with (1 := S).
        apply same_domain_put.
        apply IHn.
    Qed.

    Lemma sub_domain_value_indep
        (n: nat) (m: map) (ks: HList.tuple key n) (vs1 vs2: HList.tuple value n)
        (S: sub_domain (map.putmany_of_tuple ks vs1 map.empty) m):
        sub_domain (map.putmany_of_tuple ks vs2 map.empty) m.
    Proof.
      pose proof (putmany_of_tuple_same_domain
                    n empty empty ks vs1 vs2 (same_domain_refl _)) as P.
      destruct P as [P1 P2].
      eauto using sub_domain_trans.
    Qed.

    Lemma sub_domain_disjoint(m1 m1' m2: map)
        (D: map.disjoint m1' m2)
        (S: sub_domain m1 m1'):
        map.disjoint m1 m2.
    Proof.
      unfold sub_domain, disjoint in *. intros k v1 v2 G1 G2.
      specialize (S _ _ G1). destruct S as [v1' S].
      eauto.
    Qed.

    Lemma putmany_of_tuple_preserves_domain
        (n : nat)(ks : HList.tuple key n) (oldvs vs : HList.tuple value n) (m : map)
        (G: map.getmany_of_tuple m ks = Some oldvs):
        same_domain m (map.putmany_of_tuple ks vs m).
    Proof.
      unfold same_domain. split.
      - rewrite putmany_of_tuple_to_putmany.
        apply sub_domain_putmany_r. apply sub_domain_refl.
      - unfold sub_domain. intros k v GP.
        revert ks oldvs vs k v G GP. induction n; intros ks oldvs vs k0 v0 G GP.
        + destruct ks. destruct vs. simpl in *. eauto.
        + apply invert_getmany_of_tuple_Some in G.
          destruct ks as [k ks]. destruct vs as [v vs]. destruct oldvs as [oldv oldvs].
          simpl in *. destruct G as [G1 G2].
          destr (key_eqb k0 k).
          * subst k0. eexists. exact G1.
          * rewrite get_put_diff in GP by congruence.
            specialize IHn with (1 := G2).
            specialize IHn with (1 := GP).
            exact IHn.
    Qed.

    Lemma same_domain_preserves_undef_on(m m': map)(s: key -> Prop):
      map.undef_on m s ->
      map.same_domain m m' ->
      map.undef_on m' s.
    Proof.
      intros U S. unfold undef_on, same_domain, sub_domain, agree_on in *.
      intros. specialize (U _ H). rewrite get_empty in *.
      destruct S as [S1 S2].
      destruct (get m' k) eqn: E; [exfalso|reflexivity].
      specialize S2 with (1 := E). destruct S2 as [v2 S2]. congruence.
    Qed.

    Lemma get_of_list_In_NoDup l :
      List.NoDup (List.map fst l) ->
      forall k v,
      List.In (k, v) l ->
      map.get (map.of_list l) k = Some v.
    Proof.
      induction l; cbn; intros; try contradiction.
      inversion H; subst; clear H.
      specialize (IHl H4); clear H4.
      destruct a, H0.
      { inversion H; clear H; subst.
        erewrite map.get_put_same; exact eq_refl. }
      erewrite map.get_put_diff; eauto.
      intro eqX; subst; eapply H3, List.in_map_iff.
      eexists; split; cbn; eauto; trivial.
    Qed.

    Lemma all_gets_from_map_of_NoDup_list fs :
      List.NoDup (List.map fst fs) ->
      List.Forall (fun '(k, v) => map.get (map.of_list fs) k = Some v) fs.
    Proof.
      intros.
      eapply List.Forall_forall; intros [] ?.
      eapply get_of_list_In_NoDup; eauto.
    Qed.
  End WithMap.
End map.

End Properties.

End Map.

End coqutil.

End coqutil_DOT_Map_DOT_Properties.

Module bedrock2_DOT_Memory.
Module bedrock2.
Module Memory.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_PropSet.
Import coqutil_DOT_Map_DOT_Interface.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.
Import coqutil_DOT_Z_DOT_PushPullMod.
Import coqutil_DOT_Z_DOT_bitblast.
Import coqutil_DOT_Word_DOT_Interface.
Import coqutil_DOT_Word_DOT_Properties.
Import bedrock2_DOT_Notations.
Import coqutil_DOT_dlet.
Import bedrock2_DOT_Syntax.
Import coqutil_DOT_Word_DOT_LittleEndian.
Import bedrock2_DOT_MetricLogging.
Import coqutil_DOT_Datatypes_DOT_Option.
Import coqutil_DOT_Map_DOT_Properties.
Import coqutil_DOT_Map_DOT_Properties.coqutil.
Import coqutil_DOT_Datatypes_DOT_Option.coqutil.
Import coqutil_DOT_Word_DOT_LittleEndian.coqutil.
Import coqutil_DOT_Word_DOT_Properties.coqutil.
Import coqutil_DOT_Word_DOT_Interface.coqutil.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.
Import coqutil_DOT_Map_DOT_Interface.coqutil.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import coqutil_DOT_Map_DOT_Properties.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_Option.coqutil.Datatypes.
Import bedrock2_DOT_MetricLogging.bedrock2.
Import coqutil_DOT_Word_DOT_LittleEndian.coqutil.Word.
Import bedrock2_DOT_Syntax.bedrock2.
Import coqutil_DOT_dlet.coqutil.
Import bedrock2_DOT_Notations.bedrock2.
Import coqutil_DOT_Word_DOT_Properties.coqutil.Word.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.Z.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.Z.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.Z.
Import coqutil_DOT_Map_DOT_Interface.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import Coq.ZArith.ZArith.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.Lia.
Import coqutil_DOT_sanity.coqutil.sanity.
Import coqutil_DOT_Decidable.coqutil.Decidable.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.PrimitivePair coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.HList coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.List.
Import coqutil_DOT_Map_DOT_Interface.coqutil.Map.Interface coqutil_DOT_Map_DOT_Properties.coqutil.Map.Properties.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.Tactics coqutil_DOT_Datatypes_DOT_Option.coqutil.Datatypes.Option.
Import Coq.ZArith.BinIntDef coqutil_DOT_Word_DOT_Interface.coqutil.Word.Interface coqutil_DOT_Word_DOT_LittleEndian.coqutil.Word.LittleEndian.
Import bedrock2_DOT_Notations.bedrock2.Notations bedrock2_DOT_Syntax.bedrock2.Syntax.

Open Scope Z_scope.

Section Memory.
  Context {byte: word 8} {width: Z} {word: word width} {mem: map.map word byte}.

  Definition footprint(a: word)(sz: nat): tuple word sz :=
    tuple.unfoldn (fun w => word.add w (word.of_Z 1)) sz a.

  Definition load_bytes(sz: nat)(m: mem)(addr: word): option (tuple byte sz) :=
    map.getmany_of_tuple m (footprint addr sz).

  Definition unchecked_store_bytes(sz: nat)(m: mem)(a: word)(bs: tuple byte sz): mem :=
    map.putmany_of_tuple (footprint a sz) bs m.

  Definition store_bytes(sz: nat)(m: mem)(a: word)(v: tuple byte sz): option mem :=
    match load_bytes sz m a with
    | Some _ => Some (unchecked_store_bytes sz m a v)
    | None => None (* some addresses were invalid *)
    end.

  Definition bytes_per sz :=
    match sz with
      | access_size.one => 1 | access_size.two => 2 | access_size.four => 4
      | access_size.word => Z.to_nat (Z.div (Z.add width 7) 8)
    end%nat.

  Definition load_Z(sz: access_size)(m: mem)(a: word): option Z :=
    match load_bytes (bytes_per sz) m a with
    | Some bs => Some (LittleEndian.combine _ bs)
    | None => None
    end.

  Definition store_Z(sz: access_size)(m: mem)(a: word)(v: Z): option mem :=
    store_bytes (bytes_per sz) m a (LittleEndian.split _ v).

  Definition load(sz: access_size)(m: mem)(a: word): option word :=
    match load_Z sz m a with
    | Some v => Some (word.of_Z v)
    | None => None
    end.

  Definition store(sz: access_size)(m: mem)(a: word)(v: word): option mem :=
    store_Z sz m a (word.unsigned v).

  Lemma load_None: forall sz m a,
      8 <= width ->
      map.get m a = None ->
      load sz m a = None.
  Proof.
    intros.
    destruct sz;
      try solve [
            cbv [load load_Z load_bytes map.getmany_of_tuple footprint
                 tuple.option_all tuple.map tuple.unfoldn bytes_per];
            rewrite H0; reflexivity].
    cbv [load load_Z load_bytes map.getmany_of_tuple footprint bytes_per].
    destruct (Z.to_nat ((width + 7) / 8)) eqn: E.
    - exfalso.
      assert (0 < (width + 7) / 8) as A. {
        apply Z.div_str_pos. blia.
      }
      change O with (Z.to_nat 0) in E.
      apply Z2Nat.inj in E; blia.
    - cbv [tuple.option_all tuple.map tuple.unfoldn].
      rewrite H0.
      reflexivity.
  Qed.

  Context {mem_ok: map.ok mem}.
  Context {word_ok: word.ok word}.

  Lemma store_preserves_domain: forall sz m a v m',
      store sz m a v = Some m' ->
      map.same_domain m m'.
  Proof.
    destruct sz;
      cbv [store store_Z store_bytes bytes_per load_bytes unchecked_store_bytes];
      intros;
      (destruct_one_match_hyp; [|discriminate]);
      inversion_option;
      subst;
      eapply map.putmany_of_tuple_preserves_domain;
      eassumption.
  Qed.

End Memory.

End Memory.

End bedrock2.

End bedrock2_DOT_Memory.

Module bedrock2_DOT_Semantics.
Module bedrock2.
Module Semantics.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_PropSet.
Import coqutil_DOT_Map_DOT_Interface.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.
Import coqutil_DOT_Z_DOT_PushPullMod.
Import coqutil_DOT_Z_DOT_bitblast.
Import coqutil_DOT_Word_DOT_Interface.
Import coqutil_DOT_Word_DOT_Properties.
Import bedrock2_DOT_Notations.
Import coqutil_DOT_dlet.
Import bedrock2_DOT_Syntax.
Import coqutil_DOT_Word_DOT_LittleEndian.
Import bedrock2_DOT_MetricLogging.
Import coqutil_DOT_Datatypes_DOT_Option.
Import coqutil_DOT_Map_DOT_Properties.
Import bedrock2_DOT_Memory.
Import coqutil_DOT_Map_DOT_Properties.coqutil.
Import coqutil_DOT_Datatypes_DOT_Option.coqutil.
Import coqutil_DOT_Word_DOT_LittleEndian.coqutil.
Import coqutil_DOT_Word_DOT_Properties.coqutil.
Import coqutil_DOT_Word_DOT_Interface.coqutil.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.
Import coqutil_DOT_Map_DOT_Interface.coqutil.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import bedrock2_DOT_Memory.bedrock2.
Import coqutil_DOT_Map_DOT_Properties.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_Option.coqutil.Datatypes.
Import bedrock2_DOT_MetricLogging.bedrock2.
Import coqutil_DOT_Word_DOT_LittleEndian.coqutil.Word.
Import bedrock2_DOT_Syntax.bedrock2.
Import coqutil_DOT_dlet.coqutil.
Import bedrock2_DOT_Notations.bedrock2.
Import coqutil_DOT_Word_DOT_Properties.coqutil.Word.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.Z.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.Z.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.Z.
Import coqutil_DOT_Map_DOT_Interface.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import coqutil_DOT_sanity.coqutil.sanity coqutil_DOT_Macros_DOT_subst.coqutil.Macros.subst coqutil_DOT_Macros_DOT_unique.coqutil.Macros.unique.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.PrimitivePair coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.HList.
Import coqutil_DOT_Decidable.coqutil.Decidable.
Import bedrock2_DOT_Notations.bedrock2.Notations bedrock2_DOT_Syntax.bedrock2.Syntax coqutil_DOT_Map_DOT_Interface.coqutil.Map.Interface.
Import Coq.ZArith.BinIntDef coqutil_DOT_Word_DOT_Interface.coqutil.Word.Interface coqutil_DOT_Word_DOT_LittleEndian.coqutil.Word.LittleEndian.
Import bedrock2_DOT_MetricLogging.bedrock2.MetricLogging.
Export bedrock2_DOT_Memory.bedrock2.Memory.
Import Coq.Lists.List.

Class parameters := {
  syntax :> Syntax.parameters;
  varname_eqb: varname -> varname -> bool;
  funname_eqb: funname -> funname -> bool;
  actname_eqb: actname -> actname -> bool;

  width : Z;
  word :> Word.Interface.word width;
  byte :> Word.Interface.word 8%Z;

  mem :> map.map word byte;
  locals :> map.map varname word;
  funname_env : forall T: Type, map.map funname T; (* abstract T for better reusability *)

  trace := list ((mem * actname * list word) * (mem * list word));

  ExtSpec :=
    (* Given a trace of what happened so far,
       the given-away memory, an action label and a list of function call arguments, *)
    trace -> mem -> actname -> list word ->
    (* and a postcondition on the received memory and function call results, *)
    (mem -> list word -> Prop) ->
    (* tells if this postcondition will hold *)
    Prop;

  ext_spec: ExtSpec;
}.

Module ext_spec.
  Class ok{p: parameters}: Prop := {
    (* The action name and arguments uniquely determine the footprint of the given-away memory. *)
    unique_mGive_footprint: forall t1 t2 mGive1 mGive2 a args
                                            (post1 post2: mem -> list word -> Prop),
        ext_spec t1 mGive1 a args post1 ->
        ext_spec t2 mGive2 a args post2 ->
        map.same_domain mGive1 mGive2;

    weaken :> forall t mGive act args,
        Morphisms.Proper
          (Morphisms.respectful
             (Morphisms.pointwise_relation Interface.map.rep
               (Morphisms.pointwise_relation (list word) Basics.impl)) Basics.impl)
          (ext_spec t mGive act args);

    intersect: forall t mGive a args
                      (post1 post2: mem -> list word -> Prop),
        ext_spec t mGive a args post1 ->
        ext_spec t mGive a args post2 ->
        ext_spec t mGive a args (fun mReceive resvals =>
                                   post1 mReceive resvals /\ post2 mReceive resvals);
  }.
End ext_spec.
Arguments ext_spec.ok: clear implicits.

Class parameters_ok{p: parameters}: Prop := {
  varname_eqb_spec :> EqDecider varname_eqb;
  funname_eqb_spec :> EqDecider funname_eqb;
  actname_eqb_spec :> EqDecider actname_eqb;
  width_cases : width = 32 \/ width = 64;
  word_ok :> word.ok word;
  byte_ok :> word.ok byte;
  mem_ok :> map.ok mem;
  locals_ok :> map.ok locals;
  funname_env_ok : forall T: Type, map.ok (funname_env T);
  ext_spec_ok :> ext_spec.ok p;
}.
Arguments parameters_ok: clear implicits.

Instance env{p: parameters}: map.map funname (list varname * list varname * cmd) :=
  funname_env _.

Section binops.
  Context {width : Z} {word : Word.Interface.word width}.
  Definition interp_binop (bop : bopname) : word -> word -> word :=
    match bop with
    | bopname.add => word.add
    | bopname.sub => word.sub
    | bopname.mul => word.mul
    | bopname.mulhuu => word.mulhuu
    | bopname.divu => word.divu
    | bopname.remu => word.modu
    | bopname.and => word.and
    | bopname.or => word.or
    | bopname.xor => word.xor
    | bopname.sru => word.sru
    | bopname.slu => word.slu
    | bopname.srs => word.srs
    | bopname.lts => fun a b =>
      if word.lts a b then word.of_Z 1 else word.of_Z 0
    | bopname.ltu => fun a b =>
      if word.ltu a b then word.of_Z 1 else word.of_Z 0
    | bopname.eq => fun a b =>
      if word.eqb a b then word.of_Z 1 else word.of_Z 0
    end.
End binops.

Section semantics.
  Context {pp : unique! parameters}.

  Local Notation metrics := MetricLog.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).
    Fixpoint eval_expr (e : expr) (mc : metrics) : option (word * metrics) :=
      match e with
      | expr.literal v => Some (word.of_Z v, addMetricInstructions 8
                                             (addMetricLoads 8 mc))
      | expr.var x => match map.get l x with
                      | Some v => Some (v, addMetricInstructions 1
                                           (addMetricLoads 2 mc))
                      | None => None
                      end
      | expr.load aSize a =>
          'Some (a', mc') <- eval_expr a mc | None;
          'Some v <- load aSize m a' | None;
          Some (v, addMetricInstructions 1
                   (addMetricLoads 2 mc'))
      | expr.op op e1 e2 =>
          'Some (v1, mc') <- eval_expr e1 mc | None;
          'Some (v2, mc'') <- eval_expr e2 mc' | None;
          Some (interp_binop op v1 v2, addMetricInstructions 2
                                       (addMetricLoads 2 mc''))
      end.

    Fixpoint eval_expr_old (e : expr) : option word :=
      match e with
      | expr.literal v => Some (word.of_Z v)
      | expr.var x => map.get l x
      | expr.load aSize a =>
          'Some a' <- eval_expr_old a | None;
          load aSize m a'
      | expr.op op e1 e2 =>
          'Some v1 <- eval_expr_old e1 | None;
          'Some v2 <- eval_expr_old e2 | None;
          Some (interp_binop op v1 v2)
      end.

    Fixpoint evaluate_call_args_log (arges : list expr) (mc : metrics) :=
      match arges with
      | e :: tl =>
        'Some (v, mc') <- eval_expr e mc | None;
        'Some (args, mc'') <- evaluate_call_args_log tl mc' | None;
        Some (v :: args, mc'')
      | _ => Some (nil, mc)
      end.

  End WithMemAndLocals.
End semantics.

Module exec. Section WithEnv.
  Context {pp : unique! parameters} {e: env}.

  Local Notation metrics := MetricLog.

  Implicit Types post : trace -> mem -> locals -> metrics -> Prop. (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)
  Inductive exec :
    cmd -> trace -> mem -> locals -> metrics ->
    (trace -> mem -> locals -> metrics -> Prop) -> Prop :=
  | skip
    t m l mc post
    (_ : post t m l mc)
    : exec cmd.skip t m l mc post
  | set x e
    t m l mc post
    v mc' (_ : eval_expr m l e mc = Some (v, mc'))
    (_ : post t m (map.put l x v) (addMetricInstructions 1
                                  (addMetricLoads 1 mc')))
    : exec (cmd.set x e) t m l mc post
  | unset x
    t m l mc post
    (_ : post t m (map.remove l x) mc)
    : exec (cmd.unset x) t m l mc post
  | store sz ea ev
    t m l mc post
    a mc' (_ : eval_expr m l ea mc = Some (a, mc'))
    v mc'' (_ : eval_expr m l ev mc' = Some (v, mc''))
    m' (_ : store sz m a v = Some m')
    (_ : post t m' l (addMetricInstructions 1
                     (addMetricLoads 1
                     (addMetricStores 1 mc''))))
    : exec (cmd.store sz ea ev) t m l mc post
  | if_true t m l mc e c1 c2 post
    v mc' (_ : eval_expr m l e mc = Some (v, mc'))
    (_ : word.unsigned v <> 0)
    (_ : exec c1 t m l (addMetricInstructions 2
                       (addMetricLoads 2
                       (addMetricJumps 1 mc'))) post)
    : exec (cmd.cond e c1 c2) t m l mc post
  | if_false e c1 c2
    t m l mc post
    v mc' (_ : eval_expr m l e mc = Some (v, mc'))
    (_ : word.unsigned v = 0)
    (_ : exec c2 t m l (addMetricInstructions 2
                       (addMetricLoads 2
                       (addMetricJumps 1 mc'))) post)
    : exec (cmd.cond e c1 c2) t m l mc post
  | seq c1 c2
    t m l mc post
    mid (_ : exec c1 t m l mc mid)
    (_ : forall t' m' l' mc', mid t' m' l' mc' -> exec c2 t' m' l' mc' post)
    : exec (cmd.seq c1 c2) t m l mc post
  | while_false e c
    t m l mc post
    v mc' (_ : eval_expr m l e mc = Some (v, mc'))
    (_ : word.unsigned v = 0)
    (_ : post t m l (addMetricInstructions 1
                    (addMetricLoads 1
                    (addMetricJumps 1 mc'))))
    : exec (cmd.while e c) t m l mc post
  | while_true e c
      t m l mc post
      v mc' (_ : eval_expr m l e mc = Some (v, mc'))
      (_ : word.unsigned v <> 0)
      mid (_ : exec c t m l mc' mid)
      (_ : forall t' m' l' mc'', mid t' m' l' mc'' ->
                                 exec (cmd.while e c) t' m' l' (addMetricInstructions 2
                                                               (addMetricLoads 2
                                                               (addMetricJumps 1 mc''))) post)
    : exec (cmd.while e c) t m l mc post
  | call binds fname arges
      t m l mc post
      params rets fbody (_ : map.get e fname = Some (params, rets, fbody))
      args mc' (_ : evaluate_call_args_log m l arges mc = Some (args, mc'))
      lf (_ : map.of_list_zip params args = Some lf)
      mid (_ : exec fbody t m lf mc' mid)
      (_ : forall t' m' st1 mc'', mid t' m' st1 mc'' ->
          exists retvs, map.getmany_of_list st1 rets = Some retvs /\
          exists l', map.putmany_of_list_zip binds retvs l = Some l' /\
          post t' m' l' mc'')
    : exec (cmd.call binds fname arges) t m l mc post
  | interact binds action arges
      t m l mc post
      mKeep mGive (_: map.split m mKeep mGive)
      args mc' (_ :  evaluate_call_args_log m l arges mc = Some (args, mc'))
      mid (_ : ext_spec t mGive action args mid)
      (_ : forall mReceive resvals, mid mReceive resvals ->
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          exists m', map.split m' mKeep mReceive /\
                     post (cons ((mGive, action, args), (mReceive, resvals)) t) m' l'
                       (addMetricInstructions 1
                       (addMetricStores 1
                       (addMetricLoads 2 mc'))))
    : exec (cmd.interact binds action arges) t m l mc post
  .
  End WithEnv.
  Arguments exec {_} _.
End exec. Notation exec := exec.exec.

End Semantics.

End bedrock2.

End bedrock2_DOT_Semantics.

Module bedrock2_DOT_WeakestPrecondition.
Module bedrock2.
Module WeakestPrecondition.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_PropSet.
Import coqutil_DOT_Map_DOT_Interface.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.
Import coqutil_DOT_Z_DOT_PushPullMod.
Import coqutil_DOT_Z_DOT_bitblast.
Import coqutil_DOT_Word_DOT_Interface.
Import coqutil_DOT_Word_DOT_Properties.
Import bedrock2_DOT_Notations.
Import coqutil_DOT_dlet.
Import bedrock2_DOT_Syntax.
Import coqutil_DOT_Word_DOT_LittleEndian.
Import bedrock2_DOT_MetricLogging.
Import coqutil_DOT_Datatypes_DOT_Option.
Import coqutil_DOT_Map_DOT_Properties.
Import bedrock2_DOT_Memory.
Import bedrock2_DOT_Semantics.
Import coqutil_DOT_Map_DOT_Properties.coqutil.
Import coqutil_DOT_Datatypes_DOT_Option.coqutil.
Import coqutil_DOT_Word_DOT_LittleEndian.coqutil.
Import coqutil_DOT_Word_DOT_Properties.coqutil.
Import coqutil_DOT_Word_DOT_Interface.coqutil.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.
Import coqutil_DOT_Map_DOT_Interface.coqutil.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import bedrock2_DOT_Semantics.bedrock2.
Import bedrock2_DOT_Memory.bedrock2.
Import coqutil_DOT_Map_DOT_Properties.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_Option.coqutil.Datatypes.
Import bedrock2_DOT_MetricLogging.bedrock2.
Import coqutil_DOT_Word_DOT_LittleEndian.coqutil.Word.
Import bedrock2_DOT_Syntax.bedrock2.
Import coqutil_DOT_dlet.coqutil.
Import bedrock2_DOT_Notations.bedrock2.
Import coqutil_DOT_Word_DOT_Properties.coqutil.Word.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.Z.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.Z.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.Z.
Import coqutil_DOT_Map_DOT_Interface.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.subst coqutil_DOT_Macros_DOT_unique.coqutil.Macros.unique bedrock2_DOT_Notations.bedrock2.Notations coqutil_DOT_Map_DOT_Interface.coqutil.Map.Interface.
Import Coq.ZArith.BinIntDef coqutil_DOT_Word_DOT_Interface.coqutil.Word.Interface.
Import coqutil_DOT_dlet.coqutil.dlet bedrock2_DOT_Syntax.bedrock2.Syntax bedrock2_DOT_Semantics.bedrock2.Semantics.

Section WeakestPrecondition.
  Context {p : unique! Semantics.parameters}.

  Definition literal v (post : word -> Prop) : Prop :=
    dlet! v := word.of_Z v in post v.
  Definition get (l : locals) (x : varname) (post : word -> Prop) : Prop :=
    bind_ex_Some v <- map.get l x; post v.
  Definition load s m a (post : _ -> Prop) : Prop :=
    bind_ex_Some v <- load s m a; post v.
  Definition store sz m a v post :=
    bind_ex_Some m <- store sz m a v; post m.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).
    Definition expr_body rec (e : Syntax.expr) (post : word -> Prop) : Prop :=
      match e with
      | expr.literal v =>
        literal v post
      | expr.var x =>
        get l x post
      | expr.op op e1 e2 =>
        rec e1 (fun v1 =>
        rec e2 (fun v2 =>
        post (interp_binop op v1 v2)))
      | expr.load s e =>
        rec e (fun a =>
        load s m a post)
    end.
    Fixpoint expr e := expr_body expr e.
  End WithMemAndLocals.

  Section WithF.
    Context {A B} (f: A -> (B -> Prop) -> Prop).
    Definition list_map_body rec (xs : list A) (post : list B -> Prop) : Prop :=
      match xs with
      | nil => post nil
      | cons x xs' =>
        f x (fun y =>
        rec xs' (fun ys' =>
        post (cons y ys')))
      end.
    Fixpoint list_map xs := list_map_body list_map xs.
  End WithF.

  Section WithFunctions.
    Context (call : funname -> trace -> mem -> list word -> (trace -> mem -> list word -> Prop) -> Prop).
    Definition dexpr m l e v := expr m l e (eq v).
    Definition dexprs m l es vs := list_map (expr m l) es (eq vs).
    Definition cmd_body (rec:_->_->_->_->_->Prop) (c : cmd) (t : trace) (m : mem) (l : locals)
             (post : trace -> mem -> locals -> Prop) : Prop :=
      (* give value of each pure expression when stating its subproof *)
      match c with
      | cmd.skip => post t m l
      | cmd.set x ev =>
        bind_ex v <- dexpr m l ev;
        dlet! l := map.put l x v in
        post t m l
      | cmd.unset x =>
        dlet! l := map.remove l x in
        post t m l
      | cmd.store sz ea ev =>
        bind_ex a <- dexpr m l ea;
        bind_ex v <- dexpr m l ev;
        store sz m a v (fun m =>
        post t m l)
      | cmd.cond br ct cf =>
        bind_ex v <- dexpr m l br;
        (word.unsigned v <> 0%Z -> rec ct t m l post) /\
        (word.unsigned v = 0%Z -> rec cf t m l post)
      | cmd.seq c1 c2 =>
        rec c1 t m l (fun t m l => rec c2 t m l post)
      | cmd.while e c =>
        exists measure (lt:measure->measure->Prop) (inv:measure->trace->mem->locals->Prop),
        Coq.Init.Wf.well_founded lt /\
        (exists v, inv v t m l) /\
        (forall v t m l, inv v t m l ->
          bind_ex b <- dexpr m l e;
          (word.unsigned b <> 0%Z -> rec c t m l (fun t' m l =>
            exists v', inv v' t' m l /\ lt v' v)) /\
          (word.unsigned b = 0%Z -> post t m l))
      | cmd.call binds fname arges =>
        bind_ex args <- dexprs m l arges;
        call fname t m args (fun t m rets =>
          bind_ex_Some l <- map.putmany_of_list_zip binds rets l;
          post t m l)
      | cmd.interact binds action arges =>
        bind_ex args <- dexprs m l arges;
        exists mKeep mGive, map.split m mKeep mGive /\
        ext_spec t mGive action args (fun mReceive rets =>
          bind_ex_Some l <- map.putmany_of_list_zip binds rets l;
          exists m, map.split m mKeep mReceive /\
          post (cons ((mGive, action, args), (mReceive, rets)) t) m l)
      end.
    Fixpoint cmd c := cmd_body cmd c.
  End WithFunctions.

  Definition func call '(innames, outnames, c) (t : trace) (m : mem) (args : list word) (post : trace -> mem -> list word -> Prop) :=
      bind_ex_Some l <- map.of_list_zip innames args;
      cmd call c t m l (fun t m l =>
        list_map (get l) outnames (fun rets =>
        post t m rets)).

  Definition call_body rec (functions : list (funname * (list varname * list varname * cmd.cmd)))
                (fname : funname) (t : trace) (m : mem) (args : list word)
                (post : trace -> mem -> list word -> Prop) : Prop :=
    match functions with
    | nil => False
    | cons (f, decl) functions =>
      if funname_eqb f fname
      then func (rec functions) decl t m args post
      else rec functions fname t m args post
    end.
  Fixpoint call functions := call_body call functions.

  Definition program funcs main t m l post : Prop := cmd (call funcs) main t m l post.
End WeakestPrecondition.

Ltac unfold1_cmd e :=
  lazymatch e with
    @cmd ?params ?CA ?c ?t ?m ?l ?post =>
    let c := eval hnf in c in
    constr:(@cmd_body params CA (@cmd params CA) c t m l post)
  end.
Ltac unfold1_cmd_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_cmd G in
  change G.

Ltac unfold1_expr e :=
  lazymatch e with
    @expr ?params ?m ?l ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@expr_body params m l (@expr params m l) arg post)
  end.
Ltac unfold1_expr_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_expr G in
  change G.

Ltac unfold1_list_map e :=
  lazymatch e with
    @list_map ?A ?B ?P ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@list_map_body A B P (@list_map A B P) arg post)
  end.
Ltac unfold1_list_map_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_list_map G in
  change G.

Ltac unfold1_call e :=
  lazymatch e with
    @call ?params ?fs ?fname ?t ?m ?l ?post =>
    let fs := eval hnf in fs in
    constr:(@call_body params (@call params) fs fname t m l post)
  end.
Ltac unfold1_call_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_call G in
  change G.

End WeakestPrecondition.

End bedrock2.

End bedrock2_DOT_WeakestPrecondition.

Module bedrock2_DOT_WeakestPreconditionProperties.
Module bedrock2.
Module WeakestPreconditionProperties.
Import coqutil_DOT_Macros_DOT_subst.
Import coqutil_DOT_Macros_DOT_unique.
Import coqutil_DOT_sanity.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.
Import coqutil_DOT_Datatypes_DOT_HList.
Import coqutil_DOT_Tactics_DOT_autoforward.
Import coqutil_DOT_Decidable.
Import coqutil_DOT_Tactics_DOT_destr.
Import coqutil_DOT_Tactics_DOT_forward.
Import coqutil_DOT_Tactics_DOT_Tactics.
Import coqutil_DOT_Z_DOT_Lia.
Import coqutil_DOT_Datatypes_DOT_List.
Import coqutil_DOT_Datatypes_DOT_PropSet.
Import coqutil_DOT_Map_DOT_Interface.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.
Import coqutil_DOT_Z_DOT_PushPullMod.
Import coqutil_DOT_Z_DOT_bitblast.
Import coqutil_DOT_Word_DOT_Interface.
Import coqutil_DOT_Word_DOT_Properties.
Import bedrock2_DOT_Notations.
Import coqutil_DOT_dlet.
Import bedrock2_DOT_Syntax.
Import coqutil_DOT_Word_DOT_LittleEndian.
Import bedrock2_DOT_MetricLogging.
Import coqutil_DOT_Datatypes_DOT_Option.
Import coqutil_DOT_Map_DOT_Properties.
Import bedrock2_DOT_Memory.
Import bedrock2_DOT_Semantics.
Import bedrock2_DOT_WeakestPrecondition.
Import coqutil_DOT_Map_DOT_Properties.coqutil.
Import coqutil_DOT_Datatypes_DOT_Option.coqutil.
Import coqutil_DOT_Word_DOT_LittleEndian.coqutil.
Import coqutil_DOT_Word_DOT_Properties.coqutil.
Import coqutil_DOT_Word_DOT_Interface.coqutil.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.
Import coqutil_DOT_Map_DOT_Interface.coqutil.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.
Import coqutil_DOT_Z_DOT_Lia.coqutil.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.
Import coqutil_DOT_Macros_DOT_subst.coqutil.
Import bedrock2_DOT_WeakestPrecondition.bedrock2.
Import bedrock2_DOT_Semantics.bedrock2.
Import bedrock2_DOT_Memory.bedrock2.
Import coqutil_DOT_Map_DOT_Properties.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_Option.coqutil.Datatypes.
Import bedrock2_DOT_MetricLogging.bedrock2.
Import coqutil_DOT_Word_DOT_LittleEndian.coqutil.Word.
Import bedrock2_DOT_Syntax.bedrock2.
Import coqutil_DOT_dlet.coqutil.
Import bedrock2_DOT_Notations.bedrock2.
Import coqutil_DOT_Word_DOT_Properties.coqutil.Word.
Import coqutil_DOT_Word_DOT_Interface.coqutil.Word.
Import coqutil_DOT_Z_DOT_bitblast.coqutil.Z.
Import coqutil_DOT_Z_DOT_PushPullMod.coqutil.Z.
Import coqutil_DOT_Z_DOT_div_mod_to_equations.coqutil.Z.
Import coqutil_DOT_Map_DOT_Interface.coqutil.Map.
Import coqutil_DOT_Datatypes_DOT_PropSet.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_List.coqutil.Datatypes.
Import coqutil_DOT_Z_DOT_Lia.coqutil.Z.
Import coqutil_DOT_Tactics_DOT_Tactics.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_forward.coqutil.Tactics.
Import coqutil_DOT_Tactics_DOT_destr.coqutil.Tactics.
Import coqutil_DOT_Decidable.coqutil.
Import coqutil_DOT_Tactics_DOT_autoforward.coqutil.Tactics.
Import coqutil_DOT_Datatypes_DOT_HList.coqutil.Datatypes.
Import coqutil_DOT_Datatypes_DOT_PrimitivePair.coqutil.Datatypes.
Import coqutil_DOT_sanity.coqutil.
Import coqutil_DOT_Macros_DOT_unique.coqutil.Macros.
Import coqutil_DOT_Macros_DOT_subst.coqutil.Macros.
Import  coqutil_DOT_Macros_DOT_subst.coqutil.Macros.subst coqutil_DOT_Macros_DOT_unique.coqutil.Macros.unique coqutil_DOT_Map_DOT_Interface.coqutil.Map.Interface coqutil_DOT_Word_DOT_Properties.coqutil.Word.Properties.
Import Coq.Classes.Morphisms.

Section WeakestPrecondition.
  Context {p : unique! Semantics.parameters}.

  Ltac ind_on X :=
    intros;
    repeat match goal with x : ?T |- _ => first [ constr_eq T X; move x at top | revert x ] end;
    match goal with x : X |- _ => induction x end;
    intros.

  Global Instance Proper_literal : Proper (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)) WeakestPrecondition.literal.
  Proof. cbv [WeakestPrecondition.literal]; cbv [Proper respectful pointwise_relation Basics.impl]; firstorder idtac. Qed.

  Global Instance Proper_get : Proper (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))) WeakestPrecondition.get.
  Proof. cbv [WeakestPrecondition.get]; cbv [Proper respectful pointwise_relation Basics.impl]; firstorder idtac. Qed.

  Global Instance Proper_load : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)))) WeakestPrecondition.load.
  Proof. cbv [WeakestPrecondition.load]; cbv [Proper respectful pointwise_relation Basics.impl]; firstorder idtac. Qed.

  Global Instance Proper_store : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))))) WeakestPrecondition.store.
  Proof. cbv [WeakestPrecondition.load]; cbv [Proper respectful pointwise_relation Basics.impl]; firstorder idtac. Qed.

  Global Instance Proper_expr : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)))) WeakestPrecondition.expr.
  Proof.
    cbv [Proper respectful pointwise_relation Basics.impl]; ind_on Syntax.expr.expr;
      cbn in *; intuition (try typeclasses eauto with core).
    { eapply Proper_literal; eauto. }
    { eapply Proper_get; eauto. }
    { eapply IHa1; eauto; intuition idtac. eapply Proper_load; eauto using Proper_load. }
  Qed.

  Global Instance Proper_list_map {A B} :
    Proper ((pointwise_relation _ (pointwise_relation _ Basics.impl ==> Basics.impl)) ==> pointwise_relation _ (pointwise_relation _ Basics.impl ==> Basics.impl)) (WeakestPrecondition.list_map (A:=A) (B:=B)).
  Proof.
    cbv [Proper respectful pointwise_relation Basics.impl]; ind_on (list A);
      cbn in *; intuition (try typeclasses eauto with core).
  Qed.

  Context {p_ok : Semantics.parameters_ok p}.
  Global Instance Proper_cmd :
    Proper (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ (pointwise_relation _ Basics.impl))) ==> Basics.impl)))) ==>
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl))) ==>
     Basics.impl)))))) WeakestPrecondition.cmd.
  Proof.
    cbv [Proper respectful pointwise_relation Basics.flip Basics.impl]; ind_on Syntax.cmd.cmd;
      cbn in *; cbv [dlet.dlet] in *; intuition (try typeclasses eauto with core).
    { destruct H1 as (?&?&?). eexists. split.
      1: eapply Proper_expr.
      1: cbv [pointwise_relation Basics.impl]; intuition eauto 2.
      all: eauto. }
    { destruct H1 as (?&?&?). eexists. split.
      { eapply Proper_expr.
        { cbv [pointwise_relation Basics.impl]; intuition eauto 2. }
        { eauto. } }
      { destruct H2 as (?&?&?). eexists. split.
        { eapply Proper_expr.
          { cbv [pointwise_relation Basics.impl]; intuition eauto 2. }
          { eauto. } }
        { eapply Proper_store; eauto; cbv [pointwise_relation Basics.impl]; eauto. } } }
    { destruct H1 as (?&?&?). eexists. split.
      { eapply Proper_expr.
        { cbv [pointwise_relation Basics.impl]; intuition eauto 2. }
        { eauto. } }
      { intuition eauto 6. } }
    { destruct H1 as (?&?&?&?&?&HH).
      eassumption || eexists.
      eassumption || eexists.
      eassumption || eexists.
      eassumption || eexists. { eassumption || eexists. }
      eassumption || eexists. { eassumption || eexists. }
      intros X Y Z T W.
      specialize (HH X Y Z T W).
      destruct HH as (?&?&?). eexists. split.
      1: eapply Proper_expr.
      1: cbv [pointwise_relation Basics.impl].
      all:intuition eauto 2.
      - eapply H2; eauto; cbn; intros.
        match goal with H:_ |- _ => destruct H as (?&?&?); solve[eauto] end.
      - intuition eauto. }
    { destruct H1 as (?&?&?). eexists. split.
      { eapply Proper_list_map; eauto; try exact H4; cbv [respectful pointwise_relation Basics.impl]; intuition eauto 2.
        eapply Proper_expr; eauto. }
      { eapply H; eauto. Timeout 10 firstorder eauto.
  Abort.

End WeakestPrecondition.

End WeakestPreconditionProperties.

End bedrock2.

End bedrock2_DOT_WeakestPreconditionProperties.
