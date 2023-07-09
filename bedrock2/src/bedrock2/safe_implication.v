(* Meaning: P implies Q and the only reasonable way to prove Q is to try proving P.
   Often means that Q also implies P, but not always. *)
Definition safe_implication(P: Prop)(Q: Prop): Prop := P -> Q.

Create HintDb safe_implication.

#[global] Hint Mode safe_implication - + : safe_implication.

Lemma f_equal_app[A B: Type][f g: A -> B][x y: A]: f = g -> x = y -> f x = g y.
Proof. intros. subst. reflexivity. Qed.

Ltac head_of_app t :=
  lazymatch t with
  | ?f _ => head_of_app f
  | _ => t
  end.

Ltac safe_implication_step :=
  match goal with
  | |- ?l _ = ?r _ =>
      let hl := head_of_app l in is_constructor hl;
      let hr := head_of_app r in is_constructor hr;
      constr_eq hl hr;
      eapply f_equal_app
  | |- ?Q =>
      let H := fresh in
      eassert (safe_implication _ Q) as H by (typeclasses eauto with safe_implication);
      unfold safe_implication in H;
      apply H;
      clear H
  end.

Require Import Coq.Lists.List.

Lemma list_app_eq_r: forall [A: Type] (xs ys1 ys2: list A),
    safe_implication (ys1 = ys2) (xs ++ ys1 = xs ++ ys2).
Proof. unfold safe_implication. intros. subst. reflexivity. Qed.

Lemma list_app_eq_l: forall [A: Type] (xs1 xs2 ys: list A),
    safe_implication (xs1 = xs2) (xs1 ++ ys = xs2 ++ ys).
Proof. unfold safe_implication. intros. subst. reflexivity. Qed.

Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Bitwidth coqutil.Word.Interface coqutil.Map.Interface.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.SepLib.

Section WithMem.
  Context {width: Z}{BW: Bitwidth width}{word: word.word width}
    {mem: map.map word Byte.byte}.

  (* Note: Not safe if elem doesn't fully determine its value *)
  Lemma array_impl_from_values_eq[E: Type](elem: E -> word -> mem -> Prop)
    (sz: PredicateSize elem)(n: Z)(vs1 vs2: list E)(p: word):
    safe_implication (vs1 = vs2) (impl1 (array elem n vs1 p) (array elem n vs2 p)).
  Proof. unfold safe_implication. intros. subst. reflexivity. Qed.

End WithMem.

#[export] Hint Resolve
  list_app_eq_l
  list_app_eq_r
  array_impl_from_values_eq
  : safe_implication.

Module Tests.
  Section WithMem.
    Context {width: Z}{BW: Bitwidth width}{word: word.word width}
      {mem: map.map word Byte.byte}.

    Ltac t := safe_implication_step.

    Goal forall (l1 l2 l3a l3b l4: list Z) n a,
        l3a = l3b ->
        impl1 (array (uint 16) n (l1 ++ l2 ++ l3a ++ l4) a)
              (array (uint 16) n (l1 ++ l2 ++ l3b ++ l4) a).
    Proof. intros. t. t. t. t. assumption. Succeed Qed. Abort.

    Goal forall (l1 l1' l2: list nat), l1 = l1' -> l1 ++ l2 = l1' ++ l2.
    Proof. intros. t. assumption. Succeed Qed. Abort.

    Goal forall (l1 l2 l2': list nat), l2 = l2' -> l1 ++ l2 = l1 ++ l2'.
    Proof. intros. t. assumption. Succeed Qed. Abort.

    (* eauto might unfold safe_implication, but typeclasses eauto won't: *)
    Goal forall (P Q: Prop), Q -> (P -> Q) -> Q.
    Proof. intros. Fail t. assumption. Succeed Qed. Abort.

    Goal forall (a b: nat),
        a + b = b + a.
    Proof. intros. assert_fails (idtac; t). apply Nat.add_comm. Succeed Qed. Abort.

    Inductive foo(a: nat): nat -> Set :=
    | foo_empty: foo a O
    | foo_nonempty(x y z: nat): foo a x.

    Goal forall a x y y' z z',
        y = y' -> z = z' ->
        foo_nonempty a x y z = foo_nonempty a x y' z'.
    Proof. intros. t. 2: assumption. t. 2: assumption. reflexivity. Succeed Qed. Abort.

  End WithMem.
End Tests.
