(* Meaning: P implies Q and the only reasonable way to prove Q is to try proving P.
   Often means that Q also implies P, but not always. *)
Definition safe_implication(P: Prop)(Q: Prop): Prop := P -> Q.

Create HintDb safe_implication.

(* required to make the set evars workaround in typeclasses_eauto_with_safe_implication
   work, otherwise, the let-bound evars can still be unfolded by typeclass search *)
Global Hint Variables Opaque : safe_implication.

Global Hint Constants Opaque : safe_implication.

(* Don't use Hint Mode + because it prevents typeclass search from running in
   situations where it should run: https://github.com/coq/coq/issues/18078
#[global] Hint Mode safe_implication - + : safe_implication.
*)

Lemma f_equal_app[A B: Type][f g: A -> B][x y: A]: f = g -> x = y -> f x = g y.
Proof. intros. subst. reflexivity. Qed.

Ltac head_of_app t :=
  lazymatch t with
  | ?f _ => head_of_app f
  | _ => t
  end.

Ltac typeclasses_eauto_with_safe_implication :=
  (* fail fast before we start setting all evars *)
  assert_succeeds (idtac; typeclasses eauto with safe_implication);
  (* hide all evars in q. This is our homemade `Hint Mode +` which hopefully
     does what we want... https://github.com/coq/coq/issues/18078 *)
  repeat lazymatch goal with
    | |- safe_implication _ ?q =>
        match q with
        | context[?x] => is_evar x; set x
        end
    end;
  once (typeclasses eauto with safe_implication).

Ltac safe_implication_step :=
  match goal with
  | |- ?l _ = ?r _ =>
      let hl := head_of_app l in is_constructor hl;
      let hr := head_of_app r in is_constructor hr;
      constr_eq hl hr;
      eapply f_equal_app
  | |- ?Q =>
      let H := fresh in
      eassert (safe_implication _ Q) as H by typeclasses_eauto_with_safe_implication;
      lazymatch type of H with
      | safe_implication ?p ?p =>
          (* "fail 1000" will be swallowed by ltac2, so if that happens, we still want
             to emit a warning, at least *)
          idtac "Warning: There is a safe_implication hint leading to a no-progress step on" p;
          fail 1000 "There is a safe_implication hint leading to a no-progress step on" p
      | _ => unfold safe_implication in H;
             apply H;
             clear H
      end
  end.

Require Import Coq.Lists.List.

Lemma list_app_eq_r: forall [A: Type] (xs ys1 ys2: list A),
    safe_implication (ys1 = ys2) (xs ++ ys1 = xs ++ ys2).
Proof. unfold safe_implication. intros. subst. reflexivity. Qed.

Lemma list_app_eq_l: forall [A: Type] (xs1 xs2 ys: list A),
    safe_implication (xs1 = xs2) (xs1 ++ ys = xs2 ++ ys).
Proof. unfold safe_implication. intros. subst. reflexivity. Qed.

Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import coqutil.Word.Bitwidth coqutil.Word.Interface coqutil.Map.Interface.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.SepLib.

Lemma Z_compare_eq_impl(n m: Z): safe_implication (n = m) ((n ?= m) = Eq).
Proof. unfold safe_implication. apply Z.compare_eq_iff. Qed.

Lemma Z_compare_lt_impl(n m: Z): safe_implication (n < m) ((n ?= m) = Lt).
Proof. unfold safe_implication. apply Z.compare_lt_iff. Qed.

Lemma Z_compare_gt_impl(n m: Z): safe_implication (m < n) ((n ?= m) = Gt).
Proof. unfold safe_implication. apply Z.compare_gt_iff. Qed.

#[export] Hint Resolve Z_compare_eq_impl Z_compare_lt_impl Z_compare_gt_impl
  : safe_implication.

Section WithMem.
  Context {width: Z}{BW: Bitwidth width}{word: word.word width}{word_ok: word.ok word}
    {mem: map.map word Byte.byte}{mem_ok: map.ok mem}.

  (* Note: Not safe if elem doesn't fully determine its value *)
  Lemma array_impl_from_values_eq[E: Type](elem: E -> word -> mem -> Prop)
    (sz: PredicateSize elem)(n: Z)(vs1 vs2: list E)(p: word):
    safe_implication (vs1 = vs2) (impl1 (array elem n vs1 p) (array elem n vs2 p)).
  Proof. unfold safe_implication. intros. subst. reflexivity. Qed.

  Lemma uintptr_from_uint: forall a w z,
      safe_implication (w = word.of_Z z) (impl1 (uint width z a) (uintptr w a)).
  Proof. unfold safe_implication. intros. subst. apply uint_to_uintptr. Qed.

  Lemma uint_from_uintptr: forall a w z,
      safe_implication (z = word.unsigned w) (impl1 (uintptr w a) (uint width z a)).
  Proof. unfold safe_implication. intros. subst. apply uintptr_to_uint. Qed.
End WithMem.

#[export] Hint Resolve
  list_app_eq_l
  list_app_eq_r
  array_impl_from_values_eq
  uintptr_from_uint
  uint_from_uintptr
  : safe_implication.

Global Hint Transparent PredicateSize : safe_implication.
(* Required to make sure that (PredicateSize mypred) is unfolded to Z during type
   unification in typeclass search, even though
   `Global Hint Constants Opaque : safe_implication` has been set.
   Would be resolved by https://github.com/coq/coq/issues/11536 *)

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

    Goal forall (T: Type), exists (vs1 vs2: list T), forall l, l = vs1 -> vs1 = vs2.
    Proof.
      intros. do 2 eexists. intros.
      (* without `Hint Variables Opaque : safe_implication`, this
         eapplies list_app_eq_r infinitely *)
      repeat safe_implication_step.
    Abort.

    (* eauto might unfold safe_implication, but typeclasses eauto won't: *)
    Goal forall (P Q: Prop), Q -> (P -> Q) -> Q.
    Proof. intros. Fail t. assumption. Succeed Qed. Abort.

    Goal forall (a b: nat), (a + b = b + a)%nat.
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
