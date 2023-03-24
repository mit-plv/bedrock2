Definition injective[A B: Type](f: A -> B): Prop :=
  forall x1 x2, f x1 = f x2 -> x1 = x2.
Existing Class injective.

(* we don't really need the injectivity proofs, because we're not proving that our
   proof steps are safe, so we can skip proving injectivity if we want *)
Class fake_injective[A B: Type](f: A -> B): Prop := {}.

#[export] Instance discard_injectivity_proof[A B: Type](f: A -> B)(i: injective f):
  fake_injective f. Qed.

Lemma f_equal_vary_2ndlast[A B C: Type](f: A -> B -> C)(x1 x2: A)(y: B)(H: x1 = x2):
  f x1 y = f x2 y.
Proof. intros. subst. reflexivity. Qed.

Require Import Coq.Program.Basics.

Ltac safe_f_equal_step :=
  lazymatch goal with
  | |- ?f ?y1 = ?f ?y2 =>
      let _inj := constr:(_ : fake_injective f) in
      eapply (f_equal f)
  | |- ?f ?x1 ?y = ?f ?x2 ?y =>
      let _inj := constr:(_ : fake_injective (flip f y)) in
      eapply (f_equal_vary_2ndlast f x1 x2 y)
  end.

Ltac safe_f_equal := repeat safe_f_equal_step.

Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.

(* Real instances with easy proofs: *)

#[export] Instance list_app_inj_r[A: Type](xs: list A): injective (List.app xs).
Proof. unfold injective. apply List.app_inv_head. Qed.

#[export] Instance list_app_inj_l[A: Type](xs: list A): injective (flip (@List.app A) xs).
Proof. unfold injective, flip. apply List.app_inv_tail. Qed.

(* Fake instances whose proofs would/might be harder, or even false: *)

Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Bitwidth coqutil.Word.Interface coqutil.Map.Interface.
Require Import bedrock2.SepLib.

Section WithMem.
  Context {width: Z}{BW: Bitwidth width}{word: word.word width}
    {mem: map.map word Byte.byte}.

  (* Note: doesn't hold if elem doesn't fully determine its value *)
  #[export] Instance array_val_inj[E: Type]
    (elem: E -> word -> mem -> Prop)(sz: Z)(n: Z)(p: word):
    fake_injective (Basics.flip (array (elemSize := sz) elem n) p). Qed.

  (* Note: doesn't hold if vs is empty, or if elem is emp *)
  #[export] Instance array_addr_inj[E: Type]
    (elem: E -> word -> mem -> Prop)(sz: Z)(n: Z)(vs: list E):
    fake_injective (array (elemSize := sz) elem n vs). Qed.

  Section Tests.
    Goal forall (l1 l2 l3a l3b l4: list Z) n a,
        l3a = l3b ->
        array (uint 16) n (l1 ++ l2 ++ l3a ++ l4) a =
        array (uint 16) n (l1 ++ l2 ++ l3b ++ l4) a.
    Proof. intros. f_equal. safe_f_equal. assumption. Abort.

    Goal forall (a b: nat),
        a + b = b + a.
    Proof. intros. safe_f_equal. apply Nat.add_comm. Abort.
  End Tests.
End WithMem.
