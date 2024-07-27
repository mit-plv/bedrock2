From Coq Require Import ZArith.
Require Import coqutil.Word.Interface.
Require Import bedrock2.ZnWords.
Require Import bedrock2.Lift1Prop.

Lemma f_equal_fun[A B: Type]: forall (f g: A -> B) (x: A), f = g -> f x = g x.
Proof. intros. subst. reflexivity. Qed.

Ltac syntactic_f_equal_step_with_ZnWords :=
  lazymatch goal with
  | |- ?x = ?x => reflexivity
  | |- @eq (@word.rep _ _) _ _ => ZnWords
  | |- @eq Z _ _ => ZnWords
  | |- ?f ?a = ?f ?b => eapply (@f_equal _ _ f a b)
  | |- ?f ?x = ?g ?x => eapply (f_equal_fun f g x)
  end.

Ltac syntactic_f_equal_with_ZnWords := solve [repeat syntactic_f_equal_step_with_ZnWords].
