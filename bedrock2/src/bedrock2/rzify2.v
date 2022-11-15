Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import Ltac2.Ltac2.
Local Open Scope Z_scope.

Declare Scope word_scope.
Local Open Scope word_scope.

Local Infix "^+" := word.add  (at level 50, left associativity) : word_scope.
Local Infix "^-" := word.sub  (at level 50, left associativity) : word_scope.
Local Infix "^*" := word.mul  (at level 40, left associativity) : word_scope.
Local Infix "^<<" := word.slu  (at level 37, left associativity) : word_scope.
Local Infix "^>>" := word.sru  (at level 37, left associativity) : word_scope.

(* to be used once at top-level for each Prop,
   potentially with pf=eq_refl but P1<>P2 (but convertible) *)
Lemma rew_Prop: forall (P1 P2: Prop) (pf: P1 = P2), P1 -> P2.
Proof. intros. subst. assumption. Qed.

(* word expressions:
   1) Just simplify non-word subterms, no posing of equations yet
   2) ring_simplify
   3) shallow pass over ring-simplified expression to pose unsigned equations
      (where shallow means not entering into non-word subterms)
*)


(* returns (pf, rhs, pfU, rhsU) where
   pf is a constr of type `e = rhs`
   pfU: word.unsigned e = rhsU *)
Ltac2 rzify_word(wrd: constr)(wok: constr)(e: constr) := (e, e).

(*
eg

@f_equal2 Z Z Z Z.div old1 new1 old2 new2 pf1 pf2
then if new1 and new2 both are constants:
let r := eval cbv in (Z.div new1 new2) and return r even though that differs from the rhs of the conclusion of f_equal2

*)

Set Default Proof Mode "Classic".

Section Tests.
  Context {word: word.word 32} {word_ok: word.ok word}.

  Add Ring wring : (Properties.word.ring_theory (word := word))
      ((* too expensive: preprocess [autorewrite with rew_word_morphism], *)
       morphism (Properties.word.ring_morph (word := word)),
       constants [Properties.word_cst]).

  Hypothesis P: Z -> Prop.

  (** ** Should work: *)

  Goal forall a: word, P (word.unsigned (a ^+ word.of_Z 8 ^- a) / 4) -> P 2.
  Proof.
    intros.
    ring_simplify ((a ^+ word.of_Z 8 ^- a)) in H.
  Abort.


  (** ** Not supported yet: *)

  Goal forall (z1 z2: Z) (y: word),
      word.of_Z (z1 + z2) ^- word.of_Z z1 = y ->
      word.of_Z z2 = y.
  Proof.
    intros. ring_simplify in H.
    (* only simplifies with preprocess [autorewrite with rew_word_morphism] *)
    autorewrite with rew_word_morphism in H.
    ring_simplify in H.
    exact H.
  Abort.

  Context (f: Z -> Z).

  Goal forall x y z1 z2: Z, x = f (z1 + z2) + y - f (z2 + z1) -> x = y.
  Proof.
    intros.
    (* no effect: *)
    ring_simplify (z1 + z2) in H.
    ring_simplify (z2 + z1) in H.
    (* has effect: *)
    ring_simplify (z1 + z2) (z2 + z1) in H.
    ring_simplify in H.
    assumption.
  Abort.

End Tests.
