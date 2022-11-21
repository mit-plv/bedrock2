Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import bedrock2.cancel_addsub.
Require Import bedrock2.WordNotations. Local Open Scope word_scope.
Require Import Ltac2.Ltac2.

(*
eg

@f_equal2 Z Z Z Z.div old1 new1 old2 new2 pf1 pf2
then if new1 and new2 both are constants:
let r := eval cbv in (Z.div new1 new2) and return r even though that differs from the rhs of the conclusion of f_equal2


Ltac bottom_up_simpl e :=
  let isZ := match! e with
             | Z.add _ _ => true
             | Z.sub _ _ => true
             | Z.opp _ => true
             | _ => false
             end in
  if isZ then
    let e' := cancel_addsub_unproven 'Z.add 'Z.sub 'Z.opp e in
    if Constr.equal e e' then (e, mkApp '@eq_refl [| 'Z;  e |])
    else (e', constr:(ltac:(ring) : $e = $e'))
  else
    let isWord := match! e with
                  | word.add _ _ => true
                  | word.sub _ _ => true
                  | word.opp _ _ => true
                  | _ => false
                  end in
    if isWord then
      let e' := cancel_addsub_unproven '@word.add '@word.sub '@word.opp e in
      if Constr.equal e e' then (e, mkApp '@eq_refl [| '(@word.rep _ _);  e |])
      else (e', constr:(ltac:(ring) : $e = $e'))
    else
      match! e with
      | ?f ?a =>
          let (f', eq1) := cancel_addsub f in
          let (a', eq2) := cancel_addsub a in
          (mkApp f' [| a' |],
           (* mkApp '@combine_app_eq [| '_; '_; f; f'; a; a'; eq1; eq2 |]
              doesn't work and creates evars for _ that are never instantiated
              instead of holes that are instantiated on typechecking *)
           constr:(combine_app_eq _ _ $f $f' $a $a' $eq1 $eq2))
      | _ => (e, constr:(eq_refl $e))
      end.
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
