From Hammer Require Import Tactics.

Axiom K: Type.
Axiom V: Type.
Axiom map: Type.
Axiom get: map -> K -> option V.
(* in putmany m1 m2, keys of m2 override those of m1 *)
Axiom putmany: map -> map -> map.
(* `split m m1 m2` means that m can be split into two disjoint maps m1 and m2 *)
Axiom split : map -> map -> map -> Prop.

Axiom split_spec: forall (M A B: map),
    split M A B <-> forall k,
      (exists v, get M k = Some v /\
                 ((get A k = Some v /\ get B k = None) \/
                  (get B k = Some v /\ get A k = None))) \/
      (get M k = None /\ get A k = None /\ get B k = None).

Axiom putmany_spec: forall (m1 m2: map) k,
    (exists v, get (putmany m1 m2) k = Some v /\
               (get m2 k = Some v \/ (get m2 k = None /\ get m1 k = Some v))) \/
    (get (putmany m1 m2) k = None /\ get m2 k = None /\ get m1 k = None).

Goal forall m mKeep mGive frame m2 mL mStack,
    split m mKeep mGive ->
    split m2 m mL ->
    split mL mStack frame ->
    split m2 (putmany mKeep mL) mGive.
Proof.
  intros *. intros A1 A2 A3.
  pose proof (proj1 (split_spec _ _ _) A1) as B1.
  pose proof (proj1 (split_spec _ _ _) A2) as B2.
  pose proof (proj1 (split_spec _ _ _) A3) as B3.
  apply (proj2 (split_spec _ _ _)).
  clear A1 A2 A3.

  pose proof (putmany_spec mKeep mL) as B4.

(*
  sauto inv: - ctrs: - cases: - ecases: off.

  Time hauto.
*)

  intro k.
  specialize (B1 k).
  specialize (B2 k).
  specialize (B3 k).
  specialize (B4 k).

  hauto.

(*
  Time firstorder congruence. (* 0.61 secs *)
  Time hauto. (* 1.528 secs *)
*)
Qed.
