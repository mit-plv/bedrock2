(* This file only exists because of COQBUG https://github.com/coq/coq/issues/11352:
   The more unfoldable definitions there are, the slower firstorder becomes,
   so we isolate the map goals of Spilling.v into this file where everything is kept
   as abstract as possible, so that firstorder can't unfold too much. *)
Require Import coqutil.Map.Interface coqutil.Map.Properties.

Section LEMMAS.
  Context {K V: Type} {map: map.map K V} {ok: map.ok map}.

  Axiom map__split_spec: forall (M A B: map),
      map.split M A B <-> forall k,
        (exists v, map.get M k = Some v /\
                   ((map.get A k = Some v /\ map.get B k = None) \/
                    (map.get B k = Some v /\ map.get A k = None))) \/
        (map.get M k = None /\ map.get A k = None /\ map.get B k = None).

  Axiom map__putmany_spec: forall (m1 m2: map) k,
      (exists v, map.get (map.putmany m1 m2) k = Some v /\
                 (map.get m2 k = Some v \/ (map.get m2 k = None /\ map.get m1 k = Some v))) \/
      (map.get (map.putmany m1 m2) k = None /\ map.get m2 k = None /\ map.get m1 k = None).

  Lemma split_interact:
    forall (m mKeep mGive : map) (frame m2 mL mStack : map),
      map.split m mKeep mGive ->
      map.split m2 m mL ->
      map.split mL mStack frame ->
      map.split m2 (map.putmany mKeep mL) mGive.
  Proof.
    intros.
    rewrite map__split_spec in *.
    pose proof map__putmany_spec mKeep mL.

    (* COQBUG https://github.com/coq/coq/issues/12722
    firstorder congruence.
    fails with "Error: Tactic failure: reversible in 1st order mode." *)

    (* workaround: *)
    intro k.
    repeat match goal with
           | H: forall _, _ |- _ => specialize (H k)
           end.

    firstorder congruence.
  Qed.

End LEMMAS.
