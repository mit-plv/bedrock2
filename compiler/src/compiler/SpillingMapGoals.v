(* This file only exists because of COQBUG https://github.com/coq/coq/issues/11352:
   The more unfoldable definitions there are, the slower firstorder becomes,
   so we isolate the map goals of Spilling.v into this file where everything is kept
   as abstract as possible, so that firstorder can't unfold too much. *)
Require Import coqutil.Map.Interface coqutil.Map.Properties.

Section LEMMAS.
  Context {K V: Type} {map: map.map K V} {ok: map.ok map}.
  Implicit Types (k : K) (v : V) (m : map).

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

  Lemma split_stackalloc_1: forall (m2 mSmall mL mCombined mStack0: map),
      map.split m2 mSmall mL ->
      map.split mCombined m2 mStack0 ->
      map.split (map.putmany mSmall mStack0) mSmall mStack0.
  Proof.
    intros.
    rewrite map__split_spec in *.
    pose proof map__putmany_spec mSmall mStack0.
    intro k.
    repeat match goal with
           | H: forall _, _ |- _ => specialize (H k)
           end.
    firstorder congruence.
  Qed.

  Lemma split_stackalloc_2: forall (m2 mSmall mL mCombined mStack0: map),
      map.split m2 mSmall mL ->
      map.split mCombined m2 mStack0 ->
      map.split mCombined (map.putmany mSmall mStack0) mL.
  Proof.
    intros.
    rewrite map__split_spec in *.
    pose proof map__putmany_spec mSmall mStack0.
    intro k.
    repeat match goal with
           | H: forall _, _ |- _ => specialize (H k)
           end.
    firstorder congruence.
  Qed.

  Lemma split_interact_assoc: forall m mKeep mGive m2 mL mReceive m',
      map.split m mKeep mGive ->
      map.split m2 m mL ->
      map.split m' (map.putmany mKeep mL) mReceive ->
      map.split m' (map.putmany mKeep mReceive) mL.
  Proof.
    intros.
    rewrite map__split_spec in *.
    pose proof map__putmany_spec mKeep mL.
    pose proof map__putmany_spec mKeep mReceive.
    intro k.
    repeat match goal with
           | H: forall _, _ |- _ => specialize (H k)
           end.
    firstorder congruence.
  Qed.

  Lemma split_interact_shrink: forall mKeep mL m' mReceive,
      map.split m' (map.putmany mKeep mL) mReceive ->
      map.split (map.putmany mKeep mReceive) mKeep mReceive.
  Proof.
    intros.
    rewrite map__split_spec in *.
    pose proof map__putmany_spec mKeep mL.
    pose proof map__putmany_spec mKeep mReceive.
    intro k.
    repeat match goal with
           | H: forall _, _ |- _ => specialize (H k)
           end.
    firstorder congruence.
  Qed.

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
