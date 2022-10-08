Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Decidable.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.fwd.

Section SepLog.
  Context {key value} {map : map.map key value} {ok: map.ok map}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.

  Record hprop: Type := {
    (* get_split P hWhole hOwned hFrame *)
    get_split: map -> map -> map -> Prop;

    get_split_is_split: forall hWhole hOwned hFrame,
        get_split hWhole hOwned hFrame ->
        map.split hWhole hOwned hFrame;

    get_split_monotone: forall hWhole hOwned hFrame hMore,
        map.disjoint hWhole hMore ->
        get_split hWhole hOwned hFrame ->
        get_split (map.putmany hWhole hMore) hOwned (map.putmany hFrame hMore);

    get_split_unique: forall hWhole hOwned hFrame hOwned' hFrame',
        get_split hWhole hOwned hFrame ->
        get_split hWhole hOwned' hFrame' ->
        hFrame' = hFrame /\ hOwned' = hOwned
  }.

  Definition holds(P: hprop)(m: map): Prop :=
    get_split P m m map.empty.

  (* Q: how is this different from simply using `map -> Prop`?
     A: one difference is that it disallows `fun _ => True`,
        (which would correspond to get_split h h1 h2 := map.split h h1 h2,
         which violates get_split_unique) *)

  Definition impl1(P Q: hprop): Prop := forall h, holds P h -> holds Q h.

  Definition iff1(P Q: hprop): Prop := forall h, holds P h <-> holds Q h.

  Definition satisfiable(P: hprop): Prop := exists h, holds P h.

  Axiom TODO: False.

  Definition sep(P1 P2: hprop): hprop.
    refine ({|
      get_split hWhole hOwned hFrame :=
        map.split hWhole hOwned hFrame /\
        exists h1O h1F h2O h2F,
          get_split P1 hOwned h1O h1F /\
          get_split P2 hOwned h2O h2F;
    |}).
    - (* get_split_is_split *)
      intros. fwd. assumption.
    - case TODO.
    - case TODO.
  Defined.

  Definition emp(P: Prop): hprop.
    refine ({|
      get_split hWhole hOwned hFrame := hWhole = hFrame /\ hOwned = map.empty /\ P;
    |}).
    - intros. fwd. apply map.split_empty_l. reflexivity.
    - intros. fwd. auto.
    - intros. fwd. auto.
  Defined.

  Definition ptsto(val: value)(addr: key): hprop.
    refine ({|
      get_split hWhole hOwned hFrame :=
        map.split hWhole hOwned hFrame /\ hOwned = map.put map.empty addr val;
    |}).
    - intros. fwd. assumption.
    - intros. fwd. split; auto. case TODO.
    - intros. fwd. case TODO.
  Defined.

  Lemma sep_inj_r_impl: forall (R P1 P2: hprop),
      satisfiable (sep R P1) ->
      impl1 (sep R P1) (sep R P2) ->
      impl1 P1 P2.
  Proof.
    unfold impl1, satisfiable, holds. cbn. intros *. intros.
    fwd.

    (* problem: `get_split P1 h0` (from satisfiable) vs `get_split P1 h` (from forall) *)

(* additional hyp:
forall h, holds P1 h -> exists hR, map.disjoint h hR /\ holds R hR
*)
  Abort.

  (* unique sep: *)
  Definition usep(P Q: map -> Prop): map -> Prop :=
    fun h => exists h1 h2, map.split h h1 h2 /\ P h1 /\ Q h2 /\
                           forall h1' h2', map.split h h1' h2' -> P h1' -> Q h2' ->
                                           h1' = h1 /\ h2' = h2.
  (* alternative viewpoint: there exists a (unique?) classifier that tells for each address
     whether it's in P, in Q, or in neither *)

  Definition satisfiable'(P: map -> Prop): Prop := exists h, P h.
  Require Import bedrock2.Lift1Prop.

  Lemma usep_inj_r: forall (R P1 P2: map -> Prop),
      satisfiable' (usep R P1) ->
      iff1 (usep R P1) (usep R P2) ->
      iff1 P1 P2.
  Proof.
    unfold iff1, usep, satisfiable'.
    intros R P1 P2 HS HI h.
    fwd. split; intro HP.
    - specialize (HI h0). apply proj1 in HI.
      edestruct HI as (h1' & h2' & HS' & HR' & HP' & HF). {
        do 2 eexists. ssplit; eassumption.
      }
      specialize HSp3 with (3 := HP).
      specialize HF with (3 := HP').
      Search h.

      (* witness h0 vs actual heap h2, both satisfy P1, but they are not equal *)
  Abort.
End SepLog.
