Module map.
  Class map {key value : Type} := {
    rep : Type;
     
    empty : rep;
    get : rep -> key -> option value;
    put : rep -> key -> value -> rep;
  }.
  Arguments map : clear implicits.

  Section ListOperations.
    Context {key value} {map : map key value}.
    Fixpoint putmany (keys : list key) (values : list value) (m : rep) {struct keys} : option rep :=
      match keys, values with
      | nil, nil => Some m
      | cons b binders, cons v values =>
        putmany binders values (put m b v)
      | _, _ => None
      end.
  End ListOperations.

  Section Properties.
    Context {key value} {map : map key value}.
    Definition eq (a b : rep) : Prop :=
      forall k v, get a k = Some v <-> get b k = Some v.
    Definition disjoint (a b : rep) : Prop :=
      forall k v1 v2, get a k = Some v1 -> get b k = Some v2 -> False.
    Definition subsumes (a b : rep) : Prop :=
      forall k v, get b k = Some v -> get a k = Some v.
    Definition split m m1 m2 : Prop :=
      subsumes m m1 /\ subsumes m m2 /\ disjoint m1 m2.
    Definition carve m1 m P2 : Prop :=
      exists m2, split m m1 m2 /\ P2 m2.
    Fixpoint splits m ms : Prop :=
      match ms with
      | nil => eq m empty
      | cons m0 ms' => carve m0 m (fun m => splits m ms')
      end.
                              
    (* FIXME: move *)
    Lemma disjoint_comm m1 m2 : disjoint m1 m2 <-> disjoint m2 m1.
    Proof. cbv [disjoint]. firstorder idtac. Qed.
    Lemma disjoint_subsumes a b c : disjoint a b -> subsumes b c -> disjoint a c.
    Proof. cbv [disjoint subsumes]. typeclasses eauto with core. Qed.
    Lemma split_comm m m1 m2 : split m m1 m2 <-> split m m2 m1.
    Proof. cbv [split]. pose proof disjoint_comm m1 m2. intuition idtac. Qed.

    Context (union : rep -> rep -> rep).
    Require Import Permutation.
    Require Import Coq.Classes.Morphisms.
    Print Permutation.
    Lemma splits_Permutation m : Proper (@Permutation _ ==> iff) (splits m).
    Proof.
    Abort.
  
End map. Notation map := map.map.
Global Coercion map.rep : map >-> Sortclass.