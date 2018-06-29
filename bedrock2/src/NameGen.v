Require Import Coq.Lists.List.
Import ListNotations.
Require Import compiler.util.Set.
Require Export Coq.omega.Omega.

Class NameGen(var st: Type){varsSet: SetFunctions var} := mkNameGen {
  (* Return a state which generates vars not contained in the given list.
     We use list instead of set to guarantee that it's finite. *)
  freshNameGenState: list var -> st;

  (* Generate fresh var, and return new state *)
  genFresh: st -> (var * st);

  (* Set of all vars which will be generated in the future *)
  allFreshVars: st -> set var;
  
  genFresh_spec: forall (s s': st) (x: var),
    genFresh s = (x, s') ->
    x \in allFreshVars s /\
    ~ x \in allFreshVars s' /\
    subset (allFreshVars s') (allFreshVars s);
  (* could also say
     allFreshVars s' = diff (allFreshVars s) (singleton_set x)
     but that's unnecessarily strong and requires set equality *)

  freshNameGenState_spec: forall l v, In v l -> ~ v \in (allFreshVars (freshNameGenState l));
}.

Definition listmax(l: list nat): nat := fold_right max 0 l.

Lemma listmax_spec: forall l v, In v l -> v <= listmax l.
Proof.
  induction l; intros.
  - simpl in H. contradiction.
  - simpl in *. destruct H.
    + subst. apply Nat.le_max_l. 
    + pose proof (Nat.le_max_r a (listmax l)).
      specialize (IHl v H).
      eapply Nat.le_trans; eassumption.
Qed.

Definition TODO{T: Type}: T. Admitted.

Instance NatNameGen: NameGen nat nat := {|
  freshNameGenState := fun l => S (listmax l);
  genFresh := fun s => (s, S s);
  (* allFreshVars := fun s => fun x => s <= x TODO can we still support infinite sets?? *)
|}.
  all: apply TODO. (*
  abstract (intros; inversion H; subst; unfold subset; simpl; intuition omega).
  abstract (unfold contains, Function_Set; intros; apply listmax_spec in H; omega).
*)
Defined.
(* We use "abstract" to make the proofs opaque, but "Defined" to make sure that
   "genFresh" and "allFreshVars" are transparent for reduction. *)


Definition listmaxZ(l: list Z): Z := fold_right Z.max 0%Z l.

Lemma listmaxZ_spec: forall l v, In v l -> (v <= listmaxZ l)%Z.
Proof.
  induction l; intros.
  - simpl in H. contradiction.
  - simpl in *. destruct H.
    + subst. apply Z.le_max_l. 
    + pose proof (Z.le_max_r a (listmaxZ l)).
      specialize (IHl v H).
      eapply Z.le_trans; eassumption.
Qed.

Instance ZNameGen: NameGen Z Z := {|
  freshNameGenState := fun l => (listmaxZ l + 1)%Z;
  genFresh := fun s => (s, (s + 1)%Z);
(*  allFreshVars := fun s => fun x => (s <= x)%Z *)
|}.
  all: apply TODO. (*
  abstract (intros; inversion H; subst; unfold subset; simpl; intuition omega).
  abstract (unfold contains, Function_Set; intros; apply listmaxZ_spec in H; omega).
*)
Defined.
