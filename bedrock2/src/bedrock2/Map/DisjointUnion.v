(* "Unique Separation Logic":
   If all separation logic predicates are either False or only acccept one unique
   heaplet, we can use `option mem` to represent them rather than `mem -> Prop`.

   Comparison table:

   Type of sep log predicates    mem -> Prop                 option mem

   Star operator                 (P * Q) m = exists mp mq,   P \*/ Q = if both non-None,
                                 split m mp mq /\            put all entries of Q into
                                 P mp /\ Q mq                P, None if key clash

   pure facts P                  lift1 P := fun _ => P       not supported (unless decidable)

   existentials                  exists1 P :=                not supported, need to quantify
                                   fun m => exists a, P m    outside of sep log formula

   P holds for m                 P m                         P = Some m

   Equivalent predicates         iff1 P Q :=                 P = Q
                                   forall m, P m <-> Q m

   Implication on predicates     impl1 P Q :=                not supported (or maybe lhs
                                   forall m, P m -> Q m        can be None, aka exfalso, else =)

   going from a sep log          forall m: mem, P m ->       defined P /\
   predicate P to a memory       ... m ...                   ... force P ...

   target language memory mL     H1: (P * Q) mH              H1: P \*/ Q = Some mH
   extending source language     H2: (R * eq mH) mL          H2: R \*/ Some mH = Some mL
   memory mH

   inlining source language     sep_inline_eq:               rewrite <- H1 in H2
   memory assertion into        (exists mH, A mH /\
   target language assertion                (R * eq mH) mL)
                                <-> (R * A) mL

More notes:

related sH sL = ... /\ (eq sH#mem * L) sL#mem

                ... /\ Some sH#mem \*/ L = Some sL#mem


what if the source-level used a predicate `M mH`?
H1: M mH
H2: (M * R) mL
H3: iff1 M (P * Q)
rewrite H3 in H2

What if I have a separation logic predicate about source memory and a source execution that
I invert and need to match this inversion to the separation logic predicate?
From predicate: (R1 * a ~> v_old) m
From inversion: (R2 * a ~> v_old') m
With `mem -> Prop`, we can't conclude anything like R1=R2, but with `option mem`, we can.
But does this case ever occur?


Memory.store m a v_new = Some m' ->
(exists (R: mem -> Prop) v_old, (R * a ~> v_old) m /\ (R * a ~> v_new) m')
But the other direction does not hold, R could be (fun _ => True)

We could use both kinds of separation logic in the semantics instead of Memory.store/map.put:

  Definition store(n: nat)(ctxid: SourceType)(a: word)(v: tuple byte n)(mach: State)(post: State -> Prop) :=
    exists (R: option mem) (v_old: tuple byte n),
      R \*/ bytes a v_old = Some mach#"mem" /\ post mach(#"mem" := mmap.force (R \*/ bytes a v)).

  Definition store(n: nat)(ctxid: SourceType)(a: word)(v: tuple byte n)(mach: State)(post: State -> Prop) :=
    exists (R: mem -> Prop) (v_old: tuple byte n),
      (R * bytes a v_old) mach#"mem" /\
      forall newmem, (R * bytes a v) newmem -> post mach(#"mem" := newmem)

An advantage of unique sep log: If we have two predicates about the same memory, we can invert:
[But does this advantage ever matter?]

R \*/ P1 = Some m ->
R \*/ P2 = Some m ->
P1 = P2

follows from du_inj_r:

R \*/ P1 = R \*/ P2 ->
R \*/ P1 <> None ->    (*<--needed!*)
P1 = P2

(R * P1) m /\
(R * P2) m doesn't imply
P1 = P2 nor iff1 P1 P2

iff1 P1 P2 ->
iff1 (R * P1) (R * P2)
But the opposite direction doesn't hold if R = (fun _ => False),
or R is not disjoint from P1 and P2

And just requiring that the predicate is not contradictory doesn't suffice:
iff1 (R * P1) (R * P2) ->
(exists m, (R * P1) m) ->      (*<--added*)
iff1 P1 P2                     (*<--might not hold!*)
Counterexample:
R = fun _ => True
P1 = fun m => all keys in m are < 3
P2 = fun m => all keys in m are < 4
proving any (R * P1) m is as easy as giving all of m to R and giving map.empty to P1
*)
From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith.
Require Import coqutil.Decidable.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.fwd.

Module map. Section __.
  Context {key value} {map : map.map key value} {ok: map.ok map}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.

  Definition disjointb(m1: map): map -> bool :=
    map.forallb (fun k v => if map.get m1 k then false else true).

  Lemma disjointb_spec: forall m1 m2,
      disjointb m1 m2 = true <-> map.disjoint m1 m2.
  Proof.
    unfold disjointb, map.forallb. intros. eapply map.fold_spec.
    - split; intros. 1: eapply map.disjoint_empty_r. reflexivity.
    - intros. destruct_one_match.
      + rewrite Bool.andb_false_r. split; intros. 1: discriminate.
        exfalso. unfold map.disjoint in H1. eapply H1. 1: eassumption.
        eapply map.get_put_same.
      + rewrite Bool.andb_true_r. split; intros.
        * destruct H0. eapply map.disjoint_put_r; eauto.
        * eapply H0. unfold map.disjoint in *.
          intros. eapply (H1 _ _ (if key_eqb k k0 then _ else _)). 1: eassumption.
          rewrite map.get_put_dec. rewrite H3.
          destruct_one_match; reflexivity.
  Qed.

  Definition du(m1 m2: map): option map :=
    if disjointb m1 m2 then Some (map.putmany m1 m2) else None.

  Lemma du_comm: forall p q, du p q = du q p.
  Proof.
    intros. unfold du. destruct_one_match.
    - eapply disjointb_spec in E. eapply map.disjoint_comm in E.
      rewrite (map.putmany_comm q p) by exact E.
      eapply disjointb_spec in E. rewrite E. reflexivity.
    - destruct_one_match. 2: reflexivity.
      eapply disjointb_spec in E0. eapply map.disjoint_comm in E0.
      eapply disjointb_spec in E0. rewrite E0 in E. discriminate.
  Qed.

  Lemma du_empty_l: forall m, du map.empty m = Some m.
  Proof.
    intros. unfold du. rewrite map.putmany_empty_l.
    destruct_one_match.
    - reflexivity.
    - exfalso.
      unshelve epose proof (proj2 (disjointb_spec map.empty m) _) as P.
      1: eapply map.disjoint_empty_l. congruence.
  Qed.

  Lemma du_empty_r: forall m, du m map.empty = Some m.
  Proof. intros. rewrite du_comm. eapply du_empty_l. Qed.

  Lemma du_inj_r: forall (R P1 P2 m: map),
      du R P1 = Some m ->
      du R P2 = Some m ->
      P1 = P2.
  Proof.
    unfold du. intros. fwd.
    eapply disjointb_spec in E0.
    eapply disjointb_spec in E.
    eapply map.map_ext.
    intro k.
    eapply (f_equal (fun m => map.get m k)) in H0.
    rewrite 2map.get_putmany_dec in H0.
    unfold map.disjoint in *.
    do 2 destruct_one_match_hyp.
    - assumption.
    - exfalso. eapply E0. 1: symmetry. all: eassumption.
    - exfalso. eapply E. all: eassumption.
    - reflexivity.
  Qed.

End __. End map.

(* maybe-map *)
Module mmap. Section __.
  Context {key value} {map : map.map key value} {ok: map.ok map}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.

  Inductive mmap :=
  | Def(m: map)
  | Undef.

  Definition equal_union(value_eqb: value -> value -> bool)(om1 om2: mmap): mmap :=
    match om1, om2 with
    | Def m1, Def m2 =>
        if map.eqb value_eqb m1 m2 then Def m1 else Undef
    | _, _ => Undef
    end.

  Definition defined(mm: mmap): Prop := exists m, mm = Def m.

  Definition force(mm: mmap): map :=
    match mm with
    | Def m => m
    | Undef => map.empty
    end.

  Definition of_option(om: option map): mmap :=
    match om with
    | Some m => Def m
    | None => Undef
    end.

  Lemma eq_of_eq_Def: forall m1 m2, Def m1 = Def m2 -> m1 = m2.
  Proof. intros. congruence. Qed.

  (* disjoint union *)
  Definition du(a b: mmap): mmap :=
    match a, b with
    | Def a, Def b => of_option (map.du a b)
    | _, _ => Undef
    end.

  (* disjoint-unions *)
  Definition dus'(l: list mmap): mmap := List.fold_right du (Def map.empty) l.

  Fixpoint dus (xs : list mmap) : mmap :=
    match xs with
    | [x] => x
    | x :: xs => du x (dus xs)
    | nil => Def map.empty
    end.

  Lemma du_comm: forall p q, du p q = du q p.
  Proof.
    intros. unfold du, of_option. destruct p; destruct q; try reflexivity.
    rewrite map.du_comm. reflexivity.
  Qed.

  Lemma du_empty_l: forall mm, du (Def map.empty) mm = mm.
  Proof.
    intros. unfold du. destruct mm as [m|]. 2: reflexivity. rewrite map.du_empty_l.
    reflexivity.
  Qed.

  Lemma du_empty_r: forall mm, du mm (Def map.empty) = mm.
  Proof.
    intros. unfold du. destruct mm as [m|]. 2: reflexivity. rewrite map.du_empty_r.
    reflexivity.
  Qed.

  Lemma du_assoc: forall p q r, du (du p q) r = du p (du q r).
  Proof.
    intros. unfold du.
    destruct p as [p|]. 2: reflexivity.
    destruct q as [q|]. 2: reflexivity.
    destruct r as [r|]. 2: destruct (map.du p q); reflexivity.
    unfold map.du, of_option.
    destr (map.disjointb p q).
    - eapply map.disjointb_spec in E.
      destr (map.disjointb q r).
      + eapply map.disjointb_spec in E0.
        destr (map.disjointb p r).
        * eapply map.disjointb_spec in E1.
          replace (map.disjointb (map.putmany p q) r) with true.
          2: {
            symmetry. eapply map.disjointb_spec.
            eapply map.disjoint_putmany_l. auto.
          }
          replace (map.disjointb p (map.putmany q r)) with true.
          2: {
            symmetry. eapply map.disjointb_spec.
            eapply map.disjoint_putmany_r. auto.
          }
          f_equal.
          symmetry. eapply map.putmany_assoc.
        * destr (map.disjointb (map.putmany p q) r).
          { exfalso.
            eapply map.disjointb_spec in E2.
            eapply map.disjoint_putmany_l in E2. apply proj1 in E2.
            eapply map.disjointb_spec in E2.
            congruence. }
          destr (map.disjointb p (map.putmany q r)).
          { exfalso.
            eapply map.disjointb_spec in E3.
            eapply map.disjoint_putmany_r in E3. apply proj2 in E3.
            eapply map.disjointb_spec in E3.
            congruence. }
          reflexivity.
      + destr (map.disjointb (map.putmany p q) r). 2: reflexivity.
        exfalso.
        eapply map.disjointb_spec in E1. eapply map.disjoint_putmany_l in E1.
        apply proj2 in E1. eapply map.disjointb_spec in E1. congruence.
    - destr (map.disjointb q r). 2: reflexivity.
      destr (map.disjointb p (map.putmany q r)). 2: reflexivity.
      exfalso.
      eapply map.disjointb_spec in E1. eapply map.disjoint_putmany_r in E1.
      apply proj1 in E1. eapply map.disjointb_spec in E1. congruence.
  Qed.

  Lemma dus'_dus: forall xs, dus' xs = dus xs.
  Proof.
    induction xs; [reflexivity|].
    cbn -[du]. destruct xs.
    - cbn -[du]. apply du_empty_r.
    - cbn [dus' fold_right]. unfold dus' in *. cbn [fold_right] in IHxs.
      rewrite IHxs.
      reflexivity.
  Qed.

  Lemma dus_cons: forall (P: mmap) (Ps: list mmap),
      dus (P :: Ps) = du P (dus Ps).
  Proof. intros. rewrite <-! dus'_dus. reflexivity. Qed.

  Lemma dus_app: forall Ps Qs : list mmap,
      dus (Ps ++ Qs) = du (dus Ps) (dus Qs).
  Proof.
    induction Ps; intros.
    - cbn -[du]. simpl. symmetry. apply du_empty_l.
    - rewrite <- List.app_comm_cons. rewrite !dus_cons. rewrite IHPs.
      symmetry. apply du_assoc.
  Qed.

  Lemma du_inj_r: forall (R P1 P2: mmap) (m: map),
      du R P1 = Def m ->
      du R P2 = Def m ->
      P1 = P2.
  Proof.
    unfold du, of_option. intros. fwd. f_equal. eapply map.du_inj_r; eassumption.
  Qed.

  Definition split(m m1 m2: map): Prop :=
    Def m = du (Def m1) (Def m2).
End __. End mmap.

Arguments mmap.mmap {_ _} _.
Notation mmap := mmap.mmap.

Coercion mmap.Def : map.rep >-> mmap.

Notation "a \*/ b" := (mmap.du a b) (at level 34, no associativity).
(* Notation "a \=/ b" :=
     (mmap.equal_union TODO_value_eqb a b) (at level 34, no associativity). *)

Module Tree.
  Inductive t(A: Type): Type :=
  | Leaf(a: A)
  | Node(left right: t A).
  Arguments Leaf {A} _.
  Arguments Node {A} _ _.
  Section Interp.
    Context {A B: Type}.
    Context (interp_Leaf: A -> B).
    Context (interp_Node: B -> B -> B).
    Fixpoint interp(t: t A): B :=
      match t with
      | Leaf a => interp_Leaf a
      | Node t1 t2 => interp_Node (interp t1) (interp t2)
      end.
  End Interp.

  Definition flatten{A: Type}: t A -> list A := interp (fun a => cons a nil) (@app A).
End Tree.

Section SepLog.
  Context {key value} {map : map.map key value} {ok: map.ok map}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.

  Definition tree_to_du: Tree.t (mmap map) -> (mmap map) := Tree.interp id mmap.du.

  Lemma dus_flatten: forall t: Tree.t (mmap map),
      mmap.dus (Tree.flatten t) = tree_to_du t.
  Proof.
    induction t; [reflexivity|].
    simpl. rewrite mmap.dus_app. rewrite IHt1, IHt2. reflexivity.
  Qed.

  Lemma tree_to_du_eq_of_flatten_eq: forall LHS RHS : Tree.t (mmap map),
      mmap.dus (Tree.flatten LHS) = mmap.dus (Tree.flatten RHS) ->
      tree_to_du LHS = tree_to_du RHS.
  Proof. intros. rewrite! dus_flatten in H. exact H. Qed.

  Section cancel_lemmas.
    Let nth n xs := hd (@mmap.Def _ _ map map.empty) (skipn n xs).
    Let nth' n xs := hd (@mmap.Undef _ _ map) (skipn n xs).
    Let remove_nth n (xs : list (mmap map)) := firstn n xs ++ tl (skipn n xs).

    Lemma dus_nth_to_head n xs: mmap.du (nth n xs) (mmap.dus (remove_nth n xs)) = mmap.dus xs.
    Proof.
      cbv [nth remove_nth].
      pose proof (List.firstn_skipn n xs : (firstn n xs ++ skipn n xs) = xs).
      set (xsr := skipn n xs) in *; clearbody xsr.
      set (xsl := firstn n xs) in *; clearbody xsl.
      subst xs.
      rewrite <-2mmap.dus'_dus.
      destruct xsr.
      { cbn [mmap.dus' hd]. rewrite mmap.du_empty_l. reflexivity. }
      cbn [hd tl].
      rewrite 2mmap.dus'_dus.
      rewrite 2mmap.dus_app.
      rewrite mmap.dus_cons.
      rewrite <-2mmap.du_assoc.
      f_equal.
      apply mmap.du_comm.
    Qed.

    Lemma dus_remove_nth: forall n oms mn m,
        nth' n oms = mmap.Def mn ->
        mmap.Def m = mmap.dus oms ->
        exists m', mmap.Def m' = mmap.dus (remove_nth n oms) /\ mmap.Def m = mmap.du mn m'.
    Proof.
      induction n; intros.
      - destruct oms; cbn in H; try discriminate H. subst.
        rewrite mmap.dus_cons in H0. cbn. cbn in H0. fwd. eauto.
      - destruct oms; try discriminate H.
        change (remove_nth (S n) (m0 :: oms)) with (m0 :: remove_nth n oms).
        rewrite mmap.dus_cons in H0.
        change (nth' n oms = mmap.Def mn) in H.
        specialize IHn with (1 := H).
        pose proof H0 as B.
        unfold mmap.du in H0. fwd. specialize (IHn _ eq_refl).
        unfold mmap.of_option in *. fwd.
        rewrite mmap.dus_cons.
        rewrite IHnp1 in B. change (map.du mn m') with (mmap.du (Def mn) (Def m')) in B.
        rewrite IHnp0 in B. rewrite (mmap.du_comm (mmap.Def mn)) in B.
        rewrite <- mmap.du_assoc in B.
        unfold mmap.du at 1 in B. fwd.
        eexists. split. 1: reflexivity. rewrite mmap.du_comm. exact B.
    Qed.

    Lemma cancel_at: forall (i j: nat) (xs ys: list (mmap map)),
        nth i xs = nth j ys ->
        mmap.dus (remove_nth i xs) = mmap.dus (remove_nth j ys) ->
        mmap.dus xs = mmap.dus ys.
    Proof.
      intros.
      rewrite <-(dus_nth_to_head i xs).
      rewrite <-(dus_nth_to_head j ys).
      f_equal; assumption.
    Qed.

    Lemma cancel_at_bw: forall (i j: nat) (xs ys: list (mmap map)),
        mmap.defined (mmap.dus xs) ->
        nth i xs = nth j ys ->
        mmap.dus xs = mmap.dus ys ->
        mmap.dus (remove_nth i xs) = mmap.dus (remove_nth j ys).
    Proof.
      unfold mmap.defined. intros. fwd.
      rewrite <-(dus_nth_to_head i xs) in *.
      rewrite <-(dus_nth_to_head j ys) in *.
      eapply mmap.du_inj_r. 1: eassumption.
      congruence.
    Qed.

    Lemma cancel_at_eq: forall (i j: nat) (xs ys: list (mmap map)),
        mmap.defined (mmap.dus xs) ->
        nth i xs = nth j ys ->
        (mmap.dus (remove_nth i xs) = mmap.dus (remove_nth j ys)) =
        (mmap.dus xs = mmap.dus ys).
    Proof.
      intros.
      eapply PropExtensionality.propositional_extensionality. split.
      - eapply cancel_at; assumption.
      - eapply cancel_at_bw; assumption.
    Qed.

  End cancel_lemmas.
End SepLog.

Ltac reify e :=
  lazymatch e with
  | @mmap.du ?key ?value ?map ?a ?b =>
    let a := reify a in
    let b := reify b in
    uconstr:(@Tree.Node (option (@map.rep key value map)) a b)
  | ?a => uconstr:(Tree.Leaf a)
  end.

Ltac reify_goal :=
  lazymatch goal with
  | |- @eq (option _ (*=map.rep or something convertible to map.rep*)) ?LHS ?RHS =>
    let LHS := reify LHS in
    let RHS := reify RHS in
    change (tree_to_du LHS = tree_to_du RHS);
    eapply tree_to_du_eq_of_flatten_eq
  end;
  cbn [Tree.flatten Tree.interp app].

Ltac cancel_at i j :=
  lazymatch goal with
  | |- mmap.dus ?LHS = mmap.dus ?RHS =>
    simple refine (cancel_at i j LHS RHS _ _);
    cbn [firstn skipn List.app hd tl]
  end.
