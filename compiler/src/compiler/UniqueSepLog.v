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
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Byte.
Require Import coqutil.Decidable.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Datatypes.HList.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.Simp.
Require Import coqutil.Word.LittleEndian.
Require Import bedrock2.Memory.
Require Import bedrock2.Syntax.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Encode.

Axiom TODO: False.

(* maybe-map *)
Module mmap. Section __.
  Context {key value} {map : map.map key value} {ok: map.ok map}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.

  Definition defined(mm: option map): Prop := exists m, mm = Some m.

  Definition force(mm: option map): map :=
    match mm with
    | Some m => m
    | None => map.empty
    end.

  (* disjoint put *)
  Definition dput(mm: option map)(k: key)(v: value): option map :=
    match mm with
    | Some m =>
      match map.get m k with
      | Some _ => None
      | None => Some (map.put m k v)
      end
    | None => None
    end.

  (* disjoint union *)
  Definition du(a b: option map): option map :=
    match a, b with
    | Some a, Some b => map.fold dput (Some a) b
    | _, _ => None
    end.

  (* disjoint-unions *)
  Definition dus'(l: list (option map)): option map := List.fold_right du (Some map.empty) l.

  Fixpoint dus (xs : list (option map)) : option map :=
    match xs with
    | [x] => x
    | x :: xs => du x (dus xs)
    | nil => Some map.empty
    end.

  Lemma du_empty_l: forall mm, du (Some map.empty) mm = mm.
  Proof.
    intros. simpl. destruct mm as [m|]. 2: reflexivity.
    eapply map.fold_spec.
    - reflexivity.
    - intros. subst r. simpl. rewrite H. reflexivity.
  Qed.

  Lemma du_empty_r: forall mm, du mm (Some map.empty) = mm.
  Proof.
    intros. unfold du. destruct mm as [m|]. 2: reflexivity.
    apply map.fold_empty.
  Qed.

  Lemma dput_comm: forall mm k1 v1 k2 v2,
      dput (dput mm k1 v1) k2 v2 = dput (dput mm k2 v2) k1 v1.
  Proof.
    intros. destruct mm as [m|]; simpl. 2: reflexivity.
    destr (key_eqb k1 k2). {
      subst. destr (map.get m k2). 1: reflexivity.
      simpl. rewrite !map.get_put_same. reflexivity.
    }
    destr (map.get m k1); simpl.
    + destr (map.get m k2); simpl. 1: reflexivity.
      rewrite map.get_put_diff by assumption.
      rewrite E0. reflexivity.
    + rewrite map.get_put_diff by congruence.
      destr (map.get m k2); simpl. 1: reflexivity.
      rewrite map.get_put_diff by assumption.
      rewrite E0.
      f_equal.
      apply map.put_comm.
      assumption.
  Qed.

  Lemma fold_dput_comm: forall p q, map.fold dput (Some p) q = map.fold dput (Some q) p.
  Proof.
    intros. eapply map.fold_spec.
    - symmetry. clear q.
      eapply map.fold_spec.
      + reflexivity.
      + intros. subst r. simpl. rewrite H. reflexivity.
    - intros. subst. rewrite <- map.fold_comm.
      + f_equal. simpl. rewrite H. reflexivity.
      + intros. apply dput_comm.
  Qed.

  Lemma du_comm: forall p q, du p q = du q p.
  Proof.
    intros. unfold du. destruct p; destruct q; try reflexivity.
    apply fold_dput_comm.
  Qed.

(*
  Lemma fold_dput_assoc: forall p q r,
      map.fold dput (map.fold dput (Some p) q) r = du (Some p) (map.fold dput (Some q) r).
  Proof.
    simpl.
*)

  Lemma du_assoc: forall p q r, du (du p q) r = du p (du q r).
  Proof.
    intros. unfold du.
    destruct p as [p|]. 2: reflexivity.
    destruct q as [q|]. 2: reflexivity.
    destruct r as [r|]. 2: destruct (map.fold dput (Some p) q); reflexivity.
    rewrite (fold_dput_comm q r).
    eapply map.fold_two_spec with (P := fun m fold1 fold2 =>
      match fold1 with
      | Some a => map.fold dput (Some a) r
      | None => None
      end =
      match fold2 with
      | Some b => map.fold dput (Some p) b
      | None => None
      end).
    1: reflexivity.
    intros.

(*
    destr (map.fold dput (Some q) r); destr (map.fold dput (Some p) q).
    - rewrite (fold_dput_comm p r0). rewrite <- E.
      admit.
    - rewrite fold_dput_comm. rewrite <- E. simpl.

    - rewrite <- E0. rewrite (fold_dput_comm p r0). rewrite <- E.
      rewrite (fold_dput_comm q).
    -
 *)
  Admitted.

  Lemma dus'_dus: forall xs, dus' xs = dus xs.
  Proof.
    induction xs; [reflexivity|].
    cbn -[du]. destruct xs.
    - cbn -[du]. apply du_empty_r.
    - cbn [dus' fold_right]. unfold dus' in *. cbn [fold_right] in IHxs.
      rewrite IHxs.
      reflexivity.
  Qed.

  Lemma dus_cons: forall (P: option map) (Ps: list (option map)),
      dus (P :: Ps) = du P (dus Ps).
  Proof. intros. rewrite <-! dus'_dus. reflexivity. Qed.

  Lemma dus_app: forall Ps Qs : list (option map),
      dus (Ps ++ Qs) = du (dus Ps) (dus Qs).
  Proof.
    induction Ps; intros.
    - cbn -[du]. simpl. symmetry. apply du_empty_l.
    - rewrite <- List.app_comm_cons. rewrite !dus_cons. rewrite IHPs.
      symmetry. apply du_assoc.
  Qed.

End __. End mmap.

Notation "a \*/ b" := (mmap.du a b) (at level 34, left associativity).

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
  Context {width: Z} {word: Word.Interface.word width} {word_ok: word.ok word}.
  Context {mem: map.map word byte} {mem_ok: map.ok mem}.

  Definition tree_to_du: Tree.t (option mem) -> option mem := Tree.interp id mmap.du.

  Lemma dus_flatten: forall t: Tree.t (option mem),
      mmap.dus (Tree.flatten t) = tree_to_du t.
  Proof.
    induction t; [reflexivity|].
    simpl. rewrite mmap.dus_app. rewrite IHt1, IHt2. reflexivity.
  Qed.

  Lemma tree_to_du_eq_of_flatten_eq: forall LHS RHS : Tree.t (option mem),
      mmap.dus (Tree.flatten LHS) = mmap.dus (Tree.flatten RHS) ->
      tree_to_du LHS = tree_to_du RHS.
  Proof. intros. rewrite! dus_flatten in H. exact H. Qed.

  Section cancel_lemmas.
    Let nth n xs := hd (@Some mem map.empty) (skipn n xs).
    Let remove_nth n (xs : list (option mem)) := firstn n xs ++ tl (skipn n xs).

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

    Lemma cancel_at: forall (i j: nat) (xs ys: list (option mem)),
        nth i xs = nth j ys ->
        mmap.dus (remove_nth i xs) = mmap.dus (remove_nth j ys) ->
        mmap.dus xs = mmap.dus ys.
    Proof.
      intros.
      rewrite <-(dus_nth_to_head i xs).
      rewrite <-(dus_nth_to_head j ys).
      f_equal; assumption.
    Qed.
  End cancel_lemmas.

  Definition one_byte(addr: word)(b: byte): option mem := Some (map.singleton addr b).

  Definition bytes(addr: word){n: nat}(bs: tuple byte n): option mem :=
    Some (map.of_tuple (Memory.footprint addr n) bs).

  Definition array{T: Type}(elem: word -> T -> option mem)(size: word): word -> list T -> option mem :=
    fix rec addr ls :=
      match ls with
      | [] => Some map.empty
      | e :: es => elem addr e \*/ rec (word.add addr size) es
      end.

  Definition one(sz: Syntax.access_size.access_size)(addr value: word): option mem :=
    bytes addr (LittleEndian.split (@Memory.bytes_per width sz) (word.unsigned value)).

  Definition word_array: word -> list word -> option mem :=
    array (one access_size.word) (word.of_Z (bytes_per_word width)).

  Definition instr(addr: word)(inst: Instruction): option mem :=
    one access_size.four addr (word.of_Z (encode inst)).

  Definition program(addr: word)(prog: list Instruction): option mem :=
    array instr (word.of_Z 4) addr prog.
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
