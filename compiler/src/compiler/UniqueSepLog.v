(* "Unique Separation Logic":
   If all separation logic predicates are either False or only acccept one unique
   heaplet, we can use `option mem` to represent them rather than `mem -> Prop`.
   The advantage of this representation is that it's easier to go from a separation
   logic predicate P to a memory: Instead of `forall m: mem, P m -> ... m ...`,
   which requires quantification, we can just say `defined P /\ ... force P ...` *)
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Byte.
Require Import coqutil.Decidable.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Datatypes.HList.
Require Import coqutil.Tactics.Tactics.
Require Import compiler.Simp.
Require Import bedrock2.Memory.
Require Import bedrock2.Syntax.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Encode.

Axiom TODO: False.

Module map. Section __.
  Context {key value} {map : map.map key value} {ok: map.ok map}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.

  Lemma put_comm: forall k1 k2 v1 v2 m,
      k1 <> k2 ->
      map.put (map.put m k1 v1) k2 v2 = map.put (map.put m k2 v2) k1 v1.
  Proof.
    intros. apply map.map_ext. intros.
    rewrite ?map.get_put_dec.
    destr (key_eqb k2 k); destr (key_eqb k1 k); congruence.
  Qed.

  Definition singleton(k: key)(v: value): map := map.put map.empty k v.
End __. End map.

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
    Let nth n xs := hd (@None mem) (skipn n xs).
    Let remove_nth n (xs : list (option mem)) := firstn n xs ++ tl (skipn n xs).

    Lemma cancel_at: forall (i j: nat) (xs ys: list (option mem)),
        nth i xs = nth j ys ->
        mmap.dus (remove_nth i xs) = mmap.dus (remove_nth j ys) ->
        mmap.dus xs = mmap.dus ys.
    Proof.
    Admitted.
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
  | |- @eq (option (@map.rep _ _ _)) ?LHS ?RHS =>
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
