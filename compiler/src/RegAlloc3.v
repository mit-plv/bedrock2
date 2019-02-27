Require Import lib.fiat_crypto_tactics.Test.
Require Import Coq.ZArith.ZArith.
Require Import compiler.FlatImp.
Require Import coqutil.Decidable.
Require Import Coq.Lists.List.
Require Import riscv.Utility.
Require Import coqutil.Macros.unique.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Solver.
Require Import compiler.util.Set.
Require Import compiler.util.Tactics.
Require Import coqutil.Map.TestLemmas.
Require Import compiler.util.SetSolverTests.

(*
Section TODO.
  Context {K V: Type}.
  Context {Mf: MapFunctions K V}.
  (*
  Axiom get_in_domain: forall k m, k \in (domain m) -> exists v, get m k = Some v.
  Axiom domain_put: forall k v m, domain (put m k v) = union (domain m) (singleton_set k).
  *)

  (* specs *)
  Axiom put_put_same: forall k v1 v2 m, put (put m k v1) k v2 = put m k v2.
  Axiom reverse_reverse_get: forall k v m, reverse_get m v = Some k -> get m k = Some v.
  Axiom get_in_range: forall k v m, get m k = Some v -> v \in range m.
  Axiom remove_by_value_spec: forall k v m, get (remove_by_value m v) k <> Some v.

  (* TODO some of this should go into state calculus *)
  (* probably derived *)
  Axiom not_in_range_of_remove_by_value: forall m v, ~ v \in range (remove_by_value m v).
  Axiom extends_remove_by_value: forall m v, extends m (remove_by_value m v).

  Axiom remove_by_value_put: forall k v m,
      remove_by_value (put m k v) v = remove_by_value m v.
  Axiom remove_by_value_idemp: forall v m,
      remove_by_value (remove_by_value m v) v = remove_by_value m v.
  Axiom extends_remove_by_value_same: forall x m1 m2,
      extends m1 m2 ->
      extends (remove_by_value m1 x) (remove_by_value m2 x).
  Axiom equality_by_extends: forall m1 m2,
      extends m1 m2 ->
      extends m2 m1 ->
      m1 = m2. (* requires functional extensionality, or unique internal representation *)
End TODO.

Local Notation "'bind_opt' x <- a ; f" :=
  (match a with
   | Some x => f
   | None => None
   end)
  (right associativity, at level 70, x pattern).


Section Live.

  Context {p: unique! Syntax.parameters}.

  (* we need a computable set of vars *)
  Context {varset: SetFunctions Syntax.varname}.
  Local Notation vars := (set Syntax.varname).

  (* set of variables which is certainly written while executing s *)
  Fixpoint certainly_written(s: stmt): vars :=
    match s with
    | SLoad _ x _ | SStore _ x _ | SLit x _ | SOp x _ _ _ | SSet x _ => singleton_set x
    | SIf cond s1 s2 => intersect (certainly_written s1) (certainly_written s2)
    | SLoop s1 cond s2 => certainly_written s1
    | SSeq s1 s2 => union (certainly_written s1) (certainly_written s2)
    | SSkip => empty_set
    | SCall argnames fname resnames => of_list resnames
    | SInteract argnames fname resnames => of_list resnames    end.

  Definition live_bcond(cond: bcond) : vars :=
    match cond with
    | CondBinary _ x y =>
        union (singleton_set x) (singleton_set y)
    | CondNez x =>
        singleton_set x
    end.

  (* set of variables which is live before executing s *)
  Fixpoint live(s: stmt): vars :=
    match s with
    | SLoad _ x y  => singleton_set y
    | SStore _ x y => union (singleton_set x) (singleton_set y)
    | SLit x v     => empty_set
    | SOp x op y z => union (singleton_set y) (singleton_set z)
    | SSet x y     => singleton_set y
    | SIf cond s1 s2   => union (live_bcond cond) (union (live s1) (live s2))
    | SLoop s1 cond s2 => union (live s1) (diff (union (live_bcond cond) (live s2))
                                                (certainly_written s1))
    | SSeq s1 s2       => union (live s1) (diff (live s2) (certainly_written s1))
    | SSkip => empty_set
    | SCall argnames fname resnames => of_list argnames
    | SInteract argnames fname resnames => of_list argnames
    end.

End Live.

Section RegAlloc.

  Variable srcvar: Type.
  Context {srcvar_eq_dec: DecidableEq srcvar}.
  Variable impvar: Type.
  Context {impvar_eq_dec: DecidableEq impvar}.
  Variable func: Type.
  Context {func_eq_dec: DecidableEq func}.
  Variable act: Type.
  Context {act_eq_dec: DecidableEq act}.

  Context {mapping: coqutil.Map.Interface.map.map impvar srcvar}.

  Context {srcvarset: SetFunctions srcvar}.
  Context {impvarset: SetFunctions impvar}.
  Local Notation srcvars := (set Syntax.varname).
  Local Notation impvars := (set Syntax.varname).

  Instance srcparams: Syntax.parameters := {|
    Syntax.varname := srcvar;
    Syntax.funname := func;
    Syntax.actname := act;
  |}.

  Instance impparams: Syntax.parameters := {|
    Syntax.varname := impvar;
    Syntax.funname := func;
    Syntax.actname := act;
  |}.

  (* annotated statement: each assignment is annotated with impvar which it assigns,
     loop has map invariant *)
  Inductive astmt: Type :=
    | ASLoad(sz: Syntax.access_size.access_size)(x: srcvar)(x': impvar)(a: srcvar)
    | ASStore(sz: Syntax.access_size.access_size)(a: srcvar)(v: srcvar)
    | ASLit(x: srcvar)(x': impvar)(v: Z)
    | ASOp(x: srcvar)(x': impvar)(op: Syntax.bopname.bopname)(y z: srcvar)
    | ASSet(x: srcvar)(x': impvar)(y: srcvar)
    | ASIf(cond: bcond)(bThen bElse: astmt)
    | ASLoop(body1: astmt)(cond: bcond)(body2: astmt)
    | ASSeq(s1 s2: astmt)
    | ASSkip
    | ASCall(binds: list (srcvar * impvar))(f: func)(args: list srcvar)
    | ASInteract(binds: list (srcvar * impvar))(f: func)(args: list srcvar).

  Local Notation stmt  := (@FlatImp.stmt srcparams). (* input type *)
  Local Notation stmt' := (@FlatImp.stmt impparams). (* output type *)

  Ltac head e :=
    match e with
    | ?a _ => head a
    | _ => e
    end.

  Goal forall (s: stmt), False.
    intro s.
    destruct s eqn: E;
    match type of E with
    | _ = ?r => let h := head r in idtac "| set ( case :=" h ")"
    end.
  Abort.

  Definition loop_inv(mappings: mapping -> astmt -> mapping)
                     (m: mapping)(s1 s2: astmt): mapping. Admitted.
  (*  intersect_map m (mappings (mappings m s1) s2). *)

  (* impvar -> srcvar mappings which are guaranteed to hold after running s
     (under-approximation) *)
  Definition mappings :=
    fix rec(m: mapping)(s: astmt): mapping :=
      match s with
      | ASLoad _ x x' _ | ASLit x x' _ | ASOp x x' _ _ _ | ASSet x x' _ =>
          (* if several impvars store the value of x, they won't all store the value of
             x after the update, but only x' will, because only x' is written in the target
             program, so we first have to remove the others *)
          map.put (* (remove_by_value m x) *) m x' x
      | ASStore _ a v => m
      | _ => m (*
      | ASIf cond s1 s2 => intersect_map (rec m s1) (rec m s2)
      | ASLoop s1 cond s2 => rec (loop_inv rec m s1 s2) s1
      | ASSeq s1 s2 => rec (rec m s1) s2
      | ASSkip => m
      | ASCall binds f args => empty_map (* TODO *)
      | ASInteract binds f args => empty_map (* TODO *) *)
      end.

  Variable dummy_impvar: impvar.

  (*
  Definition start_interval(current: srcvars * impvars * map impvar srcvar)(x: srcvar)
    : srcvars * impvars * map impvar srcvar :=
    let '(o, a, m) := current in
    let o := union o (singleton_set x) in
    let '(r, a) := pick_or_else a dummy_impvar in
    let m := put m r x in
    (o, a, m).

  Variable available_impvars: impvars.

  Definition annotate_assignment(s: stmt)(y: impvar): astmt :=
    match s with
    | SLoad x a => ASLoad x y a
    | SLit x v => ASLit x y v
    | SOp x op a b => ASOp x y op a b
    | SSet x a => ASSet x y a
    | _ => ASSkip (* not an assignment *)
    end.

  Definition TODO_annotate_bcond(cond: @bcond srcparams): @bcond impparams. Admitted.
  *)

  Fixpoint regalloc
           (m: mapping)          (* current mapping *)
           (s: stmt)             (* current sub-statement *)
           (l: srcvars)          (* variables which have a life after statement s,
                                    but we don't care in what register they end up *)
           (r: mapping)          (* requirements on what variables registers should contain
                                    at the end (i.e variables which have a life after s,
                                    and moreover have to be in a specific register *)
           {struct s}
    : astmt.                     (* annotated statement *) Admitted. (*
    :=
    (* variables which currently occupy a register (maybe unjustified) *)
    let o_original := range m in
    (* these are the variables which actually deserve to occupy a register: *)
    let o := union (live s) (diff (union l (range r)) (certainly_written s)) in
    (* intervals which ended... *)
    let became_dead := diff o_original o in
    (* ... allow us to prune m: *)
    let m := remove_values m became_dead in
    (* *currently* available registers *)
    let a := diff available_impvars (union (domain m) (domain r)) in
    match s with
    | SLoad x _ | SLit x _ | SOp x _ _ _ | SSet x _ =>
        match reverse_get r x with
        | Some y => (* no matter whether a new interval for x starts here or not,
                       we're told where to put it by r *)
                    annotate_assignment s y
        | None => match reverse_get m x with
                  | Some y => (* nothing to do because no new interval starts *)
                              annotate_assignment s y
                  | None   => (* new interval starts *)
                              let y := fst (pick_or_else a dummy_impvar) in
                              annotate_assignment s y
                  end
        end
    | SStore x y => ASStore x y
    | SIf cond s1 s2   =>
        let s1' := regalloc m s1 l r in
        let s2' := regalloc m s2 l r in
        ASIf (TODO_annotate_bcond cond) s1' s2'
    | SLoop s1 cond s2 =>
        let s1' := regalloc m s1 (union (union (live_bcond cond) (live s2)) l) r in
        let s2' := regalloc (mappings m s1') s2 empty_set m in
        ASLoop s1' (TODO_annotate_bcond cond) s2'
    | SSeq s1 s2 =>
        let s1' := regalloc m s1 (union (live s2) (diff l (certainly_written s2))) r
                                 (* it would be nice to to this, but then the removed
                                    variables would be considered "available forever",
                                    instead of "available until the final value is
                                    assigned to it"
                                 (remove_values r (certainly_written s2)) *) in
        let s2' := regalloc (mappings m s1') s2 l r in
        ASSeq s1' s2'
    | SSkip => ASSkip
  (*| SCall argnames fname resnames => fold_left start_interval resnames (o, a, m) *)
    | SCall _ _ _ => ASSkip (* TODO *)
    | SInteract _ _ _ => ASSkip (* TODO *)
    end.

  Hint Resolve
       extends_put_same
       extends_remove_by_value_same
       extends_intersect_map_lr
       extends_refl
    : map_hints.

  Hint Rewrite
       remove_by_value_put
       remove_by_value_idemp
    : map_rew.

  Hint Extern 1 => autorewrite with map_rew : map_hints.

  Lemma mappings_monotone: forall s m1 m2,
      extends m1 m2 ->
      extends (mappings m1 s) (mappings m2 s).
  Proof.
    induction s; intros; simpl in *; unfold loop_inv in *; eauto 7 with map_hints.
  Qed.

  Lemma mappings_intersect_map: forall s m1 m2,
      mappings (intersect_map m1 m2) s = intersect_map (mappings m1 s) (mappings m2 s).
  Proof.
    induction s; intros; simpl in *; unfold loop_inv; eauto with map_hints.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - rewrite IHs1.
      (* used to hold at some point
      rewrite IHs2.
      forget (mappings m1 s1) as m11.
      forget (mappings m1 s2) as m12.
      forget (mappings m2 s1) as m21.
      forget (mappings m2 s2) as m22.
      rewrite? intersect_map_assoc.
      f_equal.
      rewrite <-? intersect_map_assoc.
      f_equal.
      apply intersect_map_comm.
    - rewrite IHs1. rewrite IHs2. rewrite IHs1.
      forget (mappings (mappings (mappings m2 s1) s2) s1) as m2121.
      forget (mappings (mappings (mappings m1 s1) s2) s1) as m1121.
      forget (mappings m1 s1) as m11.
      forget (mappings m2 s1) as m21.
      rewrite? intersect_map_assoc.
      f_equal.
      rewrite <-? intersect_map_assoc.
      f_equal.
      apply intersect_map_comm.
    - rewrite IHs1. rewrite IHs2. reflexivity.
  Qed.
       *)
  Admitted.

  Lemma mappings_mappings_extends_mappings: forall s m,
      extends (mappings (mappings m s) s) (mappings m s).
  Proof.
    induction s; intros; simpl in *;
      try solve [
            (* these can be specialized infinitely many times with themselves *)
            try clear IHs;
            try clear IHs1;
            try clear IHs2;
            map_solver impvar srcvar ].
    - apply intersect_map_extends.
      +
  Admitted.

  Lemma mappings_bw_monotone: forall s m1 m2,
      bw_extends m1 m2 ->
      bw_extends (mappings m1 s) (mappings m2 s).
  Proof using.
    induction s; intros; simpl in *; unfold loop_inv in *; eauto 7 with map_hints.
    admit. admit. admit. admit.
    admit.
    eapply IHs1.
    (* TODO not sure! *)
  Admitted.

  Lemma mappings_idemp: forall s m1 m2,
      m2 = mappings m1 s ->
      mappings m2 s = m2.
  Proof.
    induction s; intros; simpl in *;
      try reflexivity;
      try (subst; apply put_put_same).
(*
    {
      erewrite IHs1 with (m2 := m2); [erewrite IHs2 with (m2 := m2)|].
      subst.
      - admit. (* ok *)
      - symmetry. eapply IHs2. (* stuck in a loop *)
*)
  Admitted.

  Definition reverse_get_cond (m: map impvar srcvar) (cond: @bcond srcparams)
    : option (@bcond impparams) :=
    match cond with
    | CondBinary op x y =>
        bind_opt x' <- reverse_get m x;
        bind_opt y' <- reverse_get m y;
        Some (@CondBinary impparams op x' y')
    | CondNez x =>
        bind_opt x' <- reverse_get m x;
        Some (@CondNez impparams x')
    end.
  *)

  Existing Instance srcparams.
  (* ugly hack to change typeclass precedence, TODO how can we make Coq pick up the right
     instance automatically? *)

  Definition checker :=
    fix rec(m: mapping)(s: astmt): option stmt' :=
      match s with
(*
      | ASLoad x x' a =>
          bind_opt a' <- reverse_get m a;
          Some (@SLoad impparams x' a')
      | ASStore a v =>
          bind_opt a' <- reverse_get m a;
          bind_opt v' <- reverse_get m v;
          Some (@SStore impparams a' v')
      | ASLit x x' v =>
          Some (@SLit impparams x' v)
      | ASOp x x' op y z =>
          bind_opt y' <- reverse_get m y;
          bind_opt z' <- reverse_get m z;
          Some (@SOp impparams x' op y' z')
      | ASSet x x' y =>
          bind_opt y' <- reverse_get m y;
          Some (@SSet impparams x' y')
      | ASIf cond s1 s2 =>
          bind_opt cond' <- reverse_get_cond m cond;
          bind_opt s1' <- rec m s1;
          bind_opt s2' <- rec m s2;
          Some (SIf cond' s1' s2')
      | ASLoop s1 cond s2 =>
          let m1 := loop_inv mappings m s1 s2 in
          let m2 := mappings m1 s1 in
          bind_opt cond' <- reverse_get_cond m2 cond;
          bind_opt s1' <- rec m1 s1;
          bind_opt s2' <- rec m2 s2;
          Some (SLoop s1' cond' s2')
      | ASSeq s1 s2 =>
          bind_opt s1' <- rec m s1;
          bind_opt s2' <- rec (mappings m s1) s2;
          Some (SSeq s1' s2')
      | ASSkip => Some SSkip
      | ASCall binds f args => None (* TODO *)
      | ASInteract binds f args => None (* TODO *)
*)
      | _ => None (* TODO *)
      end.

  Definition erase :=
    fix rec(s: astmt): stmt :=
      match s with
      | ASLoad sz x x' a => SLoad sz x a
      | ASStore sz a v => SStore sz a v
      | ASLit x x' v => SLit x v
      | ASOp x x' op y z => SOp x op y z
      | ASSet x x' y => SSet x y
(*
      | ASIf cond s1 s2 => SIf cond (rec s1) (rec s2)
      | ASLoop s1 cond s2 => SLoop (rec s1) cond (rec s2)
*)
      | ASSeq s1 s2 => SSeq (rec s1) (rec s2)
      | ASSkip => SSkip
      | ASCall binds f args => SCall (List.map fst binds) f args
      | ASInteract binds f args => SCall (List.map fst binds) f args
      | _ => SSkip
      end.

  Definition register_allocation(s: stmt)(mBegin mEnd: mapping): option stmt' :=
    let annotated := regalloc mBegin s empty_set mEnd in
    checker mBegin annotated.

  (* claim: for all astmt a, if checker succeeds and returns s', then
     (erase a) behaves the same as s' *)

  Context {W: Utility.Words} {mem: map.map word byte}.
  Context {srcLocals: map.map srcvar word}.
  Context {impLocals: map.map impvar word}.
  Context {srcEnv: map.map func (list srcvar * list srcvar * stmt)}.
  Context {impEnv: map.map func (list impvar * list impvar * stmt')}.

  Axiom TODO: False.

  Local Set Refine Instance Mode.

  Instance srcFlatImpParams: Semantics.parameters := {|
    FlatImp.syntax_params := srcparams;
    FlatImp.locals := srcLocals;
  |}.
  all: case TODO.
  Defined.

  Definition eval (*: nat -> srcLocals -> mem -> stmt -> option (srcLocals * mem)*)
    := eval_stmt map.empty.

  Instance impFlatImpParams: FlatImp.parameters := {|
    FlatImp.syntax_params := impparams;
    FlatImp.locals := impLocals;
  |}.
  all: case TODO.
  Defined.

  Definition eval' (*: nat -> map impvar mword -> mem -> stmt' -> option (map impvar mword * mem)*)
    := eval_stmt map.empty.

  (*
  Definition states_compat(st: map srcvar mword)(r: map impvar srcvar)(st': map impvar mword) :=
    forall (x: srcvar) (w: mword),
      (* TODO restrict to live variables *)
      get st x = Some w ->
      exists (x': impvar), get r x' = Some x /\ get st' x' = Some w.
  *)

  Definition states_compat(st: srcLocals)(r: mapping)(st': impLocals) :=
    forall (x: srcvar) (x': impvar),
      map.get r x' = Some x ->
      forall w,
        map.get st x = Some w ->
        map.get st' x' = Some w.

  (*
  Lemma states_compat_put: forall st1 st1' v x x' r,
      ~ x \in (range r) ->
      states_compat st1 r st1' ->
      states_compat (map.put st1 x v) (map.put r x' x) (map.put st1' x' v).
  Proof.
    unfold states_compat.
    intros.
    rewrite get_put.
    do 2 match goal with
    | H: get (put _ _ _) _ = _ |- _ => rewrite get_put in H
    end.
    destruct_one_match; clear E.
    - subst.
      replace x0 with x in H2 by congruence.
      destruct_one_match_hyp; [assumption|contradiction].
    - destruct_one_match_hyp.
      + subst.
        apply get_in_range in H1.
        contradiction.
      + eauto.
  Qed.

  Lemma states_compat_extends: forall st st' r1 r2,
      extends r1 r2 ->
      states_compat st r1 st' ->
      states_compat st r2 st'.
  Proof.
    unfold states_compat. eauto.
  Qed.

  Hint Resolve
       states_compat_put
       not_in_range_of_remove_by_value
       states_compat_extends
       extends_remove_by_value
       extends_intersect_map_l
       extends_intersect_map_r
    : checker_hints.

  Lemma loop_inv_init: forall r s1 s2,
      extends r (loop_inv mappings r s1 s2).
  Proof.
    intros. unfold loop_inv. eauto with checker_hints.
  Qed.

  (* depends on unproven mappings_intersect_map mappings_mappings_extends_mappings *)
  Lemma loop_inv_step: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      extends (mappings (mappings Inv s1) s2) Inv.
  Proof.
    intros. subst Inv. unfold loop_inv.
    change (mappings (mappings r s1) s2) with (mappings r (ASSeq s1 s2)).
    change (mappings (mappings (intersect_map r (mappings r (ASSeq s1 s2))) s1) s2)
      with (mappings (intersect_map r (mappings r (ASSeq s1 s2))) (ASSeq s1 s2)).
    forget (ASSeq s1 s2) as s. clear s1 s2.
    rewrite mappings_intersect_map.
    eapply extends_trans; [|apply extends_intersect_map_r].
    apply intersect_map_extends.
    - apply extends_refl.
    - apply mappings_mappings_extends_mappings.
  Qed.

  Lemma test: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      False.
  Proof.
    intros.
    pose proof (loop_inv_step r s1 s2) as P. simpl in P.
    change (mappings (mappings (loop_inv mappings r s1 s2) s1) s2) with
           (mappings (mappings Inv s1) s2) in P.
    unfold loop_inv in P.
    (* "extends _ (intersect_map _ _)" is useless *)
  Abort.

  Lemma loop_inv_step_bw: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      bw_extends (mappings (mappings Inv s1) s2) Inv.
  Proof using.
    intros. subst Inv. unfold loop_inv.
  Admitted.

  Lemma extends_loop_inv: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      extends Inv (loop_inv mappings Inv s1 s2).
  Proof.
    intros.
    subst Inv. unfold loop_inv.
    apply extends_intersect_map_lr.
    - apply extends_intersect_map_l.
    - apply mappings_monotone. apply mappings_monotone.
      apply extends_intersect_map_l.
  Qed.

  Lemma bw_extends_loop_inv: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      bw_extends Inv (loop_inv mappings Inv s1 s2).
  Proof using.
  Admitted.

  (* this direction would be needed to get full idempotence of loop_inv *)
  Lemma loop_inv_extends: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      extends (loop_inv mappings Inv s1 s2) Inv.
  Proof.
    intros. subst Inv.
    unfold loop_inv.
    change (mappings (mappings r s1) s2) with (mappings r (ASSeq s1 s2)).
    change (mappings (mappings (intersect_map r (mappings r (ASSeq s1 s2))) s1) s2)
      with (mappings (intersect_map r (mappings r (ASSeq s1 s2))) (ASSeq s1 s2)).
    forget (ASSeq s1 s2) as s. clear s1 s2.
    remember (intersect_map r (mappings r s)) as r1.
  (*
  Proof.
    intros. unfold extends, loop_inv. intros.
    apply intersect_map_spec.
    split; [assumption|].

    pose proof mappings_monotone as P. unfold extends in P.
    eapply P.

    subst Inv. unfold loop_inv.
    set (a := (intersect_map r (mappings (mappings r s1) s2))).

    pose proof extends_loop_inv as Q. simpl in Q.*)
  Abort.

  Lemma loop_inv_idemp: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      loop_inv mappings Inv s1 s2 = Inv.
  Proof using .
  Abort.
  *)

  Definition precond(m: mapping)(s: astmt): mapping :=
    match s with
    | ASLoop s1 cond s2 => loop_inv mappings m s1 s2
    | _ => m
    end.

  (*
  Lemma precond_weakens: forall m s,
      extends m (precond m s).
  Proof.
    intros. destruct s; try apply extends_refl.
    unfold precond, loop_inv.
    apply extends_intersect_map_l.
  Qed.

  Hint Resolve precond_weakens : checker_hints.
   *)

  Lemma checker_correct: forall n r st1 st1' m1 st2 m2 s annotated s',
      eval n st1 m1 s = Some (st2, m2) ->
      erase annotated = s ->
      checker r annotated = Some s' ->
      states_compat st1 (precond r annotated) st1' ->
      exists st2',
        eval' n st1' m1 s' = Some (st2', m2) /\
        states_compat st2 (mappings r annotated) st2'.
  Proof. Admitted. (*
    induction n; intros; [
      match goal with
      | H: eval 0 _ _ _ = Some _ |- _ => solve [inversion H]
      end
    |].
    unfold eval, eval' in *.
    invert_eval_stmt;
      try destruct_pair_eqs;
      match goal with
      | H: erase ?s = _ |- _ =>
        destruct s;
        inversion H;
        subst;
        clear H
      end;
      subst;
      match goal with
      | H: checker _ ?x = _ |- _ => pose proof H as C; remember x as AS in C
      end;
      simpl in *;
      repeat (destruct_one_match_hyp; [|discriminate]);
      repeat match goal with
             | H: Some _ = Some _ |- _ => inversion H; subst; clear H
             | H: reverse_get _ _ = Some _ |- _ =>
                  let H' := fresh H "_rrg" in
                  unique pose proof (reverse_reverse_get _ _ _ H) as H'
             | H: states_compat _ _ _ |- _ => erewrite H by eassumption
             end;
      repeat match goal with
             | H: states_compat _ _ _ |- _ => erewrite H by eassumption
             | H: _ = _ |- _ => rewrite H
             end;
      repeat (rewrite reg_eqb_ne by congruence);
      repeat (rewrite reg_eqb_eq by congruence);
      eauto with checker_hints.
    - clear Case_SIf_Then.
      edestruct IHn as [st2' [? ?]]; eauto with checker_hints.
    - clear Case_SIf_Else.
      edestruct IHn as [st2' [? ?]]; eauto with checker_hints.
    - clear Case_SLoop_Done.
      edestruct IHn as [st2' [? ?]]; eauto with checker_hints.
      rewrite H0.
      pose proof H1 as P.
      unfold states_compat in P.
      specialize P with (2 := H).
      rewrite P.
      + rewrite reg_eqb_eq by reflexivity. eauto.
      + eassumption.

    - clear Case_SLoop_NotDone.
      pose proof E0 as C1. pose proof E1 as C2.
      eapply IHn in E0; [| |reflexivity|]; [|eassumption|]; cycle 1. {
        eapply states_compat_extends; [|eassumption].
        apply precond_weakens.
      }
      destruct_products.
      eapply IHn in E1; [| |reflexivity|]; [|eauto with checker_hints..].
      destruct_products.
      (* get rid of r and replace it by Inv everywhere *)
      remember (loop_inv mappings r annotated1 annotated2) as Inv.
      (* Search r. only HeqInv and C *)
      specialize IHn with (annotated := (ASLoop annotated1 cond annotated2)).
      move IHn at bottom.
      specialize IHn with (r := r).
      specialize IHn with (2 := eq_refl).
      specialize IHn with (1 := H).
      specialize IHn with (s' := SLoop s i s0).
      edestruct IHn as [? [? ?]].
      + exact C.
      + unfold precond.
        eapply states_compat_extends; [|eassumption].
        subst Inv.
        apply loop_inv_step.
      + eexists.
        rewrite_match.
        pose proof E0r as P.
        unfold states_compat in P.
        erewrite P by eassumption. clear P.
        rewrite reg_eqb_ne by congruence.
        split; [eassumption|].
        simpl in H1.
        subst Inv.
        assumption.

    - clear Case_SSeq.
      eapply IHn in E.
      destruct_products.
      eapply IHn in E0.
      destruct_products.
      eexists.
      rewrite El. all: typeclasses eauto with core checker_hints.
    - clear Case_SCall.
      discriminate.
  Qed.

  Lemma regalloc_respects_afterlife: forall s m l r,
      (* TODO say something about r *)
      subset l (union (range m) (certainly_written s)) ->
      subset l (range (mappings m (regalloc m s l r))).
  Proof.
    induction s; intros;
      [ set ( case := SLoad )
      | set ( case := SStore )
      | set ( case := SLit )
      | set ( case := SOp )
      | set ( case := SSet )
      | set ( case := SIf )
      | set ( case := SLoop )
      | set ( case := SSeq )
      | set ( case := SSkip )
      | set ( case := SCall )
      | set ( case := SInteract ) ];
      move case at top;
      simpl in *;
      repeat (destruct_one_match); simpl in *.
    (*
    {
      rename H into AA.
      pose proof @reverse_get_Some as PP.
      specialize PP with (1 := E). clear E.
      revert AA PP.

      Notation "A ⟹ B" := (A -> B)  (at level 99, right associativity,
                                     format "A  ⟹  '/' B" ).
      (* Nitpick found no counterexample *)
      admit.
    }
    Focus 11. {
      remember (union (certainly_written s1) (certainly_written s2)) as c1.
      remember (union (live s1) (diff (live s2) (certainly_written s1))) as m1.
      remember (remove_values m (diff (range m) (union m1 (diff l c1)))) as m2.
      remember (regalloc m2 s1 (union (live s2) l)) as R1.
      remember (regalloc (mappings m2 R1) s2 l) as R2.
      specialize (IHs1 m2 (union (live s2) l)). rewrite <- HeqR1 in IHs1.
      specialize (IHs2 (mappings m2 R1) l). rewrite <-HeqR2 in IHs2.

      match type of IHs2 with
      | _ -> subset _ ?X => apply subset_trans with (s4 := X)
      end.
      admit.
      admit.
     *)
  Admitted.

  Lemma checker_monotone: forall r1 r2 s s',
      extends r2 r1 ->
      checker r1 s = Some s' ->
      checker r2 s = Some s'.
  Proof using.
  Admitted.

  Lemma regalloc_succeeds: forall s annotated m l r,
      (* TODO restrictions on l and r *)
      subset (live s) (range m) ->
      regalloc m s l r = annotated ->
      exists s', checker m annotated = Some s'.
  Proof.
    induction s; intros; simpl in *;
      [ set ( case := ASLoad )
      | set ( case := ASStore )
      | set ( case := ASLit )
      | set ( case := ASOp )
      | set ( case := ASSet )
      | set ( case := ASIf )
      | set ( case := ASLoop )
      | set ( case := ASSeq )
      | set ( case := ASSkip )
      | set ( case := ASCall )
      | set ( case := ASInteract ) ];
      move case at top;
      repeat (subst ||
              destruct_pair_eqs ||
              (destruct_one_match_hyp; try discriminate) ||
              (destruct_one_match; try discriminate));
      simpl.
    - (* ASLoad: reverse_get of regalloc Some *)
      destruct (reverse_get m a) eqn: F.
      + (* reverse_get of checker Some *)
        eexists. reflexivity.
      + (* reverse_get of checker None *)
        exfalso. map_solver impvar srcvar.
    - (* ASLoad: reverse_get of regalloc None --> a fresh var will be picked *)
      destruct (reverse_get m a) eqn: F.
      + (* reverse_get of checker Some *)
        eexists. reflexivity.
      + (* reverse_get of checker None *)
        exfalso. map_solver impvar srcvar.

    - destruct (reverse_get m a) eqn: F; destruct (reverse_get m v) eqn: G;
        [eexists; reflexivity| (exfalso; map_solver impvar srcvar)..].
    - eauto.
    - eauto.
    - destruct (reverse_get m y) eqn: F; destruct (reverse_get m z) eqn: G;
        [eexists; reflexivity| (exfalso; map_solver impvar srcvar)..].
    - destruct (reverse_get m y) eqn: F; destruct (reverse_get m z) eqn: G;
        [eexists; reflexivity| (exfalso; map_solver impvar srcvar)..].
    - destruct (reverse_get m y) eqn: F;
        [eexists; reflexivity| (exfalso; map_solver impvar srcvar)..].
    - destruct (reverse_get m y) eqn: F;
        [eexists; reflexivity| (exfalso; map_solver impvar srcvar)..].
    - destruct (reverse_get m cond) eqn: F; [| exfalso; map_solver impvar srcvar].
      repeat match goal with
      | IH: _ |- context [ checker _ (regalloc ?m' ?s ?l') ] =>
        specialize IH with (m := m') (l := l') (2 := eq_refl)
      end.
      destruct IHs1 as [s1' IHs1].
      { clear IHs2. map_solver impvar srcvar. }
      destruct IHs2 as [s2' IHs2].
      { clear IHs1. map_solver impvar srcvar. }
      eapply checker_monotone in IHs1; [ rewrite IHs1 | map_solver impvar srcvar ].
      eapply checker_monotone in IHs2; [ rewrite IHs2 | map_solver impvar srcvar ].
      eexists. reflexivity.
    - (* TODO maybe SLoop case of regalloc is bad! *)
      admit.
    - match goal with
      | |- context [ checker _ (regalloc ?m' ?s ?l') ] =>
        specialize IHs1 with (m := m') (l := l') (2 := eq_refl)
      end.
      destruct IHs1 as [s1' IHs1].
      { clear IHs2. map_solver impvar srcvar. }
      eapply checker_monotone in IHs1; [ rewrite IHs1 | map_solver impvar srcvar ].
      clear IHs1.
      match goal with
      | |- context [ checker _ (regalloc ?m' ?s ?l') ] =>
        specialize IHs2 with (m := m') (l := l') (2 := eq_refl)
      end.
      destruct IHs2 as [s2' IHs2].
      {
        remember (remove_values m
             (diff (range m)
                (union (union (live s1) (diff (live s2) (certainly_written s1)))
                       (diff l (union (certainly_written s1) (certainly_written s2))))))
                 as m1.
        specialize (regalloc_respects_afterlife s1 m1 (union (live s2)
                                                             (diff l (certainly_written s2)))).
        intro R.
        match type of R with
        | ?A -> _ => assert A; [| solve [map_solver impvar srcvar] ]
        end.
        clear R.
        subst.
        map_solver impvar srcvar.
        {
          destruct (dec (x \in certainly_written s1)); [solve[ auto ] |].
          left.
          map_solver impvar srcvar.
        }
        {
          destruct (dec (x \in certainly_written s1)); [solve[ auto ] |].
          left.
          destruct Hx as [k Hx].
          - destruct (dec (x \in live s1)); auto.
            destruct (dec (x \in live s2)); auto.
            right.
            exfalso.
            map_solver impvar srcvar.
            admit.
          - exists k.
            map_solver impvar srcvar. (* TODO this one should succeed *)
            exfalso.
            apply c_r.
            destruct (dec (s \in live s1)); auto.
            destruct (dec (s \in live s2)); auto.
            intuition auto.
        }
      }
      eapply checker_monotone in IHs2; [ rewrite IHs2; eexists; reflexivity |  ].
      clear IHs2.
      apply mappings_monotone.
      map_solver impvar srcvar.
    - eauto.
    - eauto.
  Abort.
  *)

End RegAlloc.
*)
