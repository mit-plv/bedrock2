Require Import Coq.Program.Tactics.
Require Import compiler.FlatImp.
Require Import compiler.util.MapSolverTest.
Require Import compiler.Decidable.
Require Import Coq.Lists.List.
Require Import riscv.Utility.
Require Import compiler.Op.
Require Import compiler.util.Map.
Require Import compiler.util.Set.
Require Import compiler.Memory.
Require Import compiler.util.Tactics.

Section TODO.
  Context {K V: Type}.
  Context {Mf: MapFunctions K V}.

  Local Instance Kset: SetFunctions K := map_domain_set.
  Local Instance Vset: SetFunctions V := map_range_set.

  (*
  Axiom get_in_domain: forall k m, k \in (domain m) -> exists v, get m k = Some v.
  Axiom domain_put: forall k v m, domain (put m k v) = union (domain m) (singleton_set k).
  *)

  (* specs
  Axiom put_spec: forall m k1 k2 v,
      (k1 = k2 /\ get (put m k1 v) k2 = Some v) \/ (k1 <> k2 /\ get (put m k1 v) k2 = get m k2).

  Axiom put_put_same: forall k v1 v2 m, put (put m k v1) k v2 = put m k v2.
  Axiom reverse_reverse_get: forall k v m, reverse_get m v = Some k -> get m k = Some v.
  *)
  Axiom get_in_range: forall k v m, get m k = Some v -> v \in range m.
  (*
  Axiom remove_by_value_spec: forall k v m, get (remove_by_value m v) k <> Some v.
  Axiom get_intersect_map: forall k v m1 m2,
      get (intersect_map m1 m2) k = Some v <-> get m1 k = Some v /\ get m2 k = Some v.
  *)

  Axiom union_comm: forall s1 s2,
      union s1 s2 = union s2 s1.

  Axiom put_remove_same: forall m k v,
    put (remove_key m k) k v = put m k v.

  (* TODO some of this should go into state calculus *)
  (* probably derived *)
  Axiom not_in_range_of_remove_by_value: forall m v, ~ v \in range (remove_by_value m v).
  Axiom extends_remove_by_value: forall m v, extends m (remove_by_value m v).
  Axiom extends_intersect_map_l: forall r1 r2, extends r1 (intersect_map r1 r2).
  Axiom extends_intersect_map_r: forall r1 r2, extends r2 (intersect_map r1 r2).
  Axiom extends_intersect_map_lr: forall m11 m12 m21 m22,
      extends m11 m21 ->
      extends m12 m22 ->
      extends (intersect_map m11 m12) (intersect_map m21 m22).
  Axiom intersect_empty_map_l: forall m, intersect_map empty_map m = m.
  Axiom intersect_empty_map_r: forall m, intersect_map m empty_map = m.

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

  Axiom intersect_map_put_put_same: forall m1 m2 k v,
      intersect_map (put m1 k v) (put m2 k v) = put (intersect_map m1 m2) k v.
  Axiom intersect_map_remove_by_value: forall m1 m2 x,
      intersect_map (remove_by_value m1 x) (remove_by_value m2 x)
      = remove_by_value (intersect_map m1 m2) x.

  Axiom intersect_map_assoc: forall m1 m2 m3,
      intersect_map (intersect_map m1 m2) m3 = intersect_map m1 (intersect_map m2 m3).
  Axiom intersect_map_comm: forall m1 m2,
      intersect_map m1 m2 = intersect_map m2 m1.

  Axiom remove_keys_update_map_remove_keys: forall m R U,
      remove_keys (update_map (remove_keys m R) U) R =
      remove_keys (update_map m U) R.
  Axiom update_map_remove_keys_update_map: forall m R U,
      update_map (remove_keys (update_map m U) R) U =
      update_map (remove_keys m R) U.

  Axiom remove_values_update_map_remove_values: forall m R U,
      remove_values (update_map (remove_values m R) U) R =
      remove_values (update_map m U) R.
  Axiom update_map_remove_values_update_map: forall m R U,
      update_map (remove_values (update_map m U) R) U =
      update_map (remove_values m R) U.

  Axiom update_map_with_singleton: forall m k v,
      update_map m (put empty_map k v) = put m k v.
  Axiom update_map_with_empty: forall m,
      update_map m empty_map = m.

  Axiom remove_keys_empty_set: forall m,
      remove_keys m empty_set = m.
  Axiom remove_keys_singleton_set: forall m k,
      remove_keys m (singleton_set k) = remove_key m k.

  Axiom remove_values_empty_set: forall m,
      remove_values m empty_set = m.
  Axiom remove_values_singleton_set: forall m v,
      remove_values m (singleton_set v) = remove_by_value m v.

  Axiom domain_update_map: forall m1 m2,
      subset (domain (update_map m1 m2)) (union (domain m1) (domain m2)) /\
      subset (union (domain m1) (domain m2)) (domain (update_map m1 m2)).
  Axiom range_update_map: forall m1 m2,
      subset (range (update_map m1 m2)) (union (range m1) (range m2)).

  Axiom range_update_map_r: forall m1 m2,
      subset (range m2) (range (update_map m1 m2)).

  Axiom domain_intersect_map: forall m1 m2,
      subset (domain (intersect_map m1 m2)) (intersect (domain m1) (domain m2)).

  Axiom range_intersect_map: forall m1 m2,
      subset (range (intersect_map m1 m2)) (intersect (range m1) (range m2)).

  (* easy but mostly useless *)
  Lemma update_map_extends: forall m1 m2 m3,
      extends m1 m3 ->
      extends m2 m3 ->
      extends (update_map m1 m2) m3.
  Proof.
    unfold extends. intros.
    destruct (get m2 x) eqn: E.
    - apply get_update_map_r.
      apply H0.
      assumption.
    - rewrite get_update_map_l; eauto.
  Qed.

  Lemma update_map_extends_disjoint: forall m1 m2 m3 m4,
      extends m1 m3 ->
      extends m2 m4 ->
      disjoint (domain m1) (domain m2) ->
      extends (update_map m1 m2) (update_map m3 m4).
  Proof.
    unfold extends. intros.
    destruct (get m4 x) eqn: E.
    - apply get_update_map_r.
      erewrite get_update_map_r in H2 by eassumption.
      apply H0.
      congruence.
    - erewrite get_update_map_l in H2 by eassumption.
      destruct (get m2 x) eqn: F.
      + unfold disjoint in H1.
        specialize (H1 x).
        do 2 rewrite domain_spec in H1.
        exfalso.
        intuition eauto.
      + rewrite get_update_map_l; eauto.
  Qed.

  Lemma extends_remove_values_union_l: forall m vs1 vs2,
      extends (remove_values m vs1) (remove_values m (union vs1 vs2)).
  Proof.
    unfold extends. intros.
    destruct (get m x) eqn: F.
    - destruct (contains_dec v (union vs1 vs2)) as [E|N].
      + pose proof remove_values_removed as P.
        specialize P with (1 := F) (2 := E).
        rewrite P in H.
        discriminate.
      + pose proof remove_values_not_removed as P.
        specialize P with (1 := F) (2 := N).
        rewrite P in H.
        inversion H; subst; clear H.
        apply remove_values_not_removed; [eassumption|].
        intro C.
        apply N.
        apply union_spec.
        left. apply C.
    - pose proof remove_values_never_there as P.
      specialize P with (1 := F).
      rewrite P in H.
      discriminate.
  Qed.

  Lemma extends_remove_values_union_r: forall m vs1 vs2,
      extends (remove_values m vs2) (remove_values m (union vs1 vs2)).
  Proof.
    intros.
    rewrite union_comm.
    apply extends_remove_values_union_l.
  Qed.

  Lemma remove_values_spec: forall m vs k,
      get (remove_values m vs) k =
      match get m k with
      | Some v => if dec (v \in vs) then None else Some v
      | None => None
      end.
  Admitted.

  Lemma disjoint_domain_remove_values_range: forall m1 m2,
      disjoint (domain (remove_values m1 (range m2))) (domain m2).
  Proof.
    unfold disjoint.
    intros.
    destruct (contains_dec x (domain m2)) as [HIn | HNotIn]; [left|right;assumption].
    intro C.
    rewrite domain_spec in HIn, C.
    destruct_products.
    rewrite remove_values_spec in C.
    repeat (destruct_one_match_hyp; try discriminate).
    inversion C; subst; clear C.
    clear E0.
    rewrite range_spec in n.
    apply n.
    exists x.
  Abort.

  Lemma intersect_map_1234_1423: forall m1 m2 m3 m4,
      intersect_map (intersect_map m1 m2) (intersect_map m3 m4) =
      intersect_map (intersect_map m1 m4) (intersect_map m2 m3).
  Proof.
    intros.
    rewrite? intersect_map_assoc.
    f_equal.
    rewrite <- intersect_map_assoc.
    rewrite intersect_map_comm.
    reflexivity.
  Qed.

End TODO.

Local Notation "'bind_opt' x <- a ; f" :=
  (match a with
   | Some x => f
   | None => None
   end)
  (right associativity, at level 70, x pattern, only parsing).


Section RegAlloc.

  Variable srcvar: Set.
  Variable impvar: Set.
  Variable func: Set.
  Context {func_eq_dec: DecidableEq func}.

  Hypothesis func_empty: func = Empty_set.

  Context {Map: MapFunctions impvar srcvar}.
  Local Instance srcvarSet: SetFunctions srcvar := map_range_set.
  Local Instance impvarSet: SetFunctions impvar := map_domain_set.
  Notation srcvars := (@set srcvar srcvarSet).
  Notation impvars := (@set impvar impvarSet).
  Local Instance srcvar_eq_dec: DecidableEq srcvar := set_elem_eq_dec.
  Local Instance impvar_eq_dec: DecidableEq impvar := set_elem_eq_dec.

  (* annotated statement: each assignment is annotated with impvar which it assigns,
     loop has map invariant *)
  Inductive astmt: Type :=
    | ASLoad(x: srcvar)(x': impvar)(a: srcvar)
    | ASStore(a: srcvar)(v: srcvar)
    | ASLit(x: srcvar)(x': impvar)(v: Z)
    | ASOp(x: srcvar)(x': impvar)(op: bopname)(y z: srcvar)
    | ASSet(x: srcvar)(x': impvar)(y: srcvar)
    | ASIf(cond: bcond srcvar)(bThen bElse: astmt)
    | ASLoop(body1: astmt)(cond: bcond srcvar)(body2: astmt)
    | ASSeq(s1 s2: astmt)
    | ASSkip
    | ASCall(binds: list (srcvar * impvar))(f: func)(args: list srcvar).

  Local Notation stmt  := (FlatImp.stmt srcvar func). (* input type *)
  Local Notation stmt' := (FlatImp.stmt impvar func). (* output type *)

  Definition guaranteed_updates :=
    fix rec(s: astmt): map impvar srcvar :=
      match s with
      | ASLoad x x' _ | ASLit x x' _ | ASOp x x' _ _ _ | ASSet x x' _ =>
          put empty_map x' x
      | ASStore a v => empty_map
      | ASIf cond s1 s2 => intersect_map (rec s1) (rec s2)
      | ASLoop s1 cond s2 => rec s1
      | ASSeq s1 s2 => update_map (rec s1) (rec s2)
      | ASSkip => empty_map
      | ASCall binds f args => fold_left (fun m '(x, x') => put m x' x) binds empty_map
      end.

  Definition possibly_written_srcvars :=
    fix rec(s: astmt): set srcvar :=
      match s with
      | ASLoad x x' _ | ASLit x x' _ | ASOp x x' _ _ _ | ASSet x x' _ =>
          singleton_set x
      | ASStore a v => empty_set
      | ASIf _ s1 s2 | ASLoop s1 _ s2 | ASSeq s1 s2 => union (rec s1) (rec s2)
      | ASSkip => empty_set
      | ASCall binds f args =>
        fold_left (fun s '(x, x') => union s (singleton_set x)) binds empty_set
      end.

  Definition possibly_written_impvars :=
    fix rec(s: astmt): set impvar :=
      match s with
      | ASLoad x x' _ | ASLit x x' _ | ASOp x x' _ _ _ | ASSet x x' _ =>
          singleton_set x'
      | ASStore a v => empty_set
      | ASIf _ s1 s2 | ASLoop s1 _ s2 | ASSeq s1 s2 => union (rec s1) (rec s2)
      | ASSkip => empty_set
      | ASCall binds f args =>
        fold_left (fun s '(x, x') => union s (singleton_set x')) binds empty_set
      end.

  Definition updateWith_modular(m: map impvar srcvar)(s: astmt): map impvar srcvar :=
    let m := remove_values m (possibly_written_srcvars s) in
    let m := remove_keys m (possibly_written_impvars s) in
    update_map m (guaranteed_updates s).

  Lemma guaranteed_updates_are_possibly_written_srcvars: forall s,
      subset (range (guaranteed_updates s)) (possibly_written_srcvars s).
  Proof.
    induction s; simpl; try (
      repeat intro;
      repeat match goal with
             | |- _ => progress autorewrite with rew_map_specs rew_set_op_specs in *
             | H: _ /\ _ |- _ => destruct H
             | E: exists y, _ |- _ => let yf := fresh y in destruct E as [yf E]
             | H: context[if ?e then _ else _] |- _ => destruct e
             (* needed because of https://github.com/coq/coq/issues/8635 *)
             | H: _ |- _ => rewrite get_put in H
             end;
      congruence).
    - pose proof (range_intersect_map (guaranteed_updates s1) (guaranteed_updates s2)).
      set_solver_generic srcvar.
    - pose proof (range_intersect_map (guaranteed_updates s1) (guaranteed_updates s2)).
      set_solver_generic srcvar.
    - pose proof (range_update_map (guaranteed_updates s1) (guaranteed_updates s2)).
      set_solver_generic srcvar.
    - rewrite func_empty in f. destruct f.
  Qed.

  Lemma guaranteed_updates_are_possibly_written_impvars: forall s,
      subset (domain (guaranteed_updates s)) (possibly_written_impvars s).
  Proof.
    induction s; simpl; try (
      repeat intro;
      repeat match goal with
             | |- _ => progress autorewrite with rew_map_specs rew_set_op_specs in *
             | H: _ /\ _ |- _ => destruct H
             | E: exists y, _ |- _ => let yf := fresh y in destruct E as [yf E]
             | H: context[if ?e then _ else _] |- _ => destruct e
             (* needed because of https://github.com/coq/coq/issues/8635 *)
             | H: _ |- _ => rewrite get_put in H
             end;
      congruence).
    - pose proof (domain_intersect_map (guaranteed_updates s1) (guaranteed_updates s2)).
      set_solver_generic impvar.
    - pose proof (domain_intersect_map (guaranteed_updates s1) (guaranteed_updates s2)).
      set_solver_generic impvar.
    - pose proof (domain_update_map (guaranteed_updates s1) (guaranteed_updates s2)).
      set_solver_generic impvar.
    - rewrite func_empty in f. destruct f.
  Qed.

  (* impvar -> srcvar mappings which are guaranteed to hold after running s
     (under-approximation) *)
  Definition updateWith_recursive :=
    fix rec(m: map impvar srcvar)(s: astmt): map impvar srcvar :=
      match s with
      | ASLoad x x' _ | ASLit x x' _ | ASOp x x' _ _ _ | ASSet x x' _ =>
          (* if several impvars store the value of x, they won't all store the value of
             x after the update, but only x' will, because only x' is written in the target
             program, so we first have to remove the others *)
          put (remove_by_value m x) x' x
      | ASStore a v => m
      | ASIf cond s1 s2 => intersect_map (rec m s1) (rec m s2)
      | ASLoop s1 cond s2 =>
          (* mi = map if loop was repeated i times *)
          let m0 := rec m s1 in
          let m1 := rec (rec m0 s2) s1 in
          (*
          let m2 := rec (rec m1 s2) s1 in
          let m3 := rec (rec m2 s2) s1 in
          ...
          all further fixpoint iterations will do the same, so m1=m2=m3=...,
          so no need to perform them *)
          intersect_map m0 m1
      | ASSeq s1 s2 => rec (rec m s1) s2
      | ASSkip => m
      | ASCall binds f args => empty_map (* TODO *)
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
       intersect_map_put_put_same
       intersect_map_remove_by_value
       intersect_empty_map_l
       intersect_empty_map_r
    : map_rew.

  Hint Extern 1 => autorewrite with map_rew : map_hints.

  (*
  Lemma updateWith_monotone: forall s m1 m2,
      extends m1 m2 ->
      extends (updateWith m1 s) (updateWith m2 s).
  Proof.
    induction s; intros; simpl in *; eauto 7 with map_hints.
  Qed.

  Lemma updateWith_intersect_map: forall s m1 m2,
      updateWith (intersect_map m1 m2) s = intersect_map (updateWith m1 s) (updateWith m2 s).
  Proof.
    induction s; intros; simpl in *; eauto with map_hints.
    - rewrite IHs1. rewrite IHs2.
      forget (updateWith m1 s1) as m11.
      forget (updateWith m1 s2) as m12.
      forget (updateWith m2 s1) as m21.
      forget (updateWith m2 s2) as m22.
      rewrite? intersect_map_assoc.
      f_equal.
      rewrite <-? intersect_map_assoc.
      f_equal.
      apply intersect_map_comm.
    - rewrite IHs1. rewrite IHs2. rewrite IHs1.
      forget (updateWith (updateWith (updateWith m2 s1) s2) s1) as m2121.
      forget (updateWith (updateWith (updateWith m1 s1) s2) s1) as m1121.
      forget (updateWith m1 s1) as m11.
      forget (updateWith m2 s1) as m21.
      rewrite? intersect_map_assoc.
      f_equal.
      rewrite <-? intersect_map_assoc.
      f_equal.
      apply intersect_map_comm.
    - rewrite IHs1. rewrite IHs2. reflexivity.
  Qed.

  Lemma updateWith_updateWith_extends_updateWith: forall s m,
      extends (updateWith (updateWith m s) s) (updateWith m s).
  Proof.
    induction s; intros; simpl in *; eauto with map_hints.

    (* rewrite? updateWith_intersect_map.*)


    - state_calc_generic impvar srcvar.
      rewrite get_intersect_map in *.
      destruct H.
  Abort.

  Lemma updateWith_extends_updateWith_updateWith: forall s m,
      extends (updateWith m s) (updateWith (updateWith m s) s).
  Proof.
  Abort.

  Lemma updateWith_121: forall s1 s2 m,
      updateWith (updateWith (updateWith m s1) s2) s1 = updateWith (updateWith m s2) s1.
  Proof.
    induction s1; intros; simpl in *; eauto with map_hints.
    Focus 6. {

  Admitted.

  Lemma updateWith_idemp_wishful: forall s m,
      updateWith (updateWith m s) s = updateWith m s.
  Proof.
    intros. apply (updateWith_121 s ASSkip m).
  Qed.
  *)

  Lemma updateWith_idemp: forall s m,
      updateWith_modular (updateWith_modular m s) s = updateWith_modular m s.
  Proof.
    intros.
    unfold updateWith_modular.
    remember (possibly_written_srcvars s) as R1.
    remember (possibly_written_impvars s) as R2.
    remember (guaranteed_updates s) as U.
    (* TODO express remove_values in terms of "remove preimage"
    rewrite remove_values_update_map_remove_values.
    rewrite remove_keys_update_map_remove_keys.
    rewrite update_map_remove_keys_update_map.
    reflexivity.
  Qed. *)
  Admitted.

  Definition updateWith := updateWith_recursive.

  Definition reverse_get_cond (m: map impvar srcvar) (cond: bcond srcvar) 
    : option (bcond impvar) :=
    match cond with
    | CondBinary op x y =>
        bind_opt x' <- reverse_get m x;
        bind_opt y' <- reverse_get m y;
        Some (CondBinary op x' y')
    | CondNez x =>
        bind_opt x' <- reverse_get m x;
        Some (CondNez x')
    end.
    
(*
    | CondBeq _ x y =>
        bind_opt x' <- reverse_get m x;
        bind_opt y' <- reverse_get m y;
        Some (CondBeq impvar x' y')
    | CondBne _ x y =>
        bind_opt x' <- reverse_get m x;
        bind_opt y' <- reverse_get m y;
        Some (CondBne impvar x' y')
    | CondBlt _ x y =>
        bind_opt x' <- reverse_get m x;
        bind_opt y' <- reverse_get m y;
        Some (CondBlt impvar x' y')
    | CondBge _ x y =>
        bind_opt x' <- reverse_get m x;
        bind_opt y' <- reverse_get m y;
        Some (CondBge impvar x' y')
    | CondBltu _ x y =>
        bind_opt x' <- reverse_get m x;
        bind_opt y' <- reverse_get m y;
        Some (CondBltu impvar x' y')
    | CondBgeu _ x y =>
        bind_opt x' <- reverse_get m x;
        bind_opt y' <- reverse_get m y;
        Some (CondBgeu impvar x' y')
    | CondBnez _ x =>
        bind_opt x' <- reverse_get m x;
        Some (CondBnez impvar x')
    | CondTrue _ =>
        Some (CondTrue impvar)
    | CondFalse _ =>
        Some (CondFalse impvar)
    end.
*)

  Definition checker :=
    fix rec(m: map impvar srcvar)(s: astmt): option stmt' :=
      match s with
      | ASLoad x x' a =>
          bind_opt a' <- reverse_get m a;
          Some (SLoad x' a')
      | ASStore a v =>
          bind_opt a' <- reverse_get m a;
          bind_opt v' <- reverse_get m v;
          Some (SStore a' v')
      | ASLit x x' v =>
          Some (SLit x' v)
      | ASOp x x' op y z =>
          bind_opt y' <- reverse_get m y;
          bind_opt z' <- reverse_get m z;
          Some (SOp x' op y' z')
      | ASSet x x' y =>
          bind_opt y' <- reverse_get m y;
          Some (SSet x' y')
      | ASIf cond s1 s2 =>
          bind_opt cond' <- reverse_get_cond m cond;
          bind_opt s1' <- rec m s1;
          bind_opt s2' <- rec m s2;
          Some (SIf cond' s1' s2')
      | ASLoop s1 cond s2 =>
          bind_opt cond' <- reverse_get_cond m cond;
          let m1 := intersect_map m (updateWith m s) in
          let m2 := intersect_map (updateWith m s1) (updateWith m1 s) in
          bind_opt s1' <- rec m1 s1;
          bind_opt s2' <- rec m2 s2;
          Some (SLoop s1' cond' s2')
      | ASSeq s1 s2 =>
          bind_opt s1' <- rec m s1;
          bind_opt s2' <- rec (updateWith m s1) s2;
          Some (SSeq s1' s2')
      | ASSkip => Some SSkip
      | ASCall binds f args => None (* TODO *)
      end.

  Definition erase :=
    fix rec(s: astmt): stmt :=
      match s with
      | ASLoad x x' a => SLoad x a
      | ASStore a v => SStore a v
      | ASLit x x' v => SLit x v
      | ASOp x x' op y z => SOp x op y z
      | ASSet x x' y => SSet x y
      | ASIf cond s1 s2 => SIf cond (rec s1) (rec s2)
      | ASLoop s1 cond s2 => SLoop (rec s1) cond (rec s2)
      | ASSeq s1 s2 => SSeq (rec s1) (rec s2)
      | ASSkip => SSkip
      | ASCall binds f args => SCall (List.map fst binds) f args
      end.

  (* claim: for all astmt a, if checker succeeds and returns s', then
     (erase a) behaves the same as s' *)

  Context {mword: Set}.
  Context {MW: MachineWidth mword}.
  Context {srcStateMap: MapFunctions srcvar mword}.
  Context {impStateMap: MapFunctions impvar mword}.
  Context {srcFuncMap: MapFunctions func (list srcvar * list srcvar * stmt)}.
  Context {impFuncMap: MapFunctions func (list impvar * list impvar * stmt')}.

  Definition eval: nat -> map srcvar mword -> mem -> stmt -> option (map srcvar mword * mem)
    := eval_stmt _ _ empty_map.

  Definition eval': nat -> map impvar mword -> mem -> stmt' -> option (map impvar mword * mem)
    := eval_stmt _ _ empty_map.

  (*
  Definition states_compat(st: map srcvar mword)(r: map impvar srcvar)(st': map impvar mword) :=
    forall (x: srcvar) (w: mword),
      (* TODO restrict to live variables *)
      get st x = Some w ->
      exists (x': impvar), get r x' = Some x /\ get st' x' = Some w.
  *)

  Definition states_compat(st: map srcvar mword)(r: map impvar srcvar)(st': map impvar mword) :=
    forall (x: srcvar) (x': impvar),
      get r x' = Some x ->
      forall w,
        get st x = Some w ->
        get st' x' = Some w.

  Lemma states_compat_put: forall st1 st1' v x x' r,
      ~ x \in (range r) ->
      states_compat st1 r st1' ->
      states_compat (put st1 x v) (put r x' x) (put st1' x' v).
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

  (*
  Lemma updateWith_alt1: forall s m,
      extends (updateWith' m s) (updateWith m s).
  Proof.
    induction s; intros; unfold updateWith in *; simpl in *;
      rewrite? @update_map_with_singleton;
      rewrite? @remove_keys_singleton_set;
      rewrite? @remove_values_singleton_set;
      rewrite? @update_map_with_empty;
      rewrite? @remove_keys_empty_set;
      rewrite? @remove_values_empty_set;
      rewrite? @put_remove_same;
      eauto with map_hints checker_hints.
    - specialize (IHs1 m).
      specialize (IHs2 m).
      pose proof (guaranteed_updates_are_possibly_written_srcvars s1).
      pose proof (guaranteed_updates_are_possibly_written_srcvars s2).
      pose proof (guaranteed_updates_are_possibly_written_impvars s1).
      pose proof (guaranteed_updates_are_possibly_written_impvars s2).
      (*
      clear func_empty.
      forget (possibly_written_srcvars s1) as ps1.
      forget (possibly_written_impvars s1) as pi1.
      forget (possibly_written_srcvars s2) as ps2.
      forget (possibly_written_impvars s2) as pi2.
      forget (guaranteed_updates s1) as g1.
      forget (guaranteed_updates s2) as g2.
      forget (updateWith' m s1) as u1.
      forget (updateWith' m s2) as u2.
      *)

      (* Adding this makes it go from 13s to 33s (seems the wrong way round!)
         Reason:
         If we keep cond, it will be used to specialize some hypotheses, which seems
         useless, but in this specific example, it results in a hypothesis with a more
         desirable destruction candidate being the last hypothesis

      repeat match goal with
             | H: ?P |- _ => progress tryif (let T := type of P in unify T Prop)
                               then idtac else clear H
             end.
       *)

      Time map_solver impvar srcvar.

    - repeat match goal with
      | IH: forall (m: map impvar srcvar), extends (updateWith' m ?s) _
        |- context[updateWith' ?m' ?s]
        => let IH' := fresh IH "_" in unique pose proof (IH m') as IH'
      end.
      pose proof (guaranteed_updates_are_possibly_written_srcvars s1).
      pose proof (guaranteed_updates_are_possibly_written_srcvars s2).
      pose proof (guaranteed_updates_are_possibly_written_impvars s1).
      pose proof (guaranteed_updates_are_possibly_written_impvars s2).
      clear func_empty.
      repeat match goal with
             | H: ?P |- _ => progress tryif (let T := type of P in unify T Prop)
                               then idtac else clear H
             end.

      Time map_solver impvar srcvar.

    - repeat match goal with
      | IH: forall (m: map impvar srcvar), extends (updateWith' m ?s) _
        |- context[updateWith' ?m' ?s]
        => let IH' := fresh IH "_" in unique pose proof (IH m') as IH'
      end.
      pose proof (guaranteed_updates_are_possibly_written_srcvars s1).
      pose proof (guaranteed_updates_are_possibly_written_srcvars s2).
      pose proof (guaranteed_updates_are_possibly_written_impvars s1).
      pose proof (guaranteed_updates_are_possibly_written_impvars s2).


      clear func_empty.
      clear IHs1 IHs2.
      repeat match goal with
             | H: ?P |- _ => progress tryif (let T := type of P in unify T Prop)
                               then revert H else clear H
             end.
      set (f1 := fun m0 => updateWith' m0 s1). change (updateWith' m s1) with (f1 m).
      set (f2 := fun m0 => updateWith' m0 s2). change (updateWith' (f1 m) s2) with (f2 (f1 m)).
      forget (possibly_written_srcvars s1) as ps1.
      forget (possibly_written_impvars s1) as pi1.
      forget (possibly_written_srcvars s2) as ps2.
      forget (possibly_written_impvars s2) as pi2.
      forget (guaranteed_updates s1) as g1.
      forget (guaranteed_updates s2) as g2.



      Definition is_empty{E: Type}{SF: SetFunctions E}(s: set E): Prop := subset s empty_set.
      assert (is_empty pi1 <-> is_empty ps1) as IE1 by admit.
      assert (is_empty pi2 <-> is_empty ps2) as IE2 by admit.
      unfold is_empty in *.
      destruct IE1. destruct IE2. revert H H0 H1 H2.

      clearbody f1 f2. clear s1 s2. clear func.
      (* Still doesn't hold:
Nitpick found a counterexample for card 'a = 1 and card 'b = 1:

  Free variables:
    f1 = (λx. _)(Map.empty := [a⇩1 ↦ b⇩1], [a⇩1 ↦ b⇩1] := Map.empty)
    f2 = (λx. _)(Map.empty := [a⇩1 ↦ b⇩1], [a⇩1 ↦ b⇩1] := Map.empty)
    g1 = [a⇩1 ↦ b⇩1]
    g2 = Map.empty
    m = Map.empty
    pi1 = {a⇩1}
    pi2 = {a⇩1}
    ps1 = {b⇩1}
    ps2 = {b⇩1}

But this counterexample has inconsistent g2, pi2 and ps2, but how to state that they
have to be consistent?
Need a "witness": multimap of possible_updates or list (disjunction) of possible update-maps
       *)
      admit.
    - admit.
  Abort.
*)

  Lemma checker_correct: forall n r st1 st1' m1 st2 m2 s annotated s',
      eval n st1 m1 s = Some (st2, m2) ->
      erase annotated = s ->
      checker r annotated = Some s' ->
      states_compat st1 r st1' ->
      exists st2',
        eval' n st1' m1 s' = Some (st2', m2) /\
        states_compat st2 (updateWith r annotated) st2'.
  Proof.
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
        subst *;
        clear H
      end;
      subst *;
      simpl in *;
      repeat (destruct_one_match_hyp; [|discriminate]);
      repeat match goal with
             | H: Some _ = Some _ |- _ => inversion H; subst *; clear H
             | H: reverse_get _ _ = Some _ |- _ => apply reverse_reverse_get in H
             | H: states_compat _ _ _ |- _ => erewrite H by eassumption
             end;
      repeat match goal with
             | H: states_compat _ _ _ |- _ => erewrite H by eassumption
             | H: _ = _ |- _ => rewrite H
             end;
      repeat (rewrite reg_eqb_ne by congruence);
      repeat (rewrite reg_eqb_eq by congruence);
      unfold updateWith in *;
      simpl;
      rewrite? @update_map_with_singleton;
      rewrite? @remove_values_singleton_set;
      rewrite? @update_map_with_empty;
      rewrite? @remove_keys_singleton_set;
      rewrite? @remove_values_empty_set;
      rewrite? @remove_keys_empty_set;
      rewrite? @put_remove_same;
      eauto with checker_hints.

    - admit.
    - admit.
    - admit.
    - admit.
    - (* if then *)
      edestruct IHn as [st2' [? ?]]; [ (eassumption || reflexivity).. | ].
      eexists; split; cycle 1.
      + clear IHn.
        eapply states_compat_extends; [|eassumption].
        admit.
      + (*
      pose proof (guaranteed_updates_are_possibly_written annotated1) as P1.
      pose proof (guaranteed_updates_are_possibly_written annotated2) as P2.
      pose proof (guaranteed_updates_are_possibly_written (ASIf cond annotated1 annotated2))
        as P3.
      simpl in P3.
      clear -impvar_eq_dec func_empty P1 P2 P3.
      *)

      admit.
    - admit.
    - admit.
    - (* loop not done *)
      admit.
    - (* SSeq *)
      admit.

(*
    - edestruct IHn as [st2' [? ?]]; [ (eassumption || reflexivity).. | ].
      eexists; split; [eassumption|].
      clear IHn.
      eapply states_compat_extends; [|eassumption].
      pose proof (guaranteed_updates_are_possibly_written annotated1) as P1.
      pose proof (guaranteed_updates_are_possibly_written annotated2) as P2.
      pose proof (guaranteed_updates_are_possibly_written (ASIf cond annotated1 annotated2))
        as P3.
      simpl in P3.
      clear -impvar_eq_dec func_empty P1 P2 P3.

      forget (possibly_written annotated1) as p1.
      forget (guaranteed_updates annotated1) as g1.
      forget (possibly_written annotated2) as p2.
      forget (guaranteed_updates annotated2) as g2.

      clear func_empty.

      repeat match goal with
             | H: ?P |- _ =>
               progress tryif (let T := type of P in unify T Prop)
                        then revert H else clear H
             end.

      apply update_map_extends_disjoint.
      + apply extends_remove_values_union_l.
      + apply extends_intersect_map_l.
      +

        pose proof (guaranteed_updates_are_possibly_written annotated1) as P.
        remember (possibly_written annotated1) as p1.
        remember (guaranteed_updates annotated1) as g1.
        remember (possibly_written annotated2) as p2.
        remember (guaranteed_updates annotated2) as g2.

        enough (disjoint (domain (remove_values r (range g1))) (domain g1)) as A.


        {
          admit. (* A, P *)
        }

      eauto with checker_hints.
    - edestruct IHn as [st2' [? ?]]; [ (eassumption || reflexivity).. | ].
      eauto with checker_hints.
    - edestruct IHn as [st2' [? ?]]; eauto with checker_hints.
      rewrite H0.
      pose proof H1 as P.
      unfold states_compat in P.
      specialize P with (2 := H).
      rewrite P.
      + rewrite reg_eqb_eq by reflexivity.
        eexists; split; [ reflexivity | ].
        eapply states_compat_extends; [|eassumption].

        eauto 10 with checker_hints.
        eauto with checker_hints.
*)

  Abort.

End RegAlloc.
