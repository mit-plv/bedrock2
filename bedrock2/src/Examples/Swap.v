Require Import bedrock2.Macros bedrock2.Syntax.
Require Import bedrock2.StringNames bedrock2.BasicALU bedrock2.NotationsInConstr.

Import BinInt String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Section bsearch.
  Context {p : unique! StringNames.Syntax.parameters} {b : BasicALU.operations}.
  Local Coercion literal (z : Z) : expr := expr.literal z.
  Local Coercion var (x : String.string) : expr := expr.var x.

  Definition swap : list varname * list varname * cmd := (("a"::"b"::nil), nil, bedrock_func(
    "t" = *(uint8_t*) "b";
    *(uint8_t*) "b" = *(uint8_t*) "a";
    *(uint8_t*) "a" = "t"
  )).
End bsearch.

Require bedrock2.BasicC64Syntax.

Example swap_c_string := Eval compute in
  BasicC64Syntax.c_func "swap" swap.
(* Print swap_c_string. *)

Require Import bedrock2.BasicC64Semantics bedrock2.Map.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Import List.ListNotations Word.

Lemma get_sep {key value} {map : map key value} (a:key) (v:value) R m (H : sep (ptsto a v) R m) : map.get m a = Some v.
Admitted.
Lemma put_sep {key value} {map : map key value} (k:key) (v1:value) (v2:value) R m :
  sep (ptsto k v1) R m -> sep (ptsto k v2) R (map.put m k v2).
Admitted.
Lemma split_combine n a b : Semantics.split n (Semantics.combine n a b) = (a, b).
Admitted.

Goal
  map.ok Semantics.mem ->
  forall a_addr a b_addr b (m:map.rep (value:=@Semantics.byte _)) R t,
    (sep (ptsto a_addr a) (sep (ptsto b_addr b) R)) m ->
  WeakestPrecondition.func
    (fun _ => True) (fun _ => False) (fun _ _ => True) (fun _ _ _ _ _ => False)
    (@swap BasicC64Syntax.parameters) t m (a_addr::b_addr::nil)
    (fun t' m' rets => t=t' /\ (sep (ptsto a_addr b) (sep (ptsto b_addr a) R)) m' /\ rets = nil).
Proof.
  intros.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.

  change (BinIntDef.Z.to_nat 1) with 1%nat.
  unfold Semantics.load.
  unshelve erewrite (get_sep b_addr b); shelve_unifiable. reflexivity.
  revert H0. generalize m.
  instantiate (1 := ltac:(clear H0 m)).
  lazymatch goal with |- forall (x:?T) (H:?A x), ?B x => change (@Lift1Prop.impl1 T A B) end.
  cancel. reflexivity.

  eexists.
  eexists.
  subst; eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  subst; eexists.

  change (BinIntDef.Z.to_nat 1) with 1%nat.
  unfold Semantics.load.
  unshelve erewrite (get_sep a_addr a); shelve_unifiable. reflexivity.
  revert H0. generalize m.
  instantiate (1 := ltac:(clear H0 m)).
  lazymatch goal with |- forall (x:?T) (H:?A x), ?B x => change (@Lift1Prop.impl1 T A B) end.
  cancel. reflexivity.
  
  eexists.
  eexists.

  change (BinIntDef.Z.to_nat 1) with 1%nat.
  unfold Semantics.store.
  rewrite split_combine.
  unshelve erewrite (get_sep b_addr b); shelve_unifiable. reflexivity.
  revert H0. generalize m.
  instantiate (1 := ltac:(clear H0 m)).
  lazymatch goal with |- forall (x:?T) (H:?A x), ?B x => change (@Lift1Prop.impl1 T A B) end.
  cancel. reflexivity.
  intros.
  unshelve (let pf := open_constr:(put_sep b_addr b a _ m _) in pose proof pf); shelve_unifiable.
  revert H0.
  generalize m.
  instantiate (1 := ltac:(clear dependent m)).
  lazymatch goal with |- forall (x:?T) (H:?A x), ?B x => change (@Lift1Prop.impl1 T A B) end.
  cancel. reflexivity.
  rewrite <-H2 in H3. clear dependent m. rename m0 into m. rename H3 into H0.

  eexists.
  subst l; eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.

  change (BinIntDef.Z.to_nat 1) with 1%nat.
  unfold Semantics.store.
  rewrite split_combine.
  unshelve erewrite (get_sep a_addr a); shelve_unifiable. reflexivity.
  revert H0. generalize m.
  instantiate (1 := ltac:(clear dependent m)).
  lazymatch goal with |- forall (x:?T) (H:?A x), ?B x => change (@Lift1Prop.impl1 T A B) end.
  cancel. reflexivity.
  intros.
  unshelve (let pf := open_constr:(put_sep a_addr a b _ m _) in pose proof pf); shelve_unifiable.
  revert H0.
  generalize m.
  instantiate (1 := ltac:(clear dependent m)).
  lazymatch goal with |- forall (x:?T) (H:?A x), ?B x => change (@Lift1Prop.impl1 T A B) end.
  cancel. reflexivity.
  rewrite <-H1 in H2. clear dependent m. rename m0 into m. rename H2 into H0.

  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  assumption.
  eexists.
Qed.
  