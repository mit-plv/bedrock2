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

Import List.ListNotations.
Require Import bbv.Word.
Require Import bedrock2.Semantics bedrock2.BasicC64Semantics bedrock2.Map.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Lemma get_sep {key value} {map : map key value} (a:key) (v:value) R m (H : sep (ptsto a v) R m) : map.get m a = Some v.
Admitted.
Lemma put_sep {key value} {map : map key value} (k:key) (v1:value) (v2:value) R m :
  sep (ptsto k v1) R m -> sep (ptsto k v2) R (map.put m k v2).
Admitted.
Lemma split_combine n a b : split n (Semantics.combine n a b) = (a, b).
Admitted.

Definition ptsto sz a v m := m = unchecked_store sz map.empty a v.
Lemma load_sep sz a v R m (H : sep (ptsto sz a v) R m) : load sz m a = Some v.
Admitted.
Lemma store_sep sz a v1 v2 R m (H : sep (ptsto sz a v1) R m)
      (Q : _ -> Prop) (HQ : forall m', sep (ptsto sz a v2) R m' -> Q m') :
  exists m', store sz m a v2 = Some m' /\ Q m'.
Admitted.

Ltac sep m Hm :=
  revert Hm; revert m;
  lazymatch goal with |- forall (x:?T), ?A x -> ?B x => change (@Lift1Prop.impl1 T A B) end;
  cancel; reflexivity.
Ltac intros_mem m Hm :=
  let m' := fresh in let Hm' := fresh in
  intros m' Hm'; clear m Hm; rename m' into m; rename Hm' into Hm.
Ltac t :=
  let m := lazymatch goal with m : @map.rep word byte mem |- _ => m end in
  let Hm := lazymatch goal with Hm : _ m |- _ => Hm end in
  lazymatch goal with
  |- load ?sz ?m ?a = Some _
    => lazymatch type of Hm with context [ptsto sz a ?v]
                             (* FIXME this VV Hm is dynamically scoped, not the Hm above *)
    => refine (load_sep sz a v ltac:(clear Hm m) m ltac:(sep m Hm)) end
  | |- exists _, store ?sz ?m ?a ?v2 = Some _ /\ _
    => lazymatch type of Hm with context [ptsto sz a ?v1]
    => refine (store_sep sz a v1 v2 ltac:(clear m Hm) m ltac:(sep m Hm) _ ?[cont]); intros_mem m Hm end
  | _ => first [ eassumption | eexists | subst; eexists ]
end.

Goal
  map.ok Semantics.mem ->
  forall a_addr a b_addr b (m:map.rep (value:=@Semantics.byte _)) R t,
    (sep (ptsto 1 a_addr a) (sep (ptsto 1 b_addr b) R)) m ->
  WeakestPrecondition.func
    (fun _ => True) (fun _ => False) (fun _ _ => True) (fun _ _ _ _ _ => False)
    (@swap BasicC64Syntax.parameters) t m (a_addr::b_addr::nil)
    (fun t' m' rets => t=t' /\ (sep (ptsto 1 a_addr b) (sep (ptsto 1 b_addr a) R)) m' /\ rets = nil).
Proof.
  intros. rename H0 into Hm.
  repeat t.
Qed.
  