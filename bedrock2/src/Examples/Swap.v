Require Import bedrock2.Macros bedrock2.Syntax.
Require Import bedrock2.BasicC64Syntax bedrock2.BasicALU bedrock2.NotationsInConstr.

Import BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Existing Instance bedrock2.BasicC64Syntax.Basic_bopnames_params.
Local Coercion literal (z : Z) : expr := expr.literal z.
Local Coercion var (x : string) : expr := expr.var x.

Definition swap := ("swap", (["a";"b"], ([]:list varname), bedrock_func_body:(
  "t" = *(uint8_t*) "b";;
  *(uint8_t*) "b" = *(uint8_t*) "a";;
  *(uint8_t*) "a" = "t"
))).

Definition swap_swap := ("swap_swap", (("a"::"b"::nil), ([]:list varname), bedrock_func_body:(
  cmd.call [] "swap" [var "a"; var "b"];;
  cmd.call [] "swap" [var "a"; var "b"]
))).

Require Import bedrock2.Semantics bedrock2.BasicC64Semantics bedrock2.Map.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require bedrock2.WeakestPrecondition bedrock2.WeakestPreconditionProperties.
Context (FIXME_MAP_OK : map.ok Semantics.mem).

(*
Lemma get_sep {key value} {map : map key value} (a:key) (v:value) R m (H : sep (ptsto a v) R m) : map.get m a = Some v.
Admitted.
Lemma put_sep {key value} {map : map key value} (k:key) (v1:value) (v2:value) R m :
  sep (ptsto k v1) R m -> sep (ptsto k v2) R (map.put m k v2).
Admitted.
Lemma split_combine n a b : split n (Semantics.combine n a b) = (a, b).
Admitted.
*)

Definition ptsto sz a v m := load sz m a = Some v.
Lemma load_sep sz a v R m (H : sep (ptsto sz a v) R m) : load sz m a = Some v.
  cbv [load ptsto] in *.
  revert H; revert R; revert v; revert a; revert m.
  generalize (BinIntDef.Z.to_nat sz) as n; clear sz.
  induction n.
  { intros; destruct H as (?&?&?&?&?); auto. }
  { intros.
    cbn [load_rec] in *.
    destruct H as (?&?&?&?&?).
    destruct (map.get x a) eqn:?; [|discriminate].
    { assert (map.get m a = Some b) by admit.
      rewrite H2.
      destruct (load_rec n x (word_succ a)) eqn:?; [|discriminate].
      { unshelve erewrite (_:load_rec n m (word_succ a) = Some w); [admit|].
        assumption. } } }
Admitted.

Lemma store_sep sz a v1 v2 R m (H : sep (ptsto sz a v1) R m)
      (post : _ -> Prop) (cont : forall m', sep (ptsto sz a v2) R m' -> post m') :
  exists m', store sz m a v2 = Some m' /\ post m'.
Admitted.

Ltac intros_mem m Hm :=
  let m' := fresh in let Hm' := fresh in
  intros m' Hm'; clear m Hm; rename m' into m; rename Hm' into Hm.
Ltac t :=
  let m := lazymatch goal with m : @map.rep word byte mem |- _ => m end in
  let Hm := lazymatch goal with Hm : _ m |- _ => Hm end in
  let Tm := type of m in
  let Pm := lazymatch type of Hm with ?P m => P end in
  lazymatch goal with
  |- load ?sz ?m ?a = Some _
    => lazymatch type of Hm with context [ptsto sz a ?v]
    => refine (load_sep sz a v ?[frame] m ((?[sep]:@Lift1Prop.impl1 Tm Pm _) m Hm));
       cancel; reflexivity end
  | |- WeakestPrecondition.store ?sz ?m ?a ?v2 _
    => lazymatch type of Hm with context [ptsto sz a ?v1]
    => refine (store_sep sz a v1 v2 ?[frame] m ((?[sep]:@Lift1Prop.impl1 Tm Pm _) m Hm) _ ?[cont]); [ cancel; reflexivity | intros_mem m Hm ] end
  | |- ?G =>
    match goal with
    | H: G |- _ => exact H
    | _ => eexists
    | _ => subst; eexists
    end
end.

Local Infix "*" := sep.
Local Infix "*" := sep : type_scope.

Definition spec_of_swap := fun functions =>
  forall a_addr a b_addr b m R t,
    (ptsto 1 a_addr a * (ptsto 1 b_addr b * R)) m ->
    WeakestPrecondition.call (fun _ => True) (fun _ => False) (fun _ _ => True) functions
      (fst swap) t m [a_addr; b_addr]
      (fun t' m' rets => t=t'/\ (ptsto 1 a_addr b * (ptsto 1 b_addr a * R)) m' /\ rets = nil).

Lemma swap_ok : forall functions, spec_of_swap (swap::functions).
Proof.
  cbv[spec_of_swap].
  intros. rename H into Hm.
  repeat t.
Qed.

Definition spec_of_swap_swap := fun functions =>
  forall a_addr a b_addr b m R t,
    (ptsto 1 a_addr a * (ptsto 1 b_addr b * R)) m ->
    WeakestPrecondition.call (fun _ => True) (fun _ => False) (fun _ _ => True) functions
      (fst swap_swap) t m [a_addr; b_addr]
      (fun t' m' rets => t=t' /\ (ptsto 1 a_addr a * (ptsto 1 b_addr b * R)) m' /\ rets = nil).
  
Lemma swap_swap_ok :
  forall functions, spec_of_swap functions -> spec_of_swap_swap (swap_swap::functions).
Proof.
  cbv [spec_of_swap spec_of_swap_swap].
  intros ? Hcall; intros. rename H into Hm.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  cbn [WeakestPrecondition.list_map WeakestPrecondition.expr].
  eapply WeakestPreconditionProperties.Proper_call.
  5: eapply Hcall.
  1,2,3 : cbv [Morphisms.pointwise_relation trace Basics.flip Basics.impl Morphisms.respectful]; solve [typeclasses eauto with core].
  1,2: cycle 1.
  refine ((?[sep]:@Lift1Prop.impl1 mem _ _) m Hm). reflexivity. (* TODO: ecancel *)
  intros ? m' ? (?&Hm'&?).
  clear Hm.
  clear m.
  rename m' into m.
  rename Hm' into Hm.
  subst a0.
  subst a1.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  cbn [WeakestPrecondition.list_map WeakestPrecondition.expr].
  eapply WeakestPreconditionProperties.Proper_call.
  5: eapply Hcall.
  1,2,3 : cbv [Morphisms.pointwise_relation trace Basics.flip Basics.impl Morphisms.respectful]; solve [typeclasses eauto with core].
  1,2: cycle 1.
  refine ((?[sep]:@Lift1Prop.impl1 mem _ _) m Hm). reflexivity. (* TODO: ecancel *)
  intros ? m' ? (?&Hm'&?).
  clear Hm.
  clear m.
  rename m' into m.
  rename Hm' into Hm.
  eexists.
  subst a0.
  subst a1.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eassumption.
  eexists.
Qed.

Lemma link_swap_swap_swap_swap : spec_of_swap_swap (swap_swap::swap::nil).
Proof. apply swap_swap_ok, swap_ok. Qed.