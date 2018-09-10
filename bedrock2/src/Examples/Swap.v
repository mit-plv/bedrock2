Require Import bedrock2.Macros bedrock2.Syntax.
Require Import bedrock2.StringNamesSyntax bedrock2.BasicALU bedrock2.NotationsInConstr.

Import BinInt String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Section bsearch.
  Context {p : unique! StringNamesSyntax.parameters} {b : BasicALU.operations}.
  Local Coercion literal (z : Z) : expr := expr.literal z.
  Local Coercion var (x : String.string) : expr := expr.var x.

  Definition swap : list varname * list varname * cmd := (("a"::"b"::nil), nil, bedrock_func_body:(
    "t" = *(uint8_t*) "b";
    *(uint8_t*) "b" = *(uint8_t*) "a";
    *(uint8_t*) "a" = "t"
  )).

  Definition swap_swap : list varname * list varname * cmd := (("a"::"b"::nil), nil, bedrock_func_body:(
    cmd.call nil (expr.global "swap") (var "a"::var "b"::nil);
    cmd.call nil (expr.global "swap") (var "a"::var "b"::nil)
  )).
End bsearch.

Require bedrock2.BasicC64Syntax.

Example swap_c_string := Eval compute in
  BasicC64Syntax.c_func "swap" swap.
(* Print swap_c_string. *)

Import List.ListNotations.
Require Import bbv.Word.
Require Import bedrock2.Semantics bedrock2.BasicC64Semantics bedrock2.Map.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require bedrock2.WeakestPrecondition bedrock2.WeakestPreconditionProperties.

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

Context (__A : map.ok Semantics.mem).
Lemma swap_ok : 
  forall l a_addr a b_addr b (m:map.rep (value:=@Semantics.byte _)) R t,
    (sep (ptsto 1 a_addr a) (sep (ptsto 1 b_addr b) R)) m ->
  WeakestPrecondition.func
    (fun _ => True) (fun _ => False) (fun _ _ => True) l (fun _ _ _ _ _ => False)
    (@swap BasicC64Syntax.params) t m (a_addr::b_addr::nil)
    (fun t' m' rets => t=t' /\ (sep (ptsto 1 a_addr b) (sep (ptsto 1 b_addr a) R)) m' /\ rets = nil).
Proof.
  intros. rename H into Hm.
  repeat t.
Qed.

Lemma swap_swap_ok : 
  forall l a_addr a b_addr b (m:map.rep (value:=@Semantics.byte _)) R t,
    (sep (ptsto 1 a_addr a) (sep (ptsto 1 b_addr b) R)) m ->
  WeakestPrecondition.func
    (fun _ => True) (fun _ => False) (fun _ _ => True) l (WeakestPrecondition.call (fun _ => True) (fun _ => False) (fun _ _ => True) l [("swap", (@swap BasicC64Syntax.params))])
    (@swap_swap BasicC64Syntax.params) t m (a_addr::b_addr::nil)
    (fun t' m' rets => t=t' /\ (sep (ptsto 1 a_addr a) (sep (ptsto 1 b_addr b) R)) m' /\ rets = nil).
Proof.
  Print WeakestPrecondition.func.
  intros. rename H into Hm.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  unfold WeakestPrecondition.list_map.
  intros. eapply WeakestPreconditionProperties.Proper_func.
  6: eapply swap_ok.
  1,2,3,4,5 : cbv [Morphisms.pointwise_relation trace Basics.flip Basics.impl Morphisms.respectful]; try solve [typeclasses eauto with core].
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
  intros. eapply WeakestPreconditionProperties.Proper_func.
  6: eapply swap_ok.
  1,2,3,4,5 : cbv [Morphisms.pointwise_relation trace Basics.flip Basics.impl Morphisms.respectful]; try solve [typeclasses eauto with core].
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
  