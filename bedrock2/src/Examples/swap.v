Require Import bedrock2.BasicC64Syntax bedrock2.BasicALU bedrock2.NotationsInConstr.

Import BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Existing Instance bedrock2.BasicC64Syntax.Basic_bopnames_params.
Local Coercion literal (z : Z) : Syntax.expr := Syntax.expr.literal z.
Local Coercion var (x : string) : Syntax.expr := Syntax.expr.var x.

Definition swap := ("swap", (["a";"b"], ([]:list varname), bedrock_func_body:(
  "t" = *(uint8_t*) "b";;
  *(uint8_t*) "b" = *(uint8_t*) "a";;
  *(uint8_t*) "a" = "t"
))).

Definition swap_swap := ("swap_swap", (("a"::"b"::nil), ([]:list varname), bedrock_func_body:(
  Syntax.cmd.call [] "swap" [var "a"; var "b"];;
  Syntax.cmd.call [] "swap" [var "a"; var "b"]
))).

Require bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.BasicC64Semantics.
Require Import bedrock2.Map bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Local Instance FIXME_mem_ok : Map.map.ok Semantics.mem.
  cbv [mem parameters word byte mem].
  try exact SortedList.map_ok || (* TODO: the first fails... *)
  (set {|SortedList.parameters.key := _;
        SortedList.parameters.value := _;
        SortedList.parameters.key_eqb := _;
        SortedList.parameters.key_ltb := _|};
     exact SortedList.map_ok).
Defined.


Require bedrock2.WeakestPreconditionProperties.
From bedrock2.Tactics Require Import eabstract.
Require Import bedrock2.ProgramLogic.

Definition ptsto sz a v m := load sz m a = Some v.

Local Infix "*" := sep.
Local Infix "*" := sep : type_scope.
Instance spec_of_swap : spec_of "swap" := fun functions =>
  forall a_addr a b_addr b m R t,
    (ptsto 1 a_addr a * (ptsto 1 b_addr b * R)) m ->
    WeakestPrecondition.call (fun _ => True) (fun _ => False) (fun _ _ => True) functions
      "swap" t m [a_addr; b_addr]
      (fun t' m' rets => t=t'/\ (ptsto 1 a_addr b * (ptsto 1 b_addr a * R)) m' /\ rets = nil).

Instance spec_of_swap_swap : spec_of "swap_swap" := fun functions =>
  forall a_addr a b_addr b m R t,
    (ptsto 1 a_addr a * (ptsto 1 b_addr b * R)) m ->
    WeakestPrecondition.call (fun _ => True) (fun _ => False) (fun _ _ => True) functions
      "swap_swap" t m [a_addr; b_addr]
      (fun t' m' rets => t=t' /\ (ptsto 1 a_addr a * (ptsto 1 b_addr b * R)) m' /\ rets = nil).

From bedrock2.Tactics Require Import eabstract letexists.

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

Ltac _syntactic_unify x y :=
  match constr:(Set) with
  | _ => is_evar x; unify x y
  | _ => is_evar y; unify x y
  | _ => lazymatch x with
         | ?f ?a => lazymatch y with ?g ?b => _syntactic_unify f g; _syntactic_unify a b end
         | (fun (a:?Ta) => ?f a)
           => lazymatch y with (fun (b:?Tb) => ?g b) =>
                               let __ := constr:(fun (a:Ta) (b:Tb) => ltac:(_syntactic_unify f g; exact Set)) in idtac end
         | let a : ?Ta := ?v in ?f a
           => lazymatch y with let b : ?Tb := ?w in ?g b =>
                               _syntactic_unify v w;
                               let __ := constr:(fun (a:Ta) (b:Tb) => ltac:(_syntactic_unify f g; exact Set)) in idtac end
         (* TODO: fail fast in more cases *)
         | _ => unify x y; constr_eq x y
         end
  end.
Tactic Notation "syntactic_unify" open_constr(x) open_constr(y) :=  _syntactic_unify x y.

Lemma swap_ok : program_logic_goal_for_function! swap.
Proof.
  bind_body_of_function swap; cbv [spec_of spec_of_swap].
  intros.
  letexists. split. exact eq_refl. (* argument initialization *)

  repeat straightline.

  letexists; split.
  { letexists; split.
    { eabstract repeat straightline. }
    repeat straightline.
    letexists; split.
    { let m := m in
      let Hm := H in
      let Tm := type of m in
      let Pm := lazymatch type of Hm with ?P m => P end in
      lazymatch goal with
      | |- load ?sz ?m ?a = Some ?v
        => simple refine (load_sep sz a v _ m ((?[sep]:@Lift1Prop.impl1 Tm Pm _) m Hm));
             [ shelve | .. ]
      end.
      let __ := constr:(eq_refl : v0 = b) in idtac.
      repeat straightline.
      eabstract (cancel; exact (RelationClasses.reflexivity _)). }
    eabstract repeat straightline. }

  repeat straightline.
  letexists; split.
  { repeat straightline.
    letexists; split.
    { let Hm := H in
      let Tm := type of m in
      let Pm := lazymatch type of Hm with ?P m => P end in
      lazymatch goal with
      | |- load ?sz ?m ?a = Some ?v
        => simple refine (load_sep sz a v _ m ((?[sep]:@Lift1Prop.impl1 Tm Pm _) m Hm));
             [ shelve | .. ]
      end.
      let __ := constr:(eq_refl : v0 = a) in idtac. eabstract (cancel; reflexivity). }
    repeat straightline. }

  repeat straightline.
  let Hm := H in
  let Tm := type of m in
  let Pm := lazymatch type of Hm with ?P m => P end in
  lazymatch goal with
  | |- WeakestPrecondition.store ?sz ?m ?a ?v2 ?post
    => simple refine (store_sep sz a _ v2 _ m ((_:@Lift1Prop.impl1 Tm Pm _) m Hm) post _);
         [ shelve | shelve | .. ]
  end.
  { eabstract (instantiate (2 := b); cancel; reflexivity). }
  clear H m; intros m H.
  cbv beta.

  letexists; split.
  { eabstract repeat ((letexists; split) || exact eq_refl). }
  letexists; split.
  { eabstract repeat ((letexists; split) || exact eq_refl). }
  repeat straightline.

  let Hm := H in
  let Tm := type of m in
  let Pm := lazymatch type of Hm with ?P m => P end in
  lazymatch goal with
  | |- WeakestPrecondition.store ?sz ?m ?a ?v2 ?post
    => simple refine (store_sep sz a _ v2 _ m ((_:@Lift1Prop.impl1 Tm Pm _) m Hm) post _);
         [ shelve | shelve | .. ]
  end.
  eabstract (instantiate (2 := a); cancel; reflexivity).
  clear H m; intros m H.
  cbv beta. (* FIXME *)

  (* FIXME *)
  hnf.
  split. exact eq_refl.
  split. 2:exact eq_refl.
  assumption.
Defined.

Lemma swap_swap_ok : program_logic_goal_for_function! swap_swap.
Proof.
  bind_body_of_function swap_swap; cbv [spec_of_swap_swap].
  intros.
  letexists. split. exact eq_refl. (* argument initialization *)

  repeat straightline.
  straightline_call.
  { refine ((?[sep]:@Lift1Prop.impl1 mem _ _) _ H1). reflexivity. (* TODO: ecancel *) }
  repeat straightline.
  letexists; split.
  { exact eq_refl. }

  repeat straightline.
  straightline_call.
  { refine ((?[sep]:@Lift1Prop.impl1 mem _ _) _ H3). reflexivity. (* TODO: ecancel *) }
  repeat straightline.
  letexists; split.
  { exact eq_refl. }

  repeat straightline.

  repeat split; assumption.
Defined.

Lemma link_swap_swap_swap_swap : spec_of_swap_swap (swap_swap::swap::nil).
Proof. auto using swap_swap_ok, swap_ok. Qed.