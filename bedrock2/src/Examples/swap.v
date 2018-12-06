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

Local Infix "*" := sep.
Local Infix "*" := sep : type_scope.
Instance spec_of_swap : spec_of "swap" := fun functions =>
  forall a_addr a b_addr b m R t,
    (ptsto a_addr a * (ptsto b_addr b * R)) m ->
    WeakestPrecondition.call (fun _ => True) (fun _ => False) (fun _ _ => True) functions
      "swap" t m [a_addr; b_addr]
      (fun t' m' rets => t=t'/\ (ptsto a_addr b * (ptsto b_addr a * R)) m' /\ rets = nil).

Instance spec_of_swap_swap : spec_of "swap_swap" := fun functions =>
  forall a_addr a b_addr b m R t,
    (ptsto a_addr a * (ptsto b_addr b * R)) m ->
    WeakestPrecondition.call (fun _ => True) (fun _ => False) (fun _ _ => True) functions
      "swap_swap" t m [a_addr; b_addr]
      (fun t' m' rets => t=t' /\ (ptsto a_addr a * (ptsto b_addr b * R)) m' /\ rets = nil).

From bedrock2.Tactics Require Import eabstract letexists syntactic_unify.

Lemma load1_sep a (v:byte) R m (H:(ptsto a v * R) m) :
  load 1 m a = Some (combine 0 v word_zero).
  cbv [load].
  change (BinIntDef.Z.to_nat 1) with 1%nat.
  cbn [load_rec].
  eapply get_sep in H; rewrite H.
  reflexivity.
Qed.

Lemma store1_sep a (v1:byte) v2 R m (H : sep (ptsto a v1) R m)
    (post : _ -> Prop) (cont : forall m', sep (ptsto a (fst (split 0 v2))) R m' -> post m') :
  exists m', store 1 m a v2 = Some m' /\ post m'.
Proof.
Admitted.

Lemma fst_split0_combine0 v w : fst (split 0 (combine 0 v w)) = v.
Admitted.

Ltac sep :=
  let m := lazymatch goal with |- _ ?m => m end in
  let H := multimatch goal with H: _ m |- _ => H end  in
  refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H;
  SeparationLogic.ecancel; fail.

Lemma swap_ok : program_logic_goal_for_function! swap.
Proof.
  bind_body_of_function swap; cbv [spec_of spec_of_swap].
  intros.
  letexists. split. exact eq_refl. (* argument initialization *)

  repeat straightline.
  letexists; split.
  { repeat straightline. letexists; split; [eapply load1_sep; sep|repeat straightline]. }

  repeat straightline.
  letexists; split.
  { repeat straightline. letexists; split; [eapply load1_sep; sep|repeat straightline]. }

  repeat straightline.
  eapply store1_sep; [sep|].

  repeat straightline.
  eapply store1_sep; [sep|].

  repeat straightline.
  (* final postcondition *)
  split. exact eq_refl.
  split. 2:exact eq_refl.
  repeat match goal with x := _ |- _ => subst x end.
  rewrite 2fst_split0_combine0 in *.
  assumption.
Defined.

Lemma swap_swap_ok : program_logic_goal_for_function! swap_swap.
Proof.
  bind_body_of_function swap_swap; cbv [spec_of_swap_swap].
  intros.
  letexists. split. exact eq_refl. (* argument initialization *)

  repeat straightline.
  straightline_call; [sep|].
  repeat straightline.
  letexists; split.
  { exact eq_refl. }

  repeat straightline.
  straightline_call; [sep|].
  repeat straightline.
  letexists; split.
  { exact eq_refl. }

  repeat straightline.

  repeat split; assumption.
Defined.

Lemma link_swap_swap_swap_swap : spec_of_swap_swap (swap_swap::swap::nil).
Proof. auto using swap_swap_ok, swap_ok. Qed.

(* Print Assumptions link_swap_swap_swap_swap. *)
(* store1_sep SortedList.sorted_remove SortedList.sorted_put SortedList.map_ok fst_split0_combine0 *)