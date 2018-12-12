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
Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Local Instance FIXME_mem_ok : map.ok Semantics.mem.
Admitted. (* FIXME *)


Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import eabstract.
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

From coqutil.Tactics Require Import eabstract letexists syntactic_unify.
Require Import coqutil.Datatypes.PrimitivePair.
Import coqutil.Word.Interface.

Lemma load1_sep a (v:Semantics.byte) R m (H:(ptsto a v * R) m) :
  load Syntax.access_size.one m a = Some (word.of_Z (LittleEndian.combine 1 (pair.mk v tt))).
  cbv [load Semantics.bytes_per bytes_per footprint List.map List.option_all List.unfoldn].
  eapply get_sep in H; rewrite H.
  exact eq_refl.
Qed.

Lemma store1_sep a (v1:Semantics.byte) v2 (R:mem->Prop) (m:mem) (H : sep (ptsto a v1) R m)
    (p := (ptsto a (pair._1 (LittleEndian.split 1 (word.unsigned v2)))))
    (post : mem -> Prop) (cont : forall (m':mem), sep p R m' -> post m') :
  exists (m':mem), store Syntax.access_size.one m a v2 = Some m' /\ post m'.
Proof.
Admitted.

Lemma split_combine_1 a :
  (pair._1 (LittleEndian.split 1 (word.unsigned (word.of_Z (LittleEndian.combine 1 (pair.mk a tt )))))) = a.
Proof.
  cbn -[word.of_Z word.unsigned].
  rewrite Z.lor_0_r.
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
  rewrite word.unsigned_of_Z in H0.
  rewrite 2split_combine_1 in *.
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