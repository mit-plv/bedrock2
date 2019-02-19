Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax.
Require Import bedrock2.StringNamesSyntax bedrock2.NotationsCustomEntry.
Require Import coqutil.Z.HexNotation.
Require Import bedrock2.FE310CSemantics.
Require Import bedrock2.Array.
Import Syntax BinInt String List.ListNotations.

Import BinInt String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.


Local Coercion literal (z : Z) : expr := expr.literal z.
Local Coercion var (x : String.string) : expr := expr.var x.

Definition lightbulb := 
    let packet : varname := "packet" in
    let len : varname := "len" in
    let ethertype : varname := "ethertype" in
    let protocol : varname := "protocol" in
    let port : varname := "port" in
    let mmio_val : varname := "mmio_val" in
    let command : varname := "command" in
    let MMIOREAD : varname := "MMIOREAD" in
    let MMIOWRITE : varname := "MMIOWRITE" in
    let r : varname := "r" in

  ("lightbulb", ((packet::len::nil), (r::nil), bedrock_func_body:(

    ethertype = ((load1(packet + constr:(12)) << constr:(8)) | (load1(packet + constr:(13))));
    require (constr:(1536 - 1) < ethertype) else { r = (constr:(-1)) };

    protocol = (load1(packet + constr:(23)));
    require (protocol == constr:(Ox"11")) else { r = (constr:(-1)) };

    command = (load1(packet + constr:(42))); (* TODO: one bit only *)

    io! mmio_val = MMIOREAD(constr:(Ox"10012008"));
    output! MMIOWRITE(constr:(Ox"10012008"), mmio_val | constr:(1) << constr:(23));

    io! mmio_val = MMIOREAD(constr:(Ox"1001200c"));
    output! MMIOWRITE(constr:(Ox"1001200c"), mmio_val | command << constr:(23));

    r = (constr:(0))
  ))).


(* MMIO macro cannot be implemented in bedrock2 b/c volatile *)

Require bedrock2.BasicCSyntax.

Example lightbulb_c_string := Eval compute in
  BasicCSyntax.c_func (lightbulb).


Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.

Require Import bedrock2.Semantics.
Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Axiom __map_ok : map.ok Semantics.mem. Local Existing Instance __map_ok. (* FIXME *)

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.

Local Infix "*" := sep.
Local Infix "*" := sep : type_scope.

Require Import coqutil.Word.Interface.
Require bedrock2.WeakestPrecondition coqutil.Word.Properties.
Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Instance spec_of_lightbulb : spec_of "lightbulb" := fun functions => 
  forall p_addr p l_addr l ps m R t,
    sep (array scalar8 (word.of_Z 1) p_addr ps) R m ->
    (scalar p_addr p * (scalar l_addr l * R)) m ->
    WeakestPrecondition.call functions 
      "lightbulb" t m [p_addr; l_addr]
      (fun t' m' rets => exists v, rets = [v]).

(* bsearch.v has examples to deal with arrays *)
Lemma lightbulb_ok : program_logic_goal_for_function! lightbulb.
Proof.
  bind_body_of_function lightbulb; cbv [spec_of spec_of_lightbulb]. intros.
  (* argument initialization *) intros. letexists. split; [exact eq_refl|].
  (* code *) repeat straightline.



SeparationLogic.seprewrite_in @array_address_inbounds H0.

1: admit. 1: admit. 1: reflexivity. letexists. split. {
   repeat straightline. letexists. {
  split. {try subst v1; eapply Scalars.load_one.
  change ptsto with scalar8 in *.
  ecancel_assumption. }
 { repeat straightline. letexists. subst v4. split. { 
     eapply Scalars.load_one.
     clear H0.
     SeparationLogic.seprewrite_in @array_address_inbounds H.
    { 1: admit. } { 1: admit. } 1: reflexivity.
    refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H.
    cancel.
    refine (cancel_seps_at_indices 1 0 _ _ _ _);
    cbn[List.firstn List.skipn app List.hd List.tl].
    { refine (RelationClasses.reflexivity _). (* TODO: we totally saw a stack overflow here??*) }
    cbn[seps]; exact (RelationClasses.reflexivity _). }
{ subst v. (* exact eq_refl (* FIXME *) *) admit. } } } }
  repeat straightline.

  letexists. split. { repeat straightline. }
  split; cycle 1. { repeat straightline. eauto. }
  { repeat straightline. letexists.

    split. 1:admit.
    repeat straightline.
    letexists. repeat straightline.
    split. { repeat straightline. }
    split; cycle 1.
    { repeat straightline. eauto. } 

    repeat straightline.
    letexists.
    split. { admit. }

(* the 1st MMIOREAD *)
    repeat straightline.

  { hnf. letexists. split. { 
       left. split. { exact eq_refl. } { split. { exact eq_refl. }
       intros. { letexists. split. { subst l1. exact eq_refl. } 
    repeat straightline.

  { hnf. letexists. split. { 
       right. split. { exact eq_refl. } { letexists. split. { subst args0. exact eq_refl. }
       intros. { letexists. split. { subst l1. exact eq_refl. } 

    repeat straightline.

  { hnf. letexists. split. { 
       left. split. { exact eq_refl. } { split. { exact eq_refl. }
       intros. { letexists. split. { subst l1. exact eq_refl. } 
    repeat straightline.

  { hnf. letexists. split. { 
       right. split. { exact eq_refl. } { letexists. split. { subst args0. exact eq_refl. }
       intros. { letexists. split. { subst l1. exact eq_refl. } 
  (* TODO: accumulate trace in context instead of goal *)
    repeat straightline.
    eauto. } } }
  cbv. eauto. 
  (* TODO: reorder subgoals in ext_spec -- address range checks should be earlier *)
} } } }
  cbv. eauto. } } } }
  cbv. eauto. } } } }
  cbv. eauto. } }
Unshelve.
all:admit.
Admitted.

Print lightbulb_c_string.


