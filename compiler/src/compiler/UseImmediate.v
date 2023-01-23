Require Import compiler.util.Common.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.fwd.
Require Import String.
Require Import compiler.UseImmediateDef.

Section WithArguments.
  Context {width : Z}.
  Context {BW :  Bitwidth.Bitwidth width }.
  Context {word :  word width } {word_ok : word.ok word}.
  Context {env :  map.map string (list string * list string * stmt string) } {env_ok : map.ok env}.
  Context {mem :  map.map word (Init.Byte.byte : Type) } {mem_ok: map.ok mem}.
  Context {locals :  map.map string word } {locals_ok: map.ok locals}.
  Context {ext_spec : Semantics.ExtSpec} {ext_spec_ok: Semantics.ext_spec.ok ext_spec}.
  Context (is5BitImmediate : Z -> bool).
  Context (is12BitImmediate  : Z -> bool).
  Local Hint Constructors exec: core.
  Lemma useImmediateCorrect :
    forall e st t m l mc post, exec e st t m l mc post -> exec e (useImmediate is5BitImmediate is12BitImmediate st) t m l mc post.
  Proof.
    intros.
    induction H; simpl in *; try eauto.
    destr s1; destr s2; try eauto; simpl in *. clear IHexec H1.
    destr z.
    1: { destr op.
         { destr (is12BitImmediate v); clear E.
           { destr ((x =? v0)%string).
             { inversion H. clear H1 H2 H3 H4 H5 H6 H7.  specialize H0 with (t' := t) (m' := m) (l' := (map.put l v0 (word.of_Z v))) (mc' := (MetricLogging.addMetricLoads 8 (MetricLogging.addMetricInstructions 8 mc))). apply H0 in H8. clear H0. apply exec.seq_cps.  apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. rewrite  map.get_put_same in H11. fwd. eapply exec.op.
               { apply H10. }
               { simpl. reflexivity. }
               { apply H12. }
             }
             { destr ((x =? y)%string).
               { inversion H.  clear H1 H3 H2 H4 H5 H6 H7.  specialize H0 with (t' := t) (m' := m) (l' := (map.put l y (word.of_Z v))) (mc' := (MetricLogging.addMetricLoads 8 (MetricLogging.addMetricInstructions 8 mc))). apply H0 in H8.  clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. rewrite map.get_put_same in H10. fwd. eapply exec.op.
                 { apply H11. }
                 { simpl. reflexivity. }
                 { idtac. progress simpl in *.  Search word.add. apply H12. }



                 ((Search exec.exec.
    (* 2: { inversion IHexec. clear H H1 H2 H3 H4 H5 H6 IHexec.  specialize H0 with (t' := t) (m' := m) (l' := (map.put l x (word.of_Z v))) (mc' := (MetricLogging.addMetricLoads 8 (MetricLogging.addMetricInstructions 8 mc))). apply H0 in H7. clear H0. *)

End WithArguments.
