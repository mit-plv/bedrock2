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

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
        constants [word_cst]).

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
             { inversion H. clear H1 H2 H3 H4 H5 H6 H7.  eapply H0 in H8. clear H0. apply exec.seq_cps.  apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. rewrite  map.get_put_same in H11. fwd. eapply exec.op.
               { apply H10. }
               { simpl. reflexivity. }
               { apply H12. }
             }
             { destr ((x =? y)%string).
               { inversion H.  clear H1 H3 H2 H4 H5 H6 H7.  eapply H0 in H8.  clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. rewrite map.get_put_same in H10. fwd. eapply exec.op.
                 { apply H11. }
                 { simpl. reflexivity. }
                 { progress simpl in *. progress replace (word.add z' (word.of_Z v))  with  (word.add (word.of_Z v) z') by ring. apply H12. }
               }
               { inversion H. clear H1 H3 H2 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. eapply exec.op.
                 { apply H10. }
                 { apply H11. }
                 { apply H12. }
               }
             }
           }
           {
             inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. eapply exec.op.
             { apply H10. }
             { apply H11. }
             { apply H12. }
           }
         }
         {
           destr (is12BitImmediate (- v)).
           {
             destr (x =? v0)%string; clear E.
             {
               inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. rewrite  map.get_put_same in H11. fwd. eapply exec.op.
               { apply H10. }
               { simpl. reflexivity. }
               { simpl. simpl in H12. replace (word.add y' (word.of_Z (- v)))  with  (word.sub  y' (word.of_Z v)) by ring. apply H12. }
             }
             {
               inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. eapply exec.op.
               { apply H10. }
               { apply H11. }
               { apply H12. }
             }
           }
           {
             inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. eapply exec.op.
             { apply H10. }
             { apply H11. }
             { apply H12. }
           }
         }
         {
           inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. eapply exec.op.
           { apply H10. }
           { apply H11. }
           { apply H12. }
         }
         {
           inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. eapply exec.op.
           { apply H10. }
           { apply H11. }
           { apply H12. }
         }
         {
           inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. eapply exec.op.
           { apply H10. }
           { apply H11. }
           { apply H12. }
         }
         {
           inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. eapply exec.op.
           { apply H10. }
           { apply H11. }
           { apply H12. }
         }
         { destr (is12BitImmediate v); clear E.
           { destr ((x =? v0)%string).
             { inversion H. clear H1 H2 H3 H4 H5 H6 H7.  eapply H0 in H8. clear H0. apply exec.seq_cps.  apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. rewrite  map.get_put_same in H11. fwd. eapply exec.op.
               { apply H10. }
               { simpl. reflexivity. }
               { apply H12. }
             }
             { destr ((x =? y)%string).
               { inversion H.  clear H1 H3 H2 H4 H5 H6 H7.  eapply H0 in H8.  clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. rewrite map.get_put_same in H10. fwd. eapply exec.op.
                 { apply H11. }
                 { simpl. reflexivity. }
                 { progress simpl in *. replace (word.and z' (word.of_Z v))  with  (word.and (word.of_Z v) z').
                   { apply H12. }
                   { Search word.and. induction (word.of_Z v).
(*
                     Tried to add
Hint Rewrite
       unsigned_of_Z signed_of_Z of_Z_unsigned unsigned_add unsigned_sub unsigned_opp unsigned_or unsigned_and unsigned_xor unsigned_not unsigned_ndn unsigned_mul signed_mulhss signed_mulhsu unsigned_mulhuu unsigned_divu signed_divs unsigned_modu signed_mods unsigned_slu unsigned_sru signed_srs unsigned_eqb unsigned_ltu signed_lts
       using trivial
  : word_laws.

from coqutil/Word/Properties.v with attempt at trying to copy over
  Ltac bitwise :=
      autorewrite with word_laws;
      unfold wrap;
      generalize_wrap_unsigned;
      Z.bitblast. and using bitwise, based on proof of unsigned_and_wrap in Properties.v.


Using Search word.and also seems to turn up Word.build_ok which has something like word.unsigned (word.and x y) =
   wrap (Z.land (word.unsigned x) (word.unsigned y))) but mixed with a lot of other propositions in an implies chain.

Also tried `induction (word.of_Z v)` and got error "Unable to satisfy the following constraints: ?word : "Interface.word ?width"
                    *)
                 }
               }
               { inversion H. clear H1 H3 H2 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. eapply exec.op.
                 { apply H10. }
                 { apply H11. }
                 { apply H12. }
               }
             }
           }
           {
             inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. eapply exec.op.
             { apply H10. }
             { apply H11. }
             { apply H12. }
           }
         }





                 ((Search exec.exec.
    (* 2: { inversion IHexec. clear H H1 H2 H3 H4 H5 H6 IHexec.  specialize H0 with (t' := t) (m' := m) (l' := (map.put l x (word.of_Z v))) (mc' := (MetricLogging.addMetricLoads 8 (MetricLogging.addMetricInstructions 8 mc))). apply H0 in H7. clear H0. *)

End WithArguments.
