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
  Search word.add.
  Print word.unsigned_inj.
  Lemma word_and_comm:
    forall {width: Z} {word: Interface.word width},
      word.ok word -> forall x y : word, word.and x y = word.and y x.
  Proof.
    intros. eapply word.unsigned_inj. rewrite word.unsigned_and_nowrap. rewrite word.unsigned_and_nowrap. apply Z.land_comm.
  Qed.

  Lemma word_or_comm:
    forall {width: Z} {word: Interface.word width},
      word.ok word -> forall x y : word, word.or x y = word.or y x.
  Proof.
    intros. eapply word.unsigned_inj. rewrite word.unsigned_or_nowrap. rewrite word.unsigned_or_nowrap. apply Z.lor_comm.
  Qed.

  Lemma word_xor_comm:
    forall {width: Z} {word: Interface.word width},
      word.ok word -> forall x y : word, word.xor x y = word.xor y x.
  Proof.
    intros. eapply word.unsigned_inj. rewrite word.unsigned_xor_nowrap. rewrite word.unsigned_xor_nowrap. apply Z.lxor_comm.
  Qed.

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
                   { apply word_and_comm. assumption.  }
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
                 { progress simpl in *. replace (word.or z' (word.of_Z v))  with  (word.or (word.of_Z v) z').
                   { apply H12. }
                   { apply word_or_comm. assumption.  }
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
                 { progress simpl in *. replace (word.xor z' (word.of_Z v))  with  (word.xor (word.of_Z v) z').
                   { apply H12. }
                   { apply word_xor_comm. assumption.  }
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
          {
            destr (is5BitImmediate v).
            {
              destr (x=?v0)%string.
              {
                inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. rewrite map.get_put_same in H11. fwd. eapply exec.op.
                { apply H10. }
                { simpl. reflexivity. }
                { apply H12. }
              }
              {
                inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. eapply exec.op.
                { apply H10. }
                { apply H11. }
                { apply H12. }
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
            destr (is5BitImmediate v).
            {
              destr (x=?v0)%string.
              {
                inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. rewrite map.get_put_same in H11. fwd. eapply exec.op.
                { apply H10. }
                { simpl. reflexivity. }
                { apply H12. }
              }
              {
                inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. eapply exec.op.
                { apply H10. }
                { apply H11. }
                { apply H12. }
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
            destr (is5BitImmediate v).
            {
              destr (x=?v0)%string.
              {
                inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. rewrite map.get_put_same in H11. fwd. eapply exec.op.
                { apply H10. }
                { simpl. reflexivity. }
                { apply H12. }
              }
              {
                inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. eapply exec.op.
                { apply H10. }
                { apply H11. }
                { apply H12. }
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
            destr (is12BitImmediate v).
            {
              destr (x=?v0)%string.
              {
                inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. rewrite map.get_put_same in H11. fwd. eapply exec.op.
                { apply H10. }
                { simpl. reflexivity. }
                { apply H12. }
              }
              {
                inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. eapply exec.op.
                { apply H10. }
                { apply H11. }
                { apply H12. }
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
            destr (is12BitImmediate v).
            {
              destr (x=?v0)%string.
              {
                inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. rewrite map.get_put_same in H11. fwd. eapply exec.op.
                { apply H10. }
                { simpl. reflexivity. }
                { apply H12. }
              }
              {
                inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. eapply exec.op.
                { apply H10. }
                { apply H11. }
                { apply H12. }
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
            inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. eapply exec.op.
            { apply H10. }
            { apply H11. }
            { apply H12. }
          }
       }
       {
         inversion H. clear H1 H2 H3 H4 H5 H6 H7. eapply H0 in H8. clear H0. apply exec.seq_cps. apply exec.lit. inversion H8. clear H0 H1 H2 H3 H4 H5 H6 H7 H9. simpl in H11. fwd. eapply exec.op.
         { apply H10. }
         { simpl. reflexivity. }
         { apply H12. }
       }
Qed.

End WithArguments.
