Require Import compiler.util.Common.
Require Import compiler.FlatImp.
From Coq Require Import List. Import ListNotations.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.fwd.
Require Import String.
Require Import compiler.UseImmediateDef.
Require Import bedrock2.MetricLogging.

Local Notation var := String.string (only parsing).

Section WithArguments.
  Context {width : Z}.
  Context {BW :  Bitwidth.Bitwidth width }.
  Context {word :  word width } {word_ok : word.ok word}.
  Context {env :  map.map string (list var * list var * stmt var) } {env_ok : map.ok env}.
  Context {mem :  map.map word (Init.Byte.byte : Type) } {mem_ok: map.ok mem}.
  Context {locals :  map.map string word } {locals_ok: map.ok locals}.
  Context {ext_spec : Semantics.ExtSpec} {ext_spec_ok: Semantics.ext_spec.ok ext_spec}.
  Context (is5BitImmediate : Z -> bool).
  Context (is12BitImmediate  : Z -> bool).

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
        constants [word_cst]).

  Local Hint Constructors exec: core.

  Lemma useImmediate_correct_aux:
    forall eH eL,
       (useimmediate_functions is5BitImmediate is12BitImmediate) eH = Success eL ->
       forall sH t m mcH lH post,
       exec eH sH t m lH mcH post ->
       exec eL (useImmediate is5BitImmediate is12BitImmediate sH) t m lH mcH post.
  Proof.
    induction 2.
    (* most cases stay the same *)
    all: try solve [simpl; eauto].

    (* SCall *)
    { simpl.
      eapply @exec.call; try eassumption.
      assert (exists v2, (useimmediate_function is5BitImmediate is12BitImmediate) (params, rets, fbody) = Success v2 /\ map.get eL fname = Some v2).
      { eapply map.try_map_values_fw.
        - simpl in H; eapply H.
        - eassumption.
      }
      destruct H5. destruct H5. simpl in H5. inversion H5. fwd.
      eassumption.
    }

    (* SSeq *)
    { simpl.
      repeat (match goal with
              | |- context[match ?x with _ => _ end] => destr x
              | |- context[if ?x then _ else _ ] => destr x
              end;
              try solve [eapply @exec.seq; eassumption]);
        simpl in *.

      all: eapply @exec.seq_cps; eapply @exec.lit.

      all: match goal with
           | H: exec _ _ _ _ _ _ ?mid,
               H': forall t m l mc,
                 ?mid _ _ _ _ -> exec ?eL _ _ _ _ _ ?post
                 |- _ => inversion H
           end.

      all: match goal with
           | H: ?mid _ _ _ _,
               H0: forall t m l mc,
                 ?mid t m l mc -> exec ?eL _ _ _ _ _ ?post
                 |- exec ?eL _ _ _ _ _ ?post
             => apply H0 in H; inversion H
           end.

      all: simpl in *;
        match goal with
        | [ H: map.get (map.put _ ?x _) ?x = _ |- _ ]
          => rewrite map.get_put_same in H; fwd
        end.

      all: eapply @exec.op; simpl in *; [ eassumption |  reflexivity | try eassumption ].

      { rewrite word.add_comm. assumption. }
      { replace (word.add y' (word.of_Z (- v)))  with  (word.sub  y' (word.of_Z v)) by ring. assumption. }
      { rewrite word.and_comm. assumption. }
      { rewrite word.or_comm. assumption. }
      { rewrite word.xor_comm. assumption. }
    }
  Qed.
End WithArguments.
