Require Import compiler.util.Common.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.fwd.
Require Import String.
Require Import compiler.DeadAssignmentDef.
Require Import compiler.DeadAssignmentHelper.
Require Import bedrock2.MetricLogging.
Require Import coqutil.Datatypes.PropSet.

Local Notation var := String.string (only parsing).

Section WithArguments.
  Context {width : Z}.
  Context {BW :  Bitwidth.Bitwidth width }.
  Context {word :  word width } {word_ok : word.ok word}.
  Context {env :  map.map string (list var * list var * stmt var) } {env_ok : map.ok env}.
  Context {mem :  map.map word (Init.Byte.byte : Type) } {mem_ok: map.ok mem}.
  Context {locals :  map.map string word } {locals_ok: map.ok locals}.
  Context {ext_spec : Semantics.ExtSpec} {ext_spec_ok: Semantics.ext_spec.ok ext_spec}.

  Local Hint Constructors exec: core.
  Create HintDb set_hints.
  Hint Resolve
    subset_diff
    in_singleton
    subset_union_rr : set_hints.

  Definition compile_post used_after (postH : Semantics.trace -> mem  -> locals -> MetricLog  -> Prop) : (Semantics.trace -> mem  -> locals -> MetricLog  -> Prop) :=
    (fun t' m' lL' mcL' =>
       exists lH' mcH',
         map.agree_on (PropSet.of_list used_after) lH' lL'
         /\ postH t' m' lH' mcH' ).
  Lemma deadassignment_correct_aux:
    forall eH eL,
       deadassignment_functions eH = Success eL ->
       forall sH t m mcH lH postH,
         exec eH sH t m lH mcH postH ->
         forall used_after lL mcL,
           map.agree_on (of_list (live (deadAssignment used_after sH) used_after)) lH lL
           -> exec eL (deadAssignment used_after sH) t m lL mcL (compile_post used_after postH).
  Proof.
    induction 2.
    - simpl.
      intros.
      eapply @exec.interact; fwd.
      + match goal with
        | H: map.split ?m _ _ |- map.split m _ _ => eapply H
        end.
      + match goal with
        | H1: map.getmany_of_list ?l ?argvars = Some ?argvals,
            H2: map.agree_on _ ?l ?lL
          |- map.getmany_of_list ?lL ?argvars = Some ?y =>
            cut (map.getmany_of_list l argvars = map.getmany_of_list lL argvars);
            intros;
            match goal with
            | H: map.getmany_of_list l argvars
                 = map.getmany_of_list lL argvars
              |- map.getmany_of_list lL argvars = Some _ =>
                rewrite <- H; eassumption
            | |- map.getmany_of_list l argvars
                 = map.getmany_of_list lL argvars =>
                eapply agree_on_getmany; eapply agree_on_subset;
                [ eapply H2 | ]
            end
        end.
        repeat match goal with
               | |- context[of_list (ListSet.list_union _ _ _)]  => rewrite ListSet.of_list_list_union
               | |- context[ListSet.list_diff] => rewrite of_list_list_diff
               end.
        match goal with
        | |- subset ?x (union ?x ?y)  =>
            eapply subset_union_rl; eapply subset_ref
        end.
      + match goal with
        | |- ext_spec _ _ _ _ _ => eassumption
        end.
      + intros.
        match goal with
        | H: outcome ?mReceive ?resvals,
            H1: forall mReceive resvals,
              outcome mReceive resvals -> _ |- _ =>
            apply H1 in H;
            repeat match goal with
              | H: exists l, _ |- _ => destr H
              | H: _ /\ _ |- _ => destr H
              end
        end.
        match goal with
        | H: map.putmany_of_list_zip ?resvars ?resvals _ = _ |-
            exists l,
              map.putmany_of_list_zip resvars resvals _ = Some _ /\ _
          =>
            let Heq := fresh in
            pose proof H as Heq; eapply putmany_Some in H; destr H
        end.
        match goal with
        | H: map.putmany_of_list_zip _ _ _ = Some ?x0 |- _ => eexists x0; split; [ eapply H | ]
        end.
        match goal with
        | |- forall m', map.split m' mKeep mReceive -> _
          => intros
        end.
        match goal with
        | H: map.split ?m ?mKeep ?mReceive,
            H': forall m',
              map.split m' mKeep mReceive -> _
              |- _ => eapply H' in H
        end.
        match goal with
        | |- context[compile_post] => unfold compile_post
        end.
        match goal with
        | H: post ?t ?m' ?x _ |- exists lH' mcH',
            map.agree_on _ lH' _ /\
              (post _ _ lH' _)  =>
            exists x; eexists;  split;  [ | eapply H ]
        end.
        (* miscellaneous set reasoning;
           unclear how to automate this across cases *)
        repeat match goal with
               | H: context[of_list (ListSet.list_union _ _ _)] |- _ => rewrite ListSet.of_list_list_union in H
               | H: context[ListSet.list_diff] |- _ => rewrite of_list_list_diff in H
               end.
        match goal with
        | H: map.agree_on (union _ _) _ _ |- _ => apply agree_on_union in H; destr H
        end.
        match goal with
        | H: map.agree_on (diff (of_list ?l1) (of_list ?l2)) ?l ?lL
          |- _ =>
            match goal with
            | H': map.putmany_of_list_zip l2 ?v l = Some ?x |- _ =>
                match goal with
                | H'': map.putmany_of_list_zip l2 v lL = Some ?x0
                  |-  map.agree_on (of_list l1) x x0 =>
                    eapply agree_on_subset;
                    [ eauto using agree_on_putmany
                    |  eapply subset_trans;
                       [ eapply subset_union_rl; eapply subset_ref
                       | eapply sameset_union_diff_oflist ]
                    ]
                end
            end
        end.
    - simpl.
      intros.
      eapply @exec.call; fwd.
      + match goal with
        | H: deadassignment_functions ?eH = Success ?eL,
          H1: map.get eH ?fname = Some ?x |-
            map.get eL fname = Some _ =>
            unfold deadassignment_functions in H;
            unfold deadassignment_function in H;
            eapply map.try_map_values_fw in H; [ | eapply H1 ];
            repeat (destr H; simpl in H)
        end.
        match goal with
        | H: Success _ = Success ?x,
            H1: map.get ?eL ?fname = Some x
          |- map.get eL fname = Some _
          => inversion H; fwd; eapply H1
        end.
      + match goal with
        | H: map.getmany_of_list ?l ?args = Some ?argvs
          |- map.getmany_of_list lL args = Some _ =>
            replace (map.getmany_of_list lL args)  with (map.getmany_of_list l args); [ eapply H | ]
        end.
        match goal with
        | H: map.agree_on ?s ?l ?lL
          |- map.getmany_of_list l ?args
             = map.getmany_of_list lL ?args
          => eapply agree_on_getmany;
             eapply agree_on_subset; [ eapply H | ]
        end.
        (* set reasoning *)
        repeat match goal with
               | |- context[of_list (ListSet.list_union _ _ _)]  => rewrite ListSet.of_list_list_union
               | |- context[ListSet.list_diff] => rewrite of_list_list_diff
               end.
        match goal with
        | |- subset ?x (union ?x ?y)  =>
            eapply subset_union_rl; eapply subset_ref
        end.
      + match goal with
        | |- map.putmany_of_list_zip _ _ _ = Some _ => eassumption
        end.
      + match goal with
        | |- exec _ _ _ _ _ _ _ => eauto using agree_on_refl
        end.
      + match goal with
        | |- forall t' m' mc' st1,
            compile_post ?rets ?outcome t' m' st1 mc' -> _
          => unfold compile_post; intros; fwd
        end.

        match goal with
        | H: outcome _ _ _ _,
            H1: forall t' m' mc' st1,
              outcome _ _ _ _ ->
              exists retvs l',
                map.getmany_of_list st1 ?rets = Some retvs /\ _
                |- _ => eapply H1 in H; fwd
        end.

        match goal with
        | H: map.putmany_of_list_zip ?binds ?x1 ?l = Some ?x2,
            H1: map.agree_on _ l ?lL
          |- context[map.putmany_of_list_zip ?binds _ ?lL] =>
            let Heq := fresh in
            pose proof H as Heq; eapply putmany_Some in H; destr H; fwd
        end.

        match goal with
        | H: map.agree_on (of_list ?rets) ?lH' ?st1,
            H1: map.getmany_of_list ?lH' ?rets = Some ?retvs,
          H2: map.putmany_of_list_zip ?binds ?retvs _ = Some ?x |-
            exists retvs0 l'0,
              map.getmany_of_list st1 rets = Some retvs0 /\ _
          => exists retvs; exists x; repeat split; [ | eapply H2 | ]
        end.
        * match goal with
          | H: map.agree_on (of_list ?rets) ?lH' ?st1,
              H1: map.getmany_of_list ?lH' ?rets = Some ?retvs
            |- map.getmany_of_list ?st1 ?rets = Some ?retvs
            => apply agree_on_getmany in H; rewrite <- H; eapply H1
          end.
        * match goal with
          | H: post ?t' ?m' ?l' _
            |- exists lH'0 mcH'0,
              map.agree_on (of_list ?used_after) lH'0 ?x /\
                post ?t' ?m' lH'0 mcH'0
            => exists l'; eexists; split; [ | eapply H ]
          end.
          repeat match goal with
               | H: context[of_list (ListSet.list_union _ _ _)] |- _ => rewrite ListSet.of_list_list_union in H
               | H: context[ListSet.list_diff] |- _ => rewrite of_list_list_diff in H
                 end.
          match goal with
          | H: map.agree_on (union _ _) ?l ?lL
            |- _ => apply agree_on_union in H; destr H
          end.
          match goal with
          | H: map.agree_on (diff (of_list ?used_after) (of_list ?binds)) ?l ?lL,
              H1: map.putmany_of_list_zip binds ?retvs l = Some ?l',
                H2:  map.putmany_of_list_zip binds retvs lL = Some ?x
            |- map.agree_on (of_list used_after) l' x
            => eapply agree_on_subset;
               [ eauto using agree_on_putmany |
                 eapply subset_trans;
                 [ eapply subset_union_rl; eapply subset_ref |
                 eapply sameset_union_diff_oflist ]
               ]
          end.
    - simpl.
      intros.
      match goal with
      | H: map.agree_on (of_list (if _ then _ else _)) _ _ |- _ =>
          apply agree_on_find in H; destr H
      end.
      eapply @exec.load; fwd.
      + match goal with
        | H: map.agree_on (of_list [?a]) ?l ?lL,
            H1: map.get ?l ?a = Some ?addr |-
            map.get ?lL ?a = Some _ => rewrite <- H; [ eassumption | ]
        end.
        match goal with
        | |- ?s \in of_list [?s] => cut (of_list [s] s); [ simpl; intro; auto | unfold of_list; simpl; auto ]
        end.
      + match goal with
        | H: Memory.load _ _ _ = Some _ |- Memory.load _ _ _ = Some _ => eapply H
        end.
      + match goal with
        | |- compile_post _ _ _ _ _ _ => unfold compile_post
        end.
        match goal with
        | H: post ?t m (map.put ?l ?x ?v) _,
            H1: map.agree_on (of_list (List.removeb eqb ?x ?used_after)) ?l ?lL
          |- exists lH' mcH',
            map.agree_on (of_list used_after) lH'
              (map.put lL x v) /\
              post t m lH' mcH'
          => exists (map.put l x v); eexists; split; [ | ] ;
             match goal with
             | H: post ?t ?m (map.put ?l ?x ?v) _ |- post t m (map.put l x v) _ => eapply H
             | |- _ => idtac
             end
        end.

        match goal with
        | H: map.agree_on (of_list (List.removeb eqb ?x ?used_after)) ?l ?lL
          |- map.agree_on (of_list used_after) (map.put ?l ?x ?v) (map.put ?lL ?x ?v)
          => rewrite ListSet.of_list_removeb in H;
             apply agree_on_diff_of_list_singleton;
             assumption
        end.

    - simpl. intros.
      repeat match goal with
             | H: map.agree_on (of_list (if _ then _ else _)) _ _ |- _
               => apply agree_on_find in H; destr H
             end.
      eapply @exec.store; fwd.
      + match goal with
        | H: map.get ?l ?a = Some _,
          H1: map.agree_on (of_list [?a]) ?l ?lL|- map.get ?lL ?a = Some _ =>
            rewrite <- H1; [ eapply H | ]; cut (of_list [a] a); [ auto | constructor; reflexivity ]
        end.
      + match goal with
        | H: map.get ?l ?a = Some _,
          H1: map.agree_on (of_list [?a]) ?l ?lL|- map.get ?lL ?a = Some _ =>
            rewrite <- H1; [ eapply H | ]; cut (of_list [a] a); [ auto | constructor; reflexivity ]
        end.
      + match goal with
        | |- Memory.store _ _ (word.add _ _) _ = Some _ => eassumption
        end.
      + match goal with
        | |- context[compile_post] => unfold compile_post
        end.
        match goal with
        | H: map.agree_on ?s ?l ?lL,
            H1: post ?t ?m' ?l ?mcH'
          |- exists lH' mcH',
            map.agree_on ?s lH' ?lL /\
              post ?t ?m' lH' mcH'
          => exists l; eexists; split; [ eapply H | eapply H1 ]
        end.
    - simpl. intros.
      match goal with
      | H: map.agree_on (of_list (if _ then _ else _)) _ _ |- _ =>
          apply agree_on_find in H; destr H
      end.
      eapply @exec.inlinetable.
      + match goal with
        | |- ?x <> ?i => assumption
        end.
      + match goal with
        | H: map.get ?l ?a = Some _,
          H1: map.agree_on (of_list [?a]) ?l ?lL|- map.get ?lL ?a = Some _ =>
            rewrite <- H1; [ eapply H | ]; cut (of_list [a] a); [ auto | constructor; reflexivity ]
        end.
      + match goal with
        | |- Memory.load _ (OfListWord.map.of_list_word _) _ = Some _ => eassumption
        end.
      + (* Note for further automation:
           this goal's proof is exactly lifted from
           the exec.load case's corresponding goal. *)

        match goal with
        | |- context[compile_post] => unfold compile_post
        end.

        match goal with
        | H: post ?t m (map.put ?l ?x ?v) _,
            H1: map.agree_on (of_list (List.removeb eqb ?x ?used_after)) ?l ?lL
          |- exists lH' mcH',
            map.agree_on (of_list used_after) lH'
              (map.put lL x v) /\
              post t m lH' mcH'
          => exists (map.put l x v); eexists; split; [ | ] ;
             match goal with
             | H: post ?t ?m (map.put ?l ?x ?v) _ |- post t m (map.put l x v) _ => eapply H
             | |- _ => idtac
             end
        end.
        match goal with
        | H: map.agree_on (of_list (List.removeb eqb ?x ?used_after)) ?l ?lL
          |- map.agree_on (of_list used_after) (map.put ?l ?x ?v) (map.put ?lL ?x ?v)
          => rewrite ListSet.of_list_removeb in H;
             eapply agree_on_subset;
             [ eapply agree_on_diff_of_list_singleton; eassumption
             | eapply sameset_ref ]
        end.
    - simpl.
      intros.
      eapply @exec.stackalloc.
      + match goal with
        | |- ?n mod Memory.bytes_per_word ?width = 0 => assumption
        end.
      + (* For complicated goals like this,
           unsure how sound automation will be. *)
        match goal with
        | |- forall a mStack mCombined,
            Memory.anybytes a ?n mStack ->
            map.split mCombined ?mSmall mStack ->
            exec _ _ _ mCombined _ _ _
           => intros
        end.
        match goal with
        | H: context[exec _ (deadAssignment _ _) _ _ _ _ _],
            H1: Memory.anybytes _ _ _,
              H2: map.agree_on (of_list (List.removeb eqb ?x ?l')) ?l ?lL |- exec _ (deadAssignment _ _) _ _ (map.put ?lL ?x ?a) _ _ =>
            eapply H with (lL := map.put lL x a) in H1
        end.
        all: try match goal with
               | H: map.split _ ?mSmall ?mStack |-
                   map.split _ ?mSmall ?mStack => eapply H
               end.
        all: try match goal with
          | H: map.agree_on (of_list (List.removeb eqb ?x ?used_after)) ?l ?lL
            |- map.agree_on (of_list _)
                 (map.put ?l ?x ?v)
                 (map.put ?lL ?x ?v)
            => rewrite ListSet.of_list_removeb in H; eapply  agree_on_diff_of_list_singleton; eassumption
          end.

        match goal with
        | H: exec ?eL ?s ?t ?m ?l _ ?post |- exec ?eL ?s ?t ?m ?l _ ?post' => eapply exec.weaken; [ eapply H |  simpl ]
        end.
        match goal with
        | |- context[compile_post] =>
            unfold compile_post; simpl; intros; fwd
        end.
        match goal with
        | H: Memory.anybytes ?a ?n ?mStack',
            H1: map.split ?m' ?mSmall' ?mStack',
              H2: post ?t' ?mSmall' ?lH' ?mcH',
                H3: map.agree_on (of_list ?used_after) ?lH' ?l'
          |- exists mSmall'1 mStack'1,
            Memory.anybytes ?a ?n mStack'1 /\
              map.split ?m' mSmall'1 mStack'1 /\
              (exists lH'0 mcH'0,
                  map.agree_on (of_list ?used_after) lH'0 ?l' /\
                    post ?t' mSmall'1 lH'0 mcH'0) =>
            exists mSmall'; exists mStack'; propositional idtac
        end.
    - simpl. intros.
      match goal with
      | H: context[existsb (eqb ?x) ?used_after] |-
          context[existsb (eqb ?x) ?used_after] =>
          destr (existsb (eqb x) used_after)
      end;
      match goal with
      | H: map.agree_on (of_list (live _ _)) ?l ?lL |- _ =>
          simpl in H
      end.
      + eapply @exec.lit.
        unfold compile_post.
        match goal with
        | H: existsb (eqb ?x) ?used_after = true,
            H1: map.agree_on (of_list (List.removeb eqb ?x ?used_after)) ?l ?lL,
              H2: post ?t ?m (map.put ?l ?x (word.of_Z ?v)) ?mcH
          |- exists lH' mcH',
            map.agree_on (of_list ?used_after) lH'
              (map.put ?lL ?x (word.of_Z ?v)) /\
              post ?t ?m lH' mcH' => simpl in H1; exists (map.put l x (word.of_Z v)); eexists; propositional idtac
        end.
        * match goal with
          | H: map.agree_on (of_list (List.removeb eqb ?x ?used_after)) ?l ?lL
            |- map.agree_on (of_list ?used_after)
                 (map.put ?l ?x ?v)
                 (map.put ?lL ?x ?v)
            => rewrite ListSet.of_list_removeb in H; eapply  agree_on_diff_of_list_singleton; eassumption
          end.
        * match goal with
          | H: post ?t ?m ?l ?mc |-
              post ?t ?m ?l _ => eapply H
          end.
      + eapply @exec.skip.
        unfold compile_post.
        match goal with
        | H: post ?t ?m (map.put ?l ?x ?v) ?mcH,
            H1: map.agree_on (of_list ?used_after) ?l ?lL
          |- exists lH' mcH',
            map.agree_on (of_list ?used_after) lH' ?lL
            /\ post ?t ?m lH' mcH' =>
            exists (map.put l x v);
            exists mcH; propositional idtac;
            apply agree_on_put_not_in; eauto
        end.
    - simpl. intros.
      match goal with
      | H: context[existsb (eqb ?x) ?used_after] |-
          context[existsb (eqb ?x) ?used_after] =>
          destr (existsb (eqb x) used_after)
      end;
      match goal with
      | H: map.agree_on (of_list (live _ _)) ?l ?lL |- _ =>
          simpl in H
      end.
      all: try repeat match goal with
             | H: context[match ?z with _ => _ end] |- _ => destr z
             end; simpl.
      all: try match goal with
             | H: find (eqb ?y) ?l = Some ?y' |- _ =>
                 apply find_some in H; destr H;
                 match goal with
                 | H: (?a = ?b)%string |- _ =>
                     apply eqb_eq in H; rewrite H in *
                 end;
                 match goal with
                 | H: In ?x (ListSet.list_union _ _ _) |- _ =>
                     apply in_of_list in H4
                 end
             end.

      all: try repeat rewrite ListSet.of_list_list_union, ListSet.of_list_removeb in *.
      + eapply @exec.op.
        * match goal with
          | H: map.get ?l ?s = Some ?y',
              H1: ?s \in ?s',
              H2: map.agree_on ?s' ?l ?lL
            |- map.get ?lL ?s = _ => rewrite H2 in H; [ eapply H | eapply H1 ]
          end.
        * match goal with
          | H: exec.lookup_op_locals ?l (Var ?v) = Some ?z',
              H1: map.agree_on (union (of_list [?v]) _) ?l ?lL |- exec.lookup_op_locals ?lL (Var ?v) = Some _ => unfold exec.lookup_op_locals in *; simpl; rewrite H1 in H; [ eapply H | ]
          end.

          match goal with
          | |- ?v \in union (of_list [?v]) _ =>
              apply in_union_l; constructor; reflexivity
          end.
        * match goal with
          | |- context[compile_post] => unfold compile_post
          end.
          match goal with
          | H: post ?t ?m (map.put ?l ?x ?v) ?mcH,
              H1: map.agree_on
                    (union _
                       (diff (of_list ?used_after) (singleton_set ?x)))
                    ?l ?lL

            |- exists lH' mcH',
              map.agree_on (of_list ?used_after) lH'
                (map.put ?lL ?x ?v) /\ post ?t ?m lH' mcH'
            => exists (map.put l x v); exists mcH; split
          end.
          -- match goal with
             | H: map.agree_on
                    (union _ (diff (of_list ?used_after) (singleton_set ?x)))
                    ?l ?lL
               |- map.agree_on (of_list ?used_after)
                      (map.put ?l ?x ?v)
                      (map.put ?lL ?x ?v)
               => apply agree_on_union in H; destr H
             end.
             match goal with
             | H: map.agree_on
                    (diff (of_list ?used_after) (singleton_set ?x))
                    ?l ?lL
               |- map.agree_on (of_list ?used_after)
                      (map.put ?l ?x ?v)
                      (map.put ?lL ?x ?v)
               => eapply  agree_on_diff_of_list_singleton; eassumption
             end.
          -- match goal with
             | H: post ?t ?m ?l ?mc |- post ?t ?m ?l ?mc
               => eapply H
             end.
      + (* Note: duplicated from previous '+' case,
           with change from Var v -> Const c *)
        eapply @exec.op.
        * match goal with
          | H: map.get ?l ?s = Some ?y',
              H1: ?s \in ?s',
              H2: map.agree_on ?s' ?l ?lL
            |- map.get ?lL ?s = _ => rewrite H2 in H; [ eapply H | eapply H1 ]
          end.
        * match goal with
          | |- exec.lookup_op_locals ?lL (Const ?v) = Some _ => unfold exec.lookup_op_locals in *; simpl; reflexivity
          end.
        * match goal with
          | |- context[compile_post] => unfold compile_post
          end.
          match goal with
          | H: exec.lookup_op_locals _ (Const ?c) = Some ?z' |- _ =>
              simpl in H; inversion H; fwd
          end.
          match goal with
          | H: post ?t ?m (map.put ?l ?x ?v) ?mcH,
              H1: map.agree_on
                    (union _
                       (diff (of_list ?used_after) (singleton_set ?x))) ?l ?lL

            |- exists lH' mcH',
              map.agree_on (of_list ?used_after) lH'
                (map.put ?lL ?x ?v) /\ post ?t ?m lH' mcH'
            => exists (map.put l x v); exists mcH; split;
               [ | eapply H ]
          end.
          match goal with
          | H: map.agree_on
                 (union _ (diff (of_list ?used_after) (singleton_set ?x)))
                 ?l ?lL
            |- map.agree_on (of_list ?used_after)
                 (map.put ?l ?x ?v)
                 (map.put ?lL ?x ?v)
            => apply agree_on_union in H; destr H
          end.
          match goal with
          | H: map.agree_on
                 (diff (of_list ?used_after) (singleton_set ?x))
                 ?l ?lL
            |- map.agree_on (of_list ?used_after)
                 (map.put ?l ?x ?v)
                 (map.put ?lL ?x ?v)
            => eapply  agree_on_diff_of_list_singleton; eassumption
          end.
      + eapply @exec.op.
        * match goal with
          | H: map.agree_on (of_list (?y :: ?c)) ?l ?lL
            |- _ => eapply agree_on_cons in H; destr H
          end.
          match goal with
          | H: map.get ?l ?y = Some ?y',
              H1: map.get ?l ?y = map.get ?lL ?y
            |- map.get ?lL ?y = Some _ => rewrite <- H1; eapply H
          end.
        * match goal with
          | H: map.agree_on (of_list (?y :: ?c)) ?l ?lL
            |- _ => eapply agree_on_cons in H; destr H
          end.

          match goal with
          | H: exec.lookup_op_locals ?l (Var ?v) = Some ?z' |- exec.lookup_op_locals ?lL (Var ?v) = Some _ => unfold exec.lookup_op_locals in *; simpl
          end.

          match goal with
          | H: map.agree_on
                 (of_list
                       (ListSet.list_union eqb [?v]
                          _))  ?l ?lL,
            H1: map.get ?l ?v = Some ?z' |- map.get ?lL ?v = Some _ => rewrite H in H1; [ apply H1 | rewrite ListSet.of_list_list_union; apply in_union_l ]
          end.
          match goal with
          | |- ?v \in of_list [?v] => constructor; reflexivity
          end.
        * match goal with
          | |- context[compile_post] => unfold compile_post
          end.
          match goal with
          | H: map.agree_on (of_list (?y :: ?c)) ?l ?lL
            |- _ => eapply agree_on_cons in H; destr H
          end.
          match goal with
          | H: map.agree_on
                 (of_list
                    (ListSet.list_union eqb _ _)) ?l ?lL
            |- _ => rewrite ListSet.of_list_list_union in H;
                    apply agree_on_union in H; destr H
          end.
          match goal with
          | H: map.agree_on
                 (of_list (List.removeb eqb _ _)) ?l ?lL
            |- _ => rewrite ListSet.of_list_removeb in H
          end.
          match goal with
          | H: context[exec.lookup_op_locals] |- _ => simpl in H
          end.
          match goal with
          | H: map.agree_on
                 (diff (of_list ?used_after)
                    (singleton_set ?x))
                 ?l ?lL,
              H1: post ?t ?m (map.put ?l ?x (?f ?op ?y' ?z')) ?mcH
            |- exists lH' mcH',
                map.agree_on (of_list ?used_after)
                  lH'
                  (map.put ?lL ?x (?f ?op ?y' ?z')) /\
                  post ?t ?m lH' mcH'
            => exists (map.put l x (f op y' z')); exists mcH; split;
               [ | eapply H1 ]
          end.
          match goal with
          | H: map.agree_on
                 (diff (of_list ?used_after) (singleton_set ?x))
                 ?l ?lL
            |- map.agree_on (of_list ?used_after)
                 (map.put ?l ?x ?v)
                 (map.put ?lL ?x ?v)
            => eapply  agree_on_diff_of_list_singleton; eassumption
          end.
      + match goal with
        | H: map.agree_on (of_list (?y :: ?c)) ?l ?lL
          |- _ => eapply agree_on_cons in H; destr H
        end.
        match goal with
        | H: map.agree_on
               (of_list
                  (ListSet.list_union eqb _ _)) ?l ?lL
          |- _ => rewrite ListSet.of_list_list_union in H;
                  apply agree_on_union in H; destr H
        end.
        match goal with
        | H: map.agree_on
               (of_list (List.removeb eqb _ _)) ?l ?lL
          |- _ => rewrite ListSet.of_list_removeb in H
        end.
        match goal with
        | H: context[exec.lookup_op_locals] |- _ =>
            simpl in H; fwd
        end.
        eapply @exec.op.
        * match goal with
          | H: map.get ?l ?y = Some ?y',
              H1: map.get ?l ?y = map.get ?lL ?y
            |- map.get ?lL ?y = Some _ =>
              rewrite H1 in H; eapply H
          end.
        * match goal with
          | |- context[exec.lookup_op_locals] =>
            simpl; auto
          end.
        * match goal with
          | |- context[compile_post] => unfold compile_post
          end.
          match goal with
          | H: post ?t ?m
                 (map.put ?l ?x (?f ?op ?y' ?z'))
                 ?mcH,
              H1: map.agree_on (diff (of_list ?used_after)
                                  (singleton_set ?x))
                    ?l ?lL
            |- exists lH' mcH',
              map.agree_on (of_list ?used_after) lH'
                (map.put ?lL ?x (?f ?op ?y' ?z')) /\
                post ?t ?m lH' mcH'
            => exists (map.put l x (f op y' z')); exists mcH; split
          end.
          -- match goal with
             | H: map.agree_on
                    (diff (of_list ?used_after) (singleton_set ?x))
                    ?l ?lL
               |- map.agree_on (of_list ?used_after)
                    (map.put ?l ?x ?v)
                    (map.put ?lL ?x ?v)
               => eapply  agree_on_diff_of_list_singleton;
                  eassumption
             end.
          -- match goal with
             | H: post ?t ?m ?l ?mcH |- post ?t ?m ?l ?mcH
               => eapply H
             end.
      + eapply @exec.skip.
        match goal with
        | |- context[compile_post] => unfold compile_post
        end.
        match goal with
        | H: post ?t ?m (map.put ?l ?x ?v) ?mcH,
            H1: existsb (eqb ?x) ?used_after = false,
              H2: map.agree_on (of_list ?used_after) ?l ?lL
          |- exists lH' mcH',
            map.agree_on (of_list ?used_after) lH' ?lL /\
              post ?t ?m lH' mcH'
          => exists (map.put l x v); exists mcH; split; [ | eapply H ]
        end.
        match goal with
        | H: existsb (eqb ?x) ?used_after = false,
            H1: map.agree_on (of_list ?used_after) ?l ?lL
            |- map.agree_on (of_list ?used_after)
                 (map.put ?l ?x ?v) ?lL =>
            eapply agree_on_put_not_in; [ eapply H1 | eapply H ]
        end.
    - simpl. intros.
      match goal with
      | H: context[existsb (eqb ?x) ?used_after] |-
          context[existsb (eqb ?x) ?used_after] =>
          destr (existsb (eqb x) used_after)
      end;
      match goal with
      | H: map.agree_on (of_list (live _ _)) ?l ?lL |- _ =>
          simpl in H
      end.

      all: try repeat match goal with
             | H: context[match ?z with _ => _ end] |- _ => destr z
             end; simpl.

      all: try match goal with
             | H: find (eqb ?y) ?l = Some ?y' |- _ =>
                 apply find_some in H; destr H;
                 match goal with
                 | H: (?a = ?b)%string |- _ =>
                     apply eqb_eq in H; rewrite H in *
                 end;
                 match goal with
                 | H: In ?s _ |- _ =>
                     apply in_of_list in H
                 end
             end.
      + eapply @exec.set.
        * match goal with
          | H: map.get ?l ?s = Some ?y'
              , H1: map.agree_on (of_list ?l') ?l ?lL
                , H2: ?s \in of_list ?l' |- _ =>
              rewrite H1 in H; [ eapply H | eapply H2 ]
          end.
        * match goal with
          | |- context[compile_post] => unfold compile_post; simpl
          end.
          repeat match goal with
          | H: context[of_list (List.removeb eqb _ _)] |- _ =>
              rewrite ListSet.of_list_removeb in H
          end.

          match goal with
          | H: map.agree_on  (diff (of_list ?used_after) (singleton_set ?x)) ?l ?lL,
              H1: post ?t ?m (map.put ?l ?x ?y') ?mcH,
                H2: ?s \in (diff (of_list ?used_after) (singleton_set ?x))
                           |- exists lH' mcH',
                map.agree_on (of_list ?used_after) lH' (map.put ?lL ?x ?y) /\ post ?t ?m lH' mcH'  =>
              exists (map.put l x y); exists mcH; split; [ | eapply H1 ]
          end.
          match goal with
          | H: map.agree_on (diff (of_list ?used_after) (singleton_set ?x)) ?l ?lL |-
              map.agree_on (of_list ?used_after) (map.put ?l ?x ?y') (map.put ?lL ?x ?y') =>
              eapply agree_on_diff_of_list_singleton;
              eapply H
          end.
      + match goal with
        | H: map.agree_on (of_list (_ :: _)) _ _ |- _ =>
            eapply agree_on_cons in H; destr H
        end.
        eapply @exec.set.
        * match goal with
          | H: map.get ?l ?y = Some ?y',
              H1: map.get ?l ?y = map.get ?lL ?y
            |- map.get ?lL ?y = Some _ =>
              rewrite H1 in H; eapply H
          end.
        * match goal with | |- context[compile_post] => unfold compile_post end.

          repeat match goal with
          | H: context[of_list (List.removeb eqb _ _)] |- _ =>
              rewrite ListSet.of_list_removeb in H
          end.
          match goal with
          | H: post ?t ?m (map.put ?l ?x ?y') ?mcH,
            H1: map.agree_on (diff (of_list ?used_after) (singleton_set ?x)) ?l ?lL |- exists lH' mcH',
              map.agree_on (of_list ?used_after) lH' (map.put ?lL ?x ?y')  /\ post ?t ?m lH' mcH' => exists (map.put l x y'); exists mcH; split; [ | eapply H ]
          end.
          match goal with
          | H: map.agree_on  (diff (of_list ?used_after) (singleton_set ?x)) ?l ?lL |-  map.agree_on (of_list ?used_after) (map.put ?l ?x ?y') (map.put ?lL ?x ?y') =>
              eapply  agree_on_diff_of_list_singleton; eapply H
          end.
      + eapply @exec.skip.
        match goal with
        | |- context[compile_post] => unfold compile_post
        end.
        match goal with
        | H: post ?t ?m (map.put ?l ?x ?v) ?mcH,
            H1: existsb (eqb ?x) ?used_after = false,
              H2: map.agree_on (of_list ?used_after) ?l ?lL
          |- exists lH' mcH',
            map.agree_on (of_list ?used_after) lH' ?lL /\
              post ?t ?m lH' mcH'
          => exists (map.put l x v); exists mcH; split; [ | eapply H ]
        end.
        match goal with
        | H: existsb (eqb ?x) ?used_after = false,
            H1: map.agree_on (of_list ?used_after) ?l ?lL
            |- map.agree_on (of_list ?used_after)
                 (map.put ?l ?x ?v) ?lL =>
            eapply agree_on_put_not_in; [ eapply H1 | eapply H ]
        end.
    - simpl. intros.
      repeat match goal with
      | H: map.agree_on (of_list (ListSet.list_union _ _ _)) ?l ?lL |- _ => rewrite ListSet.of_list_list_union in H; eapply agree_on_union in H; destr H
             end.
      eapply @exec.if_true.
      + eauto 2 using accessed_vars_bcond_eval.
      + eauto 2 using IHexec.
    - simpl. intros.
      repeat match goal with
      | H: map.agree_on (of_list (ListSet.list_union _ _ _)) ?l ?lL |- _ => rewrite ListSet.of_list_list_union in H; eapply agree_on_union in H; destr H
             end.
      eapply @exec.if_false.
      + eauto 2 using accessed_vars_bcond_eval.
      + eauto 2 using IHexec.
    - intros.
      simpl in *.
      eapply @exec.loop.
      (* All the unsure goals are
         about map.agree_on and live *)
      + eapply IHexec.
        eapply agree_on_subset.
        * eapply H7.
        * (* The goal here isn't true; see the helper file for attempts. *)
        admit.
      + intros.
        unfold compile_post in H8.
        repeat destr H8.
        apply H1 in H9.
        admit. (* easier; apply eval_bcond equality *)
      + intros.
        unfold compile_post in *.
        inversion H9.
        repeat destr H8.
        eapply H2 in H10.
        2: admit. (* followes from accessed_vars_bcond *)
        exists x. eexists.
        split; admit. (* follows from assumptions *)
      + intros.
        unfold compile_post in H8.
        repeat destr H8.
        eapply H4 in H10.
        2: admit. (* follows from accessed_vars_bcond *)
        * eapply H10.
        * admit. (* goal here also might be untrue *)
      +  intros.
         unfold compile_post in * .
         repeat destr H8.
         eapply H6 in H9.
         * eapply H9.
         * admit.  (* unsure *)
    -


        eexists. split.
        * admit.
        *

    13: {
      intros.
      simpl.
      eapply @exec.seq with (mid := compile_post (live (deadAssignment used_after s2) used_after) mid).
      - eapply IHexec. simpl in H3. eapply H3.
      - intros. unfold compile_post in H4. fwd.
        eapply H2.
        + eapply H4p1.
        + eapply H4p0.
    }
  Proof.
    induction 2; unfold compile_post in *; simpl.
    { simpl.
      intros.
      eapply @exec.interact; eauto.
      eauto.
      intros. apply H3 in H5.
      destruct H5. destruct H5.
      eexists. split.
      all: eauto using agree_on_refl.
    }
    { simpl. intros.
      eapply @exec.call.
      * unfold deadassignment_functions in H.
        unfold deadassignment_function in H.
        simpl in H.
        eapply map.try_map_values_fw in H.
        2: { eapply H0. }
        destruct H.
        destruct H.
        inversion H.
        rewrite <- H8 in H6.
        apply H6.
      * eassumption.
      * eassumption.
      * eapply IHexec. apply agree_on_refl.
      * intros. destruct H6. destruct H6.
        destruct H6. eapply H4 in H7.
        destruct H7. destruct H7.
        destruct H7. destruct H8.
        eexists. eexists.
        split.
        -- eapply agree_on_getmany in H6.
           rewrite <- H6.
           eassumption.
        -- split.
           ++ eapply H8.
           ++ eexists. eexists.
              split.
              2: eapply H9.
              eapply agree_on_refl.

    }
    { simpl. intros.
      eapply @exec.load; eauto.
      destr (find (eqb a) (List.removeb eqb x used_after)).
      all: eauto using agree_on_refl.
    }
    { simpl. intros.
      destr (find (eqb v) used_after).
      - destr (find (eqb a) used_after); eauto using agree_on_refl.
      - destr (find (eqb a) (v :: used_after)); eauto using agree_on_refl.
    }
    { simpl. intros.
      eauto using agree_on_refl.
    }
    { simpl. intros.
      all: eauto using agree_on_refl.
      apply @exec.stackalloc; auto.
      simpl. intros.
      eapply @exec.weaken.
      -- eauto using agree_on_refl.
      -- simpl. intros.
         propositional idtac.
    }
    { simpl. intros.
      destr (existsb (eqb x) used_after).
      all: eauto 6 using agree_on_refl, agree_on_not_in.
    }
    { simpl. intros.
      destr (existsb (eqb x) used_after).
      all: eauto 6 using agree_on_refl, agree_on_not_in.
    }
    { simpl; eauto.
      intros. destr (existsb (eqb x) used_after).
      all: eauto 6 using agree_on_refl, agree_on_not_in.
    }
    { simpl. intros.
      eapply @exec.if_true; eauto.
      eapply IHexec.
      eapply agree_on_subset.
      -- eapply H2.
      -- unfold subset. intros.
         rewrite ListSet.of_list_list_union.
         apply in_union_l.
         rewrite ListSet.of_list_list_union.
         apply in_union_l.
         assumption.
    }
    { simpl. intros.
      eapply @exec.if_false; eauto.
      eapply IHexec.
      all: eauto.
      eapply agree_on_subset.
      -- eapply H2.
      -- unfold subset. intros.
         rewrite ListSet.of_list_list_union.
         apply in_union_l.
         rewrite ListSet.of_list_list_union.
         apply in_union_r.
         assumption.
    }
    { simpl. intros.
      eapply @exec.loop; eauto.
      - eapply @exec.weaken.
        + eapply IHexec.
          admit.
        + admit.
      - intros. eapply H2 in H8.
        2: eassumption.
        repeat eexists.
        eapply H8.
      - intros. eapply H4 in H8.
        2: eassumption.
        + eapply H8.
        + admit.
      - admit.
    }
    { simpl.
      intros.
      eapply @exec.seq with (mid := compile_post (live (deadAssignment used_after s2) used_after) mid).
      - (* specialize (IHexec (live s2 used_after)).
        specialize IHexec with (1 := H3).
        apply IHexec in H3.
        eapply IHexec. *)

        eapply IHexec.
        + eapply H3.
        (* eapply agree_on_subset.
        + eapply H3. *)
     (*
        + admit. (* eapply live_monotone. *)
          (* replace (live sH used_after) with (live sH used_after')
             where subset used_after used_after'
           *)

          (* show that
             of_list (live (deadAss used_after s2) used_after)
             is subset of (live s2 used_after), and that
             forall s1 u u',
             subset u u' ->
             subset (of_list (live s1 u)) (of_list live s1 u') *)
*)
      - simpl. intros.
        unfold compile_post in H4.
        fwd.
        eapply H2.

        (* context has that there exists some lH' and mcH',
           but goal has that a specific lH and mcH that satisfy mid
        eexists. eexists.
        all: eauto.
      all: ad   mit.
       exec.seq *)
        all: admit.
    }
    { simpl.
      intros.
      eapply @exec.skip; eauto.
      eexists. eexists.
      split.
      2: eassumption.
      apply agree_on_refl.
    }
  Admitted.

End WithArguments.
(*
 Lemma live_monotone :
    forall s used_after used_after',
      subset (of_list used_after) (of_list used_after') ->
      subset (of_list (live s used_after)) (of_list (live s used_after')).
  Proof.
    induction s; intros.

    - (* SLoad *)
      simpl.
      destr (find (eqb a) (List.removeb eqb x used_after)).
      + eapply find_some in E.
        destr E.
        eapply eqb_eq in H1.
        subst.
        eapply in_of_list in H0.
        repeat rewrite ListSet.of_list_removeb in *.

        assert (subset (diff (of_list used_after) (singleton_set x)) (diff (of_list used_after') (singleton_set x))) by (eauto using subset_diff).

        assert (s \in diff (of_list used_after') (singleton_set x)) by eauto.
        rewrite <- ListSet.of_list_removeb in H2.

        destr (find (eqb s) (List.removeb eqb x used_after')).
        * rewrite ListSet.of_list_removeb. auto.
        * eapply find_none in E.
          2: eapply H2.
          rewrite eqb_refl in E. discriminate.
      + simpl.
        rewrite of_list_cons.
        unfold add.
        eapply subset_union_l.
        * destr (find (eqb a) (List.removeb eqb x used_after')).
          -- eapply find_some in E0.
             destr E0.
             eapply eqb_eq in H1.
             subst.
             eauto with set_hints.

          -- rewrite of_list_cons.
             unfold add. eapply subset_union_rl.
             eapply subset_ref.
        * destr (find (eqb a) (List.removeb eqb x used_after')).
          -- do 2 (rewrite ListSet.of_list_removeb).
             eauto using subset_diff.
          -- rewrite of_list_cons.
             unfold add.
             eapply subset_union_rr.
             do 2 (rewrite ListSet.of_list_removeb).
             eauto using subset_diff.
    - (* SStore *)
      simpl.
      (* destruct_one_match *)
      repeat match goal with
      | |- context[if ?c then _ else _] =>
          lazymatch c with
          | context[if ?c' then _ else _] => fail
          |  _ => destr c
          end
      end.
      destruct_one_match.
      destr (find (eqb v) used_after).
      + eapply find_some in E.
        destr E.
        eapply eqb_eq in H1.
        subst.
        assert (of_list used_after s) by (propositional idtac).
        assert (of_list used_after' s).
        { eapply H. auto. }
        destr (find (eqb s) used_after').
        * destr (find (eqb a) used_after).
          -- eapply find_some in E0. destr E0.
             eapply eqb_eq in H4.
             symmetry in H4.
             subst.
             assert (of_list used_after' a).
             { eapply H. auto. }
             destr (find (eqb a) used_after').
             ++ auto.
             ++ eapply find_none in E0.
                2: { eapply H4. }
                rewrite eqb_refl in E0. discriminate.
          -- destr (find (eqb a) used_after').
             ++ rewrite of_list_cons.
                unfold add.
                eapply find_some in E1.
                destr E1.
                eapply eqb_eq in H4.
                subst.
                apply subset_union_l.
                ** eauto using in_singleton.
                ** eauto.
             ++ repeat rewrite of_list_cons.
                unfold add.
                apply subset_union_l.
                ** apply subset_union_rl.
                   eapply subset_ref.
                ** apply subset_union_rr.
                   auto.
        * destr (find (eqb a) used_after).
          -- eapply find_some in E0. destr E0.
             eapply eqb_eq in H4.
             symmetry in H4.
             subst.
             assert (of_list used_after' a).
             { eapply H. auto. }
             destr (find (eqb a) (s :: used_after')).
             ++ rewrite of_list_cons.
                unfold add.
                eauto using subset_union_rr.
             ++ rewrite of_list_cons.
                unfold add.
                eauto using subset_union_rr.
          -- rewrite of_list_cons.
             unfold add.
             apply subset_union_l.
             ++ destr (find (eqb a) (s :: used_after')).
                ** eapply find_some in E1.
                   destr E1.
                   eapply eqb_eq in H4.
                   symmetry in H4.
                   subst.
                   eauto using in_singleton.
                ** rewrite of_list_cons.
                   unfold add.
                   apply subset_union_rl.
                   eauto using subset_refl.
             ++ destr (find (eqb a) (s :: used_after')).
                ** rewrite of_list_cons.
                   unfold add.
                   apply subset_union_rr.
                   eauto.
                ** rewrite of_list_cons.
                   unfold add.
                   apply subset_union_rr.
                   rewrite of_list_cons.
                   unfold add.
                   apply subset_union_rr.
                   eauto.
      + destr (find (eqb a) (v :: used_after)).
        * eapply find_some in E0.
          destr E0.
          eapply eqb_eq in H1.
          symmetry in H1.
          subst.
          eapply in_inv in H0.
          propositional idtac.
          -- destr (find (eqb a) used_after').
             ++ simpl. rewrite E0.
                rewrite of_list_cons.
                unfold add.
                eapply subset_union_l.
                ** eapply in_singleton.
                   apply find_some in E0.
                   destr E0.
                   eapply eqb_eq in H1.
                   subst.
                   auto.
                ** auto.
             ++ rewrite of_list_cons.
                unfold add.
                apply subset_union_l.
                ** destr (find (eqb a) (a :: used_after')).
                   --- rewrite of_list_cons.
                       unfold add.
                       apply subset_union_rl.
                       apply subset_ref.
                   --- rewrite of_list_cons.
                       unfold add.
                       apply subset_union_rl.
                       apply subset_ref.
                ** destr (find (eqb a) (a :: used_after')).
                   --- rewrite of_list_cons.
                       unfold add.
                       apply subset_union_rr.
                       assumption.
                   --- rewrite of_list_cons.
                       unfold add.
                       apply subset_union_rr.
                       rewrite of_list_cons.
                       unfold add.
                       apply subset_union_rr.
                       assumption.
          -- destr (find (eqb v) used_after').
             ++ rewrite of_list_cons.
                unfold add.
                apply subset_union_l.
                ** apply find_some in E0.
                   destr E0.
                   apply eqb_eq in H2.
                   symmetry in H2. subst.
                   destr (find (eqb a) used_after').
                   --- eapply find_some in E0.
                       destr E0. eapply eqb_eq in H3.
                       subst.
                       auto using in_singleton.
                   --- eapply subset_trans.
                       2: { rewrite of_list_cons.
                            unfold add.
                            eapply subset_union_rr.
                            eapply subset_ref. }
                       eauto using in_singleton.
                ** destr (find (eqb a) used_after').
                   --- auto.
                   --- rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_rr.
                       auto.
             ++ rewrite of_list_cons.
                unfold add.
                apply subset_union_l.
                ** destr (find (eqb a) (v :: used_after')).
                   --- rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_rl.
                       eapply subset_ref.
                   --- rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_rr.
                       rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_rl.
                       apply subset_ref.
                ** destr (find (eqb a) (v :: used_after')).
                   --- rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_rr.
                       assumption.
                   --- rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_rr.
                       rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_rr.
                       assumption.
        * simpl in E0.
          destr (a =? v)%string; [ discriminate | ].
          destr (find (eqb v) used_after').
          -- apply find_some in E2.
             destr E2.
             apply eqb_eq in H1.
             symmetry in H1.
             subst.
             destr (find (eqb a) used_after').
             ++ apply find_some in E2.
                destr E2.
                apply eqb_eq in H2.
                symmetry in H2.
                subst.
                rewrite of_list_cons.
                unfold add.
                apply subset_union_l; [ eauto using in_singleton | ].
                rewrite of_list_cons.
                unfold add.
                apply subset_union_l; [ eauto using in_singleton | eauto ].
             ++ rewrite of_list_cons.
                unfold add.
                apply subset_union_l.
                ** rewrite of_list_cons.
                   unfold add.
                   apply subset_union_rl.
                   apply subset_ref.
                ** rewrite of_list_cons.
                   unfold add.
                   apply subset_union_l.
                   --- rewrite of_list_cons.
                       unfold add.
                       apply subset_union_rr.
                       eauto using in_singleton.
                   --- rewrite of_list_cons.
                       unfold add.
                       apply subset_union_rr.
                       eauto.
          -- rewrite of_list_cons.
             unfold add.
             apply subset_union_l.
             ++ destr (find (eqb a) (v :: used_after')).
                ** simpl in E3.
                   destr ((a =? v)%string).
                   --- rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_rl.
                       eapply subset_ref.
                   --- apply find_some in E3.
                       destr E3.
                       apply eqb_eq in H1.
                       symmetry in H1.
                       subst.
                       rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_rr.
                       eauto using in_singleton.
                ** rewrite of_list_cons.
                   unfold add.
                   eapply subset_union_rl.
                   eapply subset_ref.
             ++ destr (find (eqb a) (v :: used_after')).
                ** simpl in E3.
                   destr ((a =? v)%string).

                   ---
                     (* context here has something like
                      v <> v in premises, which should
                      make this trivial, but unsure how *)
                     rewrite of_list_cons.
                     unfold add.
                     rewrite of_list_cons.
                     unfold add.
                     eapply subset_union_l.
                     +++ eapply subset_union_rl.
                         eapply subset_ref.
                     +++ eauto using subset_union_rr.
                   --- rewrite of_list_cons.
                     unfold add.
                     rewrite of_list_cons.
                     unfold add.
                     eapply subset_union_l.
                     +++ eapply subset_union_rl.
                         eapply subset_ref.
                     +++ eauto using subset_union_rr.
                ** rewrite of_list_cons.
                   unfold add.
                   rewrite of_list_cons.
                   unfold add.
                   eapply subset_union_l.
                   --- eapply subset_union_rr.
                       rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_rl.
                       eapply subset_ref.
                   --- eapply subset_union_rr.
                       rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_rr.
                       auto.
    - simpl.
      destr (find (eqb i) (List.removeb eqb x used_after)).
      + apply find_some in E.
        destr E.
        apply eqb_eq in H1.
        symmetry in H1.
        subst.
        destr (find (eqb i) (List.removeb eqb x used_after')).
        * repeat rewrite ListSet.of_list_removeb.
          eauto using subset_diff.
        * rewrite of_list_cons.
          unfold add.
          repeat rewrite ListSet.of_list_removeb.
          eauto using subset_diff, subset_union_rr.
      + rewrite of_list_cons.
        unfold add.
        apply subset_union_l.
        * destr (find (eqb i) (List.removeb eqb x used_after')).
          -- apply find_some in E0.
             destr E0.
             eapply eqb_eq in H1.
             symmetry in H1.
             subst.
             eauto using in_singleton.
          -- rewrite of_list_cons.
             unfold add.
             eapply subset_union_rl.
             eapply subset_ref.
        * destr (find (eqb i) (List.removeb eqb x used_after')).
          -- repeat rewrite ListSet.of_list_removeb.
             eauto using subset_diff.
          -- rewrite of_list_cons.
             unfold add.
             eapply subset_union_rr.
             repeat rewrite ListSet.of_list_removeb.
             eauto using subset_diff.
    - (* SStackalloc *)
      simpl.
      repeat rewrite ListSet.of_list_removeb.
      eauto using subset_diff.
    - (* SLit *)
      simpl.
      repeat rewrite ListSet.of_list_removeb.
      eauto using subset_diff.
    - (* SOp *)
      simpl. destr z.
      + simpl.
        destr (find (eqb v) (List.removeb eqb x used_after)).
        * simpl.
          apply find_some in E.
          destr E.
          apply eqb_eq in H1.
          symmetry in H1.
          subst.
          destr (find (eqb y) (List.removeb eqb x used_after)).
          -- simpl.
             apply find_some in E.
             destr E.
             apply eqb_eq in H2.
             symmetry in H2.
             subst.
             destr (find (eqb v) (List.removeb eqb x used_after')).
             ++ apply find_some in E.
                destr E.
                eapply eqb_eq in H3.
                symmetry in H3.
                subst.
                destr (find (eqb y) (List.removeb eqb x used_after')).
                ** apply find_some in E.
                   destr E.
                   eapply eqb_eq in H4.
                   symmetry in H4.
                   subst.
                   repeat rewrite ListSet.of_list_removeb.
                   eauto using subset_diff.
                ** rewrite of_list_cons.
                   unfold add.
                   eapply subset_union_rr.
                   repeat rewrite ListSet.of_list_removeb.
                   eauto using subset_diff.
             ++  destr (find (eqb y) (v :: List.removeb eqb x used_after')).
                 ** rewrite of_list_cons.
                    unfold add.
                    eapply subset_union_rr.
                    repeat rewrite ListSet.of_list_removeb.
                    eauto using subset_diff.
                 ** rewrite of_list_cons.
                    unfold add.
                    eapply subset_union_rr.
                    rewrite of_list_cons.
                    unfold add.
                    eapply subset_union_rr.
                    repeat rewrite ListSet.of_list_removeb.
                    auto using subset_diff.
          -- rewrite of_list_cons.
             unfold add.
             eapply subset_union_l.
             ++ destr (find (eqb v) (List.removeb eqb x used_after')).
                ** destr (find (eqb y) (List.removeb eqb x used_after')).
                   --- apply find_some in E1.
                       destr E1.
                       apply eqb_eq in H2.
                       symmetry in H2.
                       subst.
                       auto using in_singleton.
                   --- rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_rl.
                       eapply subset_ref.
                ** destr (find (eqb y) (v :: List.removeb eqb x used_after')).
                   --- apply find_some in E1.
                       destr E1.
                       apply eqb_eq in H2.
                       symmetry in H2.
                       subst.
                       eauto using in_singleton.
                   --- rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_rl.
                       eapply subset_ref.
             ++ destr (find (eqb v) (List.removeb eqb x used_after')).
                ** destr (find (eqb y) (List.removeb eqb x used_after')).
                   --- repeat rewrite ListSet.of_list_removeb.
                       eauto using subset_diff.
                   --- rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_rr.
                       repeat rewrite ListSet.of_list_removeb.
                       eauto using subset_diff.
                ** destr (find (eqb y) (v :: List.removeb eqb x used_after')).
                   --- rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_rr.
                       repeat rewrite ListSet.of_list_removeb.
                       eauto using subset_diff.
                   --- rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_rr.
                       rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_rr.
                       repeat rewrite ListSet.of_list_removeb.
                       auto using subset_diff.
        * destr (find (eqb y) (v :: List.removeb eqb x used_after)).
             ++ rewrite of_list_cons.
                unfold add.
                eapply subset_union_l.
                ** destr (find (eqb v) (List.removeb eqb x used_after')).
                   --- eapply find_some in E1.
                       destr E1.
                       apply eqb_eq in H1.
                       symmetry in H1.
                       subst.
                       destr (find (eqb y) (List.removeb eqb x used_after')).
                       +++ eauto using in_singleton.
                       +++ rewrite of_list_cons.
                           unfold add.
                           eapply subset_union_rr.
                           eauto using in_singleton.
                   --- destr (find (eqb y) (v :: List.removeb eqb x used_after')).
                       +++ rewrite of_list_cons.
                           unfold add.
                           eapply subset_union_rl.
                           eapply subset_ref.
                       +++ rewrite of_list_cons.
                           unfold add.
                           eapply subset_union_rr.
                           rewrite of_list_cons.
                           unfold add.
                           eapply subset_union_rl.
                           eapply subset_ref.
                ** destr (find (eqb v) (List.removeb eqb x used_after')).
                   --- eapply find_some in E1.
                       destr E1.
                       apply eqb_eq in H1.
                       symmetry in H1.
                       subst.
                       destr (find (eqb y) (List.removeb eqb x used_after')).
                       +++ repeat rewrite ListSet.of_list_removeb.
                           eauto using subset_diff.
                       +++ rewrite of_list_cons.
                           unfold add.
                           eapply subset_union_rr.
                           repeat rewrite ListSet.of_list_removeb.
                           eauto using subset_diff.
                   --- destr (find (eqb y) (v :: List.removeb eqb x used_after')).
                       +++ rewrite of_list_cons.
                           unfold add.
                           eapply subset_union_rr.
                           repeat rewrite ListSet.of_list_removeb.
                           eauto using subset_diff.
                       +++ rewrite of_list_cons.
                           unfold add.
                           eapply subset_union_rr.
                           rewrite of_list_cons.
                           unfold add.
                           eapply subset_union_rr.
                           repeat rewrite ListSet.of_list_removeb.
                           eauto using subset_diff.
             ++ rewrite of_list_cons.
                unfold add.
                eapply subset_union_l.
                ** destr (find (eqb v) (List.removeb eqb x used_after')).
                   --- destr (find (eqb y) (List.removeb eqb x used_after')).
                       +++ apply find_some in E2.
                           destr E2.
                           apply eqb_eq in H1.
                           symmetry in H1.
                           subst.
                           eauto using in_singleton.
                       +++ rewrite of_list_cons.
                           unfold add.
                           eapply subset_union_rl.
                           eapply subset_ref.
                   --- destr (find (eqb y) (v :: List.removeb eqb x used_after')).
                       +++ apply find_some in E2.
                           destr E2.
                           apply eqb_eq in H1.
                           symmetry in H1.
                           subst.
                           eauto using in_singleton.
                       +++ rewrite of_list_cons.
                           unfold add.
                           eapply subset_union_rl.
                           eapply subset_ref.
                ** destr (find (eqb v) (List.removeb eqb x used_after')).
                   --- apply find_some in E1.
                       destr E1.
                       apply eqb_eq in H1.
                       symmetry in H1.
                       subst.
                       rewrite of_list_cons.
                       unfold add.
                       eapply subset_union_l.
                       +++ destr (find (eqb y) (List.removeb eqb x used_after')).
                           *** eauto using in_singleton.
                           *** rewrite of_list_cons.
                               unfold add.
                               eapply subset_union_rr.
                               eauto using in_singleton.
                       +++ destr (find (eqb y) (List.removeb eqb x used_after')).
                           *** repeat rewrite ListSet.of_list_removeb.
                               eauto using subset_diff.
                           *** rewrite of_list_cons.
                               unfold add.
                               eapply subset_union_rr.
                               repeat rewrite ListSet.of_list_removeb.
                               eauto using subset_diff.
                   --- rewrite of_list_cons.
                       unfold add.
                       apply subset_union_l.
                       +++ destr (find (eqb y) (v :: List.removeb eqb x used_after')).
                           *** rewrite of_list_cons.
                               unfold add.
                               eapply subset_union_rl.
                               apply subset_ref.
                           *** rewrite of_list_cons.
                               unfold add.
                               eapply subset_union_rr.
                               rewrite of_list_cons.
                               unfold add.
                               eapply subset_union_rl.
                               apply subset_ref.
                       +++ destr (find (eqb y) (v :: List.removeb eqb x used_after')).
                           *** rewrite of_list_cons.
                               unfold add.
                               eapply subset_union_rr.
                               repeat rewrite ListSet.of_list_removeb.
                               eauto using subset_diff.
                           *** rewrite of_list_cons.
                               unfold add.
                               eapply subset_union_rr.
                               rewrite of_list_cons.
                               unfold add.
                               eapply subset_union_rr.
                               repeat rewrite ListSet.of_list_removeb.
                               eauto using subset_diff.
      + simpl.
        destr (find (eqb y) (List.removeb eqb x used_after)).
        * apply find_some in E.
          destr E.
          apply eqb_eq in H1.
          symmetry in H1.
          subst.
          destr (find (eqb y) (List.removeb eqb x used_after')).
          -- repeat rewrite ListSet.of_list_removeb.
             eauto using subset_diff.
          -- rewrite of_list_cons.
             unfold add.
             apply subset_union_rr.
             repeat rewrite ListSet.of_list_removeb.
             eauto using subset_diff.
        * rewrite of_list_cons.
          unfold add.
          apply subset_union_l.
          -- destr (find (eqb y) (List.removeb eqb x used_after')).
             ++ apply find_some in E0.
                destr E0.
                apply eqb_eq in H1.
                symmetry in H1.
                subst.
                eauto using in_singleton.
             ++ rewrite of_list_cons.
                unfold add.
                apply subset_union_rl.
                apply subset_ref.
          -- destr (find (eqb y) (List.removeb eqb x used_after')).
             ++ repeat rewrite ListSet.of_list_removeb.
                eauto using subset_diff.
             ++ rewrite of_list_cons.
                unfold add.
                apply subset_union_rr.
                repeat rewrite ListSet.of_list_removeb.
                eauto using subset_diff.
    - (* SSet *)
      simpl.
      destr (find (eqb y) (List.removeb eqb x used_after)).
      + destr (find (eqb y) (List.removeb eqb x used_after')).
        * repeat rewrite ListSet.of_list_removeb.
          eauto using subset_diff.
        * rewrite of_list_cons.
          unfold add.
          apply subset_union_rr.
          repeat rewrite ListSet.of_list_removeb.
          eauto using subset_diff.
      + rewrite of_list_cons.
        unfold add.
        apply subset_union_l.
        * destr (find (eqb y) (List.removeb eqb x used_after')).
          -- apply find_some in E0.
             destr E0.
             apply eqb_eq in H1.
             symmetry in H1.
             subst.
             eauto using in_singleton.
          -- rewrite of_list_cons.
             unfold add.
             apply subset_union_rl.
             apply subset_ref.
        * destr (find (eqb y) (List.removeb eqb x used_after')).
          -- repeat rewrite ListSet.of_list_removeb.
             eauto using subset_diff.
          -- rewrite of_list_cons.
             unfold add.
             apply subset_union_rr.
             repeat rewrite ListSet.of_list_removeb.
             eauto using subset_diff.
    - (* SIf *)
      simpl.
      repeat rewrite ListSet.of_list_list_union.
      repeat apply subset_union_l.
      + apply subset_union_rl.
        apply subset_union_rl.
        eauto.
      + apply subset_union_rl.
        apply subset_union_rr.
        eauto.
      + apply subset_union_rr.
        eapply subset_ref.
    - (* SLoop *)
      simpl. eapply IHs1.
      repeat rewrite ListSet.of_list_list_union.
      repeat apply subset_union_l.
      + apply subset_union_rl.
        eapply subset_ref.
      + apply subset_union_rr.
        apply subset_union_rl.
        eauto.
      + apply subset_union_rr.
        apply subset_union_rr.
        apply subset_ref.
    - (* SSeq *)
      simpl.
      eauto.
    - (* SSkip *)
      simpl.
      auto.
    - (* SCall *)
      simpl.
      repeat rewrite ListSet.of_list_list_union.
      apply subset_union_l.
      + apply subset_union_rl.
        apply subset_ref.
      + apply subset_union_rr.
        all: admit.
  Admitted.


  Lemma deadAssignment_subset :
    forall s1 s2 used_after,
      subset (of_list (live s1 used_after)) (of_list (live s2 used_after)) ->
      subset (of_list (live (deadAssignment used_after s1) used_after)) (of_list (live (deadAssignment used_after s2) used_after)).
  Proof.
  Abort.

  Lemma deadAssignment_subset' :
    forall s u u',
      subset (of_list u') (of_list u) ->
      subset
        (of_list (live (deadAssignment u s) u'))
        (of_list (live s u)).
  Proof.
    induction s.
  Abort.

  Lemma deadassignment_live:
    forall sH used_after,
      subset
        (of_list (live (deadAssignment used_after sH) used_after))
        (of_list (live sH used_after)).
  Proof.
    induction sH.
    all: intros; try solve [simpl; eapply subset_refl].
    - (* SStackalloc *)
      simpl. repeat (rewrite ListSet.of_list_removeb). eauto using subset_diff.
    - (* SLit *)
      simpl. destr (existsb (eqb x) used_after); simpl.
      + eapply subset_ref.
      + rewrite ListSet.of_list_removeb.
        eapply sameset_sym.
        eapply sameset_sym.
        eauto using sameset_diff_not_in.
    - (* SOp *)
      simpl. destr (existsb (eqb x) used_after); simpl; [ eapply subset_ref | ].
      destr z; simpl.
      + destr (find (eqb v) (List.removeb eqb x used_after)).
        all: admit.
  Admitted.



*)
