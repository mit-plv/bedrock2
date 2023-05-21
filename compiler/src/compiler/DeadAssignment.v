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
