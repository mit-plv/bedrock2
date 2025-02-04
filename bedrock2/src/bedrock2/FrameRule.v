Require Import Coq.ZArith.ZArith.
Require Import coqutil.sanity coqutil.Macros.subst coqutil.Macros.unique coqutil.Byte.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.fwd coqutil.Tactics.Tactics.
Require Import bedrock2.Syntax.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.OfListWord.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.Memory bedrock2.ptsto_bytes bedrock2.Map.Separation.
Require Import bedrock2.Semantics bedrock2.MetricSemantics.
Require Import bedrock2.Map.DisjointUnion bedrock2.Map.split_alt.

Require Import Coq.Lists.List.

Section semantics.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.
  Context {mem_ok: map.ok mem} {word_ok: word.ok word}.

  Lemma frame_load: forall mSmall mBig mAdd a r (v: word),
      mmap.split mBig mSmall mAdd ->
      load a mSmall r = Some v ->
      load a mBig r = Some v.
  Proof.
    unfold load, load_Z. intros. fwd. eapply sep_of_load_bytes in E0.
    2: destruct a; simpl; destruct width_cases as [W | W]; rewrite W; cbv; discriminate.
    fwd. unfold sep in E0. fwd.
    eapply map.split_alt in E0p0.
    unfold mmap.split in *.
    rewrite E0p0 in H.
    rewrite mmap.du_assoc in H. unfold mmap.du in H at 1. fwd.
    erewrite load_bytes_of_sep. 1: reflexivity.
    unfold sep. do 2 eexists.
    rewrite map.split_alt.
    unfold mmap.split.
    ssplit. 2: eassumption. all: simpl; exact H.
  Qed.

  (* TODO share with FlatToRiscvCommon *)

  Lemma store_bytes_preserves_footprint: forall n a v (m m': mem),
      Memory.store_bytes n m a v = Some m' ->
      map.same_domain m m'.
  Proof using word_ok mem_ok.
    intros. unfold store_bytes, load_bytes, unchecked_store_bytes in *. fwd.
    eapply map.putmany_of_tuple_preserves_domain; eauto.
  Qed.

  Lemma disjoint_putmany_preserves_store_bytes: forall n a vs (m1 m1' mq: mem),
      store_bytes n m1 a vs = Some m1' ->
      map.disjoint m1 mq ->
      store_bytes n (map.putmany m1 mq) a vs = Some (map.putmany m1' mq).
  Proof using word_ok mem_ok.
    intros.
    unfold store_bytes, load_bytes, unchecked_store_bytes in *. fwd.
    erewrite map.getmany_of_tuple_in_disjoint_putmany by eassumption.
    f_equal.
    set (ks := (footprint a n)) in *.
    rename mq into m2.
    rewrite map.putmany_of_tuple_to_putmany.
    rewrite (map.putmany_of_tuple_to_putmany n m1 ks vs).
    apply map.disjoint_putmany_commutes.
    pose proof map.getmany_of_tuple_to_sub_domain _ _ _ _ E as P.
    apply map.sub_domain_value_indep with (vs2 := vs) in P.
    set (mp := (map.putmany_of_tuple ks vs map.empty)) in *.
    apply map.disjoint_comm.
    eapply map.sub_domain_disjoint; eassumption.
  Qed.

  Lemma store_bytes_frame: forall {n: nat} {m1 m1' m: mem} {a: word} {v: HList.tuple byte n} {F},
      Memory.store_bytes n m1 a v = Some m1' ->
      (eq m1 * F)%sep m ->
      exists m', (eq m1' * F)%sep m' /\ Memory.store_bytes n m a v = Some m'.
  Proof using word_ok mem_ok.
    intros.
    unfold sep in H0.
    destruct H0 as (mp & mq & A & B & C).
    subst mp.
    unfold map.split in A. destruct A as [A1 A2].
    eexists (map.putmany m1' mq).
    split.
    - unfold sep.
      exists m1', mq. repeat split; trivial.
      apply store_bytes_preserves_footprint in H.
      clear -H A2.
      unfold map.disjoint, map.same_domain, map.sub_domain in *. destruct H as [P Q].
      intros.
      edestruct Q; eauto.
    - subst m.
      eauto using disjoint_putmany_preserves_store_bytes.
  Qed.

  Lemma frame_store: forall sz (mSmall mSmall' mBig mAdd: mem) a v,
      mmap.split mBig mSmall mAdd ->
      store sz mSmall a v = Some mSmall' ->
      exists mBig', mmap.split mBig' mSmall' mAdd /\ store sz mBig a v = Some mBig'.
  Proof.
    intros. eapply (store_bytes_frame (F := eq mAdd)) in H0.
    2: {
      unfold sep. do 2 eexists. ssplit. 2,3: reflexivity. eapply map.split_alt; exact H.
    }
    fwd. unfold store, store_Z. rewrite H0p1. eexists. split. 2: reflexivity.
    unfold sep in H0p0. fwd. eapply map.split_alt. assumption.
  Qed.

  Lemma frame_eval_expr: forall l e mSmall mBig mAdd mc (v: word) mc',
      mmap.split mBig mSmall mAdd ->
      eval_expr mSmall l e mc = Some (v, mc') ->
      eval_expr mBig l e mc = Some (v, mc').
  Proof.
    induction e; cbn; intros; fwd; try reflexivity;
      erewrite ?IHe by eassumption;
      erewrite ?IHe1 by eassumption;
      try match goal with
        | |- context[word.eqb ?L ?R] => destr (word.eqb L R)
        end;
      erewrite ?IHe2 by eassumption;
      erewrite ?IHe3 by eassumption;
      erewrite ?frame_load by eassumption;
      rewrite_match;
      try reflexivity.
  Qed.

  Lemma frame_evaluate_call_args_log: forall l mSmall mBig mAdd arges
                                             mc (args: list word) mc',
      mmap.split mBig mSmall mAdd ->
      eval_call_args mSmall l arges mc = Some (args, mc') ->
      eval_call_args mBig   l arges mc = Some (args, mc').
  Proof.
    induction arges; cbn; intros.
    - assumption.
    - fwd. erewrite frame_eval_expr by eassumption. erewrite IHarges.
      1: reflexivity. all: assumption.
  Qed.

  Lemma frame_exec: forall e c t mSmall l mc P,
      exec e c t mSmall l mc P ->
      forall mBig mAdd,
        mmap.split mBig mSmall mAdd ->
        exec e c t mBig l mc (fun t' mBig' l' mc' =>
          exists mSmall', mmap.split mBig' mSmall' mAdd /\ P t' mSmall' l' mc').
  Proof.
    induction 1; intros;
      try match goal with
        | H: store _ _ _ _ = _ |- _ => eapply frame_store in H; [ | eassumption]
        end;
      fwd;
      try solve [econstructor; eauto using frame_eval_expr].
    { eapply exec.stackalloc. 1: eassumption.
      intros.
      rename mCombined into mCombinedBig.
      specialize H1 with (1 := H3).
      specialize (H1 a (mmap.force (mmap.du (mmap.Def mSmall) (mmap.Def (map.of_list_word_at a stack))))).
      eapply map.split_alt in H4. pose proof H4 as D0. unfold mmap.split in D0.
      rewrite H2 in D0.
      rewrite (mmap.du_comm (mmap.Def mSmall) (mmap.Def mAdd)) in D0.
      rewrite mmap.du_assoc in D0. unfold mmap.du at 1 in D0.
      unfold mmap.of_option in D0. fwd. rename r into mCombinedBig.
      symmetry in E0. rename E0 into D0.
      eapply exec.weaken. 1: eapply H1.
      { simpl. eapply map.split_alt. unfold mmap.split. symmetry. assumption. }
      { unfold mmap.split. simpl. rewrite map.du_comm. unfold mmap.of_option.
        rewrite <- D0. reflexivity. }
      cbv beta. intros. fwd.
      move D0 at bottom.
      repeat match reverse goal with
             | H: map.split _ _ _ |- _ => eapply map.split_alt in H
             | H: mmap.split _ _ _ |- _ =>
                 unfold mmap.split in H;
                 let F := fresh "D0" in
                 rename H into F;
                 move F at bottom
             end.
      rewrite D1 in D2. clear D1 mBig. rewrite D4 in D3. clear D4 mSmall'.
      rewrite mmap.du_assoc in D3. rewrite (mmap.du_comm (map.of_list_word_at a stack')) in D3.
      rewrite <- mmap.du_assoc in D3.
      eexists (mmap.force (mmap.du mSmall'0 mAdd)). exists stack'. ssplit.
      { simpl. eapply map.split_alt. unfold mmap.split.
        rewrite D3. f_equal. unfold mmap.du at 1 in D3. fwd. simpl in E0. rewrite E0.
        reflexivity. }
      1: trivial.
      eexists; split. 2: eassumption.
      unfold mmap.split. simpl.
      unfold mmap.du at 1 in D3. fwd. simpl in E0. rewrite E0. reflexivity. }
    { eapply exec.seq. 1: eapply IHexec; eassumption.
      cbv beta. intros. fwd. eapply H1. 1: eassumption. assumption. }
    { eapply exec.while_true.
      1: eauto using frame_eval_expr.
      1: eassumption.
      { eapply IHexec. 1: eassumption. }
      cbv beta. intros. fwd. eauto. }
    { (* call *)
      econstructor. 1: eassumption.
      { eauto using frame_evaluate_call_args_log. }
      1: eassumption.
      1: eapply IHexec. 1: eassumption.
      cbv beta. intros. fwd.
      specialize H3 with (1 := H5p1). fwd. eauto 10. }
    { (* interact *)
      eapply map.split_alt in H. pose proof H3 as A.
      unfold mmap.split in H3, H. rewrite H in H3.
      rewrite mmap.du_assoc in H3. rewrite (mmap.du_comm mGive) in H3.
      rewrite <- mmap.du_assoc in H3.
      assert (exists mKeepBig, mmap.Def mKeepBig = mmap.du mKeep mAdd) as Sp0. {
        exists (mmap.force (mmap.du mKeep mAdd)).
        unfold mmap.du in H3 at 1. unfold mmap.of_option in *.
        fwd. simpl in E. unfold mmap.of_option in E. fwd. reflexivity.
      }
      destruct Sp0 as (mKeepBig & Sp0).
      assert (mmap.split mBig mKeepBig mGive) as Sp.
      { unfold mmap.split. rewrite Sp0. assumption. }
      econstructor. 1: eapply map.split_alt; exact Sp.
      { eauto using frame_evaluate_call_args_log. }
      1: eassumption.
      intros.
      specialize H2 with (1 := H4). fwd.
      eexists. split. 1: eassumption.
      intros.
      eapply map.split_alt in H2. unfold mmap.split in *.
      assert (exists mSmall', mmap.split mSmall' mKeep mReceive) as Sp1. {
        exists (mmap.force (mmap.du mKeep mReceive)).
        eapply map.split_alt. rewrite Sp0 in H2.
        rewrite mmap.du_assoc in H2. rewrite (mmap.du_comm mAdd) in H2.
        rewrite <- mmap.du_assoc in H2.
        unfold mmap.du at 1 in H2. fwd.
        eapply map.split_alt. unfold mmap.split. simpl in E. simpl. rewrite E. reflexivity.
      }
      destruct Sp1 as (mSmall' & Sp1).
      exists mSmall'. split. 2: eapply H2p1.
      2: { eapply map.split_alt. exact Sp1. }
      rewrite Sp0 in H2.
      unfold mmap.split in Sp1. rewrite Sp1. rewrite mmap.du_assoc in H2.
      rewrite (mmap.du_comm mAdd) in H2. rewrite <- mmap.du_assoc in H2.
      exact H2.
    }
  Qed.

End semantics.
