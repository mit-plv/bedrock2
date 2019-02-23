Require Import coqutil.Decidable.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import bedrock2.Semantics.

Section WithParams.

  Context (p1: Semantics.parameters).

  Context (unmapped: @word p1 -> Prop).

  Definition respects_unmapped(m: @mem p1): Prop :=
    forall a, unmapped a -> map.get m a = None.

  Definition p2: Semantics.parameters := {|
    Semantics.syntax := @syntax p1;
    Semantics.width := @width p1;
    Semantics.word := @word p1;
    Semantics.byte := @byte p1;
    Semantics.mem := @mem p1;
    Semantics.locals := @locals p1;
    Semantics.funname_env := @funname_env p1;
    Semantics.funname_eqb := @funname_eqb p1;
    Semantics.ext_spec t m a args post :=
      respects_unmapped m -> @ext_spec p1 t m a args post;
  |}.

  Context {mem_ok: map.ok mem} {word_eq_dec: DecidableEq word}.

  Lemma store_preserves_respects_unmapped: forall sz m a v m',
      store sz m a v = Some m' ->
      respects_unmapped m ->
      respects_unmapped m'.
  Proof.
    unfold respects_unmapped.
    intros.
    pose proof @store_preserves_domain as P.
    specialize P with (3 := H).
    pose proof (P _ _) as Q. unfold map.same_domain, map.sub_domain in Q. destruct Q as [Q1 Q2].
    specialize H0 with (1 := H1).
    destruct (map.get m' a0) eqn: E; [exfalso|reflexivity].
    specialize Q2 with (1 := E). destruct Q2 as [v2 Q2]. rewrite Q2 in H0. discriminate.
  Qed.

  Hint Resolve store_preserves_respects_unmapped.

  Hint Constructors exec.exec.

  Lemma add_respects_unmapped_aux: forall e c t m l post,
      @exec.exec p1 e c t m l post ->
      respects_unmapped m ->
      @exec.exec p2 e c t m l (fun t' m' l' => respects_unmapped m' /\ post t' m' l').
  Proof.
    induction 1; intros;
      (* TODO can we make unification smart enough so that we don't have
         to list these constructors with p2 explicitly? *)
      [ eapply (@exec.skip p2)
      | eapply (@exec.set p2)
      | eapply (@exec.unset p2)
      | eapply (@exec.store p2)
      | eapply (@exec.if_true p2)
      | eapply (@exec.if_false p2)
      | eapply (@exec.seq p2)
      | eapply (@exec.while_false p2)
      | eapply (@exec.while_true p2)
      | eapply (@exec.call p2)
      | eapply (@exec.interact p2) ];
      eauto.

  Abort.

End WithParams.
