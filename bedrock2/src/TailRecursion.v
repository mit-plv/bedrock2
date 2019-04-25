Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList coqutil.dlet.
Require Import Coq.Classes.Morphisms BinIntDef.
Require Import coqutil.Macros.unique coqutil.Map.Interface coqutil.Word.Interface. Import map.
From bedrock2 Require Import Map.Separation Map.SeparationLogic.
From bedrock2 Require Import Syntax Semantics Markers.
From bedrock2 Require Import WeakestPrecondition WeakestPreconditionProperties.

Section TailRecrsion.
  Context
    {p : unique! Semantics.parameters}
    {p_ok :  forall (trace : list (mem * actname * list word * (mem * list word))) (m0 : mem) (act : actname) (args : list word),  Proper (pointwise_relation mem (pointwise_relation (list word) Basics.impl) ==> Basics.impl) (ext_spec trace m0 act args) }
    {functions : list (funname * (list varname * list varname * Syntax.cmd))}.
  Let call := WeakestPrecondition.call functions.

  Local Notation "A /\ B" := (Markers.split (A /\ B)).
  Local Notation "A /\ B" := (Markers.split (A /\ B)) : type_scope.

  Definition reconstruct (variables:list varname) (values:tuple word (length variables)) : locals :=
    map.putmany_of_tuple (tuple.of_list variables) values map.empty.
  Fixpoint gather (variables : list varname) (l : locals) : option (locals *  tuple word (length variables)) :=
    match variables with
    | nil => Some (l, tt)
    | cons x xs' =>
      match map.get l x with
      | None => None
      | Some v =>
        match gather xs' (map.remove l x) with
        | None => None
        | Some (l, vs') => Some (l, (pair.mk v vs'))
        end
      end
    end.

  Lemma putmany_gather ks vs m me (H : gather ks m = Some (me, vs)) :
    map.putmany_of_tuple (tuple.of_list ks) vs me = m.
  Proof.
    revert H; revert me; revert m; revert vs; induction ks; cbn [gather map.putmany_of_list]; intros.
    { inversion H; subst. exact eq_refl. }
    repeat match type of H with context[match ?x with _ => _ end] => destruct x eqn:? end;
      repeat (match goal with H : _ |- _ => eapply IHks in H end); inversion H; subst; clear H.
    cbn [map.putmany_of_tuple tuple.of_list length].
    match goal with H : _ |- _ => rewrite H; clear H end.
    assert (map.get m a = Some r -> put (remove m a) a r = m) by admit; auto.
    all : fail "goals remaining".
  Admitted.

  Definition enforce (variables : list varname) (values:tuple word (length variables)) (l:locals) : Prop :=
    match gather variables l with
    | None => False
    | Some (remaining, r) => values = r /\ remaining = map.empty
    end.
  Lemma reconstruct_enforce variables ll lm (H : enforce variables ll lm) : lm = reconstruct variables ll.
    progress cbv [enforce] in H.
    repeat match type of H with context[match ?x with _ => _ end] => destruct x eqn:? end;
      destruct H; subst.
    symmetry. eapply putmany_gather. assumption.
  Qed.

  Lemma hlist_forall_foralls: forall (argts : polymorphic_list.list Type) (P : hlist argts -> Prop), (forall x : hlist argts, P x) -> hlist.foralls P.
  Proof. induction argts; cbn; auto. Qed.

  Import pair.
  Lemma tailrec
    {e c t localsmap} {m : mem}
    (ghosttypes : polymorphic_list.list Type)
    (variables : list varname)
    {l0 : tuple word (length variables)}
    {Pl : enforce variables l0 localsmap}
    {post : _->_->_-> Prop}
    {measure : Type} (spec:_->HList.arrows ghosttypes (_->_->ufunc word (length variables) (Prop*(_->_->ufunc word (length variables) Prop)))) lt
    (Hwf : well_founded lt)
    (v0 : measure)
    : hlist.foralls (fun (g0 : hlist ghosttypes) => forall
    (Hpre : (tuple.apply (hlist.apply (spec v0) g0 t m) l0).(1))
    (Hbody : forall v, hlist.foralls (fun g => forall t m, tuple.foralls (fun l =>
      @dlet _ (fun _ => Prop) (reconstruct variables l) (fun localsmap : Semantics.locals =>
      match tuple.apply (hlist.apply (spec v) g t m) l with S_ =>
      S_.(1) ->
      Markers.unique (Markers.left (exists br, expr m localsmap e (eq br) /\ Markers.right (
      (word.unsigned br <> 0%Z -> cmd call c t m localsmap
        (fun t' m' localsmap' =>
          Markers.unique (Markers.left (hlist.existss (fun l' => enforce variables l' localsmap' /\ Markers.right (
          Markers.unique (Markers.left (hlist.existss (fun g' => exists v',
          match tuple.apply (hlist.apply (spec v') g' t' m') l' with S' =>
          S'.(1) /\ Markers.right (
            lt v' v /\
            forall T M, hlist.foralls (fun L => tuple.apply (S'.(2) T M) L -> tuple.apply (S_.(2) T M) L)) end))))))))) /\
      (word.unsigned br = 0%Z -> tuple.apply (S_.(2) t m) l))))end))))
    (Hpost : match (tuple.apply (hlist.apply (spec v0) g0 t m) l0).(2) with Q0 => forall t m, hlist.foralls (fun l =>  tuple.apply (Q0 t m) l -> post t m (reconstruct variables l))end)
    , cmd call (cmd.while e c) t m localsmap post ).
  Proof.
    eapply hlist_forall_foralls; intros g0 **.
    eexists measure, lt, (fun vi ti mi localsmapi =>
      exists gi li, localsmapi = reconstruct variables li /\
      match tuple.apply (hlist.apply (spec vi) gi ti mi) li with S_ =>
      S_.(1) /\ forall T M L, tuple.apply (S_.(2) T M) L ->
        tuple.apply ((tuple.apply (hlist.apply (spec v0) g0 t m) l0).(2) T M) L end).
    cbv [Markers.split Markers.left Markers.right] in *.
    split; [assumption|].
    split. { exists v0, g0, l0. split. 1: eapply reconstruct_enforce; eassumption. split; eauto. }
    intros vi ti mi lmapi (gi&?&?&?&Qi); subst.
    destruct (hlist.foralls_forall (hlist.foralls_forall (Hbody vi) gi ti mi) _ ltac:(eassumption)) as (br&?&X).
    exists br; split; [assumption|]. destruct X as (Htrue&Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [reflexivity..| | |eapply Hpc].
      { eapply Proper_call; firstorder idtac. }
      intros tj mj lmapj Hlj; eapply hlist.existss_exists in Hlj.
      destruct Hlj as (lj&Elj&HE); eapply reconstruct_enforce in Elj; subst lmapj.
      eapply hlist.existss_exists in HE. destruct HE as (l&?&?&?&HR).
      pose proof fun T M => hlist.foralls_forall (HR T M); clear HR.
      eauto 9. }
    { pose proof fun t m => hlist.foralls_forall (Hpost t m); clear Hpost; eauto. }
  Qed.

  Lemma tailrec_localsmap
    {e c t} {m : mem} {l} {post : _->_->_-> Prop}
    {measure : Type} (spec:_->_->_->_->(Prop*(_->_->_-> Prop))) lt
    (Hwf : well_founded lt)
    (v0 : measure) (P0 := (spec v0 t m l).(1)) (Hpre : P0)
    (Q0 := (spec v0 t m l).(2))
    (Hbody : forall v t m l,
      let S := spec v t m l in let (P, Q) := S in
      P ->
      exists br, expr m l e (eq br) /\
      (word.unsigned br <> 0%Z -> cmd call c t m l
        (fun t' m' l' => exists v',
          let S' := spec v' t' m' l' in let '(P', Q') := S' in
          P' /\
          lt v' v /\
          forall T M L, Q' T M L -> Q T M L)) /\
      (word.unsigned br = 0%Z -> Q t m l))
    (Hpost : forall t m l, Q0 t m l -> post t m l)
    : cmd call (cmd.while e c) t m l post.
  Proof.
    eexists measure, lt, (fun v t m l =>
      let S := spec v t m l in let '(P, Q) := S in
      P /\ forall T M L, Q T M L -> Q0 T M L).
    split; [assumption|].
    cbv [Markers.split] in *.
    split; [solve[eauto]|].
    intros vi ti mi li (?&Qi).
    destruct (Hbody _ _ _ _ ltac:(eassumption)) as (br&?&X); exists br; split; [assumption|].
    destruct X as (Htrue&Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [reflexivity..| | |eapply Hpc].
      { eapply Proper_call; firstorder idtac. }
      intros tj mj lj (vj&dP&?&dQ); eauto 9. }
    { eauto. }
  Qed.

  Context {mem_ok : map.ok mem}.
  Local Infix "*" := Separation.sep.
  Local Infix "*" := Separation.sep : type_scope.
  Local Infix "==>" := Lift1Prop.impl1.

  Lemma tailrec_sep
    e c t (m : mem) l (post : _->_->_-> Prop)
    {measure : Type} P Q lt (Hwf : well_founded lt) (v0 : measure) R0
    (Hpre : (P v0 t l * R0) m)
    (Hbody : forall v t m l R, (P v t l * R) m ->
      exists br, expr m l e (eq br) /\
      (word.unsigned br <> 0%Z -> cmd call c t m l
        (fun t' m' l' => exists v' dR, (P v' t' l' * (R * dR)) m' /\
          lt v' v /\
          forall T L, Q v' T L * dR ==> Q v T L)) /\
      (word.unsigned br = 0%Z -> (Q v t l * R) m))
    (Hpost : forall t m l, (Q v0 t l * R0) m -> post t m l)
    : cmd call (cmd.while e c) t m l post.
  Proof.
    eexists measure, lt, (fun v t m l => exists R, (P v t l * R) m /\
                          forall T L, Q v T L * R ==> Q v0 T L * R0).
    split; [assumption|].
    split. { exists v0, R0. split; [assumption|]. intros. reflexivity. }
    intros vi ti mi li (Ri&?&Qi).
    destruct (Hbody _ _ _ _ _ ltac:(eassumption)) as (br&?&X); exists br; split; [assumption|].
    destruct X as (Htrue&Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [reflexivity..| | |eapply Hpc].
      { eapply Proper_call; firstorder idtac. }
      intros tj mj lj (vj&dR&dP&?&dQ).
      exists vj; split; [|assumption].
      exists (Ri * dR); split; [assumption|].
      intros. rewrite (sep_comm _ dR), <-(sep_assoc _ dR), dQ; trivial. }
    { eapply Hpost, Qi, Hpc. }
  Qed.
End TailRecrsion.
