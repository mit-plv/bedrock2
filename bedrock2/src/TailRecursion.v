Require Import Coq.Classes.Morphisms.
From bedrock2 Require Import Macros Syntax Semantics.
From bedrock2 Require Import WeakestPrecondition WeakestPreconditionProperties.
From bedrock2 Require Import Map Map.Separation Map.SeparationLogic.

Section TailRecrsion.
  Context
    {p : unique! Semantics.parameters}
    {rely guarantee : trace -> Prop}
    {progress : trace -> trace -> Prop}
    {call : funname -> trace -> mem -> list word -> (trace -> mem -> list word -> Prop) -> Prop}
    {Proper_call : Proper (pointwise_relation _ (pointwise_relation _
      (pointwise_relation _ (pointwise_relation _ (pointwise_relation _
      (pointwise_relation _ (pointwise_relation _ Basics.impl)) ==>
      Basics.impl)))))%signature call}.

  Lemma tailrec
    e c t (m : mem) l (post : _->_->_-> Prop)
    {measure : Type} (P Q:_->_->_->_->Prop) lt (Hwf : well_founded lt) (v0 : measure)
    (Hpre : P v0 t m l)
    (Hbody : forall v t m l, P v t m l ->
      exists br, expr m l e (eq br) /\
      (word_test br = true -> cmd rely guarantee progress call c t m l
        (fun t' m' l' => exists v', P v' t' m' l' /\
          (progress t' t \/ lt v' v) /\
          forall T M L, Q v' T M L -> Q v T M L)) /\
      (word_test br = false -> Q v t m l))
    (Hpost : forall t m l, Q v0 t m l -> post t m l)
    : cmd rely guarantee progress call (cmd.while e c) t m l post.
  Proof.
    eexists measure, lt, (fun v t m l => P v t m l /\
                          forall T M L, Q v T M L -> Q v0 T M L).
    split. assumption.
    split; [solve[eauto]|].
    intros vi ti mi li (?&Qi).
    destruct (Hbody _ _ _ _ ltac:(eassumption)) as (br&?&X); exists br; split; [assumption|].
    destruct X as (Htrue&Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [reflexivity..|eassumption| |eapply Hpc].
      intros tj mj lj (vj&dP&?&dQ); eauto 9. }
    { eapply Hpost, Qi, Hpc. }
  Qed.

  Lemma tailrec2
    e c t (m : mem) l (post : _->_->_-> Prop)
    {measure : Type} {X} (P Q:_->X->_->_->_->Prop) lt (Hwf : well_founded lt)
    (v0 : measure) (x0 : X)
    (Hpre : P v0 x0 t m l)
    (Hbody : forall v x t m l, P v x t m l ->
      exists br, expr m l e (eq br) /\
      (word_test br = true -> cmd rely guarantee progress call c t m l
        (fun t' m' l' => exists v' x', P v' x' t' m' l' /\
          (progress t' t \/ lt v' v) /\
          forall T M L, Q v' x' T M L -> Q v x T M L)) /\
      (word_test br = false -> Q v x t m l))
    (Hpost : forall t m l, Q v0 x0 t m l -> post t m l)
    : cmd rely guarantee progress call (cmd.while e c) t m l post.
  Proof.
    eexists measure, lt, (fun v t m l => exists x, P v x t m l /\
                          forall T M L, Q v x T M L -> Q v0 x0 T M L).
    split. assumption.
    split; [solve[eauto]|].
    intros vi ti mi li (?&?&Qi).
    destruct (Hbody _ _ _ _ _ ltac:(eassumption)) as (br&?&XX); exists br; split; [assumption|].
    destruct XX as (Htrue&Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [reflexivity..|eassumption| |eapply Hpc].
      intros tj mj lj (vj&xj&dP&?&dQ); eauto 9. }
    { eapply Hpost, Qi, Hpc. }
  Qed.
  Notation tailrec1 := tailrec.

  Lemma tailrec3
    e c t (m : mem) l (post : _->_->_-> Prop)
    {measure : Type} {X Y} (P Q:_->X->Y->_->_->_->Prop) lt (Hwf : well_founded lt)
    (v0 : measure) (x0 : X) (y0 : Y)
    (Hpre : P v0 x0 y0 t m l)
    (Hbody : forall v x y t m l, P v x y t m l ->
      exists br, expr m l e (eq br) /\
      (word_test br = true -> cmd rely guarantee progress call c t m l
        (fun t' m' l' => exists v' x' y', P v' x' y' t' m' l' /\
          (progress t' t \/ lt v' v) /\
          forall T M L, Q v' x' y' T M L -> Q v x y T M L)) /\
      (word_test br = false -> Q v x y t m l))
    (Hpost : forall t m l, Q v0 x0 y0 t m l -> post t m l)
    : cmd rely guarantee progress call (cmd.while e c) t m l post.
  Proof.
    eexists measure, lt, (fun v t m l => exists x y, P v x y t m l /\
                          forall T M L, Q v x y T M L -> Q v0 x0 y0 T M L).
    split. assumption.
    split; [solve[eauto]|].
    intros vi ti mi li (?&?&?&Qi).
    destruct (Hbody _ _ _ _ _ _ ltac:(eassumption)) as (br&?&XX); exists br; split; [assumption|].
    destruct XX as (Htrue&Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [reflexivity..|eassumption| |eapply Hpc].
      intros tj mj lj (vj&xj&yj&dP&?&dQ); eauto 9. }
    { eapply Hpost, Qi, Hpc. }
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
      (word_test br = true -> cmd rely guarantee progress call c t m l
        (fun t' m' l' => exists v' dR, (P v' t' l' * (R * dR)) m' /\
          (progress t' t \/ lt v' v) /\
          forall T L, Q v' T L * dR ==> Q v T L)) /\
      (word_test br = false -> (Q v t l * R) m))
    (Hpost : forall t m l, (Q v0 t l * R0) m -> post t m l)
    : cmd rely guarantee progress call (cmd.while e c) t m l post.
  Proof.
    eexists measure, lt, (fun v t m l => exists R, (P v t l * R) m /\
                          forall T L, Q v T L * R ==> Q v0 T L * R0).
    split. assumption.
    split. { exists v0, R0. split. assumption. intros. reflexivity. }
    intros vi ti mi li (Ri&?&Qi).
    destruct (Hbody _ _ _ _ _ ltac:(eassumption)) as (br&?&X); exists br; split; [assumption|].
    destruct X as (Htrue&Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [reflexivity..|eassumption| |eapply Hpc].
      intros tj mj lj (vj&dR&dP&?&dQ).
      exists vj; split; [|assumption].
      exists (Ri * dR); split; [assumption|].
      intros. rewrite <-sep_213, sep_comm, dQ, Qi. reflexivity. }
    { eapply Hpost, Qi, Hpc. }
  Qed.
End TailRecrsion.