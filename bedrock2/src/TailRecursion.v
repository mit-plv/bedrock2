Require Import Coq.Classes.Morphisms.
From bedrock2 Require Import Macros Syntax Semantics.
From bedrock2 Require Import WeakestPrecondition WeakestPreconditionProperties.
From bedrock2 Require Import Map Map.Separation Map.SeparationLogic.

Section TailRecrsion.
  Context {p : unique! Semantics.parameters}.
  Local Infix "*" := Separation.sep.
  Local Infix "*" := Separation.sep : type_scope.
  Local Infix "==>" := Lift1Prop.impl1.
  Lemma tailrecursion {mem_ok:Map.map.ok mem} {rely guarantee progress call}
    {Proper_call : Proper (pointwise_relation _ (pointwise_relation _
      (pointwise_relation _ (pointwise_relation _ (pointwise_relation _
      (pointwise_relation _ (pointwise_relation _ Basics.impl)) ==>
      Basics.impl)))))%signature call}
    e c t (m : mem) l (post : _->_->_-> Prop)
    {measure : Type} P Q lt (Hwf : well_founded lt) (v0 : measure) R0
    (Hpre : (P v0 t l * R0) m)
    (Hbody : forall v t m l R, (P v t l * R) m ->
      expr m l e (fun br =>
        (word_test br = true -> cmd rely guarantee progress call c t m l
          (fun t' m' l' => exists v' dR, (P v' t' l' * (R * dR)) m' /\
            (progress t' t \/ lt v' v) /\
            forall T L, Q v' T L * dR ==> Q v T L)) /\
        (word_test br = false -> (Q v t l * R) m)))
    (Hpost : forall t m l, (Q v0 t l * R0) m -> post t m l)
    : cmd rely guarantee progress call (cmd.while e c) t m l post.
  Proof.
    eexists measure, lt, (fun v t m l => exists R, (P v t l * R) m /\
                          forall T L, Q v T L * R ==> Q v0 T L * R0).
    split. assumption.
    split. { exists v0, R0. split. assumption. intros. reflexivity. }
    intros vi ti mi li (Ri&?&Qi).
    eapply Proper_expr; [|solve[eauto using Hbody]]; clear Hbody.
    intros br (Htrue&Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [reflexivity..|eassumption| |eapply Hpc].
      intros tj mj lj (vj&dR&dP&?&dQ).
      exists vj; split; [|assumption].
      exists (Ri * dR); split; [assumption|].
      intros. rewrite <-sep_213, sep_comm, dQ, Qi. reflexivity. }
    { eapply Hpost, Qi, Hpc. }
  Qed.
End TailRecrsion.