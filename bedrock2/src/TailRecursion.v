Require Import bedrock2.PrimitivePair bedrock2.HList bedrock2.dlet.
Require Import Coq.Classes.Morphisms.
From bedrock2 Require Import Macros Syntax Semantics Markers.
From bedrock2 Require Import WeakestPrecondition WeakestPreconditionProperties.
From bedrock2 Require Import Map Map.Separation Map.SeparationLogic.

Section TailRecrsion.
  Context
    {p : unique! Semantics.parameters}
    {rely guarantee : trace -> Prop}
    {progress : trace -> trace -> Prop}
    {functions : list (funname * (list varname * list varname * Syntax.cmd))}.
  Let call := WeakestPrecondition.call rely guarantee progress functions.

  Local Notation "A /\ B" := (Markers.split (A /\ B)).
  Local Notation "A /\ B" := (Markers.split (A /\ B)) : type_scope.

  Definition reconstruct (variables:list varname) (values:tuple word (length variables)) : locals :=
    match map.putmany variables (tuple.to_list values) map.empty with
    | None => map.empty (* never happens by input types *)
    | Some x => x
    end.
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
  Definition enforce (variables : list varname) (values:tuple word (length variables)) (l:locals) : Prop :=
    match gather variables l with
    | None => False
    | Some (remaining, r) => values = r /\ remaining = map.empty
    end.
  Lemma reconstruct_enforce : forall variables ll lm, enforce variables ll lm -> lm = reconstruct variables ll.
  Admitted.

  Import pair.
  Lemma tailrec
    {e c t localsmap} {m : mem}
    (ghosttypes : list Type)
    (variables : list varname)
    {l0 : tuple word (length variables)}
    {Pl : enforce variables l0 localsmap}
    {post : _->_->_-> Prop}
    {measure : Type} (spec:_->HList.arrows ghosttypes (_->_->ufunc word (length variables) (Prop*(_->_->ufunc word (length variables) Prop)))) lt
    (Hwf : well_founded lt)
    (v0 : measure) (g0 : hlist ghosttypes)
    (Hpre : (tuple.apply (hlist.apply (spec v0) g0 t m) l0).(1))
    (Hbody : forall v, hlist.foralls (fun g => forall t m, tuple.foralls (fun l =>
      @dlet _ (fun _ => Prop) (reconstruct variables l) (fun localsmap : Semantics.locals => 
      match tuple.apply (hlist.apply (spec v) g t m) l with S_ =>
      S_.(1) ->
      Markers.unique (Markers.left (exists br, expr m localsmap e (eq br) /\ Markers.right (
      (word_test br = true -> cmd rely guarantee progress call c t m localsmap
        (fun t' m' localsmap' =>
          Markers.unique (Markers.left (hlist.existss (fun l' => enforce variables l' localsmap' /\ Markers.right (
          Markers.unique (Markers.left (hlist.existss (fun g' => exists v', 
          match tuple.apply (hlist.apply (spec v') g' t' m') l' with S' =>
          S'.(1) /\ Markers.right (
            (progress t' t \/ lt v' v) /\
            forall T M, hlist.foralls (fun L => tuple.apply (S'.(2) T M) L -> tuple.apply (S_.(2) T M) L)) end))))))))) /\
      (word_test br = false -> tuple.apply (S_.(2) t m) l))))end))))
    (Hpost : match (tuple.apply (hlist.apply (spec v0) g0 t m) l0).(2) with Q0 => forall t m l, tuple.apply (Q0 t m) l -> post t m (reconstruct variables l)end)
    : cmd rely guarantee progress call (cmd.while e c) t m localsmap post.
  Proof.
    eexists measure, lt, (fun vi ti mi localsmapi =>
      exists gi li, localsmapi = reconstruct variables li /\
      match tuple.apply (hlist.apply (spec vi) gi ti mi) li with S_ =>
      S_.(1) /\ forall T M L, tuple.apply (S_.(2) T M) L ->
        tuple.apply ((tuple.apply (hlist.apply (spec v0) g0 t m) l0).(2) T M) L end).
    cbv [Markers.split Markers.left Markers.right] in *.
    split. assumption.
    split. { exists v0, g0, l0. split. eapply reconstruct_enforce. eassumption. split; eauto. }
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
    { eauto. }
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
      (word_test br = true -> cmd rely guarantee progress call c t m l
        (fun t' m' l' => exists v',
          let S' := spec v' t' m' l' in let '(P', Q') := S' in
          P' /\
          (progress t' t \/ lt v' v) /\
          forall T M L, Q' T M L -> Q T M L)) /\
      (word_test br = false -> Q t m l))
    (Hpost : forall t m l, Q0 t m l -> post t m l)
    : cmd rely guarantee progress call (cmd.while e c) t m l post.
  Proof.
    eexists measure, lt, (fun v t m l =>
      let S := spec v t m l in let '(P, Q) := S in
      P /\ forall T M L, Q T M L -> Q0 T M L).
    split. assumption.
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
    { eapply Proper_cmd; [reflexivity..| | |eapply Hpc].
      { eapply Proper_call; firstorder idtac. }
      intros tj mj lj (vj&dR&dP&?&dQ).
      exists vj; split; [|assumption].
      exists (Ri * dR); split; [assumption|].
      intros. rewrite (sep_comm _ dR), <-(sep_assoc _ dR), dQ; trivial. }
    { eapply Hpost, Qi, Hpc. }
  Qed.
End TailRecrsion.