Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList coqutil.dlet.
Require Import Coq.Classes.Morphisms BinIntDef.
Require Import coqutil.Macros.unique coqutil.Map.Interface coqutil.Word.Interface. Import map.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.destr.
From bedrock2 Require Import Map.Separation Map.SeparationLogic.
From bedrock2 Require Import Syntax MetricSemantics Markers.
From bedrock2 Require Semantics.
From bedrock2 Require Import MetricWeakestPrecondition MetricWeakestPreconditionProperties.

Require Import bedrock2.MetricLogging.
Require Import bedrock2.MetricCosts.

Section Loops.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {fs : Semantics.env}.
  Let call := fs.

  Local Notation UNK := String.EmptyString.

  Lemma wp_while: forall e c t m l mc (post: _ -> _ -> _ -> _ -> Prop),
     (exists measure (lt:measure->measure->Prop) (inv:measure->Semantics.trace->mem->locals->MetricLog->Prop),
      Coq.Init.Wf.well_founded lt /\
      (exists v, inv v t m l mc) /\
      (forall v t m l mc, inv v t m l mc ->
        exists bv bmc, dexpr m l e mc (bv, bmc) /\
        (word.unsigned bv <> 0%Z -> cmd call c t m l bmc (fun t' m' l' mc' =>
          exists v', inv v' t' m' l' (cost_loop_true isRegStr UNK (Some UNK) mc')
            /\ lt v' v)) /\
        (word.unsigned bv = 0%Z -> post t m l
          (cost_loop_false isRegStr UNK (Some UNK) bmc)))) ->
     cmd call (cmd.while e c) t m l mc post.
  Proof.
    intros. destruct H as (measure & lt & inv & Hwf & HInit & Hbody).
    destruct HInit as (v0 & HInit).
    revert t m l mc HInit. pattern v0. revert v0.
    eapply (well_founded_ind Hwf). intros.
    specialize Hbody with (1 := HInit) (mc := mc). destruct Hbody as (bv & bmc & Hb & Ht & Hf).
    eapply expr_sound in Hb. destruct Hb as (bv' & bmc' & Hb & Heq). inversion Heq. subst bv' bmc'.
    destr.destr (Z.eqb (word.unsigned bv) 0).
    - specialize Hf with (1 := E). eapply exec.while_false; try eassumption.
    - specialize Ht with (1 := E). eapply sound_cmd in Ht.
      eapply exec.while_true; eauto.
      cbv beta. intros * (v' & HInv & HLt). eapply sound_cmd. eauto.
  Qed.

  Lemma tailrec_localsmap_1ghost
    {e c t} {m: mem} {l} {mc} {post : Semantics.trace -> mem -> locals -> MetricLog -> Prop}
    {measure: Type} {Ghost: Type}
    (P Q: measure -> Ghost -> Semantics.trace -> mem -> locals -> MetricLog -> Prop)
    (lt: measure -> measure -> Prop)
    (Hwf: well_founded lt)
    (v0: measure) (g0: Ghost)
    (Hpre: P v0 g0 t m l mc)
    (Hbody: forall v g t m l mc,
      P v g t m l mc ->
      exists brv brmc, expr m l e mc (eq (brv, brmc)) /\
      (word.unsigned brv <> 0%Z -> cmd call c t m l brmc
        (fun t' m' l' mc' => exists v' g',
          P v' g' t' m' l' (cost_loop_true isRegStr UNK (Some UNK) mc') /\
          lt v' v /\
          (forall t'' m'' l'' mc'', Q v' g' t'' m'' l'' mc'' -> Q v g t'' m'' l'' mc''))) /\
      (word.unsigned brv = 0%Z -> Q v g t m l
        (cost_loop_false isRegStr UNK (Some UNK) brmc)))
    (Hpost: forall t m l mc, Q v0 g0 t m l mc -> post t m l mc)
    : cmd call (cmd.while e c) t m l mc post.
  Proof.
    eapply wp_while.
    eexists measure, lt, (fun v t m l mc =>
      exists g, P v g t m l mc /\ forall t'' m'' l'' mc'', Q v g t'' m'' l'' mc'' -> Q v0 g0 t'' m'' l'' mc'').
    split; [assumption|].
    split; [solve[eauto]|].
    intros vi ti mi li mci (gi & HPi & HQimpl).
    specialize (Hbody vi gi ti mi li mci HPi).
    destruct Hbody as (brv & brmc & ? & Hbody). exists brv, brmc; split; [assumption|].
    destruct Hbody as (Htrue & Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [ |eapply Hpc].
      intros tj mj lj mcj (vj& gj & HPj & Hlt & Qji); eauto 9. }
    { eauto. }
  Qed.

  Lemma tailrec_localsmap_1ghost_parameterized_finalpost
    {e c rest t} {m: mem} {l mc}
    {measure: Type} {Ghost: Type}
    (P Q: measure -> Ghost -> Semantics.trace -> mem -> locals -> MetricLog -> Prop)
    (lt: measure -> measure -> Prop)
    (Hwf: well_founded lt)
    (v0: measure) (g0: Ghost)
    (Hpre: P v0 g0 t m l mc)
    (Hbody: forall v g t m l mc,
      P v g t m l mc ->
      exists brv brmc, expr m l e mc (eq (brv, brmc)) /\
      (word.unsigned brv <> 0%Z -> cmd call c t m l brmc
        (fun t' m' l' mc' => exists v' g',
          P v' g' t' m' l' (cost_loop_true isRegStr UNK (Some UNK) mc') /\
          lt v' v /\
          (forall t'' m'' l'' mc'', Q v' g' t'' m'' l'' mc'' -> Q v g t'' m'' l'' mc''))) /\
      (word.unsigned brv = 0%Z -> cmd call rest t m l
        (cost_loop_false isRegStr UNK (Some UNK) brmc) (Q v g)))
    : cmd call (cmd.seq (cmd.while e c) rest) t m l mc (Q v0 g0).
  Proof.
    cbn. eapply tailrec_localsmap_1ghost with
      (Q := fun v g t m l mc => cmd call rest t m l mc (Q v g)).
    1: eassumption.
    1: exact Hpre.
    2: intros *; exact id.
    intros vi gi ti mi li mci HPi.
    specialize (Hbody vi gi ti mi li mci HPi).
    destruct Hbody as (brv & brmc & ? & Hbody). exists brv, brmc; split; [assumption|].
    destruct Hbody as (Htrue & Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [ |eapply Hpc].
      intros tj mj lj mcj (vj& gj & HPj & Hlt & Qji). do 2 eexists.
      split. 1: eassumption. split. 1: assumption.
      intros.
      eapply Proper_cmd.
      2: eassumption.
      intros tk mk lk mck HH. eapply Qji. assumption. }
    eapply Hpc.
  Qed.

  (* marking logical connectives with the source file they were used in for limiting unfolding *)
  Local Notation "A /\ B" := (Markers.split (A /\ B)).
  Local Notation "A /\ B" := (Markers.split (A /\ B)) : type_scope.

  (* shallow reflection for resolving map accesses during symbolic execution *)
  (* each lemma below is duplicated for various levels of use of this trick *)
  Definition reconstruct (variables:list String.string) (values:tuple word (length variables)) : locals :=
    map.putmany_of_tuple (tuple.of_list variables) values map.empty.
  Fixpoint gather (variables : list String.string) (l : locals) : option (locals *  tuple word (length variables)) :=
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
    assert (map.get m a = Some r -> put (remove m a) a r = m). {
      intro A.
      apply map_ext.
      intro k.
      erewrite map.get_put_dec.
      destr (String.eqb a k); try congruence.
      rewrite map.get_remove_diff; congruence.
    }
    auto.
  Qed.

  Definition enforce (variables : list String.string) (values:tuple word (length variables)) (l:locals) : Prop :=
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

  Lemma while_localsmap
    {e c t l mc} {m : mem}
    {measure : Type} (invariant:_->_->_->_->_->Prop)
    {lt} (Hwf : well_founded lt) (v0 : measure)
    {post : _->_->_->_-> Prop}
    (Hpre : invariant v0 t m l mc)
    (Hbody : forall v t m l mc,
      invariant v t m l mc ->
      exists brv brmc, expr m l e mc (eq (Datatypes.pair brv brmc)) /\
         (word.unsigned brv <> 0 ->
          cmd fs c t m l brmc (fun t m l mc => exists v',
            invariant v' t m l (cost_loop_true isRegStr UNK (Some UNK) mc)
              /\ lt v' v)) /\
         (word.unsigned brv = 0 -> post t m l
           (cost_loop_false isRegStr UNK (Some UNK) brmc)))
    : cmd fs (cmd.while e c) t m l mc post.
  Proof.
    eapply wp_while.
    eexists measure, lt, invariant.
    split. 1: exact Hwf.
    split. 1: eauto.
    exact Hbody.
  Qed.

  Lemma while
    {e c t l mc} {m : mem}
    (variables : list String.string)
    {localstuple : tuple word (length variables)}
    {measure : Type} (invariant:_->_->_->_-> ufunc word (length variables) Prop)
    {lt} (Hwf : well_founded lt) (v0 : measure)
    {post : _->_->_-> _ -> Prop}
    (Pl : enforce variables localstuple l)
    (Hpre : tuple.apply (invariant v0 t m mc) localstuple)
    (Hbody : forall v t m mc, tuple.foralls (fun localstuple =>
      tuple.apply (invariant v t m mc) localstuple ->
      let l := reconstruct variables localstuple in
      exists brv brmc, expr m l e mc (eq (Datatypes.pair brv brmc)) /\
         (word.unsigned brv <> 0 ->
          cmd call c t m l brmc (fun t m l mc =>
            Markers.unique (Markers.left (tuple.existss (fun localstuple =>
              enforce variables localstuple l /\
              Markers.right (Markers.unique (exists v',
                tuple.apply (invariant v' t m (cost_loop_true isRegStr UNK (Some UNK) mc)) localstuple /\ lt v' v))))))) /\
         (word.unsigned brv = 0 -> post t m l (cost_loop_false isRegStr UNK (Some UNK) brmc))))
    : cmd call (cmd.while e c) t m l mc post.
  Proof.
    eapply (while_localsmap (fun v t m l mc =>
      exists localstuple, enforce variables localstuple l /\
                          tuple.apply (invariant v t m mc) localstuple));
      unfold Markers.split; eauto.
    intros vi ti mi li mci (?&X&Y).
    specialize (Hbody vi ti mi mci).
    eapply hlist.foralls_forall in Hbody.
    specialize (Hbody Y).
    rewrite <-(reconstruct_enforce _ _ _ X) in Hbody.
    destruct Hbody as (brv & brmc & Cond & Again & Done).
    exists brv. exists brmc. split; [exact Cond|].

    split; [|exact Done].
    intro NE. specialize (Again NE).
    eapply Proper_cmd; [ |eapply Again].
    cbv [Morphisms.pointwise_relation Basics.impl Markers.right Markers.unique Markers.left] in *.
    intros t' m' l' mc' Ex.
    eapply hlist.existss_exists in Ex. cbv beta in Ex. destruct Ex as (ls & E & v' & Inv' & LT).
    eauto.
  Qed.

  Lemma tailrec
    {e c t localsmap mc} {m : mem}
    (ghosttypes : polymorphic_list.list Type)
    (variables : list String.string)
    {l0 : tuple word (length variables)}
    {Pl : enforce variables l0 localsmap}
    {post : _->_->_->_-> Prop}
    {measure : Type} (spec:_->HList.arrows ghosttypes (_->_->ufunc word (length variables) (MetricLog -> Prop*(_->_->ufunc word (length variables) (MetricLog -> Prop))))) lt
    (Hwf : well_founded lt)
    (v0 : measure)
    : hlist.foralls (fun (g0 : hlist ghosttypes) => forall
                         (Hpre : (tuple.apply (hlist.apply (spec v0) g0 t m) l0 mc).(1))

    (Hbody : forall v, hlist.foralls (fun g => forall t m mc, tuple.foralls (fun l =>
      @dlet _ (fun _ => Prop) (reconstruct variables l) (fun localsmap : locals =>
      match tuple.apply (hlist.apply (spec v) g t m) l mc with S_ =>
      S_.(1) ->
      Markers.unique (Markers.left (exists brv brmc, expr m localsmap e mc (eq (Datatypes.pair brv brmc)) /\ Markers.right (
      (word.unsigned brv <> 0%Z -> cmd call c t m localsmap brmc
        (fun t' m' localsmap' mc' =>
          Markers.unique (Markers.left (hlist.existss (fun l' => enforce variables l' localsmap' /\ Markers.right (
          Markers.unique (Markers.left (hlist.existss (fun g' => exists v',
          match tuple.apply (hlist.apply (spec v') g' t' m') l' (cost_loop_true isRegStr UNK (Some UNK) mc') with S' =>
          S'.(1) /\ Markers.right (
            lt v' v /\
            forall T M, hlist.foralls (fun L => forall MC, tuple.apply (S'.(2) T M) L MC -> tuple.apply (S_.(2) T M) L MC)) end))))))))) /\
      (word.unsigned brv = 0%Z -> tuple.apply (S_.(2) t m) l (cost_loop_false isRegStr UNK (Some UNK) brmc)))))end))))
    (Hpost : match (tuple.apply (hlist.apply (spec v0) g0 t m) l0 mc).(2) with Q0 => forall t m mc, hlist.foralls (fun l =>  tuple.apply (Q0 t m) l mc -> post t m (reconstruct variables l) mc)end)
    , cmd call (cmd.while e c) t m localsmap mc post ).
  Proof.
    eapply hlist_forall_foralls; intros g0 **.
    eapply wp_while.
    eexists measure, lt, (fun vi ti mi localsmapi mci =>
      exists gi li, localsmapi = reconstruct variables li /\
      match tuple.apply (hlist.apply (spec vi) gi ti mi) li mci with S_ =>
      S_.(1) /\ forall T M L MC, tuple.apply (S_.(2) T M) L MC->
        tuple.apply ((tuple.apply (hlist.apply (spec v0) g0 t m) l0 mc).(2) T M) L MC end).
    cbv [Markers.split Markers.left Markers.right] in *.
    split; [assumption|].
    split. { exists v0, g0, l0. split. 1: eapply reconstruct_enforce; eassumption. split; eauto. }
    intros vi ti mi lmapi mci (gi&?&?&?&Qi); subst.
    destruct (hlist.foralls_forall (hlist.foralls_forall (Hbody vi) gi ti mi mci) _ ltac:(eassumption)) as (brv&brmc&?&X).


    exists brv; exists brmc; split; [assumption|]. destruct X as (Htrue&Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [ |eapply Hpc].
      intros tj mj lmapj mcj Hlj; eapply hlist.existss_exists in Hlj.
      destruct Hlj as (lj&Elj&HE); eapply reconstruct_enforce in Elj; subst lmapj.
      eapply hlist.existss_exists in HE. destruct HE as (l&?&?&?&HR).
      pose proof fun T M => hlist.foralls_forall (HR T M); clear HR.
      eauto 9. }
    { pose proof fun t m mc => hlist.foralls_forall (Hpost t m mc); clear Hpost; eauto. }
  Qed.

  Lemma tailrec_localsmap
    {e c t} {m : mem} {l mc} {post : _ -> _->_->_-> Prop}
    {measure : Type} (spec:_->_->_->_->_->(Prop*(_->_->_->_-> Prop))) lt
    (Hwf : well_founded lt)
    (v0 : measure) (P0 := (spec v0 t m l mc).(1)) (Hpre : P0)
    (Q0 := (spec v0 t m l mc).(2))
    (Hbody : forall v t m l mc,
      let S := spec v t m l mc in let (P, Q) := S in
      P ->
      exists br mc', expr m l e mc (eq (Datatypes.pair br mc')) /\
      (word.unsigned br <> 0%Z -> cmd call c t m l mc'
        (fun t' m' l' mc''=> exists v',
          let S' := spec v' t' m' l' (cost_loop_true isRegStr UNK (Some UNK) mc'') in let '(P', Q') := S' in
          P' /\
          lt v' v /\
          forall T M L MC, Q' T M L MC -> Q T M L MC)) /\
      (word.unsigned br = 0%Z -> Q t m l (cost_loop_false isRegStr UNK (Some UNK) mc')))
    (Hpost : forall t m l mc, Q0 t m l mc -> post t m l mc)
    : cmd call (cmd.while e c) t m l mc post.
  Proof.
    eapply wp_while.
    eexists measure, lt, (fun v t m l mc =>
      let S := spec v t m l mc in let '(P, Q) := S in
      P /\ forall T M L MC, Q T M L MC -> Q0 T M L MC).
    split; [assumption|].
    cbv [Markers.split] in *.
    split; [solve[eauto]|].
    intros vi ti mi li mci (?&Qi).
    destruct (Hbody _ _ _ _ _ ltac:(eassumption)) as (br&?&?&X); exists br; eexists; split; [eassumption|].
    destruct X as (Htrue&Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [ |eapply Hpc].
      intros tj mj lj mcj (vj&dP&?&dQ); eauto 9. }
    { eauto. }
  Qed.

   Definition with_bottom {T} R (x y : option T) :=
    match x, y with
    | None, Some _ => True
    | Some x, Some y => R x y
    | _, _ => False
    end.
  Lemma well_founded_with_bottom {T} R (H : @well_founded T R) : well_founded (with_bottom R).
  Proof.
    intros [x|]; cycle 1.
    { constructor; intros [] HX; cbv [with_bottom] in HX; contradiction. }
    pattern x. revert x. eapply (@well_founded_ind _ _ H). intros.
    constructor. intros [y|] pf; eauto.
    constructor. intros [] [].
  Qed.
End Loops.

Ltac loop_simpl :=
  cbn [reconstruct map.putmany_of_list HList.tuple.to_list
       HList.hlist.foralls HList.tuple.foralls
       HList.hlist.existss HList.tuple.existss
       HList.hlist.apply HList.tuple.apply HList.hlist
       List.repeat Datatypes.length
       HList.polymorphic_list.repeat HList.polymorphic_list.length
       PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
