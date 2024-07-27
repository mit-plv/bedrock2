Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList coqutil.dlet.
From Coq Require Import Morphisms BinIntDef.
Require Import coqutil.Macros.unique coqutil.Map.Interface coqutil.Word.Interface. Import map.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.destr.
From bedrock2 Require Import Map.Separation Map.SeparationLogic.
From bedrock2 Require Import Syntax Semantics Markers.
From bedrock2 Require Import WeakestPrecondition WeakestPreconditionProperties.

Section Loops.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {fs : env}.
  Let call := fs.

  Lemma wp_while: forall e c t m l (post: _ -> _ -> _ -> Prop),
     (exists measure (lt:measure->measure->Prop) (inv:measure->trace->mem->locals->Prop),
      Coq.Init.Wf.well_founded lt /\
      (exists v, inv v t m l) /\
      (forall v t m l, inv v t m l ->
        exists b, dexpr m l e b /\
        (word.unsigned b <> 0%Z -> cmd call c t m l (fun t' m l =>
          exists v', inv v' t' m l /\ lt v' v)) /\
        (word.unsigned b = 0%Z -> post t m l))) ->
     cmd call (cmd.while e c) t m l post.
  Proof.
    intros. destruct H as (measure & lt & inv & Hwf & HInit & Hbody).
    destruct HInit as (v0 & HInit).
    revert t m l HInit. pattern v0. revert v0.
    eapply (well_founded_ind Hwf). intros.
    specialize Hbody with (1 := HInit). destruct Hbody as (b & Hb & Ht & Hf).
    eapply expr_sound in Hb. destruct Hb as (b' & Hb & ?). subst b'.
    destr.destr (Z.eqb (word.unsigned b) 0).
    - specialize Hf with (1 := E). eapply exec.while_false; eassumption.
    - specialize Ht with (1 := E). eapply sound_cmd in Ht.
      eapply exec.while_true; eauto.
      cbv beta. intros * (v' & HInv & HLt). eapply sound_cmd. eauto.
  Qed.

  Lemma tailrec_localsmap_1ghost
    {e c t} {m: mem} {l} {post : trace -> mem -> locals -> Prop}
    {measure: Type} {Ghost: Type}
    (P Q: measure -> Ghost -> trace -> mem -> locals -> Prop)
    (lt: measure -> measure -> Prop)
    (Hwf: well_founded lt)
    (v0: measure) (g0: Ghost)
    (Hpre: P v0 g0 t m l)
    (Hbody: forall v g t m l,
      P v g t m l ->
      exists br, expr m l e (eq br) /\
      (word.unsigned br <> 0%Z -> cmd call c t m l
        (fun t' m' l' => exists v' g',
          P v' g' t' m' l' /\
          lt v' v /\
          (forall t'' m'' l'', Q v' g' t'' m'' l'' -> Q v g t'' m'' l''))) /\
      (word.unsigned br = 0%Z -> Q v g t m l))
    (Hpost: forall t m l, Q v0 g0 t m l -> post t m l)
    : cmd call (cmd.while e c) t m l post.
  Proof.
    eapply wp_while.
    eexists measure, lt, (fun v t m l =>
      exists g, P v g t m l /\ forall t'' m'' l'', Q v g t'' m'' l'' -> Q v0 g0 t'' m'' l'').
    split; [assumption|].
    split; [solve[eauto]|].
    intros vi ti mi li (gi & HPi & HQimpl).
    specialize (Hbody vi gi ti mi li HPi).
    destruct Hbody as (br & ? & Hbody). exists br; split; [assumption|].
    destruct Hbody as (Htrue & Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [ |eapply Hpc].
      intros tj mj lj (vj& gj & HPj & Hlt & Qji); eauto 9. }
    { eauto. }
  Qed.

  Lemma tailrec_localsmap_1ghost_parameterized_finalpost
    {e c rest t} {m: mem} {l}
    {measure: Type} {Ghost: Type}
    (P Q: measure -> Ghost -> trace -> mem -> locals -> Prop)
    (lt: measure -> measure -> Prop)
    (Hwf: well_founded lt)
    (v0: measure) (g0: Ghost)
    (Hpre: P v0 g0 t m l)
    (Hbody: forall v g t m l,
      P v g t m l ->
      exists br, expr m l e (eq br) /\
      (word.unsigned br <> 0%Z -> cmd call c t m l
        (fun t' m' l' => exists v' g',
          P v' g' t' m' l' /\
          lt v' v /\
          (forall t'' m'' l'', Q v' g' t'' m'' l'' -> Q v g t'' m'' l''))) /\
      (word.unsigned br = 0%Z -> cmd call rest t m l (Q v g)))
    : cmd call (cmd.seq (cmd.while e c) rest) t m l (Q v0 g0).
  Proof.
    cbn. eapply tailrec_localsmap_1ghost with
      (Q := fun v g t m l => cmd call rest t m l (Q v g)).
    1: eassumption.
    1: exact Hpre.
    2: intros *; exact id.
    intros vi gi ti mi li HPi.
    specialize (Hbody vi gi ti mi li HPi).
    destruct Hbody as (br & ? & Hbody). exists br; split; [assumption|].
    destruct Hbody as (Htrue & Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [ |eapply Hpc].
      intros tj mj lj (vj& gj & HPj & Hlt & Qji). do 2 eexists.
      split. 1: eassumption. split. 1: assumption.
      intros.
      eapply Proper_cmd.
      2: eassumption.
      intros tk mk lk HH. eapply Qji. assumption. }
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
    {e c t l} {m : mem}
    {measure : Type} (invariant:_->_->_->_->Prop)
    {lt} (Hwf : well_founded lt) (v0 : measure)
    {post : _->_->_-> Prop}
    (Hpre : invariant v0 t m l)
    (Hbody : forall v t m l,
      invariant v t m l ->
      exists br, expr m l e (eq br) /\
         (word.unsigned br <> 0 ->
          cmd fs c t m l (fun t m l => exists v', invariant v' t m l /\ lt v' v)) /\
         (word.unsigned br = 0 -> post t m l))
    : cmd fs (cmd.while e c) t m l post.
  Proof.
    eapply wp_while.
    eexists measure, lt, invariant.
    split. 1: exact Hwf.
    split. 1: eauto.
    exact Hbody.
  Qed.

  Lemma while
    {e c t l} {m : mem}
    (variables : list String.string)
    {localstuple : tuple word (length variables)}
    {measure : Type} (invariant:_->_->_->ufunc word (length variables) Prop)
    {lt} (Hwf : well_founded lt) (v0 : measure)
    {post : _->_->_-> Prop}
    (Pl : enforce variables localstuple l)
    (Hpre : tuple.apply (invariant v0 t m) localstuple)
    (Hbody : forall v t m, tuple.foralls (fun localstuple =>
      tuple.apply (invariant v t m) localstuple ->
      let l := reconstruct variables localstuple in
      exists br, expr m l e (eq br) /\
         (word.unsigned br <> 0 ->
          cmd call c t m l (fun t m l =>
            Markers.unique (Markers.left (tuple.existss (fun localstuple =>
              enforce variables localstuple l /\
              Markers.right (Markers.unique (exists v',
                tuple.apply (invariant v' t m) localstuple /\ lt v' v))))))) /\
         (word.unsigned br = 0 -> post t m l)))
    : cmd call (cmd.while e c) t m l post.
  Proof.
    eapply (while_localsmap (fun v t m l =>
      exists localstuple, enforce variables localstuple l /\
                          tuple.apply (invariant v t m) localstuple));
      unfold Markers.split; eauto.
    intros vi ti mi li (?&X&Y).
    specialize (Hbody vi ti mi).
    eapply hlist.foralls_forall in Hbody.
    specialize (Hbody Y).
    rewrite <-(reconstruct_enforce _ _ _ X) in Hbody.
    destruct Hbody as (br & Cond & Again & Done).
    exists br. split; [exact Cond|]. split; [|exact Done].
    intro NE. specialize (Again NE).
    eapply Proper_cmd; [ |eapply Again].
    cbv [Morphisms.pointwise_relation Basics.impl Markers.right Markers.unique Markers.left] in *.
    intros t' m' l' Ex.
    eapply hlist.existss_exists in Ex. cbv beta in Ex. destruct Ex as (ls & E & v' & Inv' & LT).
    eauto.
  Qed.

  Lemma tailrec
    {e c t localsmap} {m : mem}
    (ghosttypes : polymorphic_list.list Type)
    (variables : list String.string)
    {l0 : tuple word (length variables)}
    {Pl : enforce variables l0 localsmap}
    {post : _->_->_-> Prop}
    {measure : Type} (spec:_->HList.arrows ghosttypes (_->_->ufunc word (length variables) (Prop*(_->_->ufunc word (length variables) Prop)))) lt
    (Hwf : well_founded lt)
    (v0 : measure)
    : hlist.foralls (fun (g0 : hlist ghosttypes) => forall
    (Hpre : (tuple.apply (hlist.apply (spec v0) g0 t m) l0).(1))
    (Hbody : forall v, hlist.foralls (fun g => forall t m, tuple.foralls (fun l =>
      @dlet _ (fun _ => Prop) (reconstruct variables l) (fun localsmap : locals =>
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
    eapply wp_while.
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
    { eapply Proper_cmd; [ |eapply Hpc].
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
    eapply wp_while.
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
    { eapply Proper_cmd; [ |eapply Hpc].
      intros tj mj lj (vj&dP&?&dQ); eauto 9. }
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


  Lemma atleastonce_localsmap
    {e c t} {m : mem} {l} {post : _->_->_-> Prop}
    {measure : Type} (invariant:_->_->_->_->Prop) lt
    (Hwf : well_founded lt)
    (Henter : exists br, expr m l e (eq br) /\ (word.unsigned br = 0%Z -> post t m l))
    (v0 : measure) (Hpre : invariant v0 t m l)
    (Hbody : forall v t m l, invariant v t m l ->
       cmd call c t m l (fun t m l =>
         exists br, expr m l e (eq br) /\
         (word.unsigned br <> 0 -> exists v', invariant v' t m l /\ lt v' v) /\
         (word.unsigned br =  0 -> post t m l)))
    : cmd call (cmd.while e c) t m l post.
  Proof.
    eapply wp_while.
    eexists (option measure), (with_bottom lt), (fun ov t m l =>
      exists br, expr m l e (eq br) /\
      ((word.unsigned br <> 0 -> exists v, ov = Some v /\ invariant v t m l) /\
      (word.unsigned br =  0 -> ov = None /\ post t m l))).
    split; auto using well_founded_with_bottom; []. split.
    { destruct Henter as [br [He Henter]].
      destruct (BinInt.Z.eq_dec (word.unsigned br) 0).
      { exists None, br; split; trivial.
        split; intros; try contradiction; split; eauto. }
      { exists (Some v0), br.
        split; trivial; []; split; try contradiction.
        exists v0; split; trivial. } }
    intros vi ti mi li (br&Ebr&Hcontinue&Hexit).
    eexists; split; [eassumption|]; split.
    { intros Hc; destruct (Hcontinue Hc) as (v&?&Hinv); subst.
      eapply Proper_cmd; [ |eapply Hbody; eassumption].
      intros t' m' l' (br'&Ebr'&Hinv'&Hpost').
      destruct (BinInt.Z.eq_dec (word.unsigned br') 0).
      { exists None; split; try constructor.
        exists br'; split; trivial; [].
        split; intros; try contradiction.
        split; eauto. }
      { destruct (Hinv' ltac:(trivial)) as (v'&inv'&ltv'v).
        exists (Some v'); split; trivial. (* NOTE: this [trivial] simpl-reduces [with_bottom] *)
        exists br'; split; trivial.
        split; intros; try contradiction.
        eexists; split; eauto. } }
    eapply Hexit.
  Qed.

  Lemma tailrec_earlyout_localsmap
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
        (fun t' m' l' =>
          (exists br, expr m' l' e (eq br) /\ word.unsigned br = 0 /\ Q t' m' l') \/
          exists v', let S' := spec v' t' m' l' in let '(P', Q') := S' in
          P' /\
          lt v' v /\
          forall T M L, Q' T M L -> Q T M L)) /\
      (word.unsigned br = 0%Z -> Q t m l))
    (Hpost : forall t m l, Q0 t m l -> post t m l)
    : cmd call (cmd.while e c) t m l post.
  Proof.
    eapply wp_while.
    eexists (option measure), (with_bottom lt), (fun v t m l =>
      match v with
      | None => exists br, expr m l e (eq br) /\ word.unsigned br = 0 /\ Q0 t m l
      | Some v =>
          let S := spec v t m l in let '(P, Q) := S in
          P /\ forall T M L, Q T M L -> Q0 T M L
      end).
    split; auto using well_founded_with_bottom; []; cbv [Markers.split] in *.
    split.
    { exists (Some v0); eauto. }
    intros [vi|] ti mi li inv_i; [destruct inv_i as (?&Qi)|destruct inv_i as (br&Hebr&Hbr0&HQ)].
    { destruct (Hbody _ _ _ _ ltac:(eassumption)) as (br&?&X); exists br; split; [assumption|].
      destruct X as (Htrue&Hfalse). split; intros Hbr;
        [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; eauto.
      eapply Proper_cmd; [ |eapply Hpc].
      intros tj mj lj [(br'&Hbr'&Hz&HQ)|(vj&dP&?&dQ)];
          [exists None | exists (Some vj)]; cbn [with_bottom]; eauto 9. }
    repeat esplit || eauto || intros; contradiction.
  Qed.

  Lemma tailrec_earlyout
    {e c t localsmap} {m : mem}
    (ghosttypes : polymorphic_list.list Type)
    (variables : list String.string)
    {l0 : tuple word (length variables)}
    {Pl : enforce variables l0 localsmap}
    {post : _->_->_-> Prop}
    {measure : Type} (spec:_->HList.arrows ghosttypes (_->_->ufunc word (length variables) (Prop*(_->_->ufunc word (length variables) Prop)))) lt
    (Hwf : well_founded lt)
    (v0 : measure)
    : hlist.foralls (fun (g0 : hlist ghosttypes) => forall
    (Hpre : (tuple.apply (hlist.apply (spec v0) g0 t m) l0).(1))
    (Hbody : forall v, hlist.foralls (fun g => forall t m, tuple.foralls (fun l =>
      @dlet _ (fun _ => Prop) (reconstruct variables l) (fun localsmap : locals =>
      match tuple.apply (hlist.apply (spec v) g t m) l with S_ =>
      S_.(1) ->
      Markers.unique (Markers.left (exists br, expr m localsmap e (eq br) /\ Markers.right (
      (word.unsigned br <> 0%Z -> cmd call c t m localsmap
        (fun t' m' localsmap' =>
          Markers.unique (Markers.left (hlist.existss (fun l' => enforce variables l' localsmap' /\ Markers.right (
          Markers.unique (Markers.left (exists br, expr m' localsmap' e (eq br) /\ Markers.right ( word.unsigned br = 0 /\ tuple.apply (S_.(2) t' m') l') ) ) \/
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
    eapply wp_while.
    eexists (option measure), (with_bottom lt), (fun vi ti mi localsmapi =>
      exists li, localsmapi = reconstruct variables li /\
      match vi with None => exists br, expr mi localsmapi e (eq br) /\ word.unsigned br = 0 /\ tuple.apply ((tuple.apply (hlist.apply (spec v0) g0 t m) l0).(2) ti mi) li | Some vi =>
      exists gi, match tuple.apply (hlist.apply (spec vi) gi ti mi) li with S_ =>
      S_.(1) /\ forall T M L, tuple.apply (S_.(2) T M) L ->
        tuple.apply ((tuple.apply (hlist.apply (spec v0) g0 t m) l0).(2) T M) L end end).
    cbv [Markers.unique Markers.split Markers.left Markers.right] in *.
    split; eauto using well_founded_with_bottom.
    split. { exists (Some v0), l0. split. 1: eapply reconstruct_enforce; eassumption. exists g0; split; eauto. }
    intros [vi|] ti mi lmapi.
    2: { intros (ld&Hd&br&Hbr&Hz&Hdone).
      eexists; split; eauto.
      split; intros; try contradiction.
      subst; eapply (hlist.foralls_forall (Hpost ti mi) _ Hdone). }
    intros (?&?&gi&?&Qi); subst.
    destruct (hlist.foralls_forall (hlist.foralls_forall (Hbody vi) gi ti mi) _ ltac:(eassumption)) as (br&?&X).
    exists br; split; [assumption|]. destruct X as (Htrue&Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [ |eapply Hpc].
      intros tj mj lmapj Hlj; eapply hlist.existss_exists in Hlj.
      destruct Hlj as (lj&Elj&HE); eapply reconstruct_enforce in Elj; subst lmapj.
      destruct HE as [(br'&Hevalr'&Hz'&Hdone)|HE].
      { exists None; cbn. eauto 9. }
      { eapply hlist.existss_exists in HE. destruct HE as (l&?&?&?&HR).
        pose proof fun T M => hlist.foralls_forall (HR T M); clear HR.
        eexists (Some _); eauto 9. } }
    { pose proof fun t m => hlist.foralls_forall (Hpost t m); clear Hpost; eauto. }
  Qed.


  Lemma atleastonce
    {e c t l} {m : mem}
    (variables : list String.string)
    {localstuple : tuple word (length variables)}
    {Pl : enforce variables localstuple l}
    {measure : Type} (invariant:_->_->_->ufunc word (length variables) Prop)
    lt (Hwf : well_founded lt)
    {post : _->_->_-> Prop}
    (Henter : exists br, expr m l e (eq br) /\ (word.unsigned br = 0%Z -> post t m l))
    (v0 : measure) (Hpre : tuple.apply (invariant v0 t m) localstuple)
    (Hbody : forall v t m, tuple.foralls (fun localstuple =>
      tuple.apply (invariant v t m) localstuple ->
       cmd call c t m (reconstruct variables localstuple) (fun t m l =>
         exists br, expr m l e (eq br) /\
         (word.unsigned br <> 0 -> Markers.unique (Markers.left (tuple.existss (fun localstuple => enforce variables localstuple l /\ Markers.right (Markers.unique (exists v', tuple.apply (invariant v' t m) localstuple /\ lt v' v)))))) /\
         (word.unsigned br =  0 -> post t m l))))
    : cmd call (cmd.while e c) t m l post.
  Proof.
    eapply (atleastonce_localsmap (fun v t m l => exists localstuple, Logic.and (enforce variables localstuple l) (tuple.apply (invariant v t m) localstuple))); eauto.
    intros vi ti mi li (?&X&Y).
    specialize (Hbody vi ti mi).
    eapply hlist.foralls_forall in Hbody.
    specialize (Hbody Y).
    rewrite <-(reconstruct_enforce _ _ _ X) in Hbody.
    eapply Proper_cmd; [ |eapply Hbody].
    intros t' m' l' (?&?&HH&?).
    eexists; split; eauto.
    split; intros; eauto.
    specialize (HH ltac:(eauto)).
    eapply hlist.existss_exists in HH; destruct HH as (?&?&?&?&?).
    eexists; split; eauto.
  Qed.

  Lemma while_zero_iterations {e c t l} {m : mem} {post : _->_->_-> Prop}
    (HCond: expr m l e (eq (word.of_Z 0)))
    (HPost: post t m l)
    : cmd call (cmd.while e c) t m l post.
  Proof.
    eapply (while_localsmap (fun n t' m' l' => t' = t /\ m' = m /\ l' = l) (PeanoNat.Nat.lt_wf 0) 0%nat).
    1: unfold split; auto. intros *. intros (? & ? & ?). subst.
    eexists. split. 1: exact HCond.
    rewrite Properties.word.unsigned_of_Z_0.
    split; intros; congruence.
  Qed.


  (* Bedrock-style loop rule *)
  Local Open Scope sep_scope.
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
    eapply wp_while.
    eexists measure, lt, (fun v t m l => exists R, (P v t l * R) m /\
                          forall T L, Q v T L * R ==> Q v0 T L * R0).
    split; [assumption|].
    split. { exists v0, R0. split; [assumption|]. intros. reflexivity. }
    intros vi ti mi li (Ri&?&Qi).
    destruct (Hbody _ _ _ _ _ ltac:(eassumption)) as (br&?&X); exists br; split; [assumption|].
    destruct X as (Htrue&Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [ |eapply Hpc].
      intros tj mj lj (vj&dR&dP&?&dQ).
      exists vj; split; [|assumption].
      exists (Ri * dR); split; [assumption|].
      intros. rewrite (sep_comm _ dR), <-(sep_assoc _ dR), dQ; trivial. }
    { eapply Hpost, Qi, Hpc. }
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
