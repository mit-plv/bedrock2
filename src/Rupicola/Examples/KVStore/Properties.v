Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.KVStore.KVStore.

Section properties.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {ops key value Value}
          {kvp : kv_parameters}
          {ok : @kv_parameters_ok _ BW _ mem ops key value Value kvp}.
  Existing Instances map_ok annotated_map_ok key_eq_dec.

  Lemma Map_put_iff1 :
    forall value Value pm (m : map.rep (map:=map_gen value))
           k v1 v2 R1 R2,
      (forall pv,
          Lift1Prop.iff1
            (sep (Value pv v1) R1)
            (sep (Value pv v2) R2)) ->
      Lift1Prop.iff1
        (sep (Map_gen value Value pm (map.put m k v1)) R1)
        (sep (Map_gen value Value pm (map.put m k v2)) R2).
  Proof.
    intros *.
    intro Hiff; split; intros;
      eapply Map_put_impl1; intros; eauto;
        rewrite Hiff; reflexivity.
  Qed.

  Definition annotate (m : map) : annotated_map :=
    map.fold (fun m' k v => map.put m' k (Owned, v)) map.empty m.

  Lemma annotate_get_None m k :
    map.get m k = None -> map.get (annotate m) k = None.
  Proof.
    cbv [annotate]; eapply map.fold_spec; intros;
      try eapply map.get_empty; [ ].
    rewrite map.get_put_dec.
    match goal with H : map.get (map.put _ ?k1 _) ?k2 = None |- _ =>
                    rewrite map.get_put_dec in H;
                      destruct (key_eqb k1 k2); try congruence; [ ]
    end.
    eauto.
  Qed.

  Lemma annotate_get_Some m k v :
    map.get m k = Some v ->
    map.get (annotate m) k = Some (Owned, v).
  Proof.
    cbv [annotate]; eapply map.fold_spec;
      rewrite ?map.get_empty; intros; [ congruence | ].
    rewrite map.get_put_dec.
    match goal with H : map.get (map.put _ ?k1 _) ?k2 = Some _ |- _ =>
                    rewrite map.get_put_dec in H;
                      destruct (key_eqb k1 k2); try congruence; [ ]
    end.
    eauto.
  Qed.

  Lemma annotate_get_full m k :
    map.get (annotate m) k = match map.get m k with
                             | Some v => Some (Owned, v)
                             | None => None
                             end.
  Proof.
    destruct_one_match; eauto using annotate_get_None, annotate_get_Some.
  Qed.

  Lemma annotate_iff1 pm m :
    Lift1Prop.iff1
      (Map pm m) (AnnotatedMap pm (annotate m)).
  Proof.
    apply Map_fold_iff1; intros; reflexivity.
  Qed.

  Lemma unannotate_iff1 pm m :
    Lift1Prop.iff1
      (AnnotatedMap pm (annotate m)) (Map pm m).
  Proof. symmetry; apply annotate_iff1. Qed.

  Lemma reserved_borrowed_iff1 pm m k pv v1 v2 :
    Lift1Prop.iff1
      (AnnotatedMap pm (map.put m k (Reserved pv, v1)))
      (sep (AnnotatedMap pm (map.put m k (Borrowed pv, v2)))
           (Value pv v1)).
  Proof.
    cbv [AnnotatedMap].
    rewrite <-sep_emp_True_r.
    apply Map_put_iff1. intros.
    rewrite sep_emp_True_r.
    reflexivity.
  Qed.

  Lemma reserved_owned_impl1 pm m k pv v :
    Lift1Prop.impl1
      (AnnotatedMap pm (map.put m k (Reserved pv, v)))
      (AnnotatedMap pm (map.put m k (Owned, v))).
  Proof.
    rewrite <-(sep_emp_True_r (_ (map.put _ _ (Reserved _, _)))).
    rewrite <-(sep_emp_True_r (_ (map.put _ _ (Owned, _)))).
    cbv [AnnotatedMap]. repeat intro.
    eapply Map_put_impl1; intros; [ | eassumption ].
    cbn [AnnotatedValue_gen fst snd].
    rewrite !sep_emp_True_r.
    intro; rewrite sep_emp_l; intros;
      repeat match goal with
             | H : _ /\ _ |- _ => destruct H
             end;
      subst; eauto.
  Qed.

  Lemma put_owned_annotate m k v :
    map.put (annotate m) k (Owned, v) = annotate (map.put m k v).
  Proof.
    apply map.map_ext; intros.
    repeat first [ rewrite map.get_put_dec
                 | rewrite annotate_get_full ].
    destruct_one_match; reflexivity.
  Qed.
End properties.

Section Maps.
  Context {key value} {map : map.map key value}
          {map_ok : map.ok map}
          {key_eqb}
          {key_eq_dec :
             forall x y : key, BoolSpec (x = y) (x <> y) (key_eqb x y)}.

  Lemma put_noop' k v (m m' : map):
    m = m' ->
    map.get m' k = Some v ->
    m = map.put m' k v.
  Admitted.
End Maps.

Hint Rewrite @map.get_put_diff @map.get_put_same @map.put_put_same
     @annotate_get_Some @annotate_get_None @annotate_get_full
     using (typeclasses eauto || congruence) : mapsimpl.
