Require Import Rupicola.Lib.Api.

(* TODO: ideally, all compilation lemmas would now use seplogic for locals *)
Section Var.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Definition Var (name : string) (value : word)
    : Semantics.locals -> Prop :=
    eq (map.put map.empty name value).

  Lemma Var_get l name value R :
    (Var name value * R)%sep l ->
    map.get l name = Some value.
  Proof.
    destruct 1; cbv [Var] in *; cleanup.
    match goal with H : map.split _ _ _ |- _ =>
                    apply map.get_split with (k:=name) in H;
                      destruct H; cleanup
    end.
    all:subst; autorewrite with mapsimpl in *.
    all:congruence.
  Qed.

  Lemma Var_put_replace l n v v' (R : _ -> Prop) :
    (Var n v * R)%sep l ->
    (Var n v' * R)%sep (map.put l n v').
  Proof.
    destruct 1; cbv [Var] in *; cleanup.
    match goal with H : map.split _ _ _ |- _ =>
                    pose proof H;
                    apply map.get_split with (k:=n) in H;
                      destruct H; cleanup
    end;
      subst; autorewrite with mapsimpl in *; [ | congruence ].
    do 2 eexists.
    ssplit; [ | reflexivity | eassumption ].
    cbv [map.split] in *; cleanup; subst.
    ssplit; [ | eapply map.disjoint_put_l;
                eauto using map.disjoint_empty_l ].
    subst. rewrite map.putmany_comm by auto.
    rewrite map.put_putmany_commute.
    rewrite map.put_put_same.
    apply map.putmany_comm.
    eapply map.disjoint_put_r; eauto using map.disjoint_empty_r.
  Qed.

  Lemma Var_put_remove l n v (R : _ -> Prop) :
    R (map.remove l n) ->
    (Var n v * R)%sep (map.put l n v).
  Proof.
    intros.
    do 2 eexists.
    ssplit; [ | reflexivity | eassumption ].
    cbv [map.split] in *; cleanup; subst.
    ssplit; [ | eapply map.disjoint_put_l;
                eauto using map.disjoint_empty_l, map.get_remove_same ].
    rewrite map.putmany_comm
      by (apply map.disjoint_put_l;
          eauto using map.disjoint_empty_l, map.get_remove_same).
    rewrite <-map.put_putmany_commute.
    rewrite map.putmany_empty_r.
    eapply map.map_ext; intros.
    rewrite !map.get_put_dec, !map.get_remove_dec.
    destruct_one_match; congruence.
  Qed.

  Lemma Var_put_undef l n v (R : Semantics.locals -> Prop) :
    map.get l n = None ->
    R l ->
    (Var n v * R)%sep (map.put l n v).
  Proof.
    cbv [Var]; intros. do 2 eexists.
    ssplit; [ | reflexivity | eassumption ].
    eauto using map.split_undef_put.
  Qed.

  Lemma Var_exact n v :
    Lift1Prop.iff1 (Var n v) (eq (map.put map.empty n v)).
  Proof. reflexivity. Qed.

  Lemma Var_put_eq_l l n v :
    map.get l n = None ->
    Lift1Prop.iff1 (eq l * Var n v)%sep (eq (map.put l n v)).
  Proof.
    repeat intro; cbv [Var sep].
    split; intros; cleanup; subst.
    { match goal with H : map.split _ _ (map.put map.empty _ _) |- _ =>
                      apply map.split_put_r2l, map.split_empty_r in H;
                        [ | autorewrite with mapsimpl; reflexivity ]
      end.
      congruence. }
    { do 2 eexists. ssplit; [ | reflexivity .. ].
      apply map.split_put_l2r, map.split_empty_r; eauto. }
  Qed.

  Lemma Var_put_eq_r l n v :
    map.get l n = None ->
    Lift1Prop.iff1 (Var n v * eq l)%sep (eq (map.put l n v)).
  Proof.
    rewrite sep_comm. apply Var_put_eq_l.
  Qed.
End Var.

Ltac extract_Var H name :=
  let l := match type of H with
             sep _ _ ?l => l end in
  let i := match type of H with
             context [Var name ?i] => i end in
  let R := fresh "R" in
  let H' := fresh in
  evar (R : Semantics.locals -> Prop);
  assert ((Var name i * R)%sep l) as H' by ecancel_assumption;
  subst R; clear H; rename H' into H.

Ltac straightline_map_solver_locals :=
  match goal with
  | |- @map.get _ _ Semantics.locals _ _ = Some _ =>
    eapply Var_get; ecancel_assumption
  end.

Ltac straightline' ::=
  straightline_plus
    ltac:(first [ straightline_map_solver_locals
                | straightline_map_solver ]).
