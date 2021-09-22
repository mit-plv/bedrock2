Require Import Rupicola.Lib.Api.

(* TODO: ideally, all compilation lemmas would now use seplogic for locals *)
Section Var.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Definition Var (name : string) (value : word)
    : locals -> Prop :=
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
                eauto using @map.disjoint_empty_l with typeclass_instances ].
    subst. rewrite map.putmany_comm by auto.
    rewrite map.put_putmany_commute.
    rewrite map.put_put_same.
    apply map.putmany_comm.
    eapply map.disjoint_put_r; eauto using @map.disjoint_empty_r with typeclass_instances.
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
                eauto using @map.disjoint_empty_l, @map.get_remove_same with typeclass_instances].
    rewrite map.putmany_comm
      by (apply map.disjoint_put_l;
          eauto using @map.disjoint_empty_l, @map.get_remove_same with typeclass_instances).
    rewrite <-map.put_putmany_commute.
    rewrite map.putmany_empty_r.
    eapply map.map_ext; intros.
    rewrite !map.get_put_dec, !map.get_remove_dec.
    destruct_one_match; congruence.
  Qed.

  Lemma Var_put_undef l n v (R : locals -> Prop) :
    map.get l n = None ->
    R l ->
    (Var n v * R)%sep (map.put l n v).
  Proof.
    cbv [Var]; intros. do 2 eexists.
    ssplit; [ | reflexivity | eassumption ].
    eauto using @map.split_undef_put with typeclass_instances.
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

Ltac extract_Var locals H name :=
  let l := match type of H with
             sep _ _ ?l => l end in
  let i := match type of H with
             context [Var name ?i] => i end in
  let R := fresh "R" in
  let H' := fresh in
  evar (R : locals -> Prop);
  assert ((Var name i * R)%sep l) as H' by ecancel_assumption;
  subst R; clear H; rename H' into H.

Ltac straightline_map_solver_locals locals :=
  match goal with
  | |- @map.get _ _ locals _ _ = Some _ =>
    eapply Var_get; ecancel_assumption
  end.

Ltac straightline' locals ::=
  straightline_plus
    ltac:(first [ straightline_map_solver_locals locals
                | straightline_map_solver ]).

Ltac locals_sep' l seen_names :=
  match l with
  | map.put ?l ?n ?v =>
    let R := locals_sep' l (n :: seen_names) in
    (* check if n is already in the proposition due to a superceding put,
       and skip it if so *)
    lazymatch seen_names with
    | context [cons n] => constr:(R)
    | _ => constr:((Var n v * R)%sep)
    end
  | map.empty => constr:(emp True)
  end.
Ltac locals_sep l := locals_sep' l constr:(@nil string).

Ltac cancel_Var :=
  lazymatch goal with
  | |- (emp True * _)%sep ?l => eapply sep_emp_l
  | |- (Var ?n ?v * _)%sep ?l =>
    lazymatch l with
    | map.put ?m n _ =>
      match m with
      | context [map.put _ n] =>
        eapply Var_put_remove; push_map_remove
      | _ => eapply Var_put_undef;
             [ autorewrite with mapsimpl; reflexivity | ]
      end
    | context [map.put _ n v] =>
      repeat rewrite (map.put_put_diff_comm n _ v) by congruence
    | context [map.put _ n ?v'] =>
      fail "var" n "has mismatched value;" v "<>" v'
    | _ => fail "could not find var" n
    end
  | |- emp True map.empty => cbv [emp]; tauto
  end.

Ltac sep_from_literal_locals locals :=
  let R := locals_sep locals in
  assert (R locals) by (try subst locals; repeat cancel_Var).

Ltac literal_locals_from_sep locals :=
  let l := lazymatch goal with
           | H : @sep _ _ locals ?p ?q ?l |- context [?l] =>
             l end in
  match goal with
  | H : @sep _ _ locals ?p ?q ?l |- context [?l] =>
    seprewrite_in Var_exact H
  end;
  repeat
    lazymatch goal with
    | H : @sep _ _ locals ?p ?q ?l |- context [?l] =>
      first [ seprewrite_in Var_put_eq_r H
            | seprewrite_in Var_put_eq_l H];
      [ rewrite ?map.get_put_diff by congruence;
        apply map.get_empty | ]
    end;
  sepsimpl_hyps;
  lazymatch goal with
    H : _ = l |- _=>
    first [subst l | rewrite <-H ]
  end.

Ltac remove_unused_var :=
  let v :=
      (lazymatch goal with
       | |- WeakestPrecondition.cmd _ _ _ _ ?l (?pred ?v) =>
         lazymatch v with       (* FIXME should use IsRupicolaBinding *)
         | nlet _ _ => fail "compilation not complete!"
         | _ =>
           match l with
           | context [map.put _ ?n] =>
             let pred := (eval red in pred) in
             (* idtac pred; *)
             lazymatch pred with
             | context [n] => fail
             | _ => n
             end
           end
         end
       end) in
  eapply compile_unset with (var := v); [ ];
  push_map_remove.
