Require Import Rupicola.Lib.Api.

Section Gallina.
  Definition downto'
             {state} init start count (step:state->nat->state) : state :=
    fold_left step (rev (skipn start (seq 0 count))) init.
  Definition downto
             {state} init count (step:state->nat->state) : state :=
    downto' init 0 count step.
End Gallina.


(* TODO: move *)
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

(* TODO: move *)
Ltac extract_var H name :=
  let l := match type of H with
             sep _ _ ?l => l end in
  let i := match type of H with
             context [Var name ?i] => i end in
  let R := fresh "R" in
  let H' := fresh in
  evar (R : Semantics.locals -> Prop);
  assert ((Var name i * R)%sep l) as H' by ecancel_assumption;
  subst R; clear H; rename H' into H.

(* TODO : move *)
Ltac straightline_locals :=
  match goal with
  | |- @map.get _ _ Semantics.locals _ _ = Some _ =>
    eapply Var_get; ecancel_assumption
  end.
Ltac straightline' ::=
  straightline_plus
    ltac:(first [ straightline_locals
                | straightline_map_solver ]).

Section Compile.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Local Ltac handle_downto_locals :=
    repeat match goal with
           | H : (?P ?l1 _ * ?R)%sep ?m
             |- (?P ?l2 _ * ?R)%sep ?m =>
             replace l2 with l1; [ exact H | ]
           | H : word.unsigned ?x = _
             |- context [word.sub ?x (word.of_Z _)] =>
             rewrite <-(word.of_Z_unsigned x); rewrite H
           | H : forall l i,
               map.get (_ l i) ?x = map.get l ?x |- _ =>
             rewrite H
           | |- context [S (?x - 1)] =>
             replace (S (x-1)) with x by lia
           | H : (_ * _)%sep ?l |- _ (map.put ?l ?i_var _) =>
             extract_var H i_var; eapply Var_put_replace in H;
             ecancel_assumption
           | _ => progress subst_lets_in_goal
           | _ => progress change 1%Z with (Z.of_nat 1)
           | _ => rewrite map.get_put_same by auto
           | _ => rewrite <-word.ring_morph_sub
           | _ => rewrite <-Nat2Z.inj_sub by lia
           | _ => reflexivity
           | _ => lazymatch goal with
                  | |- (_ < _)%nat => lia
                  | |- (_ <= _)%nat => lia
                  | _ => solve [eauto]
                  end
           end.

  Local Ltac use_cmd_hyp :=
    let H := lazymatch goal with
             | H: context [WeakestPrecondition.cmd _ ?impl]
               |- WeakestPrecondition.cmd _ ?impl _ _ _ _ => H end in
    eapply Proper_cmd;
    [ solve [apply Proper_call]
    | repeat intro | eapply H ].

  (* TODO: move *)
  Lemma skipn_seq_step n start len :
    skipn n (seq start len) = seq (start + n) (len - n).
  Proof.
    revert start len.
    induction n; destruct len; cbn; try reflexivity.
    { repeat (f_equal; try lia). }
    { rewrite IHn.
      repeat (f_equal; try lia). }
  Qed.

  (* TODO: move *)
  Lemma fold_left_skipn_seq {A} i count (step :A -> _) init :
    0 < i <= count ->
    step (fold_left step (rev (skipn i (seq 0 count))) init) (i-1) =
    fold_left step (rev (skipn (i-1) (seq 0 count))) init.
  Proof.
    intros. rewrite !skipn_seq_step, !Nat.add_0_l.
    replace (count - (i - 1)) with (S (count - i)) by lia.
    cbn [seq rev]. rewrite fold_left_app. cbn [fold_left].
    replace (S (i-1)) with i by lia.
    reflexivity.
  Qed.

  Lemma downto'_step {A} i count (step :A -> _) init :
    0 < i <= count ->
    step (downto' init i count step) (i-1) = downto' init (i-1) count step.
  Proof.
    cbv [downto']; apply fold_left_skipn_seq.
  Qed.

  Definition fold_left_dependent
             {A B C} (stepA : A -> C -> A) (stepB : A -> B -> C -> B)
             cs initA initB :=
    fold_left (fun ab c =>
                 (stepA (fst ab) c, stepB (fst ab) (snd ab) c))
              cs (initA, initB).
  Lemma fold_left_dependent_fst {A B C} stepA stepB :
    forall cs initA initB,
      fst (@fold_left_dependent A B C stepA stepB cs initA initB) =
      fold_left stepA cs initA.
  Proof.
    induction cs; intros; [ reflexivity | ].
    cbn [fold_left fold_left_dependent fst snd].
    erewrite <-IHcs. reflexivity.
  Qed.

  (* helper definition *)
  Definition downto'_dependent
             {A B} initA initB start count
             (stepA : A -> nat -> A) (stepB : A -> B -> nat -> B) :=
    fold_left_dependent stepA stepB
                        (rev (skipn start (seq 0 count))) initA initB.

  Lemma downto'_dependent_fst {A B} initA initB stepA stepB i count :
      fst (@downto'_dependent A B initA initB i count stepA stepB) =
      downto' initA i count stepA.
  Proof. apply fold_left_dependent_fst. Qed.

  Lemma downto'_dependent_step
        {A B} i count stepA stepB (initA : A) (initB : B) :
    0 < i <= count ->
    (fun ab c =>
       (stepA (fst ab) c, stepB (fst ab) (snd ab) c))
      (downto'_dependent initA initB i count stepA stepB) (i-1)
    = downto'_dependent initA initB (i-1) count stepA stepB.
  Proof. apply fold_left_skipn_seq. Qed.

  (* TODO: find a better phrasing than step_locals *)
  (* TODO: use separation logic for locals? *)
  Lemma compile_downto :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr Rl R R' functions T (pred: T -> _ -> Prop)
      {state} {ghost_state} (init : state) (ginit : ghost_state)
      count wcount step step_impl k k_impl i_var
      (ghost_step : state -> ghost_state -> nat -> ghost_state)
      (Invl : ghost_state -> state -> Semantics.locals -> Prop) (* locals loop invariant *)
      (Inv : ghost_state -> state -> Semantics.mem -> Prop) (* memory loop invariant *),
      (Invl ginit init * Var i_var wcount * Rl)%sep locals ->
      (Inv ginit init * R')%sep mem ->
      word.unsigned wcount = Z.of_nat count ->
      0 < count ->
      let v := downto init count step in
      (let head := v in
       (* loop iteration case *)
       forall tr l m st gst i wi,
         let gst' := ghost_step st gst i in
         wi = word.of_Z (Z.of_nat i) ->
         (Invl gst st * Var i_var wi * Rl)%sep l ->
         (Inv gst st * R')%sep m ->
         i < count ->
         find step_impl
         implementing (Inv gst' (step st i))
         and-locals-post (Invl gst' (step st i) * Var i_var wi * Rl)%sep
         with-locals l and-memory m and-trace tr and-rest R'
         and-functions functions) ->
      (*
         WeakestPrecondition.cmd
           (WeakestPrecondition.call functions)
           step_impl tr m li
           (fun tr' m' l' =>
              tr = tr'
              /\ (exists gst',
                     (Invl (step st i) gst' * Var i_var wi * Rl)%sep l'
                     /\ (Inv (step st i) gst' * R')%sep m'))) ->
       *)
      (let head := v in
       (* continuation *)
       forall tr l m gst,
         (Invl gst head * Var i_var (word.of_Z 0) * Rl)%sep l ->
         (Inv gst head * R')%sep m ->
         find k_impl
         implementing (pred (k head))
         and-locals-post locals_ok
         with-locals l and-memory m and-trace tr and-rest R
         and-functions functions) ->
      (let head := v in
       (* while (i = n; 0 < i; pass)
          { i--; step i } *)
       find (cmd.seq
               (cmd.while
                  (expr.op bopname.ltu
                           (expr.literal 0) (expr.var i_var))
                  (cmd.seq
                     (cmd.set i_var
                              (expr.op bopname.sub
                                       (expr.var i_var)
                                       (expr.literal 1)))
                     step_impl))
               k_impl)
       implementing (pred (dlet head k))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'.

    (* handle while *)
    WeakestPrecondition.unfold1_cmd_goal;
      (cbv beta match delta [WeakestPrecondition.cmd_body]).
    exists nat, lt.
    exists (fun i t m l =>
              let stgst :=
                  downto'_dependent init ginit i count
                                    step ghost_step in
              let st := fst stgst in
              let gst := snd stgst in
              (Inv gst st * R')%sep m
              /\ i <= count
              /\ tr = t
              /\ (exists wi,
                     word.unsigned wi = Z.of_nat i
                     /\ (Invl gst st * Var i_var wi * Rl)%sep l)).
    ssplit; eauto using lt_wf; [ | ].

    { cbv zeta. subst.
      cbv [downto'_dependent downto'].
      exists count; ssplit; [ | | | exists wcount];
        repeat match goal with
               | _ => rewrite skipn_all2 by (rewrite seq_length; lia)
               | _ => progress subst_lets_in_goal
               | _ => progress cbn [rev fold_left]
               | _ => solve [eauto]
               end. }

    { intros. cleanup.
      repeat straightline'.
      lazymatch goal with x := context [word.ltu] |- _ => subst x end.
      rewrite word.unsigned_ltu, word.unsigned_of_Z_0.
      match goal with
      | H1 : ?y = Z.of_nat ?x, H2 : 0 < ?x |- _ =>
        assert (0 < y)%Z by
            (rewrite H1; change 0%Z with (Z.of_nat 0);
             apply Nat2Z.inj_lt; auto)
      end.
      destruct_one_match;
        rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1;
        ssplit; try lia; [ | ].
      { repeat straightline'.
        use_cmd_hyp;
          [ | try solve [handle_downto_locals] .. ].
        cbv [postcondition_norets postcondition_for] in *;
          cleanup; subst.
        lazymatch goal with
        | H : word.unsigned ?w = Z.of_nat ?x
          |- exists i : nat, _ /\ i < ?x =>
          exists (x-1)%nat; ssplit;
            rewrite <-?downto'_dependent_step by lia; cbn [fst snd];
            lazymatch goal with
            | |- exists _, _ => exists (word.sub w (word.of_Z 1))
            | |- sep _ _ _ => ecancel_assumption
            | _ => auto; try lia; try solve [handle_downto_locals]
            end
        end; [ ].
        ssplit; handle_downto_locals; [ ].
        rewrite word.unsigned_of_Z.
        lazymatch goal with
        | H : word.unsigned ?w = Z.of_nat ?i
          |- word.wrap (Z.of_nat (?i - 1)) = Z.of_nat (?i - 1) =>
          pose proof (word.unsigned_range w);
            apply Z.mod_small; rewrite Nat2Z.inj_sub, <-H by lia
        end.
        lia. }
      { repeat straightline'.
        rewrite @downto'_dependent_fst in *.
        match goal with
        | H : (word.unsigned ?x <= 0)%Z |- _ =>
          let H' := fresh in
          assert (word.unsigned x = 0%Z) as H'
              by (pose proof word.unsigned_range x; lia)
        end.
        match goal with
        | H : context [Var _ ?x], Hx : word.unsigned ?x = 0%Z |- _ =>
          replace x with (word.of_Z 0) in H
            by (rewrite <-(word.of_Z_unsigned x); congruence)
        end.
        match goal with
        | H : context [downto'_dependent _ _ ?i] |- _ =>
          replace i with 0 in * by lia
        end.
        use_cmd_hyp; subst_lets_in_goal; eauto. } }
  Qed.

End Compile.
