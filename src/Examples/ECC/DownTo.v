Require Import Rupicola.Lib.Api.

Section Gallina.
  Definition downto'
             {state} init start count (step:state->nat->state) : state :=
    fold_left step (rev (skipn start (seq 0 count))) init.
  Definition downto
             {state} init count (step:state->nat->state) : state :=
    downto' init 0 count step.
End Gallina.

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

  (* TODO: find a better phrasing than step_locals *)
  (* TODO: use separation logic for locals? *)
  Lemma compile_downto :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr R R' functions T (pred: T -> _ -> Prop)
      {state} (init : state)
      count wcount zcount step step_impl k k_impl i_var
      (step_locals : Semantics.locals -> nat -> Semantics.locals)
      (State : Semantics.locals -> state -> Semantics.mem -> Prop),
      let start_locals := map.put locals i_var wcount in
      let step_locals' :=
          fun l i =>
            step_locals (map.put l i_var (word.of_Z (Z.of_nat i))) i in
      (* step_locals doesn't change i *)
      (forall l i,
          map.get (step_locals l i) i_var = map.get l i_var) ->
      (State start_locals init * R')%sep mem ->
      word.unsigned wcount = Z.of_nat count ->
      word.unsigned wcount = zcount ->
      0 < count ->
      let v := downto init count step in
      (let head := v in
       (* loop iteration case *)
       forall tr l m st i wi,
         let li := map.put l i_var wi in
         wi = word.of_Z (Z.of_nat i) ->
         (State l st * R')%sep m ->
         l = downto' start_locals (S i) count step_locals' ->
         i < count ->
         find step_impl
         implementing (State (step_locals li i) (step st i))
         and-locals-post (eq (step_locals li i))
         with-locals li and-memory m and-trace tr and-rest R'
         and-functions functions) ->
      (let head := v in
       (* continuation *)
       forall tr l m,
         (State l head * R')%sep m ->
         l = downto start_locals count step_locals' ->
         find k_impl
         implementing (pred (k head))
         and-locals-post locals_ok
         with-locals l and-memory m and-trace tr and-rest R
         and-functions functions) ->
      (let head := v in
       (* while (i = n; 0 < i; pass)
          { i--; step i } *)
       find (cmd.seq
               (cmd.seq
                  (cmd.set i_var (expr.literal zcount))
                  (cmd.while
                     (expr.op bopname.ltu
                              (expr.literal 0) (expr.var i_var))
                     (cmd.seq
                        (cmd.set i_var
                                 (expr.op bopname.sub
                                          (expr.var i_var)
                                          (expr.literal 1)))
                        step_impl)))
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
              let st := downto' init i count step in
              (State l st * R')%sep m
              /\ i <= count
              /\ tr = t
              /\ l = downto' start_locals i count step_locals'
              /\ (exists wi,
                     word.unsigned wi = Z.of_nat i
                     /\ map.get l i_var = Some wi)).
    ssplit; eauto using lt_wf; [ | ].

    { cbv zeta. subst.
      exists count; ssplit; [ | | | | exists wcount];
        repeat match goal with
               | H : _ = Z.of_nat count |- _ => rewrite <-H
               | _ => rewrite map.put_put_same by auto
               | _ => rewrite map.get_put_same by auto
               | _ => rewrite word.of_Z_unsigned
               | _ => rewrite skipn_all2 by (rewrite seq_length; lia)
               | _ => progress subst_lets_in_goal
               | _ => progress cbn [rev fold_left]
               | _ => progress cbv [downto']
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
          [ | try solve [handle_downto_locals] .. ];
          [ | solve [handle_downto_locals] .. ];
        cbv [postcondition_norets postcondition_for] in *;
          cleanup; subst.
        lazymatch goal with
        | H : word.unsigned ?w = Z.of_nat ?x
          |- exists i : nat, _ /\ i < ?x =>
          exists (x-1)%nat; ssplit;
            rewrite <-?downto'_step by lia;
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
        match goal with
        | H : (word.unsigned ?x <= 0)%Z |- _ =>
          let H' := fresh in
          assert (word.unsigned x = 0%Z) as H'
              by (pose proof word.unsigned_range x; lia)
        end.
        use_cmd_hyp;
          subst_lets_in_goal;
          match goal with
          | H : context [downto' _ ?i] |- _ =>
            replace i with 0 in * by lia
          end; eauto. } }
  Qed.

End Compile.
