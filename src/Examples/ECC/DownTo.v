Require Import Rupicola.Lib.Api.

Section Gallina.
  Definition downto
             {state} init count (step:state->nat->state) : state :=
    fold_left step (rev (seq 0 count)) init.
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
           | _ => progress subst_lets_in_goal
           | _ => progress change 1%Z with (Z.of_nat 1)
           | _ => rewrite map.get_put_same by auto
           | _ => rewrite <-word.ring_morph_sub
           | _ => rewrite <-Nat2Z.inj_sub by lia
           | _ => reflexivity
           | _ => solve [eauto]
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

  Lemma compile_downto :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R R' functions T (pred: T -> _ -> Prop)
      {state} (init : state) count wcount step step_impl k k_impl i_var
      (State : Semantics.locals -> state -> Semantics.mem -> Prop),
      (State (map.put locals i_var wcount) init * R')%sep mem ->
      word.unsigned wcount = Z.of_nat count ->
      0 < count ->
      let v := downto init count step in
      (let head := v in
       (* loop iteration case *)
       forall tr l li m st i,
         let wi := word.of_Z (Z.of_nat i) in
         let IterationResult :=
             fun st tr' m' l' =>
               (tr = tr'
                /\ map.get l' i_var = Some wi (* didn't change i *)
                /\ (State l' st * R')%sep m') in
         (State l st * R')%sep m ->
         li = map.put l i_var wi ->
         WeakestPrecondition.cmd
           (WeakestPrecondition.call functions) step_impl tr m li
           (IterationResult (step st i))) ->
      (let head := v in
       (* post-loop case *)
       forall tr l m,
         (State l head * R')%sep m ->
         find k_impl
         implementing (pred (k head))
         with-locals l and-memory m and-trace tr and-rest R
         and-functions functions) ->
      (let head := v in
       (* while (i = n; 0 < i; pass)
          { i--; step i } *)
       find (cmd.seq
               (cmd.seq
                  (cmd.set i_var (expr.literal (Z.of_nat count)))
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
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'.

    (* handle while *)
    WeakestPrecondition.unfold1_cmd_goal;
      (cbv beta match delta [WeakestPrecondition.cmd_body]).
    exists nat, lt.
    exists (fun i t m l =>
              let st :=
                  fold_left step (rev (skipn i (seq 0 count))) init in
              (State l st * R')%sep m
              /\ i <= count
              /\ tr = t
              /\ (exists wi,
                     word.unsigned wi = Z.of_nat i
                     /\ map.get l i_var = Some wi)).
    ssplit; eauto using lt_wf; [ | ].

    { cbv zeta.
      exists count; ssplit; [ | | | exists wcount];
        repeat match goal with
               | H : _ = Z.of_nat count |- _ => rewrite <-H
               | _ => rewrite map.put_put_same by auto
               | _ => rewrite map.get_put_same by auto
               | _ => rewrite word.of_Z_unsigned
               | _ => rewrite skipn_all2 by (rewrite seq_length; lia)
               | _ => progress subst_lets_in_goal
               | _ => progress cbn [rev]
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
        use_cmd_hyp; [ | solve [handle_downto_locals] .. ].
        cleanup; subst.
        lazymatch goal with
        | H : word.unsigned ?w = Z.of_nat ?x
          |- exists i : nat, _ /\ i < ?x =>
          exists (x-1)%nat; ssplit;
            lazymatch goal with
            | |- exists _, _ => exists (word.sub w (word.of_Z 1))
            | |- sep _ _ _ =>
              rewrite <-fold_left_skipn_seq by lia; assumption
            | _ => auto; try lia
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
        match goal with
        | H : context [skipn ?i] |- _ =>
          replace i with 0 in H by lia; cbn [skipn] in H
        end.
        use_cmd_hyp.
        { eauto. }
        { subst_lets_in_goal. assumption. } } }
  Qed.

End Compile.
