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
  Implicit Types (x : Semantics.word).

  Lemma downto'_step {A} i count (step :A -> _) init :
    0 < i <= count ->
    step (downto' init i count step) (i-1) = downto' init (i-1) count step.
  Proof.
    cbv [downto']; apply fold_left_skipn_seq.
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

  (* helper lemma for subtracting one from the loop counter -- code does it with
     words, but proofs want nat *)
  Lemma word_to_nat_sub_1 x n :
    (0 < word.unsigned x)%Z ->
    word.unsigned x = Z.of_nat n ->
    word.unsigned (word.sub x (word.of_Z 1)) = Z.of_nat (n - 1).
  Proof.
    intros. pose proof (word.unsigned_range x).
    rewrite Nat2Z.inj_sub by lia.
    rewrite word.unsigned_sub, word.unsigned_of_Z_1.
    rewrite word.wrap_small by lia.
    f_equal. congruence.
  Qed.

  (* helper lemma for continuation case *)
  Lemma word_to_nat_0 x n :
    (word.unsigned x <= 0)%Z ->
    word.unsigned x = Z.of_nat n ->
    x = word.of_Z 0.
  Proof.
    intros. pose proof (word.unsigned_range x).
    rewrite <-(word.of_Z_unsigned x).
    assert (n = 0) by lia; subst.
    change (Z.of_nat 0) with 0%Z in *.
    congruence.
  Qed.

  (* In this lemma, state refers to the accumulator type for the Gallina downto
     loop, and ghost_state is any extra information that locals/memory invariants
     need access to. *)
  (* FIXME Do we actually need ghost state? *)
  (* TODO: consider taking in range of count instead of providing word? *)
  Lemma compile_downto {tr mem locals functions} {state} (init : state) count step:
    let v := downto init count step in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl step_impl}
      wcount {ghost_state} (ginit : ghost_state)
      (ghost_step : state -> ghost_state -> nat -> ghost_state)
      (Inv : nat -> ghost_state -> state -> predicate) (* loop invariant *)
      i_var vars,

      Inv count ginit init tr mem (map.remove locals i_var) ->

      map.get locals i_var = Some wcount ->
      word.unsigned wcount = Z.of_nat count ->
      0 < count -> (* FIXME unused *)

      (let v := v in
       (* loop iteration case *)
       forall tr l m st gst i wi,
         let inv' v tr' mem' locals :=
             map.get locals i_var = Some wi /\
             Inv i (ghost_step st gst i) v tr' mem' (map.remove locals i_var) in
         let gst' := ghost_step st gst i in
         Inv (S i) gst st tr m (map.remove l i_var) ->
         word.unsigned wi = Z.of_nat i ->
         i < count ->
         <{ Trace := tr;
            Memory := m;
            Locals := map.put l i_var wi;
            Functions := functions }>
         step_impl
         <{ inv' (step st i)}>) ->
      (let v := v in
       (* continuation *)
       forall tr l m gst,
         Inv 0 gst v tr m (map.remove l i_var) ->
         map.get l i_var = Some (word.of_Z 0) ->
         <{ Trace := tr;
            Memory := m;
            Locals := l;
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
      (* while (i = n; 0 < i; pass)
          { i--; step i } *)
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.while (expr.op bopname.ltu (expr.literal 0) (expr.var i_var))
                   (cmd.seq (cmd.set i_var (expr.op bopname.sub (expr.var i_var) (expr.literal 1))) step_impl))
        k_impl
      <{ pred (nlet_eq vars v k) }>.
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
              Inv i gst st t m (map.remove l i_var)
              /\ i <= count
              /\ (exists wi,
                     word.unsigned wi = Z.of_nat i
                     /\ map.get l i_var = Some wi)).
    ssplit; eauto using lt_wf; [ | ].

    { cbv zeta. subst.
      cbv [downto'_dependent downto'].
      exists count; ssplit; [ | | exists wcount];
        repeat match goal with
               | _ => rewrite skipn_all2 by (rewrite seq_length; lia)
               | _ => progress subst_lets_in_goal
               | _ => progress cbn [rev fold_left]
               | _ => solve [eauto]
               end. }

    { intros. cleanup; subst.
      repeat straightline'.
      lazymatch goal with x := context [word.ltu] |- _ => subst x end.
      rewrite word.unsigned_ltu, word.unsigned_of_Z_0.
      match goal with
      | H1 : ?y = Z.of_nat ?x, H2 : 0 < ?x |- _ =>
        assert (0 < y)%Z by lia
      end.
      destruct_one_match;
        rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1;
        ssplit; try lia; [ | ].
      { repeat straightline'.
        subst_lets_in_goal.
        lazymatch goal with
        | Hcmd:context [ WeakestPrecondition.cmd _ ?impl ],
               Hinv : context [Inv _ (snd ?stgst) (fst ?stgst)],
                      Hi : word.unsigned ?wi = Z.of_nat ?i
          |- WeakestPrecondition.cmd
               _ ?impl ?tr ?mem
               (map.put ?locals ?i_var (word.sub ?wi (word.of_Z 1)))
               ?post =>
          specialize (Hcmd tr locals mem (fst stgst) (snd stgst)
                           (i-1) (word.sub wi (word.of_Z 1)));
            replace (S (i-1)) with i in Hcmd by lia;
            unshelve epose proof (Hcmd _ _ _); clear Hcmd
        end;
          [ eauto using word_to_nat_sub_1; lia .. | ].
        use_hyp_with_matching_cmd; [ ].
        cbv [postcondition_cmd] in *; sepsimpl; cleanup; subst.
        repeat match goal with
               | |- exists _, _ => eexists; ssplit
               | _ => erewrite <-downto'_dependent_step;
                        [ cbn [fst snd]; ecancel_assumption | ];
                        lia
               | _ => lia
               | _ => solve [eauto using word_to_nat_sub_1]
               end. }
      { repeat straightline'.
        rewrite @downto'_dependent_fst in *.
        match goal with
        | H : (word.unsigned ?x <= 0)%Z |- _ =>
          eapply word_to_nat_0 in H; [ | solve [eauto] .. ]; subst
        end.
        match goal with
          H : word.unsigned (word.of_Z 0) = Z.of_nat ?n |- _ =>
          assert (n = 0) by (rewrite word.unsigned_of_Z_0 in H; lia)
        end; subst.
        use_hyp_with_matching_cmd; subst_lets_in_goal; eauto. } }
  Qed.
End Compile.
