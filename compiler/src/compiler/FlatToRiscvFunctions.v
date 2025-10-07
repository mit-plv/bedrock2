Require Import compiler.SmallStep.
Require Import bedrock2.LeakageSemantics.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.rewr.
Require Import coqutil.Datatypes.PropSet.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.LeakageOfInstr.
Require Import riscv.Spec.Primitives.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.util.Common.
Require Import coqutil.Datatypes.ListSet.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Tactics.fwd.
Require Import compiler.SeparationLogic.
Require Export coqutil.Word.SimplWordExpr.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.DivisibleBy4.
Require Import compiler.MetricsToRiscv.
Require Import compiler.FlatImp.
Require Import compiler.RunInstruction.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvLiterals.
Require Import compiler.load_save_regs_correct.
Require Import compiler.eqexact.
Require Import compiler.RiscvWordProperties.
Require Import compiler.on_hyp_containing.
Require Import coqutil.Word.DebugWordEq.
Require Import compiler.MemoryLayout.
Require Import coqutil.Map.MapEauto.
Require Import compiler.Registers.
Require Import bedrock2.MetricCosts.

Import MetricLogging.

Local Arguments Z.mul: simpl never.
Local Arguments Z.add: simpl never.
Local Arguments Z.of_nat: simpl never.
Local Arguments Z.modulo : simpl never.
Local Arguments Z.pow: simpl never.
Local Arguments Z.sub: simpl never.

Section Proofs.
  Context {iset: Decode.InstructionSet}.
  Context {pos_map: map.map String.string Z}.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context {word_ok: word.ok word}.
  Context {locals: map.map Z word}.
  Context {mem: map.map word byte}.
  Context {env: map.map String.string (list Z * list Z * FlatImp.stmt Z)}.
  Context {M: Type -> Type}.
  Context {MM: Monads.Monad M}.
  Context {RVM: Machine.RiscvProgramWithLeakage M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {ext_spec: LeakageSemantics.ExtSpec}.
  Context {word_riscv_ok: RiscvWordProperties.word.riscv_ok word}.
  Context {locals_ok: map.ok locals}.
  Context {mem_ok: map.ok mem}.
  Context {pos_map_ok: map.ok pos_map}.
  Context {env_ok: map.ok env}.
  Context {PR: MetricPrimitives.MetricPrimitives PRParams}.
  Context {BWM: bitwidth_iset width iset}.
  Context (compile_ext_call: pos_map -> Z -> Z -> stmt Z -> list Instruction).
  Context (leak_ext_call: word -> pos_map -> Z -> Z -> stmt Z -> list word -> list LeakageEvent).

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Local Notation RiscvMachineL := MetricRiscvMachine.

  (* high stack addresses     | stackframe of main             \
                              ...                               \
    g|                        ---                                }- stuffed into R
    r|                        | stackframe of current func      /
    o|              p_sp -->  ---                              /
    w|                        |
    s|                        | currently unused stack
     |                        | (old_stackvals)
     V                        |
            p_stacklimit -->  ---

     low stack addresses *)

  Notation functions := (functions (iset := iset) compile_ext_call).
  Notation compile_function := (compile_function iset compile_ext_call).
  Notation AEP := MetricLeakageSemantics.AEP.

  Lemma functions_expose: forall (base: word) (finfo: pos_map) impls f pos impl,
      map.get finfo f = Some pos ->
      map.get impls f = Some impl ->
      iff1 (functions base finfo impls)
           (functions base finfo (map.remove impls f) *
            program iset (word.add base (word.of_Z pos)) (compile_function finfo pos impl))%sep.
  Proof.
    intros. unfold functions.
    match goal with
    | |- context[map.fold ?F] => pose proof (map.fold_remove F) as P
    end.
    simpl in P.
    specialize P with (2 := H0).
    rewrite P.
    - unfold function at 1. rewrite H. cancel.
    - intros. apply iff1ToEq. cancel.
  Qed.

  Lemma modVars_as_list_valid_FlatImp_var: forall (s: stmt Z),
      valid_FlatImp_vars s ->
      Forall valid_FlatImp_var (modVars_as_list Z.eqb s).
  Proof.
    induction s; intros; cbn -[list_union] in *; fwd; eauto 10 using @union_Forall.
  Qed.

  Set Printing Depth 100000.

  Ltac tag P ::=
    let __ := lazymatch type of P with
              | @map.rep _ _ _ -> Prop => idtac
              | _ => fail 10000 P "is not a sep clause"
              end in
    lazymatch P with
    | array (ptsto_instr _) _ _ (compile_stmt _ _ _ _ _ ?Code) => Code
    | ptsto_instr _ _ ?Instr => Instr
    | array ptsto_word _ _ ?Words => Words
    | functions _ _ ?E_Impl => E_Impl
    | _ => fail "no recognizable tag"
    end.

  Ltac addr P ::=
    let __ := lazymatch type of P with
              | @map.rep _ _ _ -> Prop => idtac
              | _ => fail 10000 P "is not a sep clause"
              end in
    lazymatch P with
    | array _ _ ?A _ => A
    | ptsto_instr _ ?A _ => A
    | ptsto_word ?A _ => A
    | _ => fail "no recognizable address"
    end.

  Ltac safe_sidecond :=
    match goal with
    (* proving these equalties with eq_refl will make other goals harder to prove,
       so we prefer to leave these open, so that they will become instantiated,
       and we can do interesting work here
    | |- ?L = _ => is_evar L; reflexivity
    | |- _ = ?R => is_evar R; reflexivity
      However, for some equalities, it's ok to prove them with eq_refl:
    *)
    | |- @eq (list Instruction) _ _ => reflexivity
    | H: fits_stack _ _ _ ?Code |- fits_stack _ _ _ ?Code => exact H
    | H: map.get ?R RegisterNames.sp = Some _ |- map.get ?R RegisterNames.sp = Some _ => exact H
    | |- ?G => assert_fails (has_evar G);
               solve [ simpl_addrs; solve_word_eq word_ok
                     | reflexivity
                     | assumption
                     | solve_divisibleBy4
                     | solve_valid_machine word_ok ]
    | |- iff1 ?x _ =>
      simpl_MetricRiscvMachine_get_set;
      (tryif is_var x then
         lazymatch goal with
         | H: iff1 x _ |- _ => etransitivity; [exact H|]
         end
       else idtac);
      subst_sep_vars;
      wwcancel
    | H: subset (footpr _) _ |- subset (footpr ?F) _ =>
      tryif is_evar F then
        eassumption
      else
        (eapply rearrange_footpr_subset; [ exact H | solve [sidecondition] ])
    | |- _ => solve [wcancel_assumption]
    | |- ?G => is_lia G; assert_fails (has_evar G);
               (* not sure why this line is needed, lia should be able to deal with (x := _) hyps,
                  maybe it changes some implicit args or universes? *)
               repeat match goal with x := _ |- _ => subst x end;
               blia
    end.

  Declare Scope word_scope.
  Notation "! n" := (word.of_Z n) (at level 0, n at level 0, format "! n") : word_scope.
  Notation "# n" := (Z.of_nat n) (at level 0, n at level 0, format "# n") : word_scope.
  Infix "+" := word.add : word_scope.
  Infix "-" := word.sub : word_scope.
  Infix "*" := word.mul : word_scope.
  Notation "- x" := (word.opp x) : word_scope.

  Delimit Scope word_scope with word.

  Open Scope word_scope.

  Lemma preserve_valid_FlatImp_var_domain_put: forall y z (l: locals),
      valid_FlatImp_var y ->
      (forall x v, map.get l x = Some v -> valid_FlatImp_var x) ->
      (forall x v, map.get (map.put l y z) x = Some v -> valid_FlatImp_var x).
  Proof.
    intros y z l V D x v G.
    rewrite map.get_put_dec in G.
    destr (y =? x).
    * subst. assumption.
    * eauto.
  Qed.

  Lemma valid_FlatImp_var_isRegZ : forall x,
      valid_FlatImp_var x -> isRegZ x = true.
  Proof.
    unfold valid_FlatImp_var, isRegZ; blia.
  Qed.
  Hint Resolve valid_FlatImp_var_isRegZ.

  Ltac run1done :=
    apply runsToDone;
    simpl_MetricRiscvMachine_get_set;
    simpl in *;
    do 6 eexists; split; [solve [eauto]|]; simpl;
    ssplit; simpl_word_exprs word_ok;
    match goal with
    | |- _ => solve_word_eq word_ok
    | |- (_ <= _)%metricsL =>
        scost_unfold;
        repeat match goal with
               | H : valid_FlatImp_var _ |- _ => apply valid_FlatImp_var_isRegZ in H; rewrite H in *
               end;
        MetricsToRiscv.solve_MetricLog
    | |- iff1 ?x ?x => reflexivity
    (* `exists stack_trash frame_trash, ...` from goodMachine *)
    | |- exists _ _, _ = _ /\ _ = _ /\ (_ * _)%sep _ =>
      eexists _, _; (split; [|split]); [..|wcancel_assumption]; blia
    | |- exists _ _, _ => do 2 eexists; split; [align_trace|]; split; [reflexivity|]; intros;
                   rewrite fix_step; simpl; simpl_rev; repeat rewrite <- app_assoc; simpl;
                   cbn [leakage_events_rel leakage_events];
                   try solve [repeat solve_word_eq word_ok || f_equal]
    | |- _ => solve [ solve_valid_machine word_ok ]
    | H:subset (footpr _) _
      |- subset (footpr _) _ => eapply rearrange_footpr_subset; [ exact H | solve [ wwcancel ] ]
    | |- _ => solve [ rewrite ?of_list_list_union in *; eauto 8 with map_hints ]
    | |- _ => idtac
  end.

  Ltac after_IH :=
    simpl_MetricRiscvMachine_get_set;
    simpl_g_get;
    rewrite ?@length_save_regs, ?@length_load_regs in *;
    simpl_word_exprs word_ok;
    repeat match goal with
           | |- _ /\ _ => split
           | |- exists _, _ => eexists
           end.

  Lemma split_from_right{A: Type}: forall (l: list A) (len: nat),
      (len <= length l)%nat ->
      exists lL lR, l = lL ++ lR /\ length lL = (length l - len)%nat /\ length lR = len.
  Proof.
    intros.
    exists (List.firstn (List.length l - len)%nat l).
    exists (List.skipn (List.length l - len)%nat l).
    ssplit.
    - eapply List.firstn_skipn_reassemble; reflexivity.
    - rewrite List.length_firstn_inbounds; blia.
    - rewrite List.length_skipn; blia.
  Qed.

  Ltac split_from_right nameOrig nameL nameR len :=
    let nL := fresh in let nR := fresh in
    destruct (split_from_right nameOrig len) as [ nL [ nR [ ? [ ? ? ] ] ] ];
    [ try blia
    | subst nameOrig;
      rename nL into nameL, nR into nameR ].

  Lemma pigeonhole{A: Type}{aeqb: A -> A -> bool}{aeqb_sepc: EqDecider aeqb}: forall (l s: list A),
      (* no pigeonhole contains more than one pigeon: *)
      NoDup l ->
      (* all elements in l are of "type" s (which is bounded by its finite length) *)
      (forall a, In a l -> In a s) ->
      (* "type" s is a set (to make induction simpler) *)
      NoDup s ->
      (* the number of pigeons is bounded: *)
      (List.length l <= List.length s)%nat.
  Proof.
    induction l; intros.
    - simpl. blia.
    - simpl. fwd.
      specialize (IHl (removeb aeqb a s)).
      specialize_hyp IHl.
      + assumption.
      + intros.
        destr (aeqb a a0).
        * subst. contradiction.
        * apply In_removeb_diff; try congruence.
          eapply H0. simpl. auto.
      + apply NoDup_removeb. assumption.
      + specialize (H0 a (or_introl eq_refl)).
        rewrite length_NoDup_removeb in IHl by assumption.
        destruct s; [simpl in *; contradiction|].
        simpl in *. blia.
  Qed.

  Lemma NoDup_valid_FlatImp_vars_bound_length: forall xs,
      NoDup xs ->
      Forall valid_FlatImp_var xs ->
      (Datatypes.length xs <= 29)%nat.
  Proof.
    intros.
    apply (pigeonhole xs (List.unfoldn Z.succ 29 3) H).
    - intros.
      eapply (proj1 (Forall_forall valid_FlatImp_var xs)) in H0.
      2: eassumption.
      unfold valid_FlatImp_var in *.
      cbv. blia.
    - cbv. repeat apply NoDup_cons; cbv; try blia.
      apply NoDup_nil.
  Qed.

  Lemma NoDup_modVars_as_list: forall s,
      NoDup (modVars_as_list Z.eqb s).
  Proof.
    induction s; cbn -[list_union];
      repeat constructor; try (intro C; exact C);
        try (eapply list_union_preserves_NoDup; eassumption || constructor).
  Qed.

  Ltac clear_old_sep_hyps :=
    repeat match goal with
           | H1: (_ * _)%sep ?m1, H2: (_ * _)%sep ?m2 |- _ => clear H1
           end.

  Ltac getEq_length_load_save_regs t :=
    match t with
    | context [ Datatypes.length (save_regs ?iset ?vars ?offset) ] =>
      constr:(length_save_regs vars offset)
    | context [ Datatypes.length (load_regs ?iset ?vars ?offset) ] =>
      constr:(length_load_regs vars offset)
    end.

  Ltac wseplog_pre ::=
    repeat (autounfold with unf_to_array);
    repeat ( rewr getEq_length_load_save_regs in |-* || rewr get_array_rewr_eq in |-* ).

  Ltac inline_iff1 :=
    match goal with
    | H: iff1 ?x _ |- _ => is_var x; apply iff1ToEq in H; subst x
    end.

  Hint Resolve
       get_putmany_none
       Decidable.Z.eqb_spec
       coqutil.Decidable.String.eqb_spec
       get_None_in_forall_keys
       sp_not_valid_FlatImp_var
       ra_not_valid_FlatImp_var
       map.not_in_of_list_zip_to_get_None
       sp_not_in_arg_regs
       ra_not_in_arg_regs
       regs_initialized_put
       map.forall_keys_put
       only_differ_put
       in_union_l
       in_union_l
       in_of_list
       in_eq
       map.put_extends
       get_put_diff_eq_l
       only_differ_refl
       only_differ_subset
       subset_union_l
       subset_union_rl
       subset_union_rr
       subset_refl
       in_singleton_set
       only_differ_put_r
       put_extends_l
       get_None_in_forall_keys
       ra_not_valid_FlatImp_var
       extends_remove
       map.get_put_same
    : map_hints.

  Hint Extern 3 (not (@eq Z _ _)) => (discriminate 1) : map_hints.

  Hint Extern 3 (map.only_differ _ _ _)
  => eapply only_differ_trans_r; [eassumption|eauto with map_hints ..]
  : map_hints.

  (* Note: adding both only_differ_trans_l and only_differ_trans_r can lead to loops
  Hint Extern 3 (map.only_differ _ _ _)
  => eapply only_differ_trans_l; [eassumption|eauto with map_hints ..]
  : map_hints. *)
  
  Lemma leakage_events_app a i1 i2 l1 l2 :
    length i1 = length l1 ->
    leakage_events a (i1 ++ i2) (l1 ++ l2) =
      leakage_events a i1 l1 ++ leakage_events (word.add a (word.of_Z (4 * Z.of_nat (length i1)))) i2 l2.
  Proof.
    intros. revert a l1 H. induction i1; intros ad l1 H.
    - simpl. destruct l1; [|simpl in H; congruence].
      f_equal. solve_word_eq word_ok.
    - simpl. destruct l1; [simpl in H; congruence|]. simpl. f_equal.
      f_equal. simpl in H. injection H as H. rewrite IHi1 by assumption. f_equal.
      f_equal. solve_word_eq word_ok.
  Qed.

  Lemma length_load_regs i l x :
    length (load_regs i l x) = length l.
  Proof.
    revert x. induction l. 1: reflexivity.
    intros. simpl. rewrite IHl. reflexivity.
  Qed.

  Lemma length_leak_load_regs i x l :
    length (leak_load_regs i x l) = length l.
  Proof.
    revert x. induction l. 1: reflexivity.
    intros. simpl. rewrite IHl. reflexivity.
  Qed.
    
  Lemma compile_bcond_by_inverting_correct: forall cond (amt: Z) (initialL: RiscvMachineL) l b
                                                   (Exec R Rexec: mem -> Prop),
      subset (footpr Exec) (of_list (initialL.(getXAddrs))) ->
      iff1 Exec (ptsto_instr iset initialL.(getPc) (compile_bcond_by_inverting cond amt) *
                 Rexec)%sep ->
      (Exec * R)%sep initialL.(getMem) ->
      valid_machine initialL ->
      eval_bcond l cond = Some b ->
      ForallVars_bcond valid_FlatImp_var cond ->
      map.extends initialL.(getRegs) l ->
      (* [verify] (and decode-encode-id) only enforces divisibility by 2 because there could be
         compressed instructions, but we don't support them so we require divisibility by 4: *)
      amt mod 4 = 0 ->
      word.unsigned initialL.(getPc) mod 4 = 0 ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      mcomp_sat (Run.run1 iset) initialL (fun (finalL: RiscvMachineL) =>
        finalL.(getRegs) = initialL.(getRegs) /\
        finalL.(getLog) = initialL.(getLog) /\
        finalL.(getMem) = initialL.(getMem) /\
        finalL.(getXAddrs) = initialL.(getXAddrs) /\
        finalL.(getPc) = word.add initialL.(getPc)
                                  (word.of_Z (if b then 4 else amt)) /\
        finalL.(getNextPc) = word.add finalL.(getPc) (word.of_Z 4) /\
        finalL.(getMetrics) =
          (if b then
             (Platform.MetricLogging.addMetricLoads 1 (Platform.MetricLogging.addMetricInstructions 1 initialL.(getMetrics)))
           else
             (Platform.MetricLogging.addMetricJumps 1 (Platform.MetricLogging.addMetricLoads 1 (Platform.MetricLogging.addMetricInstructions 1 initialL.(getMetrics))))) /\
        finalL.(getTrace) = option_map (List.app (rev (leakage_events initialL.(getPc) [compile_bcond_by_inverting cond amt] [leak_bcond_by_inverting cond (negb b)]))) initialL.(getTrace) /\
        valid_machine finalL).
  Proof.
    intros. get_run1_valid_for_free.
    inline_iff1.
    destruct_RiscvMachine initialL.
    simulate'. simpl.
    destruct b.
    - (* don't branch *)
      destruct cond; [destruct op | ]; destruct getTrace;
        simpl in *; Simp.simp; repeat (simulate'; simpl_bools; simpl); intuition.
    - (* branch *)
      destruct cond; [destruct op | ]; destruct getTrace;
        simpl in *; Simp.simp; repeat (simulate'; simpl_bools; simpl); intuition.
  Qed.
  
  Local Notation exec e pick_sp := (@exec _ _ _ _ _ _ _ _ PostSpill isRegZ pick_sp e).

  Definition cost_compile_spec mc :=
    Platform.MetricLogging.addMetricInstructions 95
    (Platform.MetricLogging.addMetricJumps 95
    (Platform.MetricLogging.addMetricLoads 95
       (Platform.MetricLogging.addMetricStores 95 mc))).

  Ltac rewr_picksp := match goal with | H: forall (k : list leakage_event), _ (k ++ _) = _ |- _ => rewrite H end.
  Ltac rewr_leakage := match goal with | H : forall _ _, stmt_leakage _ _ _ _ _ _ _ = _ |- _ => rewrite H end.
  Notation MetricLog := bedrock2.MetricLogging.MetricLog.

  Lemma compile_function_body_correct: forall (e_impl_full : env) m l (mc : MetricLog) (argvs : list word)
    (st0 : locals) (post outcome : bool -> AEP -> leakage -> Semantics.trace -> mem -> locals -> MetricLog -> Prop)
    (argnames retnames : list Z) (body : stmt Z) (program_base : word)
    (pos : Z) initialKL (ret_addr : word) (mach : RiscvMachineL) (e_impl : env)
    (e_pos : pos_map) (binds_count : nat) (insts : list Instruction)
    (xframe : mem -> Prop) pick_sp1 q aep kH (t : list LogItem) (g : GhostConsts) cont
    (IH: forall (g0 : GhostConsts) (insts0 : list Instruction) (xframe0 : mem -> Prop)
                (initialL : RiscvMachineL) (pos0 : Z) initialKL0 cont0,
        fits_stack (rem_framewords g0) (rem_stackwords g0) e_impl body ->
        compile_stmt iset compile_ext_call e_pos pos0 (bytes_per_word * rem_framewords g0) body =
        insts0 ->
        pos0 mod 4 = 0 ->
        getPc initialL = program_base + !pos0 ->
        initialL.(getTrace) = Some initialKL0 ->
        iff1 (allx g0)
             ((xframe0 * program iset (program_base + !pos0) insts0)%sep *
              FlatToRiscvCommon.functions compile_ext_call program_base e_pos e_impl) ->
        goodMachine t m st0 g0 initialL ->
        (forall k, pick_sp1 (k ++ kH) = snd (stmt_leakage iset compile_ext_call leak_ext_call e_pos e_impl_full program_base
                                                         (body, rev k, rev initialKL0, pos0, g0.(p_sp), (bytes_per_word * rem_framewords g0)%Z, cont0 k))) ->
        runsTo' (initialL, aep) (fun '(finalL, finalAEP) =>
          exists finalQ finalK finalTrace finalMH finalRegsH finalMetricsH,
            outcome finalQ finalAEP finalK finalTrace finalMH finalRegsH finalMetricsH /\
            (if finalQ then getPc finalL = getPc initialL + !(4 * #(Datatypes.length insts0)) /\
            map.only_differ (getRegs initialL)
                   (union (of_list (modVars_as_list Z.eqb body)) (singleton_set RegisterNames.ra))
                   (getRegs finalL) else True) /\
            (getMetrics finalL - getMetrics initialL <= lowerMetrics (finalMetricsH - mc))%metricsL /\
              (exists kH'' finalKL,
                  finalK = kH'' ++ kH /\
                    finalL.(getTrace) = Some finalKL /\
                    if finalQ then
                      forall k cont,
                      stmt_leakage iset compile_ext_call leak_ext_call e_pos e_impl_full program_base
                        (body, rev kH'' ++ k, rev initialKL0, pos0, g0.(p_sp), (bytes_per_word * rem_framewords g0)%Z, cont) = cont (rev kH'') (rev finalKL) else True) /\
              (if finalQ then goodMachine finalTrace finalMH finalRegsH g0 finalL else finalL.(getLog) = finalTrace)))
    (HOutcome: forall q' aep' kH' t' m' (st1 : locals) mc',
        outcome q' aep' kH' t' m' st1 mc' ->
        if q' then
          exists (retvs : list word) (l' : locals),
            map.getmany_of_list st1 retnames = Some retvs /\
              map.putmany_of_list_zip (List.firstn binds_count (reg_class.all reg_class.arg)) retvs l =
                Some l' /\
              post q' aep' kH' t' m' l' mc'
        else post q' aep' kH' t' m' st1 mc'),
      (binds_count <= 8)%nat ->
      map.of_list_zip argnames argvs = Some st0 ->
      exec pick_sp1 e_impl_full body q aep kH t m st0 mc outcome ->
      map.getmany_of_list l (List.firstn (List.length argnames) (reg_class.all reg_class.arg)) =
      Some argvs ->
      map.extends e_impl_full e_impl ->
      good_e_impl e_impl e_pos ->
      fits_stack (stackalloc_words iset body)
                 (rem_stackwords g - framelength (argnames, retnames, body)) e_impl body ->
      FlatToRiscvDef.compile_function iset compile_ext_call e_pos pos (argnames, retnames, body) =
      insts ->
      valid_FlatImp_fun (argnames, retnames, body) ->
      pos mod 4 = 0 ->
      word.unsigned program_base mod 4 = 0 ->
      map.get (getRegs mach) RegisterNames.ra = Some ret_addr ->
      word.unsigned ret_addr mod 4 = 0 ->
      getPc mach = program_base + !pos ->
      mach.(getTrace) = Some initialKL ->
      iff1 (allx g)
           ((xframe * program iset (program_base + !pos) insts)%sep *
            FlatToRiscvCommon.functions compile_ext_call program_base e_pos e_impl) ->
      goodMachine t m l g mach ->
      (forall k, pick_sp1 (k ++ kH) = snd (fun_leakage iset compile_ext_call leak_ext_call e_pos e_impl_full program_base
                                        (rev k) (rev initialKL) pos g.(p_sp) ret_addr retnames body (cont k))) -> 
      runsTo' (mach, aep) (fun '(finalL, finalAEP) =>
        exists finalQ finalK finalTrace finalMH finalRegsH finalMetricsH,
          post finalQ finalAEP finalK finalTrace finalMH finalRegsH finalMetricsH /\
          (if finalQ then getPc finalL = ret_addr /\
          map.only_differ (getRegs mach)
           (union
              (of_list
                 (list_union Z.eqb (List.firstn binds_count (reg_class.all reg_class.arg)) []))
              (singleton_set RegisterNames.ra)) (getRegs finalL) else True) /\
          (getMetrics finalL - cost_compile_spec (getMetrics mach) <=
             lowerMetrics (finalMetricsH - mc))%metricsL /\
          (exists kH'' finalKL,
            finalK = kH'' ++ kH /\
              finalL.(getTrace) = Some finalKL /\
              (if finalQ then
                 forall k cont,
                   fun_leakage iset compile_ext_call leak_ext_call e_pos e_impl_full  program_base
                     (rev kH'' ++ k) (rev initialKL) pos g.(p_sp) ret_addr retnames body cont =
                     cont (rev kH'') (rev finalKL)
          else True)) /\
            (if finalQ then goodMachine finalTrace finalMH finalRegsH g finalL else finalL.(getLog) = finalTrace)).
  Proof.
    intros * IHexec OC BC OL Exb GetMany Ext GE FS C V Mo Mo' Gra RaM GPC GT A GM PSP.

    assert (valid_register RegisterNames.ra) by (cbv; auto).
    assert (valid_register RegisterNames.sp) by (cbv; auto).

    unfold goodMachine in GM. unfold valid_FlatImp_fun in V. subst insts. fwd.
    destruct g. simpl_g_get.

    set (FL := framelength (argnames, retnames, body)) in *.
    (* We have enough stack space for this call: *)
    assert (FL <= Z.of_nat (List.length stack_trash)) as enough_stack_space. {
      repeat match goal with
      | H: fits_stack _ _ _ _ |- _ => apply fits_stack_nonneg in H
      end.
      subst FL. simpl in *.
      blia.
    }

    (* note: left-to-right rewriting with all [length _ = length _] equations has to
       be terminating *)
    match goal with
    | H: _ |- _ => let N := fresh in pose proof H as N;
                                       apply map.putmany_of_list_zip_sameLength in N;
                                       symmetry in N
    end.
    assert (Memory.bytes_per_word (bitwidth iset) = bytes_per_word) as BPW. {
      rewrite bitwidth_matches. reflexivity.
    }

    assert (exists arg_count, (arg_count <= 8)%nat /\
               argnames = List.firstn arg_count (reg_class.all reg_class.arg)) as AC. {
      exists (List.length argnames). ssplit. 2: congruence.
      replace argnames with
          (List.firstn (Datatypes.length argnames) (reg_class.all reg_class.arg)) by (symmetry;assumption).
      rewrite List.firstn_length.
      change (Datatypes.length (reg_class.all reg_class.arg)) with 8%nat.
      clear. blia.
    }
    destruct AC as (arg_count & AC & ?). subst argnames.

    assert (bytes_per_word = 4 \/ bytes_per_word = 8) as B48. {
      unfold bytes_per_word. destruct width_cases as [E | E]; rewrite E; cbv; auto.
    }
    pose proof (stackalloc_words_nonneg body) as ScratchNonneg.
    assert (exists remaining_stack old_scratch old_modvarvals old_ra,
        stack_trash = remaining_stack ++ old_scratch ++ old_modvarvals ++ [old_ra] /\
        List.length old_scratch = Z.to_nat (stackalloc_words iset body) /\
        List.length old_modvarvals = List.length
                                       (list_diff Z.eqb (modVars_as_list Z.eqb body) retnames))
      as TheSplit. {
      clear IHexec.
      subst FL. unfold framelength in *.
      rename stack_trash into ToSplit.
      split_from_right ToSplit ToSplit old_ras 1%nat.
      split_from_right ToSplit ToSplit old_modvarvals
                (Datatypes.length (list_diff Z.eqb (modVars_as_list Z.eqb body) retnames)).
      split_from_right ToSplit ToSplit old_scratch (Z.to_nat (stackalloc_words iset body)).
      destruct old_ras as [|old_ra rest]; try discriminate.
      destruct rest; try discriminate.
      repeat match goal with
             | |- exists _, _ => eexists
             end.
      split.
      - do 2 rewrite <- List.app_assoc; reflexivity.
      - blia.
    }
    repeat match type of TheSplit with
           | exists x, _ => destruct TheSplit as [x TheSplit]
           | _ /\ _ => destruct TheSplit as [? TheSplit]
           end.
    subst stack_trash.

    (* decrease sp *)
    eapply runsToStep'_of_step. {
      eapply run_Addi with (rd := RegisterNames.sp) (rs := RegisterNames.sp);
        simpl in *;
        try solve [safe_sidecond | simpl; solve_divisibleBy4 ].
    }

    simpl_MetricRiscvMachine_get_set.
    clear_old_sep_hyps.
    intros. fwd.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    (* save ra on stack *)
    eapply runsToStep'_of_step. {
      eapply run_store_word with (rs1 := RegisterNames.sp) (rs2 := RegisterNames.ra)
                                 (addr := p_sp - !bytes_per_word);
        try solve [sidecondition | simpl; solve_divisibleBy4]; try solve_word_eq word_ok.
        simpl.
        rewrite map.get_put_diff by (clear; cbv; congruence).
        eassumption.
    }

    simpl_MetricRiscvMachine_get_set.
    clear_old_sep_hyps.
    intros. fwd.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    (* save vars modified by callee onto stack *)
    match goal with
    | |- context [ {| getRegs := ?l |} ] =>
      pose proof (@map.getmany_of_list_exists _ _ _ l valid_register
                      (list_diff Z.eqb (modVars_as_list Z.eqb body) retnames)) as P
    end.
    edestruct P as [newvalues P2]; clear P.
    { eapply Forall_impl; cycle 1.
      - eapply list_diff_Forall_weaken.
        eapply modVars_as_list_valid_FlatImp_var. assumption.
      - apply valid_FlatImp_var_implies_valid_register. }
    {
      intros.
      rewrite !map.get_put_dec.
      destruct_one_match; [eexists; reflexivity|].
      eauto.
    }
    eapply runsTo_trans'_of_step. {
      eapply save_regs_correct with (addr :=
        (p_sp - (!bytes_per_word * !#(List.length
                   (list_diff Z.eqb (modVars_as_list Z.eqb body) retnames))) - !bytes_per_word));
        simpl; cycle 1.
      2: rewrite map.get_put_same; reflexivity.
      1: exact P2.
      2: { eassumption. }
      2: { safe_sidecond. }
      2: { safe_sidecond. }
      4: assumption.
      4: {
        eapply Forall_impl; cycle 1.
        - eapply list_diff_Forall_weaken.
          eapply modVars_as_list_valid_FlatImp_var. assumption.
        - apply valid_FlatImp_var_implies_valid_register. }
      1: eassumption.
      2: reflexivity.
      1: solve_word_eq word_ok.
    }

    simpl.
    simpl_MetricRiscvMachine_get_set.
    clear_old_sep_hyps.
    intros. fwd.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    match goal with
    | H: fits_stack _ ?x _ _ |- _ => revert H; simpl_addrs; intro FS
    end.
    match type of FS with
    | _ _ ?x _ _ => ring_simplify x in FS
    end.

    (* execute function body *)
    eapply runsTo_trans. {
      unfold good_e_impl, valid_FlatImp_fun in *. fwd.
      set (argnames := List.firstn arg_count (reg_class.all reg_class.arg)).
      let p := match type of A with
               | context[compile_stmt _ _ _ ?p _ body] => p
               end in
      eapply IHexec with
           (pos0 := p)
           (g0 := {| p_sp := p_sp - !(bytes_per_word * framelength (argnames, retnames, body));
                     rem_stackwords := #(List.length remaining_stack);
                     rem_framewords := stackalloc_words iset body;
                     dframe := _;
                     allx := allx |});
      unfold goodMachine;
      simpl_MetricRiscvMachine_get_set;
      simpl_g_get;
      rewrite ?@length_save_regs, ?@length_load_regs in *;
      ssplit;
      subst FL.
      all: try safe_sidecond.
      { lazymatch goal with
        | H: fits_stack ?x ?y e_impl body |- fits_stack ?x' ?y' e_impl body =>
          replace y' with y; [exact H|]
        end.
        ring_simplify. reflexivity. }
      { reflexivity. }
      { move OL at bottom.
        unfold map.extends. intros *. intro G. rewrite !map.get_put_dec.
        destruct_one_match. {
          exfalso.
          eapply map.putmany_of_list_zip_find_index in G. 2: eassumption.
          rewrite map.get_empty in G.
          destruct G as [G | G]. 2: discriminate G.
          destruct G as (n & Gk & Gv).
          eapply List.nth_error_firstn_weaken in Gk.
          unfold reg_class.all in Gk.
          eapply nth_error_In in Gk.
          eapply filter_In in Gk.
          apply proj2 in Gk. discriminate Gk.
        }
        eapply map.putmany_of_list_zip_find_index in G. 2: eassumption.
        rewrite map.get_empty in G.
        destruct G as [G | G]. 2: discriminate G.
        destruct G as (n & Gk & Gv).
        unfold map.extends in GMp0. eapply GMp0.
        eapply map.getmany_of_list_get. 3: exact Gv. 2: exact Gk.
        rewrite <- GetMany.
        f_equal. congruence.
      }
      { unfold map.forall_keys in *.
        lazymatch goal with
        | H: map.of_list_zip _ _ = Some st0 |- _ =>
          rename H into P; clear -P locals_ok
        end.
        intros.
        pose proof (map.putmany_of_list_zip_find_index _ _ _ _ _ _ P H) as Q.
        destruct Q as [ [ n [A B] ] | C ].
        - eapply Forall_forall.
          2: eapply nth_error_In. 2: eassumption.
          unfold reg_class.all.
          eapply List.Forall_firstn.
          eapply List.Forall_filter.
          intros *. intro E. destr (reg_class.get a); try discriminate E.
          unfold reg_class.get in E0. fwd.
          unfold FlatToRiscvDef.valid_FlatImp_var.
          destruct_one_match_hyp.
          + fwd. blia.
          + destruct_one_match_hyp. 1: discriminate.
            destruct_one_match_hyp; discriminate.
        - rewrite map.get_empty in C. discriminate.
      }
      { rewrite map.get_put_same. f_equal. unfold framelength. solve_word_eq word_ok. }
      {
        eapply preserve_regs_initialized_after_put.
        assumption.
      }
      { exists remaining_stack, old_scratch. ssplit.
        - simpl_addrs. blia.
        - blia.
        - wcancel_assumption.
      }
      { simpl. intros. rewrite PSP.
        cbv [fun_leakage fun_leakage_helper].
        simpl_rev.
        rewrite BPW in *. repeat rewrite <- app_assoc. cbn [List.app].
        simpl.
        f_equal. f_equal. f_equal. 2: reflexivity. f_equal.
        remember (p_sp + _) as new_sp. eassert (Esp: new_sp = _).
        2: { rewrite Esp. reflexivity. } 
        subst. solve_word_eq word_ok. }
    }

    unfold goodMachine.
    simpl.
    simpl_MetricRiscvMachine_get_set.
    clear_old_sep_hyps.
    intros [middle middleAEP]. intros. fwd.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.
    match goal with
    | H: outcome _ _ _ _ _ _ _ |- _ => rename H into HO
    end.
    specialize OC with (1 := HO).
    move OC at bottom.
    
    destruct finalQ.
    2: { fwd. apply runsToDone. simpl_MetricRiscvMachine_get_set. do 6 eexists.
         split; [eassumption|]. simpl. split; [reflexivity|]. ssplit.
         - move H2p5 at bottom. cbv [cost_compile_spec].
           assert ((Datatypes.length (modVars_as_list Z.eqb body)) <= 29)%nat by
        auto using NoDup_valid_FlatImp_vars_bound_length, NoDup_modVars_as_list, modVars_as_list_valid_FlatImp_var.
      assert ((Datatypes.length
                 (list_diff Z.eqb (modVars_as_list Z.eqb body)
                            retnames))
              <= (Datatypes.length (modVars_as_list Z.eqb body)))%nat by
        apply list_diff_length.
      assert (#(Datatypes.length
                  (list_diff Z.eqb (modVars_as_list Z.eqb body)
                             retnames)) <= 29) by
        blia.
           cbv[lowerMetrics] in *.
           unfold withInstructions, withLoads, withStores, withJumps,
             addMetricInstructions, addMetricLoads, addMetricStores, addMetricJumps,
             subMetricInstructions, subMetricLoads, subMetricStores, subMetricJumps,
             metricsOp, metricSub, metricsSub, metricLeq, metricsLeq
             in *.
      destruct mach_metrics.
      destruct middle_metrics.
      unfold Platform.MetricLogging.metricsLeq, Platform.MetricLogging.metricLeq,
        Platform.MetricLogging.metricsSub, Platform.MetricLogging.metricSub
        in *.
      repeat
        match goal with
        | |- context[?f ?n (Platform.MetricLogging.mkMetricLog ?i ?s ?l ?j)] =>
            match type of (f n (Platform.MetricLogging.mkMetricLog i s l j)) with
            | Platform.MetricLogging.MetricLog =>
                progress let t := eval hnf in (f n (Platform.MetricLogging.mkMetricLog i s l j)) in
                           let t' := eval cbn -[BinInt.Z.add BinInt.Z.sub BinInt.Z.mul Z.of_nat Init.Nat.add] in t in
                             change (f n (Platform.MetricLogging.mkMetricLog i s l j)) with t'
            end
        end.
      cbn.
      repeat match goal with
             | |- context[?f ?n (Platform.MetricLogging.mkMetricLog ?i ?s ?l ?j)] =>
                 match type of (f n (Platform.MetricLogging.mkMetricLog i s l j)) with
              | Platform.MetricLogging.MetricLog =>
                  let t := eval hnf in (f n (Platform.MetricLogging.mkMetricLog i s l j)) in
                    let t' := eval cbn in t in
                      change (f n (Platform.MetricLogging.mkMetricLog i s l j)) with t' in H
                 end
             end.
      cbn in H2p5. Search list_diff.
      (* cost_compile_spec constraint: cost_compile_spec >= (...93...) i think? *)
      blia.
         - eauto.
         - assumption. }
    destruct OC as (retvs & finalRegsH' & ? & ? & ?). fwd.

    (* load back the modified vars *)
    eapply runsTo_trans'_of_step. {
      eapply load_regs_correct with (values := newvalues);
        simpl; cycle 1.
      - eapply only_differ_get_unchanged. 2: eassumption.
        + eapply map.get_put_same.
        + intro C. unfold union, elem_of, of_list, singleton_set in C.
          destruct C as [C|C]. 2: discriminate C.
          enough (valid_FlatImp_var RegisterNames.sp) as En. 1: apply En; reflexivity.
          eapply Forall_forall. 2: exact C.
          eapply modVars_as_list_valid_FlatImp_var. assumption.
      - repeat match goal with
               | H: map.getmany_of_list _ _ = Some _ |- _ =>
                 unique eapply @map.getmany_of_list_length in copy of H
               end.
        symmetry.
        eassumption.
      - eassumption.
      - etransitivity. 1: eassumption. wwcancel.
      - subst FL. wcancel_assumption.
      - reflexivity.
      - assumption.
      - eapply list_diff_Forall_weaken. apply modVars_as_list_valid_FlatImp_var. assumption.
    }

    simpl.
    simpl_MetricRiscvMachine_get_set.
    clear_old_sep_hyps.
    intros. fwd.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    (* load back the return address *)
    eapply runsToStep'_of_step. {
      eapply run_load_word; cycle 2; simpl_MetricRiscvMachine_get_set.
      - simpl. solve [sidecondition].
      - simpl.
        assert (forall x, In x (modVars_as_list Z.eqb body) -> valid_FlatImp_var x) as F. {
          eapply Forall_forall.
          apply modVars_as_list_valid_FlatImp_var. assumption.
        }
        revert F.
        subst FL.
        repeat match goal with
               | H: ?T |- _ => lazymatch T with
                               | map.putmany_of_list_zip _ _ _ = Some _ => revert H
                               | map.get _ RegisterNames.sp = Some _ => revert H
                               | map.ok _ => revert H
                               | _ => clear H
                               end
               end.
        repeat match goal with
               | |- forall (_: map.ok _), _ => intro
               end.
        intros G G' PM PM' F.
        eapply map.putmany_of_list_zip_get_oldval. 3: exact G'. 1: eassumption.
        intro C.
        eapply In_list_diff_weaken in C.
        specialize (F _ C).
        unfold valid_FlatImp_var, RegisterNames.sp in F. blia.
      - reflexivity.
      - eassumption.
      - etransitivity. 1: eassumption. wwcancel.
      - wcancel_assumption.
      - assumption.
      - eassumption.
      - assumption.
    }

    simpl.
    simpl_MetricRiscvMachine_get_set.
    clear_old_sep_hyps.
    intros. fwd.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m; idtac m
           end.
    subst.

    assert (exists ret_count, (ret_count <= 8)%nat /\
                   retnames = List.firstn ret_count (reg_class.all reg_class.arg) /\
                   binds_count = ret_count) as RC. {
      apply_in_hyps @map.putmany_of_list_zip_sameLength.
      apply_in_hyps @map.getmany_of_list_length.
      exists (List.length retnames). ssplit. 2: congruence. 2: {
        rewrite List.firstn_length in *.
        change (Datatypes.length (reg_class.all reg_class.arg)) with 8%nat in *.
        blia.
      }
      replace retnames with
          (List.firstn (Datatypes.length retnames) (reg_class.all reg_class.arg)) by (symmetry;assumption).
      rewrite List.firstn_length.
      change (Datatypes.length (reg_class.all reg_class.arg)) with 8%nat.
      clear. blia.
    }
    destruct RC as (ret_count & RC & ? & ?). subst retnames binds_count.


    (* increase sp *)
    eapply runsToStep'_of_step. {
      eapply (run_Addi iset RegisterNames.sp RegisterNames.sp);
        simpl_MetricRiscvMachine_get_set;
        try safe_sidecond.
      { rewrite map.get_put_diff by (clear; cbv; congruence).
        repeat match goal with
               | H: ?T |- _ => lazymatch T with
                               | map.putmany_of_list_zip _ _ _ = Some middle_regs0 => revert H
                               | map.get middle_regs RegisterNames.sp = Some _ => revert H
                               | valid_FlatImp_vars body => revert H
                               | Forall valid_FlatImp_var (List.firstn _ _) => revert H
                               | map.ok _ => revert H
                               | _ => clear H
                               end
               end.
        repeat match goal with
               | |- forall (_: map.ok _), _ => intro
               end.
        intros V G PM.
        eapply map.putmany_of_list_zip_get_oldval. 1: exact PM. 2: exact G.
        intro C.
        apply_in_hyps modVars_as_list_valid_FlatImp_var.
        lazymatch goal with
        | H: Forall ?P ?L |- _ =>
          eapply (proj1 (Forall_forall P L)) in H; [rename H into B|]
        end.
        2: eapply In_list_diff_weaken; exact C.
        clear -B.
        unfold valid_FlatImp_var, RegisterNames.sp in *.
        blia.
      }
    }

    simpl.
    simpl_MetricRiscvMachine_get_set.
    clear_old_sep_hyps.
    intros. fwd.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    (* jump back to caller *)
    eapply runsToStep'_of_step. {
      eapply run_Jalr0 with (rs1 := RegisterNames.ra); simpl; try safe_sidecond.
      3: {
        rewrite map.get_put_diff by (clear; cbv; congruence).
        rewrite map.get_put_same. reflexivity.
      }
      1: reflexivity.
      1: solve_divisibleBy4.
      (* TODO: safe_sidecond should also solve these, even though it needs shrink_footpr_subset *)
    }

    simpl.
    simpl_MetricRiscvMachine_get_set.
    clear_old_sep_hyps.
    intros. fwd.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    (* computed postcondition satisfies required postcondition: *)
    apply runsToDone.
    simpl_MetricRiscvMachine_get_set.
    do 6 eexists. split; [eassumption|]. simpl.
    match goal with
    | |- (_ /\ ?ODGoal) /\ _ => assert ODGoal as OD
    end.
    {
      apply_in_hyps (@map.only_differ_putmany _ _ _ locals_ok _ _).
      (* TODO these should be in map_solver or another automated step *)
      rewrite ?of_list_list_union in *.
      change (of_list []) with (@empty_set Register).
      (* TODO map_solver should be fast enough without this manual clearing *)
      repeat match goal with
             | H: (_ * _)%sep _ |- _ => clear H
             | H: valid_machine _ |- _ => clear H
             end.
      clear IHexec.
      (* TODO map_solver should work here, but it's too slow *)

      unfold map.only_differ.
      intros x.
      unfold PropSet.union, PropSet.elem_of, of_list.
      match goal with
      | |- context[In x ?L] => destruct (in_dec Z.eq_dec x L) as [HI | HNI]
      end.
      1: clear -HI; auto.
      destr (Z.eqb x RegisterNames.ra). {
        subst. unfold singleton_set. auto.
      }
      right.
      lazymatch goal with
      | H: map.putmany_of_list_zip ?S _ middle_regs = Some middle_regs0 |- _ =>
        destruct (in_dec Z.eq_dec x S) as [HI' | HNI']
      end.
      * (* 1) prove that LHS is in newvalues: *)
        pose proof (In_nth_error _ _ HI') as B. destruct B as [i B].
        pose proof @map.getmany_of_list_get as D. specialize D with (1 := P2) (2 := B).
        pose proof (nth_error_Some (list_diff Z.eqb (modVars_as_list Z.eqb body)
           (List.firstn ret_count (reg_class.all reg_class.arg))) i) as N.
        apply proj1 in N. specialize_hyp N. 1: congruence.
        lazymatch goal with
        | H: map.putmany_of_list_zip ?S _ middle_regs = Some middle_regs0 |- _ =>
          pose proof (map.putmany_of_list_zip_sameLength _ _ _ _ H) as Q
        end.
        rewrite Q in N.
        apply nth_error_Some in N.
        destr (nth_error newvalues i); try congruence.
        specialize D with (1 := eq_refl).
        rewrite map.get_put_diff in D.
        2: {
          move HI' at bottom.
          intro C. subst.
          apply_in_hyps modVars_as_list_valid_FlatImp_var.
          lazymatch goal with
          | H: Forall ?P ?L |- _ =>
            eapply (proj1 (Forall_forall P L)) in H; [rename H into BB|]
          end.
          2: eapply In_list_diff_weaken; eassumption.
          clear -BB.
          unfold valid_FlatImp_var, RegisterNames.sp in *.
          blia.
        }
        rewrite map.get_put_dec. destruct_one_match. 1: {
          exfalso.
          move HI' at bottom.
          apply_in_hyps modVars_as_list_valid_FlatImp_var.
          lazymatch goal with
          | H: Forall ?P ?L |- _ =>
            eapply (proj1 (Forall_forall P L)) in H; [rename H into BB|]
          end.
          2: eapply In_list_diff_weaken; eassumption.
          clear -BB.
          unfold valid_FlatImp_var, RegisterNames.sp in *.
          blia.
        }
        rewrite map.get_put_diff by congruence.
        rewrite D. rewrite <- E0.

        (* 2) prove that RHS is in newvalues: *)
        pose proof (map.putmany_of_list_zip_get_newval (ok := locals_ok)) as D'.
        lazymatch goal with
        | H: map.putmany_of_list_zip _ _ middle_regs = Some middle_regs0 |- _ =>
          specialize D' with (1 := H) (3 := B) (4 := E0)
        end.
        rewrite D'. 1: assumption.
        eapply list_diff_NoDup.
        eauto using NoDup_modVars_as_list.

      * (* if not in modvars (HNI'): *)
        destr (Z.eqb x RegisterNames.sp).
        { subst.
          transitivity (Some p_sp). 1: assumption.
          symmetry.
          rewrite map.get_put_same.
          f_equal.
          subst FL.
          simpl_addrs.
          solve_word_eq word_ok. }
        { rewrite !map.get_put_diff by assumption.
          clear A.
          (* initialL_regs to middle_regs *)
          lazymatch goal with
          | H: map.only_differ _ _ middle_regs |- _ => rename H into A; move A at bottom
          end.
          unfold map.only_differ in A. specialize (A x).
          destruct A as [A | A]. {
            unfold elem_of, of_list in A.
            exfalso. apply HNI'.
            unfold union, elem_of, of_list, singleton_set in A.
            destruct A as [A | A].
            - exfalso. eapply HNI'.
              eapply In_list_diff; assumption.
            - congruence.
          }
          rewrite !map.get_put_diff in A by assumption.
          rewrite A. clear A.

          (* middle_regs to middle_regs0 *)
          lazymatch goal with
          | H: map.only_differ _ _ middle_regs0 |- _ => rename H into A; move A at bottom
          end.
          unfold map.only_differ in A. specialize (A x).
          destruct A as [A | A]. {
            unfold elem_of, of_list in A.
            exfalso. apply HNI'. exact A.
          }
          exact A.
        }
    }

    ssplit.
    + solve_word_eq word_ok.
    + exact OD.
    + assert ((Datatypes.length (modVars_as_list Z.eqb body)) <= 29)%nat by
        auto using NoDup_valid_FlatImp_vars_bound_length, NoDup_modVars_as_list, modVars_as_list_valid_FlatImp_var.
      assert ((Datatypes.length
                 (list_diff Z.eqb (modVars_as_list Z.eqb body)
                            (List.firstn ret_count (reg_class.all reg_class.arg))))
              <= (Datatypes.length (modVars_as_list Z.eqb body)))%nat by
        apply list_diff_length.
      assert (#(Datatypes.length
                  (list_diff Z.eqb (modVars_as_list Z.eqb body)
                             (List.firstn ret_count (reg_class.all reg_class.arg)))) <= 29) by
        blia.
      clear - H8 H2p5.

      cbv[lowerMetrics] in *.
      unfold withInstructions, withLoads, withStores, withJumps,
        addMetricInstructions, addMetricLoads, addMetricStores, addMetricJumps,
        subMetricInstructions, subMetricLoads, subMetricStores, subMetricJumps,
        metricsOp, metricSub, metricsSub, metricLeq, metricsLeq
        in *.
      repeat simpl_MetricLog.
      remember (Datatypes.length
                  (list_diff Z.eqb (modVars_as_list Z.eqb body) (List.firstn ret_count (reg_class.all reg_class.arg)))) as blah.

      destruct mach_metrics.
      destruct middle_metrics.
      unfold Platform.MetricLogging.metricsLeq, Platform.MetricLogging.metricLeq,
        Platform.MetricLogging.metricsSub, Platform.MetricLogging.metricSub
        in *.
      repeat
        match goal with
        | |- context[?f ?n (Platform.MetricLogging.mkMetricLog ?i ?s ?l ?j)] =>
            match type of (f n (Platform.MetricLogging.mkMetricLog i s l j)) with
            | Platform.MetricLogging.MetricLog =>
                progress let t := eval hnf in (f n (Platform.MetricLogging.mkMetricLog i s l j)) in
                           let t' := eval cbn -[BinInt.Z.add BinInt.Z.sub BinInt.Z.mul Z.of_nat Init.Nat.add] in t in
                             change (f n (Platform.MetricLogging.mkMetricLog i s l j)) with t'
            end
        end.
      cbn.
      repeat match goal with
             | |- context[?f ?n (Platform.MetricLogging.mkMetricLog ?i ?s ?l ?j)] =>
                 match type of (f n (Platform.MetricLogging.mkMetricLog i s l j)) with
              | Platform.MetricLogging.MetricLog =>
                  let t := eval hnf in (f n (Platform.MetricLogging.mkMetricLog i s l j)) in
                    let t' := eval cbn in t in
                      change (f n (Platform.MetricLogging.mkMetricLog i s l j)) with t' in H
                 end
             end.
      cbn in H2p5.
      (* cost_compile_spec constraint: cost_compile_spec >= (...93...) i think? *)
      blia.

    + do 2 eexists. split; [solve [align_trace]|]. simpl. cbv [final_trace]. simpl.
      split; [reflexivity|]. intros. cbv [fun_leakage fun_leakage_helper].
      simpl_rev. rewrite BPW in *. repeat rewrite <- app_assoc in *. cbn [List.app] in *.
      remember (p_sp - _) as new_sp. eassert (Esp: new_sp = _).
      2: { rewrite Esp in *. rewr_leakage. f_equal. repeat f_equal.
           cbv [leakage_events_rel]. rewrite leakage_events_app.
           2: { rewrite length_load_regs, length_leak_load_regs. reflexivity. }
           rewrite length_load_regs. simpl. repeat solve_word_eq word_ok || f_equal. }
      subst. solve_word_eq word_ok.
      
    + rename l into lH, finalRegsH into lFH', finalRegsH' into lH', st0 into lFH,
             middle_regs into lL.


      (* The following list of lemmas and about that much helper code would probably be required
         even in a near-perfect proof assistant:

         Summary of what happened in FlatImp:

         Action (in order):
         ------------------------------
         put (argnames, argvals) from outer locals into new empty map
         execute function body
         take (retnames, retvals) out of map and put into outer locals



         Summary of what happened in riscv:              Original low-level locals: lL

         Action (in order):               Correctness lemma:      New low-level locals:
         -------------------------------  ---------------------   ---------------------
         jump to function                 run_Jal
         decrease sp                      run_Addi
         save ra on stack                 run_store_word
         save vars modified by callee     save_regs_correct
         execute function body            IHexec                  middle_regs
         load back the modified vars      load_regs_correct       middle_regs0
         load back the return address     run_load_word
         increase sp                      run_Addi
         jump back to caller              run_Jalr0
       *)
      match goal with
      | |- map.extends ?A lH' => remember A as middle_regs0_ra_sp
      end.
      subst FL.
      apply_in_hyps modVars_as_list_valid_FlatImp_var.
      repeat match goal with
             | H: ?T |- _ => lazymatch T with
                             | Forall valid_FlatImp_var _ => revert H
                             | regs_initialized _ => revert H
                             | map.putmany_of_list_zip _ retvs lH = Some lH' => revert H
                             | map.extends _ lH => revert H
                             | map.only_differ _ _ _ => revert H
                             | map.getmany_of_list _ _ = Some _ => revert H
                             | map.extends lL lFH' => revert H
                             | map.putmany_of_list_zip _ newvalues lL = Some _ => revert H
                             | middle_regs0_ra_sp = _ => revert H
                             | @map.get _ _ locals _ _ = _ => revert H
                             | map.forall_keys _ _ => revert H
                             | forall _ _, map.get _ _ = Some _ -> valid_FlatImp_var _ => revert H
                             | map.ok locals => revert H
                             | _ => clear H
                             end
             end.
        repeat match goal with
               | |- Forall valid_FlatImp_var _ -> _ => let F := fresh "F" in intro F
               | |- regs_initialized _ -> _ => let RI := fresh "RI" in intro RI
               | |- forall (_: map.ok _), _ => intro
               | |- (forall _ _, map.get _ _ = Some _ -> valid_FlatImp_var _) -> _ =>
                 let V := fresh "V0" in intros V
               | |- map.forall_keys _ _ -> _ =>
                 let V := fresh "V0" in intros V
               | |- map.getmany_of_list _ _ = _ -> _ => let GM := fresh "GM0" in intros GM
               | |- map.putmany_of_list_zip _ _ _ = _ -> _ => let PM := fresh "PM0" in intros PM
               | |- map.only_differ _ _ _ -> _ => let OD := fresh "OD0" in intros OD
               | |- map.extends _ _ -> _ => let Ext := fresh "Ext0" in intros Ext
               | |- map.get _ _ = _ -> _ => let G := fresh "G0" in intros G
               | |- _ = _ -> _ => let Eq := fresh "Eq0" in intros Eq
               end.

        (* turn all map.putmany_of_list_zip into map.putmany *)
        repeat match goal with
        | H: map.putmany_of_list_zip ?ks ?vs ?orig = Some ?res |- _ =>
          eapply map.putmany_of_list_zip_to_disjoint_putmany in H;
          let m0 := fresh "m0" in let m1 := fresh "m0" in let ksvs := fresh "ksvs" in
          let SD := fresh "SD0" in
          destruct H as (m0 & m1 & ksvs & H & ? & ? & ? & ? & SD);
          try subst orig; try subst res
        end.

        (* turn all map.getmany_of_list into splits *)
        repeat match goal with
        | H: map.getmany_of_list ?m _ = Some _ |- _ =>
          eapply map.getmany_of_list_to_split in H;
          let m0 := fresh "m0" in let ksvs := fresh "ksvs" in
          destruct H as (m0 & ksvs & H & ? & ?);
          try subst m
        end.

    repeat match goal with
           | H: forall _ _, map.get ?m _ = Some _ -> valid_FlatImp_var _ |- _ =>
             change (map.forall_keys valid_FlatImp_var m) in H
           end.
    repeat match goal with
           | H: map.forall_keys _ (map.putmany _ _) |- _ =>
             eapply invert_forall_keys_putmany in H;
             let H' := fresh H in destruct H as [H H']
           end.
    repeat match goal with
           | H1: ?lhs = Some ?rhs1, H2: ?lhs = Some ?rhs2 |- _ =>
             pose proof (Option.eq_of_eq_Some _ _ (eq_trans (eq_sym H1) H2));
             try ((subst rhs1 || subst rhs2); clear H2)
           end.
    repeat match goal with
           | H: map.extends _ (map.putmany _ _) |- _ =>
             eapply invert_extends_disjoint_putmany in H; [|eassumption];
             let H' := fresh H in destruct H as [H H']
           end.

    rewrite Eq0 in OD1.
    eapply only_differ_remove with (k := RegisterNames.sp) in OD1.
    rewrite remove_put_same in OD1.
    eapply only_differ_remove with (k := RegisterNames.ra) in OD1.
    rewrite (remove_comm (map.put (map.putmany m0 ksvs) RegisterNames.ra ret_addr)) in OD1.
    rewrite remove_put_same in OD1.
    match type of OD1 with
    | map.only_differ _ ?s _ => replace s with
          (of_list (List.firstn ret_count (reg_class.all reg_class.arg))) in OD1
    end.
    2: {
      extensionality k. unfold of_list, diff, union, singleton_set, elem_of.
      apply propositional_extensionality. split; intros A.
      - ssplit.
        + left. apply In_list_union_l. assumption.
        + intro C. subst. eapply sp_not_in_arg_regs. eassumption.
        + intro C. subst. eapply ra_not_in_arg_regs. eassumption.
      - destruct A as [A ?]. destruct A as [A ?]. destruct A as [A | A].
        + eapply In_list_union_invert in A. destruct A. 2: contradiction. assumption.
        + exfalso. congruence.
    }

    eapply only_differ_remove with (k := RegisterNames.sp) in OD0.
    rewrite remove_put_same in OD0.
    eapply only_differ_remove with (k := RegisterNames.ra) in OD0.
    match type of OD0 with
    | map.only_differ _ ?s _ => replace s with
          (of_list (modVars_as_list Z.eqb body)) in OD0
    end.
    2: {
      extensionality k. unfold of_list, diff, union, singleton_set, elem_of.
      apply propositional_extensionality. split; intros A.
      - ssplit.
        + left. assumption.
        + intro C. subst. eapply sp_not_valid_FlatImp_var. eapply Forall_forall; eassumption.
        + intro C. subst. eapply ra_not_valid_FlatImp_var. eapply Forall_forall; eassumption.
      - destruct A as [A ?]. destruct A as [A ?]. destruct A as [A | A].
        + assumption.
        + exfalso. congruence.
    }

    rename ksvs into m_modvars, ksvs0 into m_retvs.
    subst middle_regs0_ra_sp.
    eapply put_extends_l. 1: eauto with map_hints.
    eapply put_extends_l. 1: eauto with map_hints.
    eapply extends_putmany.
    * eapply extends_trans with (s2 :=
         map.remove (map.remove (map.putmany m0 m_modvars) RegisterNames.ra) RegisterNames.sp).
      {
        eapply extends_remove.
        eapply extends_remove.
        eapply extends_refl.
      }
      eapply extends_if_only_differ_in_undef. 3: exact OD1.
      2: {
        eapply map.undef_on_disjoint_of_list_zip; eassumption.
      }
      eapply remove_extends. 2: eauto with map_hints.
      eapply remove_extends. 2: eauto with map_hints.
      assumption.
    * eapply putmany_l_extends. 2: eassumption.
      unfold map.extends.
      intros *. intro G.
      move Ext2 at bottom. unfold map.extends in Ext2.
      rewrite map.putmany_comm in Ext2 by assumption.
      specialize Ext2 with (1 := G).
      rewrite map.get_putmany_dec in Ext2.
      destr (map.get m0 x). 1: assumption.
      exfalso.
      move GM1 at bottom.
      unfold map.sub_domain in SD0.
      specialize SD0 with (1 := Ext2). destruct SD0 as [v2 Gm].
      eapply map.get_of_list_zip in GM1. rewrite Gm in GM1. symmetry in GM1.
      eapply map.zipped_lookup_Some_in in GM1.
      move GM2 at bottom.
      eapply map.get_of_list_zip in GM2. rewrite G in GM2. symmetry in GM2.
      eapply map.zipped_lookup_Some_in in GM2.
      eapply invert_In_list_diff in GM1. destruct GM1 as [_ C]. contradiction.

    + unfold map.forall_keys in *.
      lazymatch goal with
      | H: map.putmany_of_list_zip _ _ _ = Some finalRegsH',
        L: forall _ _, map.get l _ = Some _ -> valid_FlatImp_var _ |- _
        => rename H into P, L into G; clear -P G locals_ok
      end.
      intros.
      pose proof (map.putmany_of_list_zip_find_index _ _ _ _ _ _ P H) as Q.
      destruct Q as [ [ n [A B] ] | C ].
      * eapply Forall_forall. 2: eapply nth_error_In. 2: exact A.
        unfold reg_class.all.
        eapply List.Forall_firstn.
        eapply List.Forall_filter.
        intros *. intro E. destr (reg_class.get a); try discriminate E.
        unfold reg_class.get in E0. fwd.
        unfold FlatToRiscvDef.valid_FlatImp_var. destruct_one_match_hyp.
        -- fwd. blia.
        -- destruct_one_match_hyp. 1: discriminate.
           destruct_one_match_hyp; discriminate.
      * eapply G. exact C.
    + subst FL.
      rewrite map.get_put_same. f_equal.
      replace (bitwidth iset) with width.
      replace (Memory.bytes_per_word width) with bytes_per_word by reflexivity.
      simpl_addrs.
      solve_word_eq word_ok.
    + eapply preserve_regs_initialized_after_put.
      eapply preserve_regs_initialized_after_put.
      eapply preserve_regs_initialized_after_putmany_of_list_zip; cycle 1; try eassumption.
    + reflexivity.
    + assumption.
    + epose (?[new_ra]: word) as new_ra. cbv delta [id] in new_ra.
      exists (stack_trash ++ frame_trash0 ++ newvalues ++ [new_ra]), frame_trash.
      assert (List.length newvalues =
              List.length (list_diff Z.eqb (modVars_as_list Z.eqb body)
                                     (List.firstn ret_count (reg_class.all reg_class.arg)))). {
        symmetry. eapply map.getmany_of_list_length. eassumption.
      }
      subst FL new_ra.
      simpl_addrs.
      ssplit. 1: blia. 1: reflexivity.
      wcancel_assumption.
    + reflexivity.
    + assumption.
  Qed.


  Ltac finishcost :=
    scost_unfold;
    repeat match goal with
           | H : ForallVars_bcond _ ?cond |- _ => destruct cond eqn:?; unfold ForallVars_bcond in H
           | H : valid_FlatImp_var _ |- _ => apply valid_FlatImp_var_isRegZ in H; rewrite H in *
           | H : _ /\ _ |- _ => destruct H
           end;
    MetricsToRiscv.solve_MetricLog.

  Lemma compile_stmt_correct:
    (forall resvars extcall argvars,
        compiles_FlatToRiscv_correctly compile_ext_call leak_ext_call
          compile_ext_call (SInteract resvars extcall argvars)) ->
    (forall s,
        compiles_FlatToRiscv_correctly compile_ext_call leak_ext_call
          (compile_stmt iset compile_ext_call) s).
  Proof. (* by induction on the FlatImp execution, symbolically executing through concrete
     RISC-V instructions, and using the IH for lists of abstract instructions (eg a then or else branch),
     using cancellation, bitvector reasoning, lia, and firstorder for the sideconditions. *)
    intros compile_ext_call_correct.
    unfold compiles_FlatToRiscv_correctly.
    induction 1; intros; unfold goodMachine in *; destruct g.
      all: repeat match goal with
                  | m: _ |- _ => destruct_RiscvMachine m
                  end.
      1,2,3,4,5,6,7,8,9,10,11,12,13,14(*all except the weird ones: quit, forall, exitss*): match goal with
           | H: fits_stack _ _ _ ?s |- _ =>
             let h := head_of_app s in idtac h; is_constructor h;
             inversion H; subst
           end.
      all: fwd.
    (*about this many lines should have been enough to prove this...*)

    - idtac "Case compile_stmt_correct/SInteract".
      eapply runsTo_weaken.
      + unfold compiles_FlatToRiscv_correctly in *.
        eapply compile_ext_call_correct with
            (postH := post) (g := {| allx := allx |}) (pos := pos)
            (extcall := action) (argvars := argvars) (resvars := resvars) (initialMH := m);
          simpl;
          clear compile_ext_call_correct; cycle -2.
        { unfold goodMachine, valid_FlatImp_var in *. simpl. ssplit; eauto. }
        all: eauto using exec.interact, fits_stack_interact.
      + simpl. intros [finalL finalAEP] A. destruct_RiscvMachine finalL. unfold goodMachine in *. simpl in *.
        destruct_products. subst.
        do 6 eexists; ssplit; eauto.

    - idtac "Case compile_stmt_correct/SCall".
      (* We have one "map.get e fname" from exec, one from fits_stack, make them match *)
      unfold good_e_impl, valid_FlatImp_fun in *.
      simpl in *.
      fwd.
      lazymatch goal with
      | H1: map.get e_impl_full fname = ?RHS1,
        H2: map.get e_impl fname = ?RHS2,
        H3: map.extends e_impl_full e_impl |- _ =>
        let F := fresh in assert (RHS1 = RHS2) as F
            by (clear -H1 H2 H3;
                unfold map.extends in H3;
                specialize H3 with (1 := H2); clear H2;
                etransitivity; [symmetry|]; eassumption);
        inversion F; subst; clear F
      end.
      match goal with
      | H: map.get e_impl fname = Some _, G: _ |- _ =>
          pose proof G as e_impl_reduced_props;
          specialize G with (1 := H);
          simpl in G
      end.
      fwd.
      match goal with
      | H: map.get e_pos _ = Some _ |- _ => rename H into GetPos
      end.

      rename stack_trash into old_stackvals.
      rename frame_trash into unused_part_of_caller_frame.

      assert (valid_register RegisterNames.ra) by (cbv; auto).
      assert (valid_register RegisterNames.sp) by (cbv; auto).

      (* jump to function *)
      eapply runsToStep'_of_step. {
        eapply run_Jal; simpl; try solve [sidecondition]; cycle 2.
        - solve_divisibleBy4.
        - assumption.
      }
      simpl_MetricRiscvMachine_get_set.
      clear_old_sep_hyps.
      intro mid. set (mach := mid). intros. fwd. destruct_RiscvMachine mid. subst.

      remember mach.(getLog) as t.
      assert (GM: goodMachine t m l
                              {| p_sp := p_sp;
                                 rem_stackwords := #(List.length old_stackvals);
                                 rem_framewords := #(List.length unused_part_of_caller_frame);
                                 dframe := dframe;
                                 allx := allx |}
                              mach). {
        unfold goodMachine; simpl.
        subst mach. subst. simpl. ssplit.
        all: try eauto with map_hints.
      }
      match type of GM with
      | goodMachine _ _ _ ?gh _ => remember gh as g
      end.
      match goal with
      | |- ?G => replace G with
          (runsToNonDet.runsTo (step' RiscvMachineL (mcomp_sat (Run.run1 iset))) (
    mach, aep)
    (fun '(finalL, finalAEP) =>
     exists
       (finalQ : bool) (finalK : leakage) (finalTrace : Semantics.trace) 
     (finalMH : mem) (finalRegsH : locals) (finalMetricsH : MetricLog),
       post finalQ finalAEP finalK finalTrace finalMH finalRegsH finalMetricsH /\
       (if finalQ
        then
         getPc finalL = program_base + !pos + !(4 * #1) /\
         map.only_differ initialL_regs
           (union (of_list (list_union Z.eqb binds []))
              (singleton_set RegisterNames.ra)) (getRegs finalL)
        else True) /\
       (getMetrics finalL - initialL_metrics <= lowerMetrics (finalMetricsH - mc))%metricsL /\
       (exists (kH'' : list leakage_event) (finalKL : list LeakageEvent),
          finalK = kH'' ++ k /\
          getTrace finalL = Some finalKL /\
          (if finalQ
           then
            forall (k0 : list leakage_event)
              (cont0 : leakage -> list LeakageEvent -> list LeakageEvent * word),
            stmt_leakage iset compile_ext_call leak_ext_call e_pos e_impl_full
              program_base
              (SCall binds fname args, rev kH'' ++ k0, rev initialKL, pos, p_sp,
               (bytes_per_word * #(Datatypes.length unused_part_of_caller_frame))%Z,
               cont0) = cont0 (rev kH'') (rev finalKL)
           else True)) /\
       (if finalQ
        then goodMachine finalTrace finalMH finalRegsH g finalL
        else getLog finalL = finalTrace))) end.
      2: { subst. reflexivity. }

      pose proof functions_expose as P.
      match goal with
      | H: map.get e_impl _ = Some _ |- _ => specialize P with (2 := H)
      end.
      specialize P with (1 := GetPos).
      specialize (P program_base).
      match type of P with
      | iff1 _ (functions _ _ _ * ?F)%sep => set (current_fun := F) in *
      end.
      apply iff1ToEq in P.
      match goal with
      | H: iff1 allx _ |- _ => rewrite P in H
      end.
      clear P.
      set (insts := (compile_function e_pos pos0 (argnames, retnames, body))) in *.
      rename xframe into xframe_orig.
      set (xframe := (xframe_orig *
          (ptsto_instr iset (program_base + !pos)
                       (IInstruction (Jal RegisterNames.ra (pos0 - pos))) * emp True))%sep) in *.
      match goal with
      | H: iff1 allx _ |- _ => rename H into A
      end.
      move A before GM. replace allx with (FlatToRiscvCommon.allx g) in A by (subst; reflexivity).
      rename e_impl into e_impl_orig.
      set (e_impl := (map.remove e_impl_orig fname)) in *.
      rewrite <- (sep_comm current_fun) in A. rewrite <- sep_assoc in A.
      change current_fun with (program iset (program_base + !pos0) insts) in A.
      eassert (_ = insts) as C. {
        subst insts. reflexivity.
      }
      move C after A.
      match goal with
      | H: exec _ _ body _ _ _ _ _ _ _ _ |- _ => rename H into Exb
      end.
      move Exb before C.
      assert (Ext: map.extends e_impl_full e_impl). {
        subst e_impl. eauto with map_hints.
      }
      move Ext before Exb.
      assert (GE: good_e_impl e_impl e_pos). {
        unfold good_e_impl.
        move e_impl_reduced_props at bottom.
        intros *. intro G.
        assert (map.get e_impl_orig f = Some fun_impl) as G'. {
          subst e_impl.
          eapply get_Some_remove; eassumption.
        }
        specialize e_impl_reduced_props with (1 := G'). fwd.
        repeat split; eauto.
      }
      move GE before Ext.
      match goal with
      | H: fits_stack ?x ?y e_impl body |- _ =>
        rename H into FS; move FS after GE;
          replace y with
              (g.(rem_stackwords) - framelength (argnames, retnames, body))%Z in FS
      end.
      2: {
        unfold framelength. subst g. simpl. blia.
      }
      (* already in valid_FlatImp_fun
      match goal with
      | H: FlatImpConstraints.uses_standard_arg_regs body |- _ => rename H into SA; move SA after C
      end.
      *)
      assert (V: valid_FlatImp_fun (argnames, retnames, body)). {
        simpl. eauto.
      }
      move V before C.
      match goal with
      | H: pos0 mod 4 = 0 |- _ => rename H into Mo; move Mo after V
      end.
      match goal with
      | H: word.unsigned program_base mod 4 = 0 |- _ => rename H into Mo'; move Mo' after Mo
      end.
      eassert (GPC: mach.(getPc) = program_base + !pos0). {
        subst mach. simpl. solve_word_eq word_ok.
      }
      move GPC after A.
      rename pos into pos_orig, pos0 into pos.
      replace (!(4 * #1)) with (word.of_Z (word := word) 4). 2: { solve_word_eq word_ok. }
      assert (OL: map.of_list_zip argnames argvs = Some st0) by assumption.
      move OL after Exb.
      set (stack_trash := old_stackvals).
      assert (args = List.firstn (Datatypes.length argnames) (reg_class.all reg_class.arg)). {
        replace (Datatypes.length argnames) with (Datatypes.length args). 1: assumption.
        apply_in_hyps @map.putmany_of_list_zip_sameLength.
        apply_in_hyps @map.getmany_of_list_length.
        congruence.
      }
      subst args.
      let T := type of IHexec in
      let T' :=
        open_constr:(
forall (g : GhostConsts) (e_impl : env) (e_pos : pos_map) 
      (program_base : word) (insts : list Instruction) (xframe : mem -> Prop)
      (initialL : RiscvMachineL) (pos : Z) (initialKL : list LeakageEvent)
      (cont : list leakage_event ->
              leakage -> list LeakageEvent -> list LeakageEvent * word),
    map.extends e_impl_full e_impl ->
    (forall (f : string) (fun_impl : list Z * list Z * stmt Z),
     map.get e_impl f = Some fun_impl ->
     (let
      '(argnames, retnames, body) := fun_impl in
       argnames = List.firstn (Datatypes.length argnames) (reg_class.all reg_class.arg) /\
       retnames = List.firstn (Datatypes.length retnames) (reg_class.all reg_class.arg) /\
       valid_FlatImp_vars body /\ FlatImpConstraints.uses_standard_arg_regs body) /\
     (let
      '(_, _, _) := fun_impl in
       exists pos0 : Z, map.get e_pos f = Some pos0 /\ pos0 mod 4 = 0)) ->
    fits_stack (rem_framewords g) (rem_stackwords g) e_impl body ->
    compile_stmt iset compile_ext_call e_pos pos (bytes_per_word * rem_framewords g)
      body = insts ->
    FlatImpConstraints.uses_standard_arg_regs body ->
    valid_FlatImp_vars body ->
    pos mod 4 = 0 ->
    word.unsigned program_base mod 4 = 0 ->
    getPc initialL = program_base + !pos ->
    getTrace initialL = Some initialKL ->
    iff1 (FlatToRiscvCommon.allx g)
      ((xframe * program iset (program_base + !pos) insts)%sep *
       functions program_base e_pos e_impl) ->
    map.extends (getRegs initialL) st0 /\
    map.forall_keys valid_FlatImp_var st0 /\
    map.get (getRegs initialL) RegisterNames.sp = Some (FlatToRiscvCommon.p_sp g) /\
    regs_initialized (getRegs initialL) /\
    getNextPc initialL = getPc initialL + !4 /\
    subset (footpr (FlatToRiscvCommon.allx g)) (of_list (getXAddrs initialL)) /\
    (exists stack_trash frame_trash : list word,
       #(Datatypes.length stack_trash) = rem_stackwords g /\
       #(Datatypes.length frame_trash) = rem_framewords g /\
       (FlatToRiscvCommon.allx g * FlatToRiscvCommon.dframe g * eq m *
        word_array (FlatToRiscvCommon.p_sp g - !(bytes_per_word * rem_stackwords g))
          stack_trash * word_array (FlatToRiscvCommon.p_sp g) frame_trash)%sep
         (getMem initialL)) /\ getLog initialL = mid_log /\ valid_machine initialL ->
    (forall k0 : list leakage_event,
     pick_sp1 (k0 ++ leak_unit :: k) =
     snd
       (stmt_leakage iset compile_ext_call leak_ext_call e_pos e_impl_full program_base
          (body, rev k0, rev initialKL, pos, FlatToRiscvCommon.p_sp g,
           (bytes_per_word * rem_framewords g)%Z, cont k0))) ->
    runsTo' (initialL, aep)
      (fun '(finalL, finalAEP) =>
       exists
         (finalQ : bool) (finalK : leakage) (finalTrace : Semantics.trace) 
       (finalMH : mem) (finalRegsH : locals) (finalMetricsH : MetricLog),
         outcome finalQ finalAEP finalK finalTrace finalMH finalRegsH finalMetricsH /\
         (if finalQ
          then
           getPc finalL = getPc initialL + !(4 * #(Datatypes.length insts)) /\
           map.only_differ (getRegs initialL)
             (union (of_list (modVars_as_list Z.eqb body))
                (singleton_set RegisterNames.ra)) (getRegs finalL)
          else True) /\
         (getMetrics finalL - getMetrics initialL <= lowerMetrics (finalMetricsH - mc))%metricsL /\
         (exists (kH'' : list leakage_event) (finalKL : list LeakageEvent),
            finalK = kH'' ++ leak_unit :: k /\
            getTrace finalL = Some finalKL /\
            (if finalQ
             then
              forall (k : list leakage_event)
                (cont0 : leakage -> list LeakageEvent -> list LeakageEvent * word),
              stmt_leakage iset compile_ext_call leak_ext_call e_pos e_impl_full
                program_base
                (body, rev kH'' ++ k, rev initialKL, pos, FlatToRiscvCommon.p_sp g,
                 (bytes_per_word * rem_framewords g)%Z, cont0) =
              cont0 (rev kH'') (rev finalKL)
             else True)) /\
         (if finalQ
          then goodMachine finalTrace finalMH finalRegsH g finalL
          else getLog finalL = finalTrace))) in replace T with T' in IHexec.
      2: {
        subst. reflexivity.
      }

      specialize IHexec with (1 := Ext).
      specialize IHexec with (1 := GE).
      specialize IHexec with (6 := Mo').
      match goal with
      | H: FlatImpConstraints.uses_standard_arg_regs body |- _ =>
        specialize IHexec with (3 := H)
      end.
      match goal with
      | H: valid_FlatImp_vars body |- _ => specialize IHexec with (3 := H)
      end.
      move stack_trash at top.
      move IHexec before OL.
      rename H3 into OC.
      rename H0 into GetMany.
      move GetMany after Exb.
      move OC before OL.
      remember (program_base + !pos_orig + !4) as ret_addr.
      assert (map.get mach.(getRegs) RegisterNames.ra = Some ret_addr) as Gra. {
        subst mach. cbn. eauto with map_hints.
      }
      move Gra after GPC.
      assert (word.unsigned ret_addr mod 4 = 0) as RaM by (subst ret_addr; solve_divisibleBy4).
      move RaM before Gra.
      replace mid_log with t in *.
      forget (Datatypes.length binds) as binds_count.
      subst binds.
      eapply runsTo_weaken.
      1:{
              match goal with
              | H: (binds_count <= 8)%nat |- _ => rename H into BC
              end.
              move BC after OC.
              (*We need to remember the definition of mach, or at least that getTrace mach = _ :: getTrace...*)
              eassert (Hmach : mach.(getTrace) = _).
              { subst mach. simpl. cbv [final_trace]. simpl. reflexivity. }
              repeat match goal with
                     | x := _ |- _ => clearbody x
                     end.
              eapply compile_function_body_correct; try eassumption. Check OC.
              1: eapply OC.
              intros. rewrite associate_one_left. rewr_picksp.
              cbv [fun_leakage]. rewrite fix_step. simpl_rev. cbn [stmt_leakage_body].
              rewrite H. rewrite GetPos. repeat rewrite <- app_assoc. f_equal.
              subst g. cbv [FlatToRiscvCommon.p_sp]. rewrite Heqret_addr.
              repeat Tactics.destruct_one_match.
              instantiate (1 := fun k0 a b => cont (k0 ++ [leak_unit]) (leak_unit :: a) b).
              repeat rewrite <- app_assoc. reflexivity. }
      subst mach. simpl_MetricRiscvMachine_get_set.
      intros. fwd. do 6 eexists.
      split; [ eapply H0p0 | ].
      destruct finalQ; fwd.
      + split; eauto 8 with map_hints.
        split.
        { (* cost_compile_spec constraint: cost_compile_spec + (1,1,1,0) <= cost_call *)
          unfold cost_compile_spec, cost_call in *.
          MetricsToRiscv.solve_MetricLog. }
        split; [|eassumption]. 
        do 2 eexists. split; [align_trace|]. split; [eassumption|].
        intros. simpl_rev. erewrite <- (H0p3p2 _ (fun x => cont0 (leak_unit :: x))).
        rewrite fix_step. cbv [stmt_leakage_body fun_leakage]. rewrite H. rewrite GetPos.
        repeat rewrite <- app_assoc. f_equal. subst g. cbv [FlatToRiscvCommon.p_sp].
        rewrite Heqret_addr. repeat Tactics.destruct_one_match.
        repeat rewrite <- app_assoc. reflexivity.
      + intuition.
        { unfold cost_compile_spec, cost_call in *.
          MetricsToRiscv.solve_MetricLog. }
        do 2 eexists. split; [align_trace|]. split; [eassumption|]. reflexivity.
    - idtac "Case compile_stmt_correct/SLoad".
      progress unfold Memory.load, Memory.load_Z in *. fwd.
(* <<<<<<< HEAD *)

      let Hl := constr:(SeparationMemory.sep_of_load_bytes _ _ _ _ ltac:(eassumption)) in
      let m := match type of Hl with _ ?m => m end in
      let Hm := match goal with H : context[eq m] |- _ => H end in
      epose proof seplog_subst_eq (mH:=m) Hm ltac:(ecancel) Hl as Hmem.
      lazymatch goal with H : iff1 allx _ |- _ => seprewrite_in H Hmem end.
      eapply runsTo'_det_step_with_valid_machine; [ assumption | simulate' | ].
      { unfold Memory.load, Memory.load_Z in *.
        erewrite SeparationMemory.load_bytes_of_sep; trivial.
        { ecancel_assumption. }
        { erewrite length_load_bytes; eauto. }
        { case sz, BW as [ [ -> | -> ] ]; cbv; clear; discriminate. } }
      { trivial. }
      intros.
      run1done.
      rewrite map.get_put_diff; trivial.
      intro; destruct sp_not_valid_FlatImp_var; congruence.

    - idtac "Case compile_stmt_correct/SStore".
      inline_iff1.
      simpl_MetricRiscvMachine_get_set.
      unfold Memory.store, Memory.store_Z, store_bytes in *; fwd.

      let Hl := constr:(SeparationMemory.sep_of_load_bytes _ _ _ _ ltac:(eassumption)) in
      let m := match type of Hl with _ ?m => m end in
      let Hm := match goal with H : context[eq m] |- _ => H end in
      epose proof seplog_subst_eq (mH:=m) Hm ltac:(ecancel) Hl as Hmem.

      match goal with H : context[unchecked_store_bytes ?m ?a ?v] |- _ =>
          edestruct (fun n _bs R => SeparationMemory.uncurried_store_bytes_of_sep a n _bs v R initialL_mem) as (?&Hstore&?);
          ssplit; [ecancel_assumption|..]
      end.
      { eapply length_load_bytes; eassumption. }
      { trivial. }
      { case sz, BW as [ [ -> | -> ] ]; cbv; clear; discriminate. }

      eapply runsTo'_det_step_with_valid_machine; [ assumption | simulate' | ]; trivial.
      intros.
      run1done.
      { eapply preserve_subset_of_xAddrs; eauto.
        { ecancel_assumption. } { rewrite LittleEndianList.length_le_split; trivial. }
        { case sz, BW as [ [ -> | -> ] ]; clear; cbv; trivial. } }
      { eexists _, _; ssplit; eauto.
        (* new low-level memory contains exactly new high-level memory *)
        use_sep_assumption; cancel; cbn [seps].
        rewrite sep_comm, <-sep_eq_putmany; cbv [unchecked_store_bytes sepclause_of_map].
        { Morphisms.f_equiv. apply map.map_ext; intros i.
          rewrite !map.get_putmany_dec; destruct (map.get (_$@_)) eqn:?; trivial.
          rewrite map.get_remove_many_notin; trivial; intros ?%map.in_keys_inv.
          erewrite ?map.get_of_list_word_at, ?map.get_of_list_word_at_domain, ?nth_error_None, ?LittleEndianList.length_le_split, ?length_load_bytes in  * by eauto; contradiction. }
        { intros i ? ? L%map.get_remove_many_Some_notin.
          rewrite  ?map.get_of_list_word_at; intros ?%nth_error_Some_bound_index.
          epose proof (fun v H => L (map.in_keys _ i v H)) as Hq; edestruct map.get eqn:Ei in Hq; eauto.
          erewrite ?map.get_of_list_word_at, ?nth_error_None, ?LittleEndianList.length_le_split, ?length_load_bytes in * by eauto; blia. } }

    - idtac "Case compile_stmt_correct/SInlinetable".
      inline_iff1.
      run1det.
      assert (map.get (map.put initialL_regs x (program_base + !pos + !4)) i = Some index). {
        rewrite map.get_put_diff by congruence. unfold map.extends in *. eauto.
      }
      run1det.
      assert (Memory.load sz initialL_mem (program_base + !pos + !4 + index + !0) = Some v). {
        rewrite word.add_0_r.
        eapply load_from_compile_byte_list. 1: eassumption.
        wcancel_assumption.
      }
      run1det.
      rewrite !map.put_put_same in *.
      assert (x <> RegisterNames.sp). {
        unfold valid_FlatImp_var, RegisterNames.sp in *.
        blia.
      }
      run1done.

    - idtac "Case compile_stmt_correct/SStackalloc".
      rename H1 into IHexec.
      assert (x <> RegisterNames.sp). {
        unfold valid_FlatImp_var, RegisterNames.sp in *.
        blia.
      }
      assert (valid_register RegisterNames.sp) by (cbv; auto).
      eapply runsToStep'_of_step. {
        eapply run_Addi; cycle 4; try safe_sidecond.
        apply valid_FlatImp_var_implies_valid_register. assumption.
      }
      simpl_MetricRiscvMachine_get_set.
      intros. fwd. destruct_RiscvMachine mid.
      assert (bytes_per_word = 4 \/ bytes_per_word = 8) as B48. {
        unfold bytes_per_word. destruct width_cases as [E | E]; rewrite E; cbv; auto.
      }
      assert (Memory.bytes_per_word (bitwidth iset) = bytes_per_word) as BPW. {
        rewrite bitwidth_matches. reflexivity.
      }
      assert (n / bytes_per_word <= Z.of_nat (List.length frame_trash)) as enough_stack_space. {
        match goal with
        | H: fits_stack _ _ _ _ |- _ => apply fits_stack_nonneg in H; move H at bottom
        end.
        rewrite BPW in *.
        blia.
      }
      assert (0 <= n / bytes_per_word) as Nonneg. {
        assert (0 <= n) as K by assumption. clear -B48 enough_stack_space K.
        Z.div_mod_to_equations. blia.
      }
      split_from_right frame_trash remaining_frame allocated_stack (Z.to_nat (n / bytes_per_word)).
      match goal with
      | H: Datatypes.length remaining_frame = _ |- _ => clear H
      end.

      edestruct (ll_mem_to_hl_mem mSmall mid_mem
                       (p_sp + !bytes_per_word * !#(Datatypes.length remaining_frame)))
        as (mStack & P & D & Ab). {
        use_sep_assumption.
        wseplog_pre.
        rewrite (cast_word_array_to_bytes allocated_stack).
        wcancel.
      }
      match reverse goal with
      | H: _ mid_mem |- _ => clear H
      end.
      subst.
      (* Note: this equation will be used by simpl_addrs *)
      assert ((bytes_per_word * (#(List.length remaining_frame) + n / bytes_per_word) - n)%Z
              = (bytes_per_word * (#(Datatypes.length remaining_frame)))%Z) as DeDiv. {
        rewrite BPW in *.
        forget bytes_per_word as B.
        forget (Datatypes.length remaining_frame) as L.
        assert (0 <= #L) as A1 by blia.
        assert (0 <= n) as A2 by blia.
        assert (n mod B = 0) as A3 by blia.
        assert (B = 4 \/ B = 8) as A4 by blia.
        clear -A1 A2 A3 A4.
        Z.to_euclidean_division_equations. blia.
      }

      assert (sp_val :pick_sp1 k = p_sp + !(bytes_per_word * #(Datatypes.length remaining_frame))).
      { specialize (H14 nil). simpl in H14. rewrite H14.
        rewrite fix_step. simpl. simpl_addrs. reflexivity. }
      rewrite sp_val in *. clear sp_val.

      eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
      + eapply IHexec with (g := {| p_sp := p_sp;
                                    rem_framewords := Z.of_nat (List.length remaining_frame); |})
                           (program_base := program_base)
                           (e_impl := e_impl)
                           (pos := (pos + 4)%Z)
                           (mStack := mStack)
                           (mCombined := map.putmany mSmall mStack);
          simpl_MetricRiscvMachine_get_set;
          simpl_g_get;
          rewrite ?@length_save_regs, ?@length_load_regs in *;
          simpl_word_exprs word_ok;
          ssplit;
          cycle -6.
        { reflexivity. }
        { eassumption. }
        { exists stack_trash, remaining_frame. ssplit. 1,2: reflexivity.
          wcancel_assumption. }
        { reflexivity. }
        { assumption. }
        { intros. rewrite associate_one_left. rewr_picksp.
          simpl_rev. rewrite fix_step. simpl. simpl_addrs.
          instantiate (2 := rev _). rewrite rev_involutive. reflexivity. }
        { match goal with
          | |- ?G => let t := type of Ab in replace G with t; [exact Ab|f_equal]
          end.
          1: solve_word_eq word_ok.
          rewrite @coqutil.Datatypes.List.length_flat_map with (n := Z.to_nat bytes_per_word).
          - simpl_addrs. rewrite !Z2Nat.id by blia. rewrite <- BPW. rewrite <- Z_div_exact_2; blia.
          - clear. intros. eapply LittleEndianList.length_le_split.
        }
        { unfold map.split; split. 1: reflexivity. assumption. }
        { eassumption. }
        { eassumption. }
        { rewrite BPW in *.
          match goal with
          | H: fits_stack ?N _ _ _ |- fits_stack ?N' _ _ _ => replace N' with N; [exact H|blia]
          end. }
        { reflexivity. }
        { assumption. }
        { eassumption. }
        { safe_sidecond. }
        { safe_sidecond. }
        { safe_sidecond. }
        { simpl. cbv [final_trace leakage_events_rel leakage_events].
          simpl. simpl_rev. simpl_addrs. reflexivity. }
        { etransitivity. 1: eassumption. wwcancel. }
        { match goal with
          | |- map.extends (map.put _ ?k ?v1) (map.put _ ?k ?v2) => replace v1 with v2
          end.
          - apply map.put_extends. assumption.
          - simpl_addrs. solve_word_eq word_ok. }
        { eauto with map_hints. }
        { eauto with map_hints. }
        { eauto with map_hints. }
      + intros [middle middleAEP]. intros. destruct_RiscvMachine middle. fwd.
        clear B48. rewrite BPW in *. clear BPW. simpl_addrs. destruct finalQ; fwd.
        2: { run1done. do 2 eexists. ssplit; [align_trace|reflexivity|reflexivity]. }
             
        run1done.
        * rewrite ?of_list_list_union in *.
          repeat match goal with
                 | H: (_ * _)%sep _ |- _ => clear H
                 | H: valid_machine _ |- _ => clear H
                 end.
          clear IHexec.
          repeat match goal with
                 | H: map.only_differ _ _ _ |- _ => revert H
                 end.
          intros OD.
          replace (of_list
                     (if find (Z.eqb x) (modVars_as_list Z.eqb body)
                      then modVars_as_list Z.eqb body
                      else x :: modVars_as_list Z.eqb body))
            with (union (singleton_set x) (of_list (modVars_as_list Z.eqb body))). 2: {
            clear.
            unfold union, of_list.
            extensionality y.
            apply propositional_extensionality.
            unfold PropSet.elem_of, singleton_set.
            destr (find (Z.eqb x) (modVars_as_list Z.eqb body)).
            - apply List.find_some in E. fwd. intuition congruence.
            - simpl. reflexivity.
          }
          eauto with map_hints.
        * simpl_rev. cbv [leakage_events_rel leakage_events] in *. simpl_addrs.
          rewr_leakage. reflexivity.
        * edestruct hl_mem_to_ll_mem with (mL := middle_mem) (mTraded := mStack')
            as (returned_bytes & L & Q).
          1, 2: eassumption.
          1: ecancel_assumption.
          edestruct (byte_list_to_word_list_array returned_bytes) as (returned_words & LL & QQ). {
            rewrite L. rewrite Z2Nat.id; assumption.
          }
          eexists stack_trash0, (frame_trash ++ returned_words). ssplit. 3: {
            seprewrite_in QQ Q.
            wcancel_assumption.
          }
          1: congruence.
          simpl_addrs.
          reflexivity.

    - idtac "Case compile_stmt_correct/SLit".
      inline_iff1.
      apply step_impl_step'_cps.
      Fail get_runsTo_valid_for_free. (* TODO fix this, instead of doing the thing below *)
      let R := fresh "R" in
      evar ( R : RiscvMachineL -> Prop ); eapply runsTo_get_sane with (P := R);
      [ assumption |  | ]; subst R.
      2: { intros ? ? V. instantiate (1 := fun mach' => valid_machine mach' -> _).
           simpl. intros H'. apply H'. assumption. }
      eapply compile_lit_correct_full.
      + sidecondition.
      + safe_sidecond.
      + unfold compile_stmt. simpl. ecancel_assumption.
      + sidecondition.
      + assumption.
      + simpl.
        assert (x <> RegisterNames.sp). {
          unfold valid_FlatImp_var, RegisterNames.sp in *.
          blia.
        }
        run1done.
        cbn.
        cost_unfold.
        repeat match goal with
               | H : valid_FlatImp_var _ |- _ => apply valid_FlatImp_var_isRegZ in H; try rewrite H in *
               end.
        remember (updateMetricsForLiteral v initialL_metrics) as finalMetrics;
        symmetry in HeqfinalMetrics;
        pose proof update_metrics_for_literal_bounded (width := width) as Hlit;
        specialize Hlit with (1 := HeqfinalMetrics);
        MetricsToRiscv.solve_MetricLog.

    - idtac "Case compile_stmt_correct/SOp".
      assert (x <> RegisterNames.sp). {
        unfold valid_FlatImp_var, RegisterNames.sp in *.
        blia.
      }
      inline_iff1;
      match goal with
      | op: Syntax.bopname.bopname |- _ => destr op
      end.
      Local Arguments Z.eqb : simpl never.
      all: scost_unfold; match goal with
           | y: operand, H: context[Syntax.bopname.eq] |- _ =>
               destr y; simpl in *;
               [ run1det; run1det; run1done;
                 rewrite reduce_eq_to_sub_and_lt, map.put_put_same;
                 eauto 8 with map_hints |  ]
           | y: operand |- _ =>
               destr y; simpl in *;
               [ run1det; run1done;
                 rewrite ?word.srs_ignores_hibits,
                   ?word.sru_ignores_hibits,
                   ?word.slu_ignores_hibits,
                   ?word.mulhuu_simpl,
                   ?word.divu0_simpl,
                   ?word.modu0_simpl;
                 eauto 8 with map_hints
               | try fwd; try eauto 8 with map_hints ]
           end.

      all : match goal with (* x * -1  --> -x *)
       |- context[Z.eqb (-1) ?c] => destruct (Z.eqb_spec (-1) c) as [<-|] in *; simpl in *
       | _ =>  shelve end.
      { run1det; run1done. change (-1) with (Z.opp 1).
        rewrite word.ring_morph_opp, word.mul_m1_r, word.sub_0_l; eauto with map_hints. }
      all: [> ]. Unshelve.

      all: match goal with
           | H: context[InvalidInstruction (-1)] |- _ =>  assert (Encode.verify (InvalidInstruction (-1)) iset \/
                  valid_InvalidInstruction (InvalidInstruction (-1))) by (eapply invert_ptsto_instr; ecancel_assumption)
           | |- _ => run1det; run1done
           end.
      all:
        match goal with
        | H: Encode.verify (InvalidInstruction (-1)) iset \/
               valid_InvalidInstruction (InvalidInstruction (-1)) |- _
          => exfalso; destruct H;
             [ unfold Encode.verify in H;
               simpl in H; destruct H; assumption
             | unfold valid_InvalidInstruction in H; fwd]
        end.
      all:
        match goal with
        | H: 0 <= -1 < 2^32 |- False
          => destruct H;
             match goal with
             | H: 0 <= -1 |- False => destruct H; simpl; reflexivity
             end
        end.

    - idtac "Case compile_stmt_correct/SSet".
      assert (x <> RegisterNames.sp). {
        unfold valid_FlatImp_var, RegisterNames.sp in *.
        blia.
      }
      inline_iff1.
      run1det. run1done.

    - idtac "Case compile_stmt_correct/SIf/Then".
      (* execute branch instruction, which will not jump *)
      eapply runsToStep'_of_step.
      + eapply compile_bcond_by_inverting_correct with (l := l) (b := true);
          simpl_MetricRiscvMachine_get_set;
          try safe_sidecond.
      + simpl_MetricRiscvMachine_get_set.
        intros. fwd.
        destruct_RiscvMachine mid.
        eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
        * (* use IH for then-branch *)
          eapply IHexec with (g := {| allx := allx |}) (pos := (pos + 4)%Z);
            after_IH.
          all: try safe_sidecond.
          all: try safe_sidecond.
          { simpl. subst. reflexivity. }
          { intros. rewrite associate_one_left, H13. rewrite fix_step.
            simpl_rev. simpl. cbn [leakage_events_rel leakage_events].
            repeat rewrite <- app_assoc. reflexivity. }
        * (* jump over else-branch *)
          simpl. intros [middle middleAEP]. intros. destruct_RiscvMachine middle.
          fwd. subst.
          destruct finalQ; fwd.
          2: { run1done. 1: finishcost. do 2 eexists.
               ssplit; [align_trace|reflexivity|reflexivity]. }
          eapply runsToStep'_of_step.
          { eapply run_Jal0; try safe_sidecond. solve_divisibleBy4. }
          simpl_MetricRiscvMachine_get_set.

          intros. destruct_RiscvMachine mid. fwd. run1done. 1: finishcost.
          intros. simpl. repeat rewrite <- app_assoc in *. rewr_leakage.
          repeat solve_word_eq word_ok || f_equal.

    - idtac "Case compile_stmt_correct/SIf/Else".
      (* execute branch instruction, which will jump over then-branch *)
      eapply runsToStep'_of_step.
      + eapply compile_bcond_by_inverting_correct with (l := l) (b := false);
          simpl_MetricRiscvMachine_get_set;
          try safe_sidecond.
      + simpl_MetricRiscvMachine_get_set.
        intros. fwd.
        destruct_RiscvMachine mid.
        eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
        * (* use IH for else-branch *)
          match goal with
          | H: iff1 allx ?RHS |- _ =>
            match RHS with
            | context[compile_stmt _ _ _ ?POS _ bElse] =>
              eapply IHexec with (g := {| allx := allx |}) (pos := POS)
            end
          end.
          all: after_IH.
          all: try safe_sidecond.
          all: try safe_sidecond.
          { simpl. subst. reflexivity. }
          { intros. rewrite associate_one_left, H13. rewrite fix_step.
            simpl_rev. simpl. cbn [leakage_events_rel leakage_events].
            repeat rewrite <- app_assoc. reflexivity. }
        * (* at end of else-branch, i.e. also at end of if-then-else, just prove that
             computed post satisfies required post *)
          simpl. intros [middle middleAEP]. intros.
          destruct_RiscvMachine middle. fwd. subst.
          destruct finalQ; fwd; run1done.
          1,3: finishcost.
          2: { eexists. eexists. ssplit; [align_trace|reflexivity|reflexivity]. }
          intros. simpl. repeat rewrite <- app_assoc in *. rewr_leakage.
          rewrite app_nil_r. reflexivity.          

    - idtac "Case compile_stmt_correct/SLoop".
      match goal with
      | H: context[FlatImpConstraints.uses_standard_arg_regs body1 -> _] |- _ => rename H into IH1
      end.
      match goal with
      | H: context[FlatImpConstraints.uses_standard_arg_regs body2 -> _] |- _ => rename H into IH2
      end.
      match goal with
      | H: context[FlatImpConstraints.uses_standard_arg_regs body1 /\
               FlatImpConstraints.uses_standard_arg_regs body2 -> _] |- _ => rename H into IH12
      end.
      eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
      + (* 1st application of IH: part 1 of loop body *)
        match goal with
        | H: iff1 allx ?RHS |- _ =>
          match RHS with
          | context[compile_stmt _ _ _ ?POS _ body1] =>
            eapply IH1 with (g := {| allx := allx |}) (pos := POS) (cont := fun _ => _)
          end
        end.
        all: after_IH.
        all: try safe_sidecond.
        all: try safe_sidecond.
        1: reflexivity.
        intros. rewr_picksp. rewrite fix_step. simpl. reflexivity.
      + simpl in *. simpl. intros [middle midAEP]. intros. destruct_RiscvMachine middle.
        match goal with
        | H: exists _ _ _ _ _ _, _ |- _ => destruct H as (qH' & kH' & tH' & mH' & lH' & mcH' & H)
        end.
        destruct qH'; fwd.
        2: { run1done. }
        destruct (eval_bcond lH' cond) as [condB|] eqn: E.
        2: exfalso;
           match goal with
           | H: context [_ <> None] |- _ => solve [eapply H; eauto]
           end.
        destruct condB.
        * (* true: iterate again *)
          eapply runsToStep'_of_step. {
            eapply compile_bcond_by_inverting_correct with (l := lH') (b := true);
              simpl_MetricRiscvMachine_get_set;
              try safe_sidecond.
          }
          simpl_MetricRiscvMachine_get_set.
          intros. destruct_RiscvMachine mid. fwd.
          eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
          { (* 2nd application of IH: part 2 of loop body *)
            match goal with
            | H: iff1 allx ?RHS |- _ =>
              match RHS with
              | context[compile_stmt _ _ _ ?POS _ body2] =>
                eapply IH2 with (g := {| allx := allx |}) (pos := POS) (cont := fun _ => _)
              end
            end.
            all: after_IH.
            1: eassumption.
            all: try safe_sidecond.
            all: try safe_sidecond.
            1: reflexivity.
            intros. repeat rewrite associate_one_left, app_assoc. rewr_picksp.
            rewrite fix_step. simpl. simpl_rev. rewr_leakage.
            rewrite List.skipn_app_r by reflexivity. cbn [FixEq.Let_In_pf_nd].
            simpl_rev. repeat rewrite <- app_assoc.
            cbn [leakage_events_rel leakage_events].
            repeat solve_word_eq word_ok || f_equal. reflexivity. }
          simpl in *. intros [middle midAEP0]. intros. destruct_RiscvMachine middle. fwd.
          destruct finalQ; fwd.
          2: { specialize H5 with (1 := H3p1). move H5 at bottom.
               inversion H5. subst. run1done. 1: finishcost. eexists. eexists.
               split; [align_trace|eauto]. }
         
          (* jump back to beginning of loop: *)
          eapply runsToStep'_of_step.
          { eapply run_Jal0; try safe_sidecond. solve_divisibleBy4. }
          simpl_MetricRiscvMachine_get_set.
          intros. destruct_RiscvMachine mid. fwd.
          eapply runsTo_trans. {
            (* 3rd application of IH: run the whole loop again *)
            eapply IH12 with (g := {| allx := allx |}) (pos := pos) (cont := fun _ => _).
            1: eassumption.
            all: after_IH.
            all: try safe_sidecond.
            all: try safe_sidecond.
            1: reflexivity.
            intros. rewrite associate_one_left, 2 app_assoc. rewr_picksp.
            rewrite fix_step. simpl. simpl_rev. rewr_leakage.
            rewrite List.skipn_app_r by reflexivity. cbn [FixEq.Let_In_pf_nd].
            simpl_rev. repeat rewrite <- app_assoc.
            cbn [leakage_events_rel leakage_events].
            eassert (rev finalKL ++ _ = _) as ->. 2: rewr_leakage.
            { repeat rewrite <- app_assoc. simpl. repeat solve_word_eq word_ok || f_equal. }
            rewrite List.skipn_app_r by reflexivity.
            repeat solve_word_eq word_ok || reflexivity || f_equal. }
          (* at end of loop, just prove that computed post satisfies required post *)
          simpl. intros [middle midAEP1]. intros. destruct_RiscvMachine middle. fwd.
          destruct finalQ; fwd.
          2: { run1done. 1: finishcost. do 2 eexists. split; [align_trace|eauto]. }
          run1done. 1: finishcost.
          intros. rewr_leakage. rewrite List.skipn_app_r by reflexivity.
          cbn [FixEq.Let_In_pf_nd].
          simpl_rev. repeat rewrite <- app_assoc.
            cbn [leakage_events_rel leakage_events].
            eassert (rev finalKL ++ _ = _) as ->. 2: rewr_leakage.
            { repeat rewrite <- app_assoc. simpl. repeat solve_word_eq word_ok || f_equal. }
            rewrite List.skipn_app_r by reflexivity.
            repeat solve_word_eq word_ok || reflexivity || f_equal.
            eassert (rev finalKL0 ++ _ = _) as ->. 2: rewr_leakage.
            { repeat rewrite <- app_assoc. simpl. repeat solve_word_eq word_ok || f_equal. }
            reflexivity.

        * (* false: done, jump over body2 *)
          eapply runsToStep'_of_step. {
            eapply compile_bcond_by_inverting_correct with (l := lH') (b := false);
              simpl_MetricRiscvMachine_get_set;
              try safe_sidecond.
          }
          simpl_MetricRiscvMachine_get_set.
          intros. destruct_RiscvMachine mid. fwd. run1done. 1: finishcost.
          rewr_leakage. rewrite List.skipn_app_r by reflexivity.
          cbn [FixEq.Let_In_pf_nd]. repeat solve_word_eq word_ok || f_equal.

    - idtac "Case compile_stmt_correct/SSeq".
      on hyp[(FlatImpConstraints.uses_standard_arg_regs s1); runsTo']
         do (fun H => rename H into IH1).
      on hyp[(FlatImpConstraints.uses_standard_arg_regs s2); runsTo']
         do (fun H => rename H into IH2).
      eapply runsTo_trans.
      + eapply IH1 with (g := {| allx := allx; |}) (pos := pos) (cont := fun _ => _).
        all: after_IH.
        all: try safe_sidecond.
        all: try safe_sidecond.
        1: reflexivity.
        intros. rewr_picksp. rewrite fix_step. reflexivity.
      + simpl. intros [middle midAEP]. intros. destruct_RiscvMachine middle. fwd.
        destruct finalQ; fwd.
        2: { specialize (H0 _ _ _ _ _ _ _ ltac:(eassumption)). move H0 at bottom.
             inversion H0. subst. run1done. }
        eapply runsTo_trans.
        * match goal with
          | H: iff1 allx ?RHS |- _ =>
            match RHS with
            | context[compile_stmt _ _ _ ?POS _ s2] =>
              eapply IH2 with (g := {| allx := allx |}) (pos := POS)
            end
          end.
          all: after_IH.
          1: eassumption.
          all: try safe_sidecond.
          all: try safe_sidecond.
          1: reflexivity.
          intros. rewrite app_assoc. rewr_picksp. rewrite fix_step. simpl.
          simpl_rev. rewr_leakage. rewrite List.skipn_app_r by reflexivity.
          reflexivity.
        * simpl. intros [middle midAEP0]. intros. destruct_RiscvMachine middle. fwd.
          destruct finalQ; fwd.
          2: { run1done. do 2 eexists. split; [align_trace|eauto]. }
          run1done. rewr_leakage. rewrite List.skipn_app_r by reflexivity.
          rewr_leakage. reflexivity.

    - idtac "Case compile_stmt_correct/SSkip".
      run1done.
    - idtac "Case compile_stmt_correct/quit".
      run1done. do 2 eexists. split; [align_trace|eauto].
    - idtac "Case compile_stmt_correct/forall".
      apply runsToStep_cps. apply step_A. intros.
      simpl. eapply runsTo_weaken. 1: eapply H0 with (g := {| allx := allx |}); eauto.
      all: simpl_MetricRiscvMachine_get_set; simpl. 1: solve[intuition eauto].
      intros. fwd. do 6 eexists. intuition eauto.
    - idtac "Case compile_stmt_correct/exists".
      apply runsToStep_cps. apply step_E. intros. exists x.
      simpl. eapply runsTo_weaken. 1: eapply IHexec with (g := {| allx := allx |}); eauto.
      all: simpl_MetricRiscvMachine_get_set; simpl. 1: solve[intuition eauto].
      intros. fwd. do 6 eexists. intuition eauto.      
  Qed. (* <-- takes a while *)


End Proofs.
