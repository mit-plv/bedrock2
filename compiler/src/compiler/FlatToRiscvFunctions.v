Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.rewr.
Require Import coqutil.Datatypes.PropSet.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import riscv.Spec.Decode.
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

Import MetricLogging.

Local Arguments Z.mul: simpl never.
Local Arguments Z.add: simpl never.
Local Arguments Z.of_nat: simpl never.
Local Arguments Z.modulo : simpl never.
Local Arguments Z.pow: simpl never.
Local Arguments Z.sub: simpl never.

Set Ltac Profiling.

Section Proofs.
  Context {iset: Decode.InstructionSet}.
  Context {fun_pos_env: map.map String.string Z}.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context {word_ok: word.ok word}.
  Context {locals: map.map Z word}.
  Context {mem: map.map word byte}.
  Context {env: map.map String.string (list Z * list Z * FlatImp.stmt Z)}.
  Context {M: Type -> Type}.
  Context {MM: Monads.Monad M}.
  Context {RVM: Machine.RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {ext_spec: Semantics.ExtSpec}.
  Context {word_riscv_ok: RiscvWordProperties.word.riscv_ok word}.
  Context {locals_ok: map.ok locals}.
  Context {mem_ok: map.ok mem}.
  Context {fun_pos_env_ok: map.ok fun_pos_env}.
  Context {env_ok: map.ok env}.
  Context {PR: MetricPrimitives.MetricPrimitives PRParams}.
  Context {BWM: bitwidth_iset width iset}.
  Context (compile_ext_call: fun_pos_env -> Z -> Z -> stmt Z -> list Instruction).

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

  Lemma functions_expose: forall (base: word) rel_positions impls f pos impl,
      map.get rel_positions f = Some pos ->
      map.get impls f = Some impl ->
      iff1 (functions base rel_positions impls)
           (functions base rel_positions (map.remove impls f) *
            program iset (word.add base (word.of_Z pos)) (compile_function rel_positions pos impl))%sep.
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

  Ltac run1done :=
    apply runsToDone;
    simpl_MetricRiscvMachine_get_set;
    simpl in *;
    repeat match goal with
           | |- exists _, _ => eexists
           end; ssplit; simpl_word_exprs word_ok;
    match goal with
    | |- _ => solve_word_eq word_ok
    | |- iff1 ?x ?x => reflexivity
    (* `exists stack_trash frame_trash, ...` from goodMachine *)
    | |- exists _ _, _ = _ /\ _ = _ /\ (_ * _)%sep _ =>
      eexists _, _; (split; [|split]); [..|wcancel_assumption]; blia
    | |- _ => solve [ rewrite ?of_list_list_union in *; map_solver locals_ok ]
    | |- _ => solve [ solve_valid_machine word_ok ]
    | |- _ => solve [ eauto  3 using regs_initialized_put, preserve_valid_FlatImp_var_domain_put ]
    | H:subset (footpr _) _
      |- subset (footpr _) _ => eapply rearrange_footpr_subset; [ exact H | solve [ wwcancel ] ]
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

  Ltac sidecondition_hook ::=
    try solve [ map_solver locals_ok
              | wcancel_assumption ].

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

  Lemma map_extends_remove: forall (m1 m2: env) k,
      map.extends m1 m2 ->
      map.extends m1 (map.remove m2 k).
  Proof. map_solver env_ok. Qed.

  Lemma map_get_Some_remove: forall (m: env) k1 k2 v,
      map.get (map.remove m k1) k2 = Some v ->
      map.get m k2 = Some v.
  Proof. map_solver env_ok. Qed.

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
       get_None_in_forall_keys
       sp_not_valid_FlatImp_var
       ra_not_valid_FlatImp_var
       map.not_in_of_list_zip_to_get_None
       sp_not_in_arg_regs
       ra_not_in_arg_regs
    : map_hints.

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
        valid_machine finalL).
  Proof.
    intros. get_run1_valid_for_free.
    inline_iff1.
    destruct_RiscvMachine initialL.
    simulate'.
    destruct b.
    - (* don't branch *)
      destruct cond; [destruct op | ];
        simpl in *; Simp.simp; repeat (simulate'; simpl_bools; simpl); try intuition congruence.
    - (* branch *)
      destruct cond; [destruct op | ];
        simpl in *; Simp.simp; repeat (simulate'; simpl_bools; simpl); try intuition congruence.
  Qed.

  Lemma compile_stmt_correct:
    (forall resvars extcall argvars,
        compiles_FlatToRiscv_correctly compile_ext_call
          compile_ext_call (SInteract resvars extcall argvars)) ->
    (forall s,
        compiles_FlatToRiscv_correctly compile_ext_call
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
      all: match goal with
           | H: fits_stack _ _ _ ?s |- _ =>
             let h := head_of_app s in is_constructor h;
             inversion H; clear H; subst
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
          clear compile_ext_call_correct; cycle -1.
        { unfold goodMachine, valid_FlatImp_var in *. simpl. ssplit; eauto. }
        all: eauto using exec.interact, fits_stack_interact.
      + simpl. intros finalL A. destruct_RiscvMachine finalL. unfold goodMachine in *. simpl in *.
        destruct_products. subst.
        do 4 eexists; ssplit; eauto.

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

      set (FL := framelength (argnames, retnames, body)) in *.
      (* We have enough stack space for this call: *)
      assert (FL <= Z.of_nat (List.length old_stackvals)) as enough_stack_space. {
        match goal with
        | H: fits_stack _ _ _ _ |- _ => apply fits_stack_nonneg in H
        end.
        subst FL. simpl in *.
        blia.
      }

      assert (bytes_per_word = 4 \/ bytes_per_word = 8) as B48. {
        unfold bytes_per_word. destruct width_cases as [E | E]; rewrite E; cbv; auto.
      }
      pose proof (stackalloc_words_nonneg body) as ScratchNonneg.
      assert (exists remaining_stack old_scratch old_modvarvals old_ra,
          old_stackvals = remaining_stack ++ old_scratch ++ old_modvarvals ++ [old_ra] /\
          List.length old_scratch = Z.to_nat (stackalloc_words iset body) /\
          List.length old_modvarvals = List.length
                                         (list_diff Z.eqb (modVars_as_list Z.eqb body) retnames))
        as TheSplit. {
        clear IHexec.
        subst FL. unfold framelength in *.
        rename old_stackvals into ToSplit.
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
      subst old_stackvals.

      (* note: left-to-right rewriting with all [length _ = length _] equations has to
         be terminating *)
      match goal with
      | H: _ |- _ => let N := fresh in pose proof H as N;
                     apply map.putmany_of_list_zip_sameLength in N;
                     symmetry in N
      end.
      match goal with
      | H: _ |- _ => let N := fresh in pose proof H as N;
                     apply map.getmany_of_list_length in N
      end.
      assert (Memory.bytes_per_word (bitwidth iset) = bytes_per_word) as BPW. {
        rewrite bitwidth_matches. reflexivity.
      }

      assert (exists arg_count, (arg_count <= 8)%nat /\
                argnames = List.firstn arg_count (reg_class.all reg_class.arg) /\
                args = List.firstn arg_count (reg_class.all reg_class.arg)) as AC. {
        exists (List.length argnames). ssplit. 2,3: congruence.
        replace argnames with
            (List.firstn (Datatypes.length argnames) (reg_class.all reg_class.arg)) by assumption.
        rewrite List.firstn_length.
        change (Datatypes.length (reg_class.all reg_class.arg)) with 8%nat.
        clear. blia.
      }
      destruct AC as (arg_count & AC & ? & ?). subst argnames args.

    assert (valid_register RegisterNames.ra) by (cbv; auto).
    assert (valid_register RegisterNames.sp) by (cbv; auto).

    (* jump to function *)
    eapply runsToStep. {
      eapply run_Jal; simpl; try solve [sidecondition]; cycle 2.
      - solve_divisibleBy4.
      - assumption.
    }

    simpl_MetricRiscvMachine_get_set.
    clear_old_sep_hyps.
    intros. fwd.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

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
    simpl in *.

    (* decrease sp *)
    eapply runsToStep. {
      eapply run_Addi with (rd := RegisterNames.sp) (rs := RegisterNames.sp);
        try solve [safe_sidecond | simpl; solve_divisibleBy4 ].
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

    (* save ra on stack *)
    eapply runsToStep. {
      eapply run_store_word with (rs1 := RegisterNames.sp) (rs2 := RegisterNames.ra)
                                 (addr := p_sp - !bytes_per_word);
        try solve [sidecondition | simpl; solve_divisibleBy4]; try solve_word_eq word_ok.
        simpl.
        rewrite map.get_put_diff by (clear; cbv; congruence).
        rewrite map.get_put_same. reflexivity.
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
      destruct_one_match; [eexists; reflexivity|].
      eauto.
    }
    eapply runsTo_trans. {
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
      let f := eval unfold current_fun in current_fun in
      let p := match f with
               | context[compile_stmt _ _ _ ?p _ body] => p
               end in
      eapply IHexec with (g := {|
        p_sp := word.sub p_sp !(Memory.bytes_per_word (bitwidth iset) * FL);
        allx := allx;
      |})
      (pos := p)
      (e_pos := e_pos)
      (e_impl := map.remove e_impl fname)
      (program_base := program_base);
      simpl_MetricRiscvMachine_get_set;
      simpl_g_get;
      rewrite ?@length_save_regs, ?@length_load_regs in *;
      ssplit;
      subst FL.
      all: try safe_sidecond.
      all: try safe_sidecond.
      { eapply map_extends_remove; eassumption. }
      { move e_impl_reduced_props at bottom.
        intros *. intro G.
        assert (map.get e_impl f = Some fun_impl) as G'. {
          eapply map_get_Some_remove; eassumption.
        }
        specialize e_impl_reduced_props with (1 := G'). fwd.
        repeat split; eauto.
      }
      { move H1 at bottom.
        unfold map.extends. intros *. intro G. rewrite !map.get_put_dec.
        destruct_one_match. {
          subst x.
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
        destruct_one_match. {
          subst x.
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
        clear -locals_ok G E E0 H14p0 H0 H1 H14p1.
        eapply map.putmany_of_list_zip_find_index in G. 2: eassumption.
        rewrite map.get_empty in G.
        destruct G as [G | G]. 2: discriminate G.
        destruct G as (n & Gk & Gv).
        unfold map.extends in H14p0. eapply H14p0.
        eauto using map.getmany_of_list_get.
      }
      { lazymatch goal with
        | H: map.putmany_of_list_zip _ _ map.empty = Some st0 |- _ =>
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
      {
        assert (forall x, In x (List.firstn arg_count (reg_class.all reg_class.arg)) ->
                          valid_FlatImp_var x) as F. {
          eapply Forall_forall.
          assumption.
        }
        revert F.
        repeat match goal with
               | H: ?T |- _ => lazymatch T with
                               | map.putmany_of_list_zip _ _ _ = Some _ => revert H
                               | map.ok _ => fail
                               | word.ok _ => fail
                               | _ = bytes_per_word => fail
                               | _ => clear H
                               end
               end.
        intros PM F.
        rewrite map.get_put_same. f_equal. simpl_addrs. solve_word_eq word_ok.
      }
      {
        eapply preserve_regs_initialized_after_put.
        eapply preserve_regs_initialized_after_put.
        assumption.
      }
      { exists remaining_stack, old_scratch. ssplit.
        - simpl_addrs. blia.
        - blia.
        - wcancel_assumption.
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
    match goal with
    | H: outcome _ _ _ _ |- _ => rename H into HO
    end.
    match goal with
    | H: forall _, _ |- _ =>
      specialize H with (1 := HO);
      move H at bottom;
      destruct H as (retvs & finalRegsH' & ? & ? & ?)
    end.

    (* load back the modified vars *)
    eapply runsTo_trans. {
      eapply load_regs_correct with (values := newvalues);
        simpl; cycle 1.
      - eassumption.
      - repeat match goal with
               | H: map.getmany_of_list _ _ = Some _ |- _ =>
                 unique eapply @map.getmany_of_list_length in copy of H
               end.
        symmetry.
        eassumption.
      - eassumption.
      - etransitivity. 1: eassumption. subst current_fun. wwcancel.
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
    eapply runsToStep. {
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
        intros PM G G' PM' PM'' F.
        eapply map.putmany_of_list_zip_get_oldval. 3: exact G'. 1: eassumption.
        intro C.
        eapply In_list_diff_weaken in C.
        specialize (F _ C).
        unfold valid_FlatImp_var, RegisterNames.sp in F. blia.
      - reflexivity.
      - eassumption.
      - etransitivity. 1: eassumption. subst current_fun. wwcancel.
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
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    assert (exists ret_count, (ret_count <= 8)%nat /\
                              retnames = List.firstn ret_count (reg_class.all reg_class.arg) /\
                              binds = List.firstn ret_count (reg_class.all reg_class.arg)) as RC. {
      apply_in_hyps @map.putmany_of_list_zip_sameLength.
      apply_in_hyps @map.getmany_of_list_length.
      exists (List.length retnames). ssplit. 2,3: congruence.
      replace retnames with
          (List.firstn (Datatypes.length retnames) (reg_class.all reg_class.arg)) by assumption.
      rewrite List.firstn_length.
      change (Datatypes.length (reg_class.all reg_class.arg)) with 8%nat.
      clear. blia.
    }
    destruct RC as (ret_count & RC & ? & ?). subst retnames binds.

    (* increase sp *)
    eapply runsToStep. {
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
        intros V F1 F2 G PM.
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
    eapply runsToStep. {
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
    do 4 eexists.
    match goal with
    | |- _ /\ _ /\ ?ODGoal /\ _ => assert ODGoal as OD
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
          unfold valid_FlatImp_var, RegisterNames.ra in *.
          blia.
        }
        rewrite D. rewrite <- E0.

        (* 2) prove that RHS is in newvalues: *)
        rewrite map.get_put_diff.
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
        rewrite map.get_put_diff.
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
          unfold valid_FlatImp_var, RegisterNames.ra in *.
          blia.
        }
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
    + eassumption.
    + solve_word_eq word_ok.
    + exact OD.
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
                             | map.extends initialL_regs lH => revert H
                             | map.only_differ _ _ _ => revert H
                             | map.getmany_of_list _ _ = Some _ => revert H
                             | map.extends lL lFH' => revert H
                             | map.putmany_of_list_zip _ newvalues lL = Some _ => revert H
                             | middle_regs0_ra_sp = _ => revert H
                             | @map.get _ _ locals _ _ = _ => revert H
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
    rewrite (remove_comm (map.put (map.putmany m0 ksvs)
                                  RegisterNames.ra (program_base + !pos + !4))) in OD1.
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
    rewrite (remove_comm (map.put initialL_regs RegisterNames.ra (program_base + !pos + !4)))
      in OD0.
    rewrite remove_put_same in OD0.
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

    + match goal with
      | H: map.putmany_of_list_zip _ _ _ = Some finalRegsH',
        L: forall _ _, map.get l _ = Some _ -> valid_FlatImp_var _,
        V: Forall valid_FlatImp_var (List.firstn ret_count (reg_class.all reg_class.arg)) |- _
        => rename H into P, V into N, L into G; clear -P N G locals_ok
      end.
      intros.
      pose proof (map.putmany_of_list_zip_find_index _ _ _ _ _ _ P H) as Q.
      destruct Q as [ [ n [A B] ] | C ].
      * eapply Forall_forall. 1: exact N. eapply nth_error_In. exact A.
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
      exists (stack_trash ++ frame_trash ++ newvalues ++ [new_ra]),
             unused_part_of_caller_frame.
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

    - idtac "Case compile_stmt_correct/SLoad".
      progress unfold Memory.load, Memory.load_Z in *. fwd.
      subst_load_bytes_for_eq.
      assert (x <> RegisterNames.sp). {
        unfold valid_FlatImp_var, RegisterNames.sp in *.
        blia.
      }
      inline_iff1.
      run1det. clear H0. (* <-- TODO this should not be needed *) run1done.

    - idtac "Case compile_stmt_correct/SStore".
      inline_iff1.
      simpl_MetricRiscvMachine_get_set.
      unfold Memory.store, Memory.store_Z in *.
      change Memory.store_bytes with (Platform.Memory.store_bytes(word:=word)) in *.
      match goal with
      | H: Platform.Memory.store_bytes _ _ _ _ = _ |- _ =>
        unshelve epose proof (store_bytes_frame H _) as P; cycle 2
      end.
      1: ecancel_assumption.
      destruct P as (finalML & P1 & P2).
      match goal with
      | H: _ = Some m' |- _ => move H at bottom; rename H into A
      end.
      unfold Platform.Memory.store_bytes, Memory.store_Z, Memory.store_bytes in A. fwd.
      subst_load_bytes_for_eq.
      run1det. run1done.
      eapply preserve_subset_of_xAddrs. 1: assumption.
      ecancel_assumption.

    - idtac "Case compile_stmt_correct/SInlinetable".
      inline_iff1.
      run1det.
      assert (map.get (map.put initialL_regs x (program_base + !pos + !4)) i = Some index). {
        rewrite map.get_put_diff by congruence. unfold map.extends in *. eauto.
      }
      run1det.
      assert (Memory.load sz initialL_mem (program_base + !pos + !4 + index + !0) = Some v). {
        rewrite add_0_r.
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
      eapply runsToStep. {
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

      eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
      + eapply IHexec with (g := {| p_sp := p_sp;
                                    rem_framewords := Z.of_nat (List.length remaining_frame); |})
                           (program_base := program_base)
                           (e_impl := e_impl)
                           (pos := (pos + 4)%Z)
                           (a := p_sp + !bytes_per_word * !#(Datatypes.length remaining_frame))
                           (mStack := mStack)
                           (mCombined := map.putmany mSmall mStack);
          simpl_MetricRiscvMachine_get_set;
          simpl_g_get;
          rewrite ?@length_save_regs, ?@length_load_regs in *;
          simpl_word_exprs word_ok;
          ssplit;
          cycle -5.
        { reflexivity. }
        { eassumption. }
        { exists stack_trash, remaining_frame. ssplit. 1,2: reflexivity.
          wcancel_assumption. }
        { reflexivity. }
        { assumption. }
        { match goal with
          | |- ?G => let t := type of Ab in replace G with t; [exact Ab|f_equal]
          end.
          rewrite @length_flat_map with (n := Z.to_nat bytes_per_word).
          - simpl_addrs. rewrite !Z2Nat.id by blia. rewrite <- BPW. rewrite <- Z_div_exact_2; blia.
          - clear. intros. rewrite HList.tuple.length_to_list. reflexivity.
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
        { etransitivity. 1: eassumption. wwcancel. }
        { match goal with
          | |- map.extends (map.put _ ?k ?v1) (map.put _ ?k ?v2) => replace v1 with v2
          end.
          - apply map.put_extends. assumption.
          - simpl_addrs. solve_word_eq word_ok. }
        { solve [eauto 3 using regs_initialized_put, preserve_valid_FlatImp_var_domain_put]. }
        { map_solver locals_ok. }
        { solve [eauto 3 using regs_initialized_put, preserve_valid_FlatImp_var_domain_put]. }
      + intros. destruct_RiscvMachine middle. fwd.
        clear B48. rewrite BPW in *. clear BPW. simpl_addrs. run1done.
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
          map_solver locals_ok.
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
      get_runsTo_valid_for_free.
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

    - idtac "Case compile_stmt_correct/SOp".
      assert (x <> RegisterNames.sp). {
        unfold valid_FlatImp_var, RegisterNames.sp in *.
        blia.
      }
      inline_iff1.
      match goal with
      | o: Syntax.bopname.bopname |- _ => destruct o
      end;
      simpl in *; run1det;
      rewrite ?word.sru_ignores_hibits,
              ?word.slu_ignores_hibits,
              ?word.srs_ignores_hibits,
              ?word.mulhuu_simpl,
              ?word.divu0_simpl,
              ?word.modu0_simpl in *.
      all: try solve [run1done].
      (* bopname.eq requires two instructions *)
      run1det. run1done.
      rewrite reduce_eq_to_sub_and_lt.
      rewrite map.put_put_same.
      map_solver locals_ok.

    - idtac "Case compile_stmt_correct/SSet".
      assert (x <> RegisterNames.sp). {
        unfold valid_FlatImp_var, RegisterNames.sp in *.
        blia.
      }
      inline_iff1.
      run1det. run1done.

    - idtac "Case compile_stmt_correct/SIf/Then".
      (* execute branch instruction, which will not jump *)
      eapply runsToStep.
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
        * (* jump over else-branch *)
          simpl. intros. destruct_RiscvMachine middle. fwd. subst.
          eapply runsToStep.
          { eapply run_Jal0; try safe_sidecond. solve_divisibleBy4. }
          simpl_MetricRiscvMachine_get_set.
          intros. destruct_RiscvMachine mid. fwd. run1done.

    - idtac "Case compile_stmt_correct/SIf/Else".
      (* execute branch instruction, which will jump over then-branch *)
      eapply runsToStep.
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
        * (* at end of else-branch, i.e. also at end of if-then-else, just prove that
             computed post satisfies required post *)
          simpl. intros. destruct_RiscvMachine middle. fwd. subst. run1done.

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
            eapply IH1 with (g := {| allx := allx |}) (pos := POS)
          end
        end.
        all: after_IH.
        all: try safe_sidecond.
        all: try safe_sidecond.
      + simpl in *. simpl. intros. destruct_RiscvMachine middle.
        match goal with
        | H: exists _ _ _ _, _ |- _ => destruct H as [ tH' [ mH' [ lH' [ mcH' H ] ] ] ]
        end.
        fwd.
        destruct (eval_bcond lH' cond) as [condB|] eqn: E.
        2: exfalso;
           match goal with
           | H: context [_ <> None] |- _ => solve [eapply H; eauto]
           end.
        destruct condB.
        * (* true: iterate again *)
          eapply runsToStep. {
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
                eapply IH2 with (g := {| allx := allx |}) (pos := POS)
              end
            end.
            all: after_IH.
            1: eassumption.
            all: try safe_sidecond.
            all: try safe_sidecond. }
          simpl in *. intros. destruct_RiscvMachine middle. fwd.
          (* jump back to beginning of loop: *)
          eapply runsToStep.
          { eapply run_Jal0; try safe_sidecond. solve_divisibleBy4. }
          simpl_MetricRiscvMachine_get_set.
          intros. destruct_RiscvMachine mid. fwd.
          eapply runsTo_trans. {
            (* 3rd application of IH: run the whole loop again *)
            eapply IH12 with (g := {| allx := allx |}) (pos := pos).
            1: eassumption.
            all: after_IH.
            all: try safe_sidecond.
            all: try safe_sidecond.
            1: constructor; eassumption.
            all: try safe_sidecond.
            all: try congruence.
          }
          (* at end of loop, just prove that computed post satisfies required post *)
          simpl. intros. destruct_RiscvMachine middle. fwd.
          run1done.
        * (* false: done, jump over body2 *)
          eapply runsToStep. {
            eapply compile_bcond_by_inverting_correct with (l := lH') (b := false);
              simpl_MetricRiscvMachine_get_set;
              try safe_sidecond.
          }
          simpl_MetricRiscvMachine_get_set.
          intros. destruct_RiscvMachine mid. fwd.
          run1done.

    - idtac "Case compile_stmt_correct/SSeq".
      on hyp[(FlatImpConstraints.uses_standard_arg_regs s1); runsTo]
         do (fun H => rename H into IH1).
      on hyp[(FlatImpConstraints.uses_standard_arg_regs s2); runsTo]
         do (fun H => rename H into IH2).
      eapply runsTo_trans.
      + eapply IH1 with (g := {| allx := allx; |}) (pos := pos).
        all: after_IH.
        all: try safe_sidecond.
        all: try safe_sidecond.
      + simpl. intros. destruct_RiscvMachine middle. fwd.
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
        * simpl. intros. destruct_RiscvMachine middle. fwd. run1done.

    - idtac "Case compile_stmt_correct/SSkip".
      run1done.
  Qed. (* <-- takes a while *)

End Proofs.

Show Ltac Profile.
