Require Import Coq.Logic.FunctionalExtensionality.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.MapEauto.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.fwd.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Primitives.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.util.Common.
Require Import compiler.SeparationLogic.
Require Export coqutil.Word.SimplWordExpr.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.DivisibleBy4.
Require Import compiler.MetricsToRiscv.
Require Import compiler.FlatImp.
Require Import compiler.RunInstruction.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvFunctions.
Require Import bedrock2.MetricLogging.
Require Import compiler.FitsStack.
Require Import compiler.Registers.
Require Import riscv.Utility.InstructionCoercions.

Local Arguments Z.mul: simpl never.
Local Arguments Z.add: simpl never.
Local Arguments Z.of_nat: simpl never.
Local Arguments Z.modulo : simpl never.
Local Arguments Z.pow: simpl never.
Local Arguments Z.sub: simpl never.

Section WithWordAndMem.
  Context {width: Z} {word: word.word width} {mem: map.map word byte}.

  (* bedrock2.ptsto_bytes.ptsto_bytes takes an n-tuple of bytes, whereas this one takes a list of bytes *)
  Definition ptsto_bytes: word -> list byte -> mem -> Prop := array ptsto (word.of_Z 1).

  Definition mem_available(start pastend: word) : mem -> Prop :=
    ex1 (fun anybytes: list byte =>
      emp (Z.of_nat (List.length anybytes) = word.unsigned (word.sub pastend start)) *
      (ptsto_bytes start anybytes))%sep.
End WithWordAndMem.

Section LowerPipeline.
  Context {iset: Decode.InstructionSet}.
  Context {width: Z} {BW: Bitwidth width} {BWM: bitwidth_iset width iset}.
  Context {pos_map: map.map String.string Z}.
  Context {pos_map_ok: map.ok pos_map}.
  Context {env: map.map String.string (list Z * list Z * FlatImp.stmt Z)}.
  Context {env_ok: map.ok env}.
  Context (compile_ext_call: pos_map -> Z -> Z -> stmt Z -> list Instruction).

  Local Open Scope ilist_scope.

  (* Note: we could also track code size from the source program all the way to the target
     program, and a lot of infrastructure is already there, will do once/if we want to get
     a total compiler.
     Returns the fun_pos_env so that users know where to jump to call the compiled functions. *)
  Definition riscvPhase (prog: env): result (list Instruction * pos_map * Z) :=
    stack_words_needed <- stack_usage prog;;
    let positions := FlatToRiscvDef.build_fun_pos_env iset compile_ext_call prog in
    let '(i, _) := FlatToRiscvDef.compile_funs iset compile_ext_call positions prog in
    Success (i, positions, stack_words_needed).

  Lemma get_build_fun_pos_env: forall e f argnames retnames body,
      map.get e f = Some (argnames, retnames, body) ->
      exists pos, map.get (FlatToRiscvDef.build_fun_pos_env iset compile_ext_call e) f =
                  Some pos.
  Proof.
    intros *.
    unfold FlatToRiscvDef.build_fun_pos_env, FlatToRiscvDef.compile_funs.
    eapply map.fold_spec.
    - intros. rewrite map.get_empty in H. congruence.
    - intros. destruct r as [insts en]. simpl.
      rewrite map.get_put_dec in H1.
      destruct v as ((argnames' & retnames') & body').
      unfold snd.
      rewrite map.get_put_dec.
      destruct_one_match; fwd; eauto.
  Qed.

  Lemma get_build_fun_pos_env_None: forall e f,
      map.get e f = None ->
      map.get (build_fun_pos_env iset compile_ext_call e) f = None.
  Proof.
    intros *.
    unfold FlatToRiscvDef.build_fun_pos_env, FlatToRiscvDef.compile_funs.
    eapply map.fold_spec.
    - intros. simpl. apply map.get_empty.
    - intros. destruct r as [insts en]. simpl.
      rewrite map.get_put_dec in H1.
      destruct v as ((argnames' & retnames') & body').
      unfold snd.
      rewrite map.get_put_dec.
      destruct_one_match; fwd; eauto.
      discriminate.
  Qed.

  Lemma fun_pos_div4: forall functions f p,
      map.get (FlatToRiscvDef.build_fun_pos_env iset compile_ext_call functions) f =
      Some p ->
      p mod 4 = 0.
  Proof.
    unfold FlatToRiscvDef.build_fun_pos_env, FlatToRiscvDef.compile_funs.
    intros *.
    eapply map.fold_spec; intros; unfold snd in *.
    - rewrite map.get_empty in H. discriminate.
    - intros. destruct r as [insts en].
      unfold FlatToRiscvDef.add_compiled_function in *.
      destruct v as ((argnames & retnames) & body).
      rewrite map.get_put_dec in H1.
      destruct_one_match_hyp.
      + fwd. rewrite Z.mul_comm. apply Z_mod_mult.
      + auto.
  Qed.

  Context {word: word.word width} {word_ok: word.ok word}.
  Context {locals: map.map Z word} {locals_ok: map.ok locals}.
  Context {mem: map.map word byte} {mem_ok: map.ok mem}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Lemma get_compile_funs_pos: forall e finfo0,
      let '(insts, finfo) := FlatToRiscvDef.compile_funs iset compile_ext_call finfo0 e in
      forall f impl,
        map.get e f = Some impl ->
        exists pos2,
          let '(argnames, retnames, body) := impl in
          map.get finfo f = Some pos2 /\
          pos2 mod 4 = 0.
  Proof using pos_map_ok env_ok.
    intros e finfo0.
    unfold FlatToRiscvDef.compile_funs.
    eapply map.fold_spec.
    - intros. rewrite map.get_empty in H. congruence.
    - intros. destruct r as [insts en]. simpl. destruct v as ((argnames & retnames) & body).
      intros.
      rewrite map.get_put_dec in H1.
      destruct impl as ((argnames' & retnames') & body').
      rewrite map.get_put_dec.
      destruct_one_match; fwd.
      + eexists. split; [reflexivity|].
        solve_divisibleBy4.
      + specialize H0 with (1 := H1). exact H0.
  Qed.

  Lemma program_mod_4_0: forall (a: word) instrs R m,
      instrs <> [] ->
      (program iset a instrs * R)%sep m ->
      word.unsigned a mod 4 = 0.
  Proof using .
    intros.
    destruct instrs as [|instr instrs]. 1: congruence.
    simpl in *.
    unfold sep, ptsto_instr, sep, emp in *.
    fwd.
    assumption.
  Qed.

  Lemma compile_funs_nonnil: forall e positions positions' f impl instrs,
      map.get e f = Some impl ->
      FlatToRiscvDef.compile_funs iset compile_ext_call positions e = (instrs, positions') ->
      instrs <> [].
  Proof using env_ok.
    intros e positions.
    unfold FlatToRiscvDef.compile_funs.
    eapply map.fold_spec; intros.
    - rewrite map.get_empty in H.
      discriminate.
    - rewrite map.get_put_dec in H1.
      destr (k =? f)%string.
      + subst.
        unfold FlatToRiscvDef.add_compiled_function in H2. fwd.
        intro C. destruct l; discriminate.
      + specialize H0 with (1 := H1).
        destruct r as [ instrs'' positions'' ].
        specialize H0 with (1 := eq_refl).
        intro C. subst instrs.
        unfold FlatToRiscvDef.add_compiled_function in H2. fwd.
        unfold FlatToRiscvDef.compile_function in *.
        destruct instrs''; discriminate.
  Qed.

  Ltac step :=
    match goal with
    | |- _ => reflexivity
    | |- _ => rewrite !List.app_length
    | |- _ => solve [eauto]
    | |- S _ = S _ => f_equal
    | |- (_ + _)%nat = (_ + _)%nat => f_equal
    end.

  Hypothesis compile_ext_call_length_ignores_positions: forall stackoffset posmap1 posmap2 c pos1 pos2,
      List.length (compile_ext_call posmap1 pos1 stackoffset c) =
      List.length (compile_ext_call posmap2 pos2 stackoffset c).

  Lemma compile_stmt_length_ignores_positions: forall posmap1 posmap2 c stackoffset pos1 pos2,
      List.length (FlatToRiscvDef.compile_stmt iset compile_ext_call posmap1 pos1 stackoffset c) =
      List.length (FlatToRiscvDef.compile_stmt iset compile_ext_call posmap2 pos2 stackoffset c).
  Proof using compile_ext_call_length_ignores_positions.
    induction c; intros; repeat (step || simpl).
  Qed.

  Lemma compile_function_length_ignores_positions: forall posmap1 posmap2 pos1 pos2 impl,
      List.length (FlatToRiscvDef.compile_function iset compile_ext_call posmap1 pos1 impl) =
      List.length (FlatToRiscvDef.compile_function iset compile_ext_call posmap2 pos2 impl).
  Proof using compile_ext_call_length_ignores_positions.
    intros. destruct impl as [ [args rets] body ]. repeat (step || simpl).
    apply compile_stmt_length_ignores_positions.
  Qed.

  Lemma build_fun_pos_env_ignores_posmap_aux: forall posmap1 posmap2 e i1 m1 i2 m2,
      map.fold (FlatToRiscvDef.add_compiled_function iset compile_ext_call posmap1)
               ([], map.empty) e = (i1, m1) ->
      map.fold (FlatToRiscvDef.add_compiled_function iset compile_ext_call posmap2)
               ([], map.empty) e = (i2, m2) ->
      m1 = m2 /\ List.length i1 = List.length i2.
  Proof using env_ok compile_ext_call_length_ignores_positions.
    intros until e.
    eapply map.fold_parametricity with (fa := (FlatToRiscvDef.add_compiled_function _ _ posmap1))
                                       (fb := (FlatToRiscvDef.add_compiled_function _ _ posmap2));
      intros.
    - destruct a as [insts1 map1]. destruct b as [insts2 map2].
      unfold FlatToRiscvDef.add_compiled_function in *.
      inversion H0. inversion H1. subst. clear H0 H1.
      specialize H with (1 := eq_refl) (2 := eq_refl). destruct H.
      rewrite ?H0. subst.
      destruct v as ((argnames & retnames) & body). fwd.
      split. 1: congruence.
      repeat step.
      apply compile_function_length_ignores_positions.
    - fwd. auto.
  Qed.

  Lemma build_fun_pos_env_ignores_posmap: forall posmap1 posmap2 e,
      snd (map.fold (FlatToRiscvDef.add_compiled_function iset compile_ext_call posmap1)
                    ([], map.empty) e) =
      snd (map.fold (FlatToRiscvDef.add_compiled_function iset compile_ext_call posmap2)
                    ([], map.empty) e).
  Proof using env_ok compile_ext_call_length_ignores_positions.
    intros.
    destr (map.fold (FlatToRiscvDef.add_compiled_function iset compile_ext_call posmap1)
                    ([], map.empty) e).
    destr (map.fold (FlatToRiscvDef.add_compiled_function iset compile_ext_call posmap2)
                    ([], map.empty) e).
    simpl.
    edestruct build_fun_pos_env_ignores_posmap_aux.
    - exact E.
    - exact E0.
    - assumption.
  Qed.

  (* This lemma should relate two map.folds which fold two different f over the same env e:
     1) FlatToRiscvDef.compile_funs, which folds FlatToRiscvDef.add_compiled_function.
        Note that this one is called twice: First in build_fun_pos_env, and then in
        compile_funs, and we rely on the order being the same both times.
     2) functions, which folds sep
     Note that 1) is not commutative (the iteration order determines in which order code
     is layed out in memory), while 2) should be commutative because the "function"
     separation logic predicate it seps onto the separation logic formula is the same
     if we pass it the same function position map. *)
  Lemma functions_to_program: forall (functions_start: word) e instrs pos_map stack_size,
      riscvPhase e = Success (instrs, pos_map, stack_size) ->
      iff1 (program iset functions_start instrs)
           (FlatToRiscvCommon.functions compile_ext_call functions_start
                                        (FlatToRiscvDef.build_fun_pos_env iset compile_ext_call e) e).
  Proof using word_ok mem_ok pos_map_ok env_ok compile_ext_call_length_ignores_positions.
    unfold riscvPhase.
    intros.
    fwd.
    unfold FlatToRiscvDef.compile_funs, functions in *.
    remember (FlatToRiscvDef.build_fun_pos_env iset compile_ext_call e) as positions.
    (* choose your IH carefully! *)
    lazymatch goal with
    | |- ?G => enough ((forall f, map.get r f <> None <-> map.get e f <> None) /\
             ((forall f pos, map.get r f = Some pos -> map.get positions f = Some pos) -> G))
    end.
    1: {
      fwd. apply Hp1; clear Hp1.
      intros. rewrite <- H. f_equal.
      subst.
      apply (f_equal snd) in E0. simpl in E0. rewrite <- E0.
      transitivity (snd (map.fold (FlatToRiscvDef.add_compiled_function iset compile_ext_call map.empty) ([], map.empty) e)).
      - unfold FlatToRiscvDef.build_fun_pos_env, snd. reflexivity.
      - apply build_fun_pos_env_ignores_posmap.
    }
    revert E0.
    revert instrs r. clear E stack_size.
    eapply (map.fold_spec (R:=(list Instruction * _))) with (m:=e); repeat (cbn || fwd || intros).
    { rewrite map.fold_empty. intuition try reflexivity.
      - eapply H. eapply map.get_empty.
      - eapply H. eapply map.get_empty.
    }
    rewrite map.fold_put; trivial.
    2: { intros.
      eapply functional_extensionality_dep; intros x.
      eapply PropExtensionality.propositional_extensionality; revert x.
      match goal with |- forall x, ?P x <-> ?Q x => change (iff1 P Q) end.
      cancel. }
    case r as (instrs'&r').
    specialize H0 with (1 := eq_refl).
    unfold FlatToRiscvDef.add_compiled_function in E0.
    destruct v as ((argnames & retnames) & body).
    fwd.
    unfold program in *.
    wseplog_pre.
    split. {
      intros. rewrite ?map.get_put_dec.
      destr (k =? f)%string. 2: eauto. intuition discriminate.
    }
    intros.
    rewrite H0p1. 2: {
      intros.
      eapply H0.
      rewrite map.get_put_dec.
      destr (k =? f)%string. 2: assumption.
      subst. exfalso.
      specialize (H0p0 f). unfold not in H0p0. rewrite H1 in H0p0. rewrite H in H0p0.
      intuition congruence.
    }
    cancel.
    unfold function.
    specialize (H0 k).
    rewrite map.get_put_same in H0.
    specialize H0 with (1 := eq_refl).
    rewrite H0.
    unfold program.
    cancel_seps_at_indices 0%nat 0%nat. 2: reflexivity.
    f_equal.
    f_equal.
    solve_word_eq word_ok.
  Qed.

  Open Scope ilist_scope.

  Context {M: Type -> Type}.
  Context {MM: Monads.Monad M}.
  Context {RVM: Machine.RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {PR: MetricPrimitives.MetricPrimitives PRParams}.
  Context {ext_spec: Semantics.ExtSpec}.
  Context {word_riscv_ok: RiscvWordProperties.word.riscv_ok word}.

  Definition machine_ok{BWM: bitwidth_iset width iset}
             (p_functions: word)(stack_start stack_pastend: word)
             (finstrs: list Instruction)
             (mH: mem)(Rdata Rexec: mem -> Prop)(mach: MetricRiscvMachine): Prop :=
      (program iset p_functions finstrs *
       mem_available stack_start stack_pastend *
       Rdata * Rexec * eq mH
      )%sep mach.(getMem) /\
      subset (footpr (program iset p_functions finstrs * Rexec)%sep)
             (of_list (getXAddrs mach)) /\
      word.unsigned (mach.(getPc)) mod 4 = 0 /\
      mach.(getNextPc) = word.add mach.(getPc) (word.of_Z 4) /\
      regs_initialized mach.(getRegs) /\
      map.get mach.(getRegs) RegisterNames.sp = Some stack_pastend /\
      (* configured by PrimitivesParams, can contain invariants needed for external calls *)
      valid_machine mach.

  (* Note: since the length of (reg_class.all reg_class.arg) is 8, this definition
     forces vals to be of length at most 8 *)
  Definition arg_regs_contain(regs: locals)(vals: list word): Prop :=
    map.getmany_of_list regs
      (List.firstn (List.length vals) (reg_class.all reg_class.arg))
    = Some vals.

  Hypothesis compile_ext_call_correct: forall resvars extcall argvars,
      compiles_FlatToRiscv_correctly compile_ext_call compile_ext_call
                                     (FlatImp.SInteract resvars extcall argvars).

  Definition riscv_call(p: list Instruction * pos_map * Z)
             (f_name: string)(t: Semantics.trace)(mH: mem)(argvals: list word)
             (post: Semantics.trace -> mem -> list word -> Prop): Prop :=
    let '(instrs, finfo, req_stack_size) := p in
    exists f_rel_pos,
      map.get finfo f_name = Some f_rel_pos /\
      forall p_funcs stack_start stack_pastend ret_addr Rdata Rexec (initial: MetricRiscvMachine),
        map.get initial.(getRegs) RegisterNames.ra = Some ret_addr ->
        initial.(getLog) = t ->
        word.unsigned ret_addr mod 4 = 0 ->
        arg_regs_contain initial.(getRegs) argvals ->
        req_stack_size <= word.unsigned (word.sub stack_pastend stack_start) / bytes_per_word ->
        word.unsigned (word.sub stack_pastend stack_start) mod bytes_per_word = 0 ->
        initial.(getPc) = word.add p_funcs (word.of_Z f_rel_pos) ->
        machine_ok p_funcs stack_start stack_pastend instrs mH Rdata Rexec initial ->
        runsTo initial (fun final => exists mH' retvals,
          arg_regs_contain final.(getRegs) retvals /\
          post final.(getLog) mH' retvals /\
          map.only_differ initial.(getRegs) reg_class.caller_saved final.(getRegs) /\
          final.(getPc) = ret_addr /\
          machine_ok p_funcs stack_start stack_pastend instrs mH' Rdata Rexec final).

  Definition same_finfo_and_length:
    list Instruction * pos_map -> list Instruction * pos_map -> Prop :=
    fun '(insts1, finfo1) '(insts2, finfo2) =>
      List.length insts1 = List.length insts2 /\ finfo1 = finfo2.

  Lemma compile_funs_finfo_ignores_finfo_aux(finfo1 finfo2: pos_map): forall e,
      (fun e l r => same_finfo_and_length l r) e
      (compile_funs iset compile_ext_call finfo1 e)
      (compile_funs iset compile_ext_call finfo2 e).
  Proof.
    eapply map.fold_two_spec; unfold same_finfo_and_length.
    1: split; reflexivity.
    intros. destruct r1 as [insts1 finfo1']. destruct r2 as [insts2 finfo2'].
    destruct v as ((argnames & retnames) & body).
    unfold add_compiled_function.
    fwd. rewrite !List.app_length. rewrite H0p0.
    erewrite compile_function_length_ignores_positions.
    split; try reflexivity.
  Qed.

  Lemma compile_funs_snd_ignores_finfo: forall finfo1 finfo2 e,
      snd (compile_funs iset compile_ext_call finfo1 e) =
      snd (compile_funs iset compile_ext_call finfo2 e).
  Proof.
    intros. pose proof (compile_funs_finfo_ignores_finfo_aux finfo1 finfo2 e) as P.
    unfold same_finfo_and_length in P.
    unfold snd.
    destruct_one_match.
    destruct_one_match.
    apply P.
  Qed.

  Lemma compile_funs_finfo_idemp: forall p1 insts finfo,
      compile_funs iset compile_ext_call (build_fun_pos_env iset compile_ext_call p1) p1 =
      (insts, finfo) ->
      finfo = build_fun_pos_env iset compile_ext_call p1.
  Proof.
    intros. apply (f_equal snd) in H. cbn in H. unfold build_fun_pos_env. subst finfo.
    apply compile_funs_snd_ignores_finfo.
  Qed.

  Lemma build_fun_pos_env_good_e_impl: forall e,
      map.forall_values valid_FlatImp_fun e ->
      good_e_impl e (build_fun_pos_env iset compile_ext_call e).
  Proof.
    unfold good_e_impl.
    intros *. intros H * G.
    split.
    - eapply H. eassumption.
    - unfold FlatToRiscvDef.build_fun_pos_env, FlatToRiscvDef.build_fun_pos_env.
      pose proof (get_compile_funs_pos e map.empty) as P.
      destruct (compile_funs iset _ map.empty e) as [ insts posmap ] eqn: F.
      destruct fun_impl as ((argnames' & retnames') & body').
      specialize P with (1 := G). unfold snd. cbv beta iota zeta in *.
      exact P.
  Qed.

  Lemma shrink_good_e_impl: forall e1 e2 finfo,
      good_e_impl e1 finfo ->
      map.extends e1 e2 ->
      good_e_impl e2 finfo.
  Proof.
    unfold good_e_impl, map.extends.
    intros. destruct fun_impl as ((argnames & retnames) & body).
    specialize H0 with (1 := H1).
    specialize H with (1 := H0).
    cbv beta iota zeta in H.
    exact H.
  Qed.

  Lemma flat_to_riscv_correct: forall p1 p2,
      map.forall_values FlatToRiscvDef.valid_FlatImp_fun p1 ->
      riscvPhase p1 = Success p2 ->
      forall fname t m argvals post,
      (exists argnames retnames fbody l,
          map.get p1 fname = Some (argnames, retnames, fbody) /\
          map.of_list_zip argnames argvals = Some l /\
          forall mc, FlatImp.exec p1 fbody t m l mc (fun t' m' l' mc' =>
                         exists retvals, map.getmany_of_list l' retnames = Some retvals /\
                                         post t' m' retvals)) ->
      riscv_call p2 fname t m argvals post.
  Proof.
    unfold riscv_call.
    intros. destruct p2 as ((finstrs & finfo) & req_stack_size).
    match goal with
    | H: riscvPhase _ = _ |- _ => pose proof H as RP; unfold riscvPhase in H
    end.
    fwd.
    pose proof (get_compile_funs_pos p1 (build_fun_pos_env iset compile_ext_call p1)) as P.
    rewrite E0 in P.
    specialize P with (1 := H1p0). cbn in P.
    pose proof (compile_funs_finfo_idemp _ _ _ E0) as Q. subst r. fwd.
    eexists. split. 1: eassumption.
    intros.
    assert (word.unsigned p_funcs mod 4 = 0). {
      unfold machine_ok in *. fwd.
      eapply program_mod_4_0. 2: ecancel_assumption.
      eapply compile_funs_nonnil; eassumption.
    }
    unfold map.forall_values in H.
    match goal with
    | H: map.get p1 fname = Some _ |- _ => rename H into GetFun
    end.
    specialize H with (1 := GetFun) as V.
    match goal with
    | H: context[post] |- _ => rename H into Hpost
    end.
    unfold map.of_list_zip in Hpost.
    unfold valid_FlatImp_fun in V. fwd.
    eapply runsTo_weaken.
    - pose proof compile_function_body_correct as Q.
      specialize Q with
          (e_impl := map.remove p1 fname)
          (e_pos := FlatToRiscvDef.build_fun_pos_env iset compile_ext_call p1)
          (xframe := Rexec)
          (pos := pos2)
          (program_base := p_funcs)
          (l := l)
          (post := fun t' m' l' mc' =>
                     (exists retvals,
                         map.getmany_of_list l' retnames = Some retvals /\ post t' m' retvals)).
      eapply Q with
          (g := {| rem_stackwords :=
                     word.unsigned (word.sub stack_pastend stack_start) / bytes_per_word;
                   rem_framewords := 0; |}); clear Q.
      + intros.
        pose proof compile_stmt_correct as P.
        unfold compiles_FlatToRiscv_correctly in P at 2.
        eapply P with (e_pos := (build_fun_pos_env iset compile_ext_call p1))
                      (program_base := p_funcs)
                      (e_impl := map.remove p1 fname);
          clear P.
        { eassumption. }
        { eapply Hpost. }
        { eapply extends_remove. eapply extends_refl. }
        { eapply shrink_good_e_impl.
          1: eapply build_fun_pos_env_good_e_impl; assumption.
          eapply extends_remove. eapply extends_refl. }
        { eassumption. }
        { eassumption. }
        { eassumption. }
        { eassumption. }
        { eassumption. }
        { eassumption. }
        { eassumption. }
        { eassumption. }
        { eassumption. }
      + cbv beta. intros. fwd.
        rewrite <- Vp1.
        assert (HLR: Datatypes.length retnames = Datatypes.length retvals). {
          eapply map.getmany_of_list_length. eassumption.
        }
        eapply map.sameLength_putmany_of_list in HLR.
        destruct HLR as (l' & HLR).
        do 2 eexists. ssplit.
        * eassumption.
        * eassumption.
        * eexists. split. 2: eassumption.
          eapply map.putmany_of_list_zip_to_getmany_of_list.
          1: eassumption.
          rewrite Vp1.
          eapply List.NoDup_firstn.
          unfold reg_class.all.
          eapply List.NoDup_filter.
          eapply List.NoDup_unfoldn_Z_seq.
      + rewrite Vp1. rewrite List.firstn_length.
        change (Datatypes.length (reg_class.all reg_class.arg)) with 8%nat. clear. blia.
      + eassumption.
      + eapply Hpost.
      + rewrite <- Vp0.
        eapply map.putmany_of_list_zip_to_getmany_of_list.
        1: eassumption.
        rewrite Vp0.
        eapply List.NoDup_firstn.
        unfold reg_class.all.
        eapply List.NoDup_filter.
        eapply List.NoDup_unfoldn_Z_seq.
      + apply extends_remove. apply extends_refl.
      + eapply shrink_good_e_impl.
        1: eapply build_fun_pos_env_good_e_impl; assumption.
        eapply extends_remove. eapply extends_refl.
      + eapply fits_stack_monotone.
        { eapply stack_usage_correct; eassumption. }
        1: reflexivity. simpl_g_get. blia.
      + reflexivity.
      + unfold valid_FlatImp_fun. eauto.
      + assumption.
      + assumption.
      + eassumption.
      + assumption.
      + unfold machine_ok in *. fwd. assumption.
      + simpl_g_get. reflexivity.
      + unfold machine_ok in *. subst. fwd.
        unfold goodMachine; simpl_g_get. ssplit.
        { eapply map.extends_putmany_of_list_empty. 1: eassumption.
          apply_in_hyps @map.putmany_of_list_zip_sameLength.
          congruence. }
        { eapply map.of_list_zip_forall_keys. 1: eassumption.
          rewrite Vp0.
          eapply List.Forall_firstn.
          eapply Forall_impl.
          2: eapply arg_range_Forall.
          unfold valid_FlatImp_var. clear. blia. }
        { eassumption. }
        { assumption. }
        { assumption. }
        { eapply rearrange_footpr_subset. 1: eassumption.
          wwcancel.
          cbn [seps]. etransitivity. {
            eapply functions_to_program. eassumption.
          }
          etransitivity. {
            eapply functions_expose; eassumption.
          }
          wwcancel. }
        { unfold mem_available in *.
          extract_ex1_and_emp_in_hyps.
          destruct (byte_list_to_word_list_array anybytes)
            as (stack_trash_words&Hlength_stack_trash_words&Hstack_trash_words).
          { match goal with
            | H: ?x = ?y |- ?x mod _ = 0 => rewrite H
            end.
            assumption. }
          exists stack_trash_words, nil. ssplit. 2: reflexivity.
          2: {
            unfold word_array.
            rewrite <- (iff1ToEq (Hstack_trash_words _)).
            match goal with
            | E: Z.of_nat _ = word.unsigned (word.sub _ _) |- _ => rewrite <- E
            end.
            rewrite <- Z_div_exact_2; cycle 1. {
              unfold bytes_per_word. clear -BW.
              destruct width_cases as [E | E]; rewrite E; reflexivity.
            }
            {
              match goal with
              | H: ?x = ?y |- _ => rewrite H
              end.
              assumption.
            }
            use_sep_assumption.
            unfold ptsto_bytes.
            wseplog_pre.
            simpl_addrs.
            rewrite !word.of_Z_unsigned.
            wwcancel.
            cancel_seps_at_indices 1%nat 2%nat. 1: reflexivity.
            cbn [seps].
            etransitivity. {
              eapply functions_to_program. 1: eassumption.
            }
            etransitivity. {
              eapply functions_expose; eassumption.
            }
            wwcancel.
          }
          match goal with
          | E: Z.of_nat _ = word.unsigned (word.sub _ _) |- _ => simpl in E|-*; rewrite <- E
          end.
          apply Hlength_stack_trash_words. }
        { reflexivity. }
        { assumption. }
    - cbv beta. unfold goodMachine. simpl_g_get. unfold machine_ok in *. intros. fwd.
      assert (0 < bytes_per_word). { (* TODO: deduplicate *)
        unfold bytes_per_word; simpl; destruct width_cases as [EE | EE]; rewrite EE; cbv; trivial.
      }
      eexists _, _. ssplit.
      + eapply map.getmany_of_list_extends. 1: eassumption.
        match goal with
        | H: map.getmany_of_list finalRegsH _ = Some _ |-
             map.getmany_of_list finalRegsH _ = Some _ =>
            rename H into GM; move GM at bottom
        end.
        etransitivity. 2: exact GM. f_equal.
        rewrite Vp1.
        f_equal.
        symmetry.
        eapply map.getmany_of_list_length.
        exact GM.
      + eassumption.
      + eapply only_differ_subset. 1: eassumption.
        rewrite ListSet.of_list_list_union.
        rewrite ?singleton_set_eq_of_list.
        repeat apply subset_union_l;
          unfold subset, of_list, elem_of, reg_class.caller_saved; intros k HI.
        * eapply List.In_firstn_to_In in HI.
          pose proof arg_range_Forall as F.
          eapply Forall_forall in F. 2: eassumption.
          unfold reg_class.get.
          repeat match goal with
                 | |- _ => progress cbn [andb]
                 | |- context[if (?b && _)%bool then _ else _] =>
                     destr b; try Lia.lia; []
                 | |- context[if ?b then _ else _] => destr b; try Lia.lia; []
                 end.
          destr (k <=? 17)%bool.
          1: exact I.
          Lia.lia.
        * cbn in HI. contradiction.
        * unfold reg_class.get. subst k. cbn. exact I.
        * contradiction.
      + reflexivity.
      + cbv [mem_available].
        repeat rewrite ?(iff1ToEq (sep_ex1_r _ _)), ?(iff1ToEq (sep_ex1_l _ _)).
        exists (List.flat_map (fun x => HList.tuple.to_list (LittleEndian.split (Z.to_nat bytes_per_word) (word.unsigned x))) stack_trash).
        rewrite !(iff1ToEq (sep_emp_2 _ _ _)).
        rewrite !(iff1ToEq (sep_assoc _ _ _)).
        eapply (sep_emp_l _ _); split.
        { rewrite (List.length_flat_map _ (Z.to_nat bytes_per_word)).
          { rewrite Nat2Z.inj_mul, Z2Nat.id by blia.
            replace (Z.of_nat (Datatypes.length stack_trash))
              with (word.unsigned (word.sub stack_pastend stack_start) / bytes_per_word)
              by assumption.
            rewrite <- Z_div_exact_2; try trivial.
            eapply Z.lt_gt; assumption. }
          intros w.
          rewrite HList.tuple.length_to_list; trivial. }
        destruct frame_trash. 2: discriminate.
        use_sep_assumption.
        wwcancel.
        cancel_seps_at_indices 2%nat 1%nat. {
          unfold ptsto_bytes.
          match goal with
          | |- array _ _ ?a _ = array _ _ ?a' _ => replace a with a'
          end.
          2: {
            match goal with
            | H: context[stack_trash] |- _ => rewrite <- H
            end.
            replace (Z.of_nat (Datatypes.length stack_trash))
              with (word.unsigned (word.sub stack_pastend stack_start) / bytes_per_word)
              by assumption.
            rewrite <- Z_div_exact_2. 3: assumption.
            2: eapply Z.lt_gt; assumption.
            rewrite word.of_Z_unsigned.
            solve_word_eq word_ok.
          }

          Import Morphisms.
          assert (Proper_flat_map : forall A B, Proper (pointwise_relation _ eq ==> eq ==> eq) (@flat_map A B)).
          { clear; intros ? ? ? ? ? ? ? ?; subst; cbv [pointwise_relation] in *.
            induction y0; cbn; congruence. }
          setoid_rewrite LittleEndian.to_list_split.
          apply iff1ToEq, cast_word_array_to_bytes.
        }
        cbn [seps].
        etransitivity. 2: {
          symmetry. eapply functions_to_program. 1: eassumption.
        }
        etransitivity. 2: {
          symmetry. eapply functions_expose; eassumption.
        }
        wwcancel.
      + eapply rearrange_footpr_subset. 1: eassumption.
        (* TODO remove duplication *)
        lazymatch goal with
        | H: riscvPhase _ = _ |- _ => specialize functions_to_program with (1 := H) as P
        end.
        symmetry in P.
        specialize (P p_funcs).
        eapply iff1ToEq in P.
        rewrite <- P. clear P.
        wwcancel.
        cbn [seps].
        etransitivity. 2: {
          symmetry. eapply functions_expose; eassumption.
        }
        wwcancel.
      + destr_RiscvMachine final. subst. solve_divisibleBy4.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
    Unshelve.
    all: try exact EmptyMetricLog.
  Qed.

End LowerPipeline.
