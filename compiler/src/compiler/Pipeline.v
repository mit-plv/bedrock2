Require Export Coq.Lists.List.
Require Import bedrock2.LeakageSemantics.
Require Import Coq.ZArith.ZArith.
Export ListNotations.
Require Export coqutil.Decidable.
Require        compiler.ExprImp.
Require Export compiler.FlattenExprDef.
Require Export compiler.FlattenExpr.
Require        compiler.FlatImp.
Require Import compiler.FlatToRiscvDef.
Require Export riscv.Spec.Machine.
Require Export riscv.Platform.Run.
Require Export riscv.Platform.RiscvMachine.
Require Export riscv.Platform.MetricLogging.
Require Export riscv.Utility.Monads.
Require Import riscv.Utility.runsToNonDet.
Require Export riscv.Platform.MetricRiscvMachine.
Require Import coqutil.Z.Lia.
Require Import coqutil.Tactics.fwd.
Require Import compiler.ExprImp.
Require Import compiler.FlattenExprDef.
Require Import compiler.FlattenExpr.
Require Import compiler.FlatImp.
Require Import compiler.NameGen.
Require Import compiler.StringNameGen.
Require Export compiler.util.Common.
Require Export coqutil.Decidable.
Require Export riscv.Utility.Encode.
Require Import riscv.Spec.LeakageOfInstr.
Require Import riscv.Spec.Decode.
Require Export riscv.Spec.Primitives.
Require Export riscv.Spec.MetricPrimitives.
Require Import compiler.GoFlatToRiscv.
Require Import riscv.Utility.MkMachineWidth.
Require Export riscv.Proofs.DecodeEncode.
Require Export riscv.Proofs.EncodeBound.
Require Import riscv.Utility.Utility.
Require Export riscv.Platform.Memory.
Require Export riscv.Utility.InstructionCoercions.
Require Import compiler.SeparationLogic.
Require Import compiler.Spilling.
Require Import compiler.RegAlloc.
Require Import compiler.RiscvEventLoop.
Require Import compiler.MetricsToRiscv.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.MetricCosts.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvFunctions.
Require Import compiler.DivisibleBy4.
Require Export coqutil.Word.SimplWordExpr.
Require Export compiler.Registers.
Require Import compiler.ForeverSafe.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import coqutil.Tactics.autoforward.
Require Import compiler.FitsStack.
Require Import compiler.LowerPipeline.
Require Import bedrock2.MetricWeakestPreconditionProperties.
Require Import compiler.UseImmediateDef.
Require Import compiler.UseImmediate.
Require Import compiler.DeadCodeElimDef.
Require Import compiler.DeadCodeElim.
Import Utility.

Section WithWordAndMem.
  Context {width: Z} {BW: Bitwidth width} {word: Interface.word width} {mem : map.map word byte}.

  Record Lang := {
    Program: Type;
      Valid: Program -> Prop;
      Settings: Type;
      SettingsInhabited: Settings;
      Leakage: Type;
      Call(pick_sp: list Leakage -> word)(p: Program)(s: Settings)(funcname: string)
        (k: list Leakage)(t: trace)(m: mem)(argvals: list word)(mc: MetricLog)
        (post: list Leakage -> trace -> mem -> list word -> MetricLog -> Prop): Prop;
      WeakenCall: forall pick_sp p s funcname k t m mc argvals (post1: _ -> _ -> _ -> _ -> _ -> Prop),
        Call pick_sp p s funcname k t m argvals mc post1 ->
        forall post2 : _ -> _ -> _ -> _ -> _ -> Prop,
        (forall k' t' m' retvals mc', post1 k' t' m' retvals mc' -> post2 k' t' m' retvals mc') ->
        Call pick_sp p s funcname k t m argvals mc post2;
  }.

  Record phase_correct{L1 L2: Lang}
    {compile: L1.(Program) -> result L2.(Program)}: Prop :=
  {
    phase_preserves_valid: forall p1 p2,
        compile p1 = Success p2 ->
        L1.(Valid) p1 ->
        L2.(Valid) p2;
    phase_preserves_post: forall p1 p2,
        L1.(Valid) p1 ->
        compile p1 = Success p2 ->
        forall s1 s2 fname,
          exists pick_spH L,
        forall pick_spL kH kL t m argvals mcH post,
        L1.(Call) (pick_spH pick_spL kH kL) p1 s1 fname kH t m argvals mcH post ->
        forall mcL,
          L2.(Call) pick_spL p2 s2 fname kL t m argvals mcL
               (fun kL' t m a mcL' =>
                  exists mcH' kH' kH'',
                    post kH' t m a mcH' /\
                      kH' = kH'' ++ kH /\
                      kL' = L kH'' ++ kL /\
                      metricsLeq (mcL' - mcL) (mcH' - mcH));
  }.

  Arguments phase_correct : clear implicits.

  Definition compose_phases{A B C: Type}(phase1: A -> result B)(phase2: B -> result C):
    A -> result C :=
    fun a => match phase1 a with
             | Success b => phase2 b
             | Failure e => Failure e
             end.

  Ltac post_ext :=
    repeat (eapply functional_extensionality; intro);
    apply propositional_extensionality.

  Lemma compose_phases_correct{L1 L2 L3: Lang}
        {compile12: L1.(Program) -> result L2.(Program)}
        {compile23: L2.(Program) -> result L3.(Program)}:
    phase_correct L1 L2 compile12 ->
    phase_correct L2 L3 compile23 ->
    phase_correct L1 L3 (compose_phases compile12 compile23).
  Proof.
    unfold compose_phases.
    intros [V12 C12] [V23 C23].
    split; intros; fwd; eauto.
    specialize (V12 p1 a E H).
    specialize (C23 a p2 V12 H0 L2.(SettingsInhabited) s2 fname).
    specialize (C12 p1 a H E s1 L2.(SettingsInhabited) fname).
    destruct C12 as [f12 [nps12 C12] ]. destruct C23 as [f23 [nps23 C23] ].
    exists (fun pick_sp3 k1 k3 => f12 (f23 pick_sp3 nil k3) k1 nil).
    exists (fun k1 => nps23 (nps12 k1)).
    intros. eapply L3.(WeakenCall).
    { eapply C23. eapply C12. eapply H1. }
    simpl. intros. fwd. do 3 eexists. split; [eassumption|]. split; [reflexivity|].
    split; [|eauto with metric_arith].
    f_equal. f_equal. apply app_inv_tail in H2p0p2. assumption.
    Unshelve. all: auto.
  Qed.

  Section WithMoreParams.
    Context {Zlocals: map.map Z word}
            {string_keyed_map: forall T: Type, map.map string T} (* abstract T for better reusability *)
            {ext_spec: LeakageSemantics.ExtSpec}
            {word_ok : word.ok word}
            {mem_ok: map.ok mem}
            {string_keyed_map_ok: forall T, map.ok (string_keyed_map T)}
            {Zlocals_ok: map.ok Zlocals}.

    Context {ext_spec_ok : LeakageSemantics.ext_spec.ok ext_spec}.

    (* for riscv phase: *)
    Context {Registers: map.map Z word}.
    Context {M: Type -> Type}.
    Context {MM: Monad M}.
    Context {RVM: RiscvProgramWithLeakage M word}.
    Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
    Context {word_riscv_ok: RiscvWordProperties.word.riscv_ok word}.
    Context {Registers_ok: map.ok Registers}.
    Context {PR: MetricPrimitives PRParams}.
    Context {iset: InstructionSet}.
    Context {BWM: bitwidth_iset width iset}.
    Context (compile_ext_call : string_keyed_map Z -> Z -> Z -> FlatImp.stmt Z ->
                                list Instruction).
    Context (leak_ext_call : string_keyed_map Z -> Z -> Z -> FlatImp.stmt Z ->
                             list word -> list LeakageEvent).
    Context (compile_ext_call_correct: forall resvars extcall argvars,
                compiles_FlatToRiscv_correctly compile_ext_call leak_ext_call compile_ext_call
                                               (FlatImp.SInteract resvars extcall argvars)).
    Context (compile_ext_call_length_ignores_positions:
               forall stackoffset posmap1 posmap2 c pos1 pos2,
                List.length (compile_ext_call posmap1 pos1 stackoffset c) =
                List.length (compile_ext_call posmap2 pos2 stackoffset c)).

    Definition is5BitImmediate(x: Z) : bool :=
      andb (Z.leb 0 x) (Z.ltb x 32).
    Definition is12BitImmediate(x: Z) : bool :=
      andb (Z.leb (-2048) x) (Z.ltb x 2048).

    Definition locals_based_call_spec{Var Cmd: Type}{locals: map.map Var word}
               {string_keyed_map: forall T: Type, map.map string T}
               (Exec: PickSp -> string_keyed_map (list Var * list Var * Cmd)%type ->
                      Cmd -> leakage -> trace -> mem -> locals -> MetricLog ->
                      (leakage -> trace -> mem -> locals -> MetricLog -> Prop) -> Prop)
               (pick_sp: PickSp)
               (e: string_keyed_map (list Var * list Var * Cmd)%type)(s : unit) (f: string)
               (k: leakage)(t: trace)(m: mem)(argvals: list word)(mc: MetricLog)
               (post: leakage -> trace -> mem -> list word -> MetricLog -> Prop): Prop :=
      exists argnames retnames fbody l,
        map.get e f = Some (argnames, retnames, fbody) /\
        map.of_list_zip argnames argvals = Some l /\
        Exec pick_sp e fbody k t m l (cost_spill_spec mc) (fun k' t' m' l' mc' =>
                       exists retvals, map.getmany_of_list l' retnames = Some retvals /\
                                       post k' t' m' retvals mc').

    Definition locals_based_call_spec_spilled{Var Cmd: Type}{locals: map.map Var word}
               {string_keyed_map: forall T: Type, map.map string T}
               (Exec: PickSp -> string_keyed_map (list Var * list Var * Cmd)%type ->
                      Cmd -> leakage -> trace -> mem -> locals -> MetricLog ->
                      (leakage -> trace -> mem -> locals -> MetricLog -> Prop) -> Prop)
               (pick_sp : PickSp)
               (e: string_keyed_map (list Var * list Var * Cmd)%type)(s : unit)(f: string)
               (k: leakage) (t: trace)(m: mem)(argvals: list word)(mc: MetricLog)
               (post: leakage -> trace -> mem -> list word -> MetricLog -> Prop): Prop :=
      exists argnames retnames fbody l,
        map.get e f = Some (argnames, retnames, fbody) /\
        map.of_list_zip argnames argvals = Some l /\
        Exec pick_sp e fbody k t m l mc (fun k' t' m' l' mc' =>
                       exists retvals, map.getmany_of_list l' retnames = Some retvals /\
                                       post k' t' m' retvals mc').

    Lemma thing_locals_based_call_spec_weaken{Var Cmd: Type}{locals: map.map Var word}
      {string_keyed_map_: forall T: Type, map.map string T}
      thing :
      forall
      (Exec: PickSp -> string_keyed_map_ (list Var * list Var * Cmd)%type ->
             Cmd -> leakage -> trace -> mem -> locals -> MetricLog ->
             (leakage -> trace -> mem -> locals -> MetricLog -> Prop) -> Prop),
      (forall pick_sp e c k t m l mc (post1: _ -> _ -> _ -> _ -> _ -> Prop),
          Exec pick_sp e c k (t : trace) m (l : map.rep) (mc : MetricLog) post1 ->
          forall (post2 : _ -> _ -> _ -> _ -> _ -> Prop),
            (forall k' t' m' l' mc', post1 k' t' m' l' mc' -> post2 k' t' m' l' mc') ->
            Exec pick_sp e c k t m l mc post2) ->
      forall
        (pick_sp : PickSp)(e: string_keyed_map_ (list Var * list Var * Cmd)%type)(s : unit)(f: string)
        (k: leakage)(t: trace)(m: mem)(argvals: list word)(mc: MetricLog)
        (post1: leakage -> trace -> mem -> list word -> MetricLog -> Prop),
        (match thing with | true => locals_based_call_spec | false => locals_based_call_spec_spilled end) Exec pick_sp e s f k t m argvals mc post1 ->
        forall (post2 : _ -> _ -> _ -> _ -> _ -> Prop),
          (forall k' t' m' retvals mc', post1 k' t' m' retvals mc' -> post2 k' t' m' retvals mc') ->
          (match thing with | true => locals_based_call_spec | false => locals_based_call_spec_spilled end) Exec pick_sp e s f k t m argvals mc post2.
    Proof.
      destruct thing; simpl.
      - intros. cbv [locals_based_call_spec] in *.
        destruct H0 as (argnames & retnames & fbody & l & H2 & H3 & H4).
        exists argnames, retnames, fbody, l. intuition eauto.
        eapply H. 1: apply H4. simpl. intros.
        destruct H0 as [retvals [H5 H6] ]. exists retvals. eauto.
      - intros. cbv [locals_based_call_spec_spilled] in *.
        destruct H0 as (argnames & retnames & fbody & l & H2 & H3 & H4).
        exists argnames, retnames, fbody, l. intuition eauto.
        eapply H. 1: apply H4. simpl. intros.
        destruct H0 as [retvals [H5 H6] ]. exists retvals. eauto.
    Qed.

    Definition locals_based_call_spec_weaken {Var Cmd: Type}{locals: map.map Var word}
      := ltac:(let t := eval compute in (thing_locals_based_call_spec_weaken (Var := Var) (Cmd := Cmd) true) in exact t).
    Check locals_based_call_spec_weaken.

    Definition locals_based_call_spec_spilled_weaken {Var Cmd: Type}{locals: map.map Var word}
      := thing_locals_based_call_spec_weaken (Var := Var) (Cmd := Cmd) false.
    
    Definition ParamsNoDup{Var: Type}: (list Var * list Var * FlatImp.stmt Var) -> Prop :=
      fun '(argnames, retnames, body) => NoDup argnames /\ NoDup retnames.

    Check @MetricLeakageSemantics.exec. Print mem.
    Check locals_based_call_spec_weaken. Print env.
    Print string_keyed_map.

    Definition SrcLang: Lang. refine ({|
      Program := Semantics.env;
      Valid := map.forall_values ExprImp.valid_fun;
      Call := locals_based_call_spec (fun pick_sp e => @MetricLeakageSemantics.exec _ _ _ _ _ _ _ pick_sp);
      SettingsInhabited := tt;
                                       |}).
      intros. Fail apply @locals_based_call_spec_weaken. (* why :( *)
      cbv [locals_based_call_spec] in *. fwd. do 4 eexists. intuition eauto.
      eapply MetricLeakageSemantics.exec.weaken; eauto. simpl. intros. fwd.
      intuition eauto. Unshelve. assumption.
    Defined.
     (* |                 *)
    (* | FlattenExpr     *)
    (* V                 *) Check FlatImp.exec.
    Definition FlatWithStrVars: Lang.
      refine ({|
                 Program := string_keyed_map (list string * list string * FlatImp.stmt string);
                 Valid := map.forall_values ParamsNoDup;
                 Call := locals_based_call_spec (fun pick_sp e => @FlatImp.exec _ _ _ _ _ _ _  _ PreSpill isRegStr e pick_sp);
               |}).
      1: exact tt. intros.
      cbv [locals_based_call_spec] in *. fwd. do 4 eexists. intuition eauto.
      eapply FlatImp.exec.weaken; eauto. simpl. intros. fwd.
      intuition eauto.
    Defined.                         

    (* |                 *)
    (* | UseImmediate    *)
    (* V                 *)
    (* FlatWithStrVars   *)

    (* |                 *)
    (* | DeadCodeElim    *)
    (* V                 *)
    (* FlatWithStrVars   *)

    (* |                 *)
    (* | RegAlloc        *)
    (* V                 *)
    Definition FlatWithZVars: Lang.
      refine ({|
                 Program := string_keyed_map (list Z * list Z * FlatImp.stmt Z);
                 Valid := map.forall_values ParamsNoDup;
                 Call := locals_based_call_spec (fun pick_sp e => @FlatImp.exec _ _ _ _ _ _ _ _ PreSpill isRegZ e pick_sp);
               |}).
      1: exact tt. intros.
      cbv [locals_based_call_spec] in *. fwd. do 4 eexists. intuition eauto.
      eapply FlatImp.exec.weaken; eauto. simpl. intros. fwd.
      intuition eauto.
    Defined.
                                    
    (* |                 *)
    (* | Spilling        *)
    (* V                 *)
    Definition FlatWithRegs: Lang.
      refine ({|
                 Program := string_keyed_map (list Z * list Z * FlatImp.stmt Z);
                 Valid := map.forall_values FlatToRiscvDef.valid_FlatImp_fun;
                 Call := locals_based_call_spec_spilled (fun e pick_sp => @FlatImp.exec _ _ _ _ _ _ _ _ PostSpill isRegZ pick_sp e);
               |}).
      1: exact tt. intros.
      cbv [locals_based_call_spec_spilled] in *. fwd. do 4 eexists. intuition eauto.
      eapply FlatImp.exec.weaken; eauto. simpl. intros. fwd.
      intuition eauto.
    Defined.

    (*Lemma riscv_call_weaken :
      forall (pick_sp: list LeakageEvent -> word) (p : list Instruction * string_keyed_map Z * Z)
             (s : word * word) (funcname : string) (k : list LeakageEvent)
             (t : trace) (m : mem) (argvals : list word)
             (post1 : list LeakageEvent -> trace -> mem -> list word -> Prop),
        (fun _ => riscv_call p s funcname k t m argvals post1) pick_sp ->
        forall
          post2 : list LeakageEvent -> trace -> mem -> list word -> Prop,
          (forall (k' : list LeakageEvent) (t' : io_trace) 
                  (m' : mem) (retvals : list word),
              post1 k' t' m' retvals -> post2 k' t' m' retvals) ->
          (fun _ => riscv_call p s funcname k t m argvals post2) pick_sp.
    Proof.
      intros. cbv [riscv_call] in *. destruct p. destruct p. destruct s.
      destruct H as [f_rel_pos H]. exists f_rel_pos. intuition eauto.
      cbv [runsTo]. eapply runsToNonDet.runsTo_weaken. 1: eapply H2.
      all: try eassumption. simpl. intros. fwd. exists mH', retvals.
      intuition eauto.
    Qed.*)
    (* |                 *)
    (* | FlatToRiscv     *)
    (* V                 *)
    Definition RiscvLang: Lang.
      refine ({|
                 Program :=
                   list Instruction *      (* <- code of all functions concatenated       *)
                     string_keyed_map Z *    (* <- position (offset) for each function      *)
                     Z;                      (* <- required stack space in XLEN-bit words   *)
                 (* bounds in instructions are checked by `ptsto_instr` *)
                 Valid '(insts, finfo, req_stack_size) := True;
                 Call := (fun _ => riscv_call);
               |}).
      1: exact (word.of_Z 0, word.of_Z 0, word.of_Z 0). intros.
      intros. cbv [riscv_call] in *. destruct p. destruct p. destruct s as [ [? ?] ?].
      destruct H as [f_rel_pos H]. exists f_rel_pos. intuition eauto.
      cbv [runsTo]. eapply runsToNonDet.runsTo_weaken. 1: eapply H2.
      all: try eassumption. simpl. intros. fwd. do 3 eexists.
      intuition eauto.
    Defined.

    Lemma flatten_functions_NoDup: forall funs funs',
        (forall f argnames retnames body,
          map.get funs f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames) ->
        flatten_functions funs = Success funs' ->
        forall f argnames retnames body,
          map.get funs' f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames.
    Proof.
      unfold flatten_functions. intros.
      eapply map.try_map_values_bw in H0. 2: eassumption.
      unfold flatten_function in *. fwd.
      eapply H. eassumption.
    Qed.

    Lemma flattening_correct: phase_correct SrcLang FlatWithStrVars flatten_functions.
    Proof.
      unfold SrcLang, FlatWithStrVars.
      split; cbn -[flatten_functions].
      { unfold map.forall_values, ParamsNoDup.
        intros. destruct v as ((argnames & retnames) & body).
        eapply flatten_functions_NoDup; try eassumption.
        unfold valid_fun in *.
        intros. specialize H0 with (1 := H2). simpl in H0. eapply H0.
      }
      unfold locals_based_call_spec. intros.
      exists (fun pick_spL kH kL k => pick_spL ((rev (skipn (length kH) (rev k)) ++ kL))).
      exists (fun k => k). intros. fwd.
      pose proof H0 as GF.
      unfold flatten_functions in GF.
      eapply map.try_map_values_fw in GF. 2: eassumption.
      unfold flatten_function in GF. fwd.
      eexists _, _, _, _. split. 1: eassumption. split. 1: eassumption.
      intros.
      eapply FlatImp.exec.weaken.
      - eapply flattenStmt_correct_aux.
        + eassumption.
        + eapply MetricLeakageSemantics.exec.exec_ext. 
          1: eapply MetricLeakageSemantics.exec.exec_to_other_trace.
          1: eapply H1p2.
          intros. simpl. simpl_rev. rewrite List.skipn_app_r.
          2: rewrite length_rev; reflexivity.
          simpl_rev. rewrite List.skipn_app_r.
          2: rewrite length_rev; reflexivity.
          rewrite rev_involutive. reflexivity.
        + reflexivity.
        + match goal with
          | |- ?p = _ => rewrite (surjective_pairing p)
          end.
          reflexivity.
        + intros x k A. assumption.
        + unfold map.undef_on, map.agree_on. cbn. intros k A.
          rewrite map.get_empty. destr (map.get l k). 2: reflexivity. exfalso.
          unfold map.of_list_zip in H1p1.
          edestruct (map.putmany_of_list_zip_find_index _ _ _ _ _ _ H1p1 E) as [G | G].
          2: {
            rewrite map.get_empty in G. discriminate.
          }
          destruct G as (i & G1 & G2).
          eapply nth_error_In in G1.
          eapply start_state_spec. 2: exact A.
          eapply ListSet.In_list_union_l. eapply ListSet.In_list_union_l. assumption.
        + eapply @freshNameGenState_disjoint_fbody.
      - simpl. intros. fwd. eexists. split.
        + eauto using map.getmany_of_list_extends.
        + do 3 eexists. split; [eassumption|]. ssplit; [align_trace|align_trace|].
          unfold cost_spill_spec in *; solve_MetricLog.
    Qed.

    Lemma useimmediate_functions_NoDup: forall funs funs',
        (forall f argnames retnames body,
          map.get funs f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames) ->
        (useimmediate_functions is5BitImmediate is12BitImmediate) funs = Success funs' ->
        forall f argnames retnames body,
          map.get funs' f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames.
    Proof.
      unfold useimmediate_functions. intros.
      eapply map.try_map_values_bw in H0.
      2: { eassumption.  }
      unfold useimmediate_function in *.
      fwd.
      eapply H.
      eassumption.
    Qed.

    Lemma useimmediate_correct: phase_correct FlatWithStrVars FlatWithStrVars (useimmediate_functions is5BitImmediate is12BitImmediate).
    Proof.
      unfold FlatWithStrVars.
      split; cbn.
      { unfold map.forall_values, ParamsNoDup. intros.
        destruct v as  ((argnames & retnames) & body).
        eapply useimmediate_functions_NoDup; try eassumption.
        intros. specialize H0 with (1 := H2).
        simpl in H0. assumption.
      }

      unfold locals_based_call_spec. intros.
      exists (fun pick_spL kH kL k => pick_spL ((rev (skipn (length kH) (rev k)) ++ kL))).
      exists (fun k => k). intros. fwd.
      pose proof H0 as GI.
      unfold  useimmediate_functions in GI.
      eapply map.try_map_values_fw in GI. 2: eassumption.
      unfold useimmediate_function in GI. fwd.
      eexists _, _, _, _. split. 1: eassumption. split. 1: eassumption.
      intros.
      eapply exec.weaken.
      - eapply useImmediate_correct_aux; eauto.
        eapply FlatImp.exec.exec_ext. 
          1: eapply FlatImp.exec.exec_to_other_trace.
          1: eassumption.
          intros. simpl. simpl_rev. rewrite List.skipn_app_r.
          2: rewrite length_rev; reflexivity.
          simpl_rev. rewrite List.skipn_app_r.
          2: rewrite length_rev; reflexivity.
          rewrite rev_involutive. reflexivity.
      - simpl. intros. fwd. eexists. intuition eauto.
        do 3 eexists. intuition eauto.
        unfold cost_spill_spec in *; solve_MetricLog.
    Qed.


    Lemma dce_functions_NoDup: forall funs funs',
        (forall f argnames retnames body,
          map.get funs f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames) ->
        dce_functions funs = Success funs' ->
        forall f argnames retnames body,
          map.get funs' f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames.
    Proof.
      unfold dce_functions. intros.
      eapply map.try_map_values_bw in H0. 2: eassumption.
      unfold dce_function in *. fwd.
      eapply H. eassumption.
    Qed.

    Lemma dce_correct: phase_correct FlatWithStrVars FlatWithStrVars dce_functions.
    Proof.
      unfold FlatWithStrVars.
      split; cbn.
      { unfold map.forall_values, ParamsNoDup. intros.
        destruct v as  ((argnames & retnames) & body).
        eapply dce_functions_NoDup; try eassumption.
        intros. specialize H0 with (1 := H2).
        simpl in H0. assumption.
      }

      unfold locals_based_call_spec. intros.
      exists (fun pick_spL kH kL k => let '(argnames, retnames, fbody) :=
                                match (map.get p1 fname) with Some finfo => finfo | None => (nil, nil, SSkip) end in
                              fun kk => let k := rev (skipn (length kH) (rev kk)) in
                                     pick_spL (rev kL ++ stmt_leakage eH (rev k, sH, used_
                                  
      eexists. eexists. intros. fwd.
      pose proof H0 as GI.
      unfold dce_functions in GI.
      eapply map.try_map_values_fw in GI. 2: eassumption.
      unfold dce_function in GI. fwd.
      eexists _, _, _, _. split. 1: eassumption. split. 1: eassumption.
      intros.
      eapply @exec.weaken.
      - eapply exec.exec_ext. 1: eapply dce_correct_aux; eauto.
        { eapply MapEauto.agree_on_refl. }
        2: { intros. simpl. instantiate (1 := fun x => pick_spL (rev x)).
             simpl. rewrite rev_involutive. reflexivity. }
        intros. remember (k ++ kH) as kk eqn:Hkk.
        replace k with (rev (skipn (length kH) (rev (k ++ kH)))).
        { forget (k ++ kH) as kk0. subst.
          set (finfo :=
                 match (map.get p1 fname) with | Some finfo => finfo | None => (nil, nil, SSkip) end).
          replace fbody with (snd finfo). 1: replace argnames with (fst (fst finfo)).
          1: replace retnames with (snd (fst finfo)).
          { 
          instantiate (2 := fun _ _ _ _ => _). simpl. reflexivity.
        1: reflexivity.
        1: forget (k ++ kH) as kk. 1: instantiate (2 := fun _ _ _ _ => _). 1: reflexivity.
        insta
        intros. simpl. instantiate (2 := fun _ _ _ _ => _). simpl. reflexivity.
      - unfold compile_post. intros. fwd.
        exists retvals.
        split.
        + erewrite MapEauto.agree_on_getmany; [ eauto | eapply MapEauto.agree_on_comm; [ eassumption ] ].
        + eexists; split; eauto. unfold cost_spill_spec in *; solve_MetricLog.
    Qed.

    Lemma regalloc_functions_NoDup: forall funs funs',
        regalloc_functions funs = Success funs' ->
        forall f argnames retnames body,
          map.get funs' f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames.
    Proof.
      unfold regalloc_functions, check_funcs. intros.
      fwd.
      eapply map.try_map_values_bw in E. 2: eassumption.
      fwd.
      eapply map.get_forall_success in E0. 2: eassumption.
      unfold lookup_and_check_func, check_func, assert in *.
      destruct v1 as ((args1 & rets1) & body1). fwd.
      rewrite <- E1, <- E4.
      split; apply List.NoDup_dedup.
    Qed.

    Lemma regalloc_correct: phase_correct FlatWithStrVars FlatWithZVars regalloc_functions.
    Proof.
      unfold FlatWithStrVars, FlatWithZVars. split; cbn.
      { unfold map.forall_values, ParamsNoDup. intros.
        destruct v as ((argnames & retnames) & body).
        eapply regalloc_functions_NoDup; eassumption.
      }
      unfold locals_based_call_spec.
      intros. fwd.
      pose proof H0 as GR.
      unfold regalloc_functions in GR.
      fwd. rename E into GR.
      eapply map.try_map_values_fw in GR. 2: eassumption.
      fwd. clear GRp0.
      pose proof E0 as C.
      unfold check_funcs in E0.
      eapply map.get_forall_success in E0. 2: eassumption.
      unfold lookup_and_check_func, check_func in E0. fwd.

      rename l0 into argregs, l1 into retregs.
      apply_in_hyps assert_ins_same_length.
      apply_in_hyps assignments_same_length.
      apply_in_hyps @map.putmany_of_list_zip_sameLength.
      assert (exists l', map.of_list_zip argregs argvals = Some l'). {
        eapply map.sameLength_putmany_of_list. congruence.
      }
      fwd.
      eexists _, _, _, _. split. 1: eassumption. split. 1: eassumption. intros.
      unfold map.of_list_zip in *.
      eapply FlatImp.exec.weaken.
      - eapply checker_correct; eauto.
        eapply states_compat_precond.
        edestruct putmany_of_list_zip_states_compat as (lL' & P' & Cp); try eassumption.
        1: eapply states_compat_empty.
        rewrite H1 in P'. inversion P'. exact Cp.
      - simpl. intros. fwd. eexists. split.
        + eauto using states_compat_getmany.
        + eexists. split; [|eassumption]. unfold cost_spill_spec in *; solve_MetricLog.
    Qed.

    Ltac debool :=
      repeat match goal with
             | H: (_ && _)%bool = true |- _ => apply Bool.andb_true_iff in H
             | H: _ /\ _ |- _ => destruct H as [? H]
             | H: _ <? _ = true |- _ => eapply Z.ltb_lt in H
             | H: (_ <=? _)%nat = true |- _ => eapply Nat.leb_le in H
             end.

    Lemma spilling_preserves_valid: forall p1 p2 : string_keyed_map (list Z * list Z * stmt Z),
        spill_functions p1 = Success p2 ->
        map.forall_values ParamsNoDup p1 ->
        map.forall_values FlatToRiscvDef.valid_FlatImp_fun p2.
    Proof.
      unfold spill_functions, map.forall_values. intros.
      eapply map.try_map_values_bw in H. 2: eassumption.
      unfold spill_fun in H. fwd.
      unfold FlatToRiscvDef.valid_FlatImp_fun, FlatToRiscvDef.valid_FlatImp_var,
      FlatToRiscvDef.valid_FlatImp_vars,
      FlatToRiscvDef.valid_FlatImp_var, fp in *.
      debool.
      ssplit.
      - rewrite ?List.firstn_length. change (List.length (Registers.reg_class.all _)) with 8%nat.
        f_equal. blia.
      - rewrite ?List.firstn_length. change (List.length (Registers.reg_class.all _)) with 8%nat.
        f_equal. blia.
      - cbn. ssplit.
        + blia.
        + blia.
        + eapply set_vars_to_reg_range_valid_vars; unfold a0, a7; try blia.
          eapply List.forallb_to_Forall. 2: eassumption.
          unfold is_valid_src_var. intros. debool. assumption.
        + eapply spill_stmt_valid_vars. 1: reflexivity.
          unfold valid_vars_src.
          eapply max_var_sound.
          eapply FlatImp.forallb_vars_stmt_correct.
          2: eassumption.
          unfold is_valid_src_var.
          intros; rewrite ?Bool.andb_true_iff, ?Z.ltb_lt; unfold fp; blia.
        + eapply set_reg_range_to_vars_valid_vars; unfold a0, a7; try blia.
          eapply List.forallb_to_Forall. 2: eassumption.
          unfold is_valid_src_var. intros. debool. assumption.
      - cbn. ssplit.
        + apply set_vars_to_reg_range_uses_standard_arg_regs.
        + apply spill_stmt_uses_standard_arg_regs.
        + apply set_reg_range_to_vars_uses_standard_arg_regs.
    Qed.

    Lemma spilling_correct: phase_correct FlatWithZVars FlatWithRegs spill_functions.
    Proof.
      unfold FlatWithZVars, FlatWithRegs. split; cbn.
      1: exact spilling_preserves_valid.
      unfold locals_based_call_spec, locals_based_call_spec_spilled. intros. fwd.
      pose proof H0 as GL.
      unfold spill_functions in GL.
      eapply map.try_map_values_fw in GL. 2: eassumption.
      destruct GL as (((argnames2 & retnames2) & fbody2) & Sp & G2).
      apply_in_hyps @map.putmany_of_list_zip_sameLength.
      assert (exists l', map.of_list_zip argnames2 argvals = Some l'). {
        eapply map.sameLength_putmany_of_list.
        unfold spill_fun in Sp. fwd.
        rewrite !List.firstn_length.
        change (Datatypes.length (reg_class.all reg_class.arg)) with 8%nat.
        blia.
      }
      fwd.
      exists argnames2, retnames2, fbody2, l'.
      split. 1: exact G2. split. 1: eassumption.
      intros.
      eapply FlatImp.exec.weaken.
      - eapply spill_fun_correct; try eassumption.
        unfold call_spec. intros * E. rewrite E in *. fwd. eauto.
      - simpl. intros. fwd. repeat (eexists; split; eauto with metric_arith).
    Qed.

    Lemma riscv_phase_correct: phase_correct FlatWithRegs RiscvLang (riscvPhase compile_ext_call).
    Proof.
      unfold FlatWithRegs, RiscvLang.
      split; cbn.
      - intros p1 ((? & finfo) & ?). intros. exact I.
      - eapply flat_to_riscv_correct; eassumption.
    Qed.

    Definition composed_compile:
      Semantics.env ->
      result (list Instruction * string_keyed_map Z * Z) :=
      (compose_phases flatten_functions
      (compose_phases (useimmediate_functions is5BitImmediate is12BitImmediate)
      (compose_phases dce_functions
      (compose_phases regalloc_functions
      (compose_phases spill_functions
                      (riscvPhase compile_ext_call)))))).

    Lemma composed_compiler_correct: phase_correct SrcLang RiscvLang composed_compile.
    Proof.
      unfold composed_compile.
      exact (compose_phases_correct flattening_correct
            (compose_phases_correct useimmediate_correct
            (compose_phases_correct dce_correct
            (compose_phases_correct regalloc_correct
            (compose_phases_correct spilling_correct
                                    riscv_phase_correct))))).
    Qed.

    Definition compile(funs: list (string * (list string * list string * cmd))):
      result (list Instruction * list (string * Z) * Z) :=
      match composed_compile (map.of_list funs) with
      | Success (insts, pos, space) => Success (insts, map.tuples pos, space)
      | Failure e => Failure e
      end.

    Definition valid_src_fun: (string * (list string * list string * cmd)) -> bool :=
      fun '(name, (args, rets, body)) =>
        andb (List.list_eqb String.eqb (List.dedup String.eqb args) args)
             (List.list_eqb String.eqb (List.dedup String.eqb rets) rets).

    Lemma valid_src_fun_correct: forall name f,
        valid_src_fun (name, f) = true -> ExprImp.valid_fun f.
    Proof.
      unfold valid_src_fun, valid_fun. intros. destruct f as ((args & rets) & body).
      fwd. split.
      - rewrite <- Hp0. apply List.NoDup_dedup.
      - rewrite <- Hp1. apply List.NoDup_dedup.
    Qed.

    Definition valid_src_funs: list (string * (list string * list string * cmd)) -> bool :=
      List.forallb valid_src_fun.

    Lemma valid_src_funs_correct fs:
        valid_src_funs fs = true ->
        ExprImp.valid_funs (map.of_list fs).
    Proof.
      unfold valid_funs. induction fs; intros.
      - cbn [map.of_list] in H0. rewrite map.get_empty in H0. discriminate.
      - destruct a as (name & body). cbn [map.of_list] in H0. rewrite map.get_put_dec in H0. fwd.
        destruct_one_match_hyp.
        + fwd. eapply valid_src_fun_correct. eassumption.
        + eapply IHfs; eassumption.
    Qed.

    (* restate composed_compiler_correct by unfolding definitions used to compose phases *)
    Lemma compiler_correct: forall
        (* input of compilation: *)
        (functions: list (string * (list string * list string * cmd)))
        (* output of compilation: *)
        (instrs: list Instruction) (finfo: list (string * Z)) (req_stack_size: Z)
        (* function we choose to call: *)
        (fname: string)
        (* high-level initial state & post on final state: *)
        (t: trace) (mH: mem) (argvals: list word) (mc: MetricLog) (post: trace -> mem -> list word -> MetricLog -> Prop),
        valid_src_funs functions = true ->
        compile functions = Success (instrs, finfo, req_stack_size) ->
        (exists (argnames retnames: list string) (fbody: cmd) l,
            map.get (map.of_list (map := Semantics.env) functions) fname =
              Some (argnames, retnames, fbody) /\
            map.of_list_zip argnames argvals = Some l /\
              MetricSemantics.exec (map.of_list functions) fbody t mH l
                (cost_spill_spec mc)
                (fun t' m' l' mc' => exists retvals: list word,
                     map.getmany_of_list l' retnames = Some retvals /\
                     post t' m' retvals mc')) ->
        forall mcL,
        exists (f_rel_pos: Z),
          map.get (map.of_list finfo) fname = Some f_rel_pos /\
          forall (* low-level machine on which we're going to run the compiled program: *)
                 (initial: MetricRiscvMachine)
                 (* ghost vars that help describe the low-level machine: *)
                 (stack_lo stack_hi: word) (ret_addr p_funcs: word) (Rdata Rexec: mem -> Prop),
            req_stack_size <= word.unsigned (word.sub stack_hi stack_lo) / bytes_per_word ->
            word.unsigned (word.sub stack_hi stack_lo) mod bytes_per_word = 0 ->
            initial.(getPc) = word.add p_funcs (word.of_Z f_rel_pos) ->
            map.get (getRegs initial) RegisterNames.ra = Some ret_addr ->
            word.unsigned ret_addr mod 4 = 0 ->
            arg_regs_contain initial.(getRegs) argvals ->
            initial.(getLog) = t ->
            raiseMetrics (cost_compile_spec initial.(getMetrics)) = mcL ->
            machine_ok p_funcs stack_lo stack_hi instrs mH Rdata Rexec initial ->
            runsTo initial (fun final : MetricRiscvMachine =>
              exists mH' retvals,
                arg_regs_contain (getRegs final) retvals /\
                (exists mcH' : MetricLog,
                  ((raiseMetrics final.(getMetrics)) - mcL <= mcH' - mc)%metricsH /\
                  post (getLog final) mH' retvals mcH') /\
                map.only_differ initial.(getRegs) reg_class.caller_saved final.(getRegs) /\
                final.(getPc) = ret_addr /\
                machine_ok p_funcs stack_lo stack_hi instrs mH' Rdata Rexec final).
    Proof.
      intros.
      pose proof (phase_preserves_post composed_compiler_correct) as C.
      unfold Call, SrcLang, RiscvLang, locals_based_call_spec, riscv_call in C.
      eapply valid_src_funs_correct in H.
      specialize C with (1 := H).
      assert (composed_compile (map.of_list functions) =
                Success (instrs, map.of_list finfo, req_stack_size)) as H0'. {
        clear -H0 string_keyed_map_ok. unfold compile in H0. fwd.
        rewrite map.of_list_tuples. reflexivity.
      }
      specialize C with (1 := H0').
      specialize C with (1 := H1).
      specialize (C mcL).
      cbv iota in C.
      fwd. eauto 10.
    Qed.

    Definition instrencode(p: list Instruction): list byte :=
      List.flat_map (fun inst => HList.tuple.to_list (LittleEndian.split 4 (encode inst))) p.

    Ltac hyp p :=
      multimatch goal with
      | H: context[p] |- _ => H
      end.

    (* combines the above theorem with WeakestPrecondition soundness,
       and makes `map.get (map.of_list finfo) fname` a hyp rather than conclusion because
       in concrete instantiations, users need to lookup that position themselves anyways *)
    Lemma compiler_correct_wp: forall
        (* input of compilation: *)
        (fs: list (string * (list string * list string * cmd)))
        (* output of compilation: *)
        (instrs: list Instruction) (finfo: list (string * Z)) (req_stack_size: Z)
        (* function we choose to call: *)
        (fname: string) (f_rel_pos: Z)
        (* high-level initial state & post on final state: *)
        (t: trace) (mH: mem) (argvals: list word) (mc: MetricLog) (post: trace -> mem -> list word -> MetricLog -> Prop)
        (* ghost vars that help describe the low-level machine: *)
        (stack_lo stack_hi ret_addr p_funcs: word) (Rdata Rexec: mem -> Prop)
        (* low-level machine on which we're going to run the compiled program: *)
        (initial: MetricRiscvMachine),
        valid_src_funs fs = true ->
        NoDup (map fst fs) ->
        compile fs = Success (instrs, finfo, req_stack_size) ->
        MetricWeakestPrecondition.call (map.of_list fs) fname t mH argvals
          (cost_spill_spec mc) post ->
        forall mcL,
        map.get (map.of_list finfo) fname = Some f_rel_pos ->
        req_stack_size <= word.unsigned (word.sub stack_hi stack_lo) / bytes_per_word ->
        word.unsigned (word.sub stack_hi stack_lo) mod bytes_per_word = 0 ->
        initial.(getPc) = word.add p_funcs (word.of_Z f_rel_pos) ->
        map.get (getRegs initial) RegisterNames.ra = Some ret_addr ->
        word.unsigned ret_addr mod 4 = 0 ->
        arg_regs_contain initial.(getRegs) argvals ->
        initial.(getLog) = t ->
        raiseMetrics (cost_compile_spec initial.(getMetrics)) = mcL ->
        machine_ok p_funcs stack_lo stack_hi instrs mH Rdata Rexec initial ->
        runsTo initial (fun final : MetricRiscvMachine =>
          exists mH' retvals,
            arg_regs_contain (getRegs final) retvals /\
            (exists mcH' : MetricLog,
              ((raiseMetrics final.(getMetrics)) - mcL <= mcH' - mc)%metricsH /\
              post (getLog final) mH' retvals mcH') /\
            map.only_differ initial.(getRegs) reg_class.caller_saved final.(getRegs) /\
            final.(getPc) = ret_addr /\
            machine_ok p_funcs stack_lo stack_hi instrs mH' Rdata Rexec final).
    Proof.
      intros.
      let H := hyp MetricWeakestPrecondition.call in rename H into WP.
      edestruct compiler_correct with (fname := fname) (argvals := argvals) (post := post) as (f_rel_pos' & G & C);
        try eassumption.
      2: { eapply C; clear C; try assumption; try congruence; try eassumption. }
      intros.
      unfold MetricSemantics.call in WP. fwd.
      do 5 eexists. 1: eassumption. split. 1: eassumption.
      intros. assumption.
    Qed.

  End WithMoreParams.
End WithWordAndMem.
