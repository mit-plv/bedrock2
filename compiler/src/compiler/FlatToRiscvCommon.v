From coqutil Require Import HList Memory SeparationMemory LittleEndianList.
Require Import riscv.Utility.Monads. Require Import riscv.Utility.MonadNotations.
Require Import coqutil.Macros.unique.
Require Import bedrock2.LeakageSemantics.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Spec.Execute.
Require Import riscv.Platform.Run.
Require Import riscv.Platform.Memory.
Require Import riscv.Utility.PowerFunc.
Require Import coqutil.Decidable.
Require Import Coq.Program.Tactics.
Require Import coqutil.Tactics.rewr.
Require Import Coq.Bool.Bool.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.MetricPrimitives.
Require Import coqutil.Z.Lia.
Require Import compiler.util.Misc.
Require Import riscv.Utility.Utility.
Require Import coqutil.Z.BitOps.
Require Import compiler.util.Common.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.FlatImpConstraints.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.SeparationLogic.
Require Import bedrock2.Scalars.
Require Import coqutil.Tactics.Simp.
Require Export coqutil.Word.SimplWordExpr.
Require Import compiler.RiscvWordProperties.
Require Import compiler.eqexact.
Require Import compiler.on_hyp_containing.
Require Import coqutil.Z.bitblast.
Require Import coqutil.Z.prove_Zeq_bitwise.
Require Import compiler.RunInstruction.
Require Import compiler.DivisibleBy4.
Require Import compiler.MetricsToRiscv.
Require Export compiler.regs_initialized.
Require Import bedrock2.MetricCosts.
Require Import riscv.Spec.LeakageOfInstr.

Require Import coqutil.Word.Interface.
Local Hint Mode Word.Interface.word - : typeclass_instances.

Import Utility.

Local Open Scope ilist_scope.
Local Open Scope Z_scope.

Set Implicit Arguments.

Local Arguments Z.mul: simpl never.
Local Arguments Z.add: simpl never.
Local Arguments Z.of_nat: simpl never.
Local Arguments Z.modulo : simpl never.
Local Arguments Z.pow: simpl never.
Local Arguments Z.sub: simpl never.

Arguments run1: simpl never.

Arguments compile_store: simpl never.
Arguments compile_load: simpl never.

Class bitwidth_iset(width: Z)(iset: InstructionSet): Prop :=
  bitwidth_matches: bitwidth iset = width.

Section WithParameters.
  Context {iset: InstructionSet}.
  Context {width} {BW: Bitwidth width} {word: word.word width}.
  Context {locals: map.map Z word}.

  Context {pos_map: map.map String.string Z}.
  Context (compile_ext_call: pos_map -> Z -> Z -> stmt Z -> list Instruction).
  Context (leak_ext_call: word -> pos_map -> Z -> Z -> stmt Z -> list word -> list LeakageEvent).
  Context {word_ok: word.ok word}.
  Context {mem: map.map word byte}.
  Context {env: map.map String.string (list Z * list Z * stmt Z)}.
  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgramWithLeakage M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {ext_spec: LeakageSemantics.ExtSpec}.

  Definition runsTo{BWM: bitwidth_iset width iset}: (* BWM is unused, but makes iset inferrable *)
    MetricRiscvMachine -> (MetricRiscvMachine -> Prop) -> Prop :=
    runsTo (mcomp_sat (run1 iset)).

  Definition function{BWM: bitwidth_iset width iset}(base: word)(finfo: pos_map)
             (fname: String.string)(impl : list Z * list Z * stmt Z): mem -> Prop :=
    match map.get finfo fname with
    | Some pos =>
      program iset (word.add base (word.of_Z pos))
              (compile_function iset compile_ext_call finfo pos impl)
    | _ => emp False
    end.

  (* Note: This definition would not be usable in the same way if we wanted to support
     recursive functions, because separation logic would prevent us from mentioning
     the snippet of code being run twice (once in [program initialL.(getPc) insts] and
     a second time inside [functions]).
     To avoid this double mentioning, we will remove the function being called from the
     list of functions before entering the body of the function. *)
  Definition functions{BWM: bitwidth_iset width iset}(base: word)(rel_positions: pos_map):
    env -> mem -> Prop :=
    map.fold (fun P fname fbody => (function base rel_positions fname fbody * P)%sep) (emp True).

  (*
     high addresses!             ...
                      p_sp   --> mod_var_0 of previous function call arg0
                                 stack scratch space last byte
                                 ...
        new_sp + stackoffset --> stack scratch space first byte
                                 argn
                                 ...
                                 arg0
                                 retn
                                 ...
                                 ret0
                                 ra
                                 mod_var_n
                                 ...
                      new_sp --> mod_var_0
     low addresses               ...
  *)

  (* measured in words, needs to be multiplied by 4 or 8 *)
  Definition framelength{BWM: bitwidth_iset width iset}: list Z * list Z * stmt Z -> Z :=
    fun '(argvars, resvars, body) =>
      stackalloc_words iset body +
      1 + (Z.of_nat (List.length (ListSet.list_diff Z.eqb (modVars_as_list Z.eqb body) resvars))).

  (* "fits_stack M N env s" means that statement s will not run out of stack space
     if there are M words available before the stack pointer (in current frame),
     and there are N words available after the stack pointer (for the frames of the
     callees). Note:
     - This predicate cannot be proved for recursive functions
     - Measured in words, needs to be multiplied by 4 or 8 *)
  Inductive fits_stack{BWM: bitwidth_iset width iset}: Z -> Z -> env -> stmt Z -> Prop :=
  | fits_stack_load: forall M N e sz x y o,
      0 <= M -> 0 <= N ->
      fits_stack M N e (SLoad sz x y o)
  | fits_stack_store: forall M N e sz x y o,
      0 <= M -> 0 <= N ->
      fits_stack M N e (SStore sz x y o)
  | fits_stack_inlinetable: forall M N e sz x table i,
      0 <= M -> 0 <= N ->
      fits_stack M N e (SInlinetable sz x table i)
  | fits_stack_stackalloc: forall M N e x n body,
      0 <= M ->
      0 <= n ->
      n mod (Memory.bytes_per_word (Decode.bitwidth iset)) = 0 ->
      fits_stack (M - n / (Memory.bytes_per_word (Decode.bitwidth iset))) N e body ->
      fits_stack M N e (SStackalloc x n body)
  | fits_stack_lit: forall M N e x v,
      0 <= M -> 0 <= N ->
      fits_stack M N e (SLit x v)
  | fits_stack_op: forall M N e op x y z,
      0 <= M -> 0 <= N ->
      fits_stack M N e (SOp x op y z)
  | fits_stack_set: forall M N e x y,
      0 <= M -> 0 <= N ->
      fits_stack M N e (SSet x y)
  | fits_stack_if: forall M N e c s1 s2,
      fits_stack M N e s1 ->
      fits_stack M N e s2 ->
      fits_stack M N e (SIf c s1 s2)
  | fits_stack_loop: forall M N e c s1 s2,
      fits_stack M N e s1 ->
      fits_stack M N e s2 ->
      fits_stack M N e (SLoop s1 c s2)
  | fits_stack_seq: forall M N e s1 s2,
      fits_stack M N e s1 ->
      fits_stack M N e s2 ->
      fits_stack M N e (SSeq s1 s2)
  | fits_stack_skip: forall M N e,
      0 <= M -> 0 <= N ->
      fits_stack M N e SSkip
  | fits_stack_call: forall M N e binds fname args argnames retnames body,
      0 <= M ->
      map.get e fname = Some (argnames, retnames, body) ->
      fits_stack (stackalloc_words iset body)
                 (N - framelength (argnames, retnames, body))
                 (map.remove e fname) body ->
      fits_stack M N e (SCall binds fname args)
  | fits_stack_interact: forall M N e binds act args,
      0 <= M -> 0 <= N ->
      (* TODO it would be nice to allow external functions to use the stack too by requiring
         stack_needed act <= N *)
      fits_stack M N e (SInteract binds act args).

  Lemma stackalloc_words_nonneg{BWM: bitwidth_iset width iset}: forall s,
      0 <= stackalloc_words iset s.
  Proof using .
    clear.
    assert (Memory.bytes_per_word (bitwidth iset) = 4 \/ Memory.bytes_per_word (bitwidth iset) = 8). {
      unfold Memory.bytes_per_word. destruct iset; cbv; auto.
    }
    induction s; simpl; Z.div_mod_to_equations; blia.
  Qed.

  Lemma framesize_nonneg{BWM: bitwidth_iset width iset}: forall argvars resvars body,
      0 <= framelength (argvars, resvars, body).
  Proof using BW.
    clear -BW.
    intros. unfold framelength.
    pose proof (stackalloc_words_nonneg body).
    assert (bytes_per_word = 4 \/ bytes_per_word = 8). {
      unfold bytes_per_word. destruct width_cases as [E | E]; rewrite E; cbv; auto.
    }
    Z.div_mod_to_equations.
    blia.
  Qed.

  Lemma fits_stack_nonneg{BWM: bitwidth_iset width iset}: forall M N e s,
      fits_stack M N e s ->
      0 <= M /\ 0 <= N.
  Proof using BW.
    induction 1; try blia. pose proof (framesize_nonneg argnames retnames body). blia.
  Qed.

  (* Ghost state used to describe low-level state introduced by the compiler.
     Called "ghost constants" because after executing a piece of code emitted by
     the compiler, these values should still be the same.
     Note, though, that when focusing on a sub-statement (i.e. when invoking the IH)
     the ghost constants will change: instructions are shoveled from insts into the frame,
     the amount of available stack shrinks, the stack pointer decreases, and if we're
     in a function call, the function being called is removed from funnames so that
     it can't be recursively called again. *)
  Record GhostConsts := {
    (* stack pointer *)
    p_sp: word;
    (* remaining number of available stack words (not including those in current frame) *)
    rem_stackwords: Z;
    (* remaining number of available stack words inside the current frame *)
    rem_framewords: Z;
    (* data frame *)
    dframe: mem -> Prop;
    (* all executable memory (ie xframe, insts and the functions), but potentially in a
       less-unfolded way to enable more concise computed postconditions *)
    allx: mem -> Prop;
  }.

  Definition goodMachine{BWM: bitwidth_iset width iset}
      (* high-level state ... *)
      (t: list LogItem)(m: mem)(l: locals)
      (* ... plus ghost constants ... *)
      (g: GhostConsts)
      (* ... equals low-level state *)
      (lo: MetricRiscvMachine): Prop :=
    (* registers: *)
    map.extends lo.(getRegs) l /\
    map.forall_keys valid_FlatImp_var l /\
    map.get lo.(getRegs) RegisterNames.sp = Some g.(p_sp) /\
    regs_initialized lo.(getRegs) /\
    (* pc: *)
    lo.(getNextPc) = word.add lo.(getPc) (word.of_Z 4) /\
    (* memory: *)
    subset (footpr g.(allx)) (of_list lo.(getXAddrs)) /\
    (exists stack_trash frame_trash,
        (* Note: direction of equalities is deliberate:
           When destructing a goodMachine that comes from an IH,
           this direction of the equalities will be
           "length of new thing equals old known value from before IH",
           so rewriting with these equalities will result in
           replacing newer values by older, "more basic" ones *)
        Z.of_nat (List.length stack_trash) = g.(rem_stackwords) /\
        Z.of_nat (List.length frame_trash) = g.(rem_framewords) /\
        (g.(allx) * g.(dframe) * eq m *
         word_array (word.sub g.(p_sp) (word.of_Z (bytes_per_word * g.(rem_stackwords))))
                    stack_trash *
         word_array g.(p_sp) frame_trash)%sep lo.(getMem)) /\
    (* trace: *)
    lo.(getLog) = t /\
    (* misc: *)
    valid_machine lo.

  Definition good_e_impl(e_impl: env)(finfo: pos_map) :=
    forall f (fun_impl: list Z * list Z * stmt Z),
      map.get e_impl f = Some fun_impl ->
      valid_FlatImp_fun fun_impl /\
      let '(argnames, retnames, fbody) := fun_impl in
      exists pos, map.get finfo f = Some pos /\ pos mod 4 = 0.

  Local Notation stmt := (stmt Z).
  Local Notation exec pick_sp e := (@exec _ _ _ _ _ _ _ _ PostSpill isRegZ e pick_sp).
  
  (* note: [e_impl_reduced] and [funnames] will shrink one function at a time each time
     we enter a new function body, to make sure functions cannot call themselves, while
     [e_impl] and [e_pos] remain the same throughout because that's mandated by
     [FlatImp.exec] and [compile_stmt], respectively *)
  Definition compiles_FlatToRiscv_correctly{BWM: bitwidth_iset width iset}
    (f: pos_map -> Z -> Z -> stmt -> list Instruction)
    (s: stmt): Prop :=
    forall e_impl_full pick_sp1 initialK initialTrace initialMH initialRegsH initialMetricsH postH,
    exec pick_sp1 e_impl_full s initialK initialTrace (initialMH: mem) initialRegsH initialMetricsH postH ->
    forall g e_impl e_pos program_base insts xframe (initialL: MetricRiscvMachine) pos initialKL cont,
    map.extends e_impl_full e_impl ->
    good_e_impl e_impl e_pos ->
    fits_stack g.(rem_framewords) g.(rem_stackwords) e_impl s ->
    f e_pos pos (bytes_per_word * g.(rem_framewords)) s = insts ->
    uses_standard_arg_regs s ->
    valid_FlatImp_vars s ->
    pos mod 4 = 0 ->
    word.unsigned program_base mod 4 = 0 ->
    initialL.(getPc) = word.add program_base (word.of_Z pos) ->
    initialL.(getTrace) = Some initialKL ->
    iff1 g.(allx) (xframe *
                   program iset (word.add program_base (word.of_Z pos)) insts *
                   functions program_base e_pos e_impl)%sep ->
    goodMachine initialTrace initialMH initialRegsH g initialL ->
    (forall k, pick_sp1 (k ++ initialK) = snd (stmt_leakage iset compile_ext_call leak_ext_call e_pos e_impl_full program_base
                                                    (s, rev k, rev initialKL, pos, g.(p_sp), bytes_per_word * rem_framewords g, cont k))) ->
    runsTo initialL (fun finalL => exists finalK finalTrace finalMH finalRegsH finalMetricsH,
         postH finalK finalTrace finalMH finalRegsH finalMetricsH /\
         finalL.(getPc) = word.add initialL.(getPc)
                                   (word.of_Z (4 * Z.of_nat (List.length insts))) /\
         map.only_differ initialL.(getRegs)
                 (union (of_list (modVars_as_list Z.eqb s)) (singleton_set RegisterNames.ra))
                 finalL.(getRegs) /\
         (finalL.(getMetrics) - initialL.(getMetrics) <=
            lowerMetrics (finalMetricsH - initialMetricsH))%metricsL /\
           (exists kH'' finalKL,
               finalK = kH'' ++ initialK /\
                 finalL.(getTrace) = Some finalKL /\
                 forall k cont,
                   stmt_leakage iset compile_ext_call leak_ext_call e_pos e_impl_full program_base
                     (s, rev kH'' ++ k, rev initialKL, pos, g.(p_sp), bytes_per_word * rem_framewords g, cont) =
                     cont (rev kH'') (rev finalKL)) /\
           goodMachine finalTrace finalMH finalRegsH g finalL).

End WithParameters.

Ltac simpl_g_get :=
  cbn [p_sp rem_framewords rem_stackwords dframe allx] in *.

Ltac simpl_bools :=
  repeat match goal with
         | H : ?x = false |- _ =>
           progress rewrite H in *
         | H : ?x = true |- _ =>
           progress rewrite H in *
         | |- context [negb true] => progress unfold negb
         | |- context [negb false] => progress unfold negb
         | H : negb ?x = true |- _ =>
           let H' := fresh in
           assert (x = false) as H' by (eapply negb_true_iff; eauto);
           clear H
         | H : negb ?x = false |- _ =>
           let H' := fresh in
           assert (x = true) as H' by (eapply negb_false_iff; eauto);
           clear H
         end.

Section FlatToRiscv1.
  Context {iset: InstructionSet}.
  Context {fun_info: map.map String.string Z}.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context (compile_ext_call: fun_info -> Z -> Z -> stmt Z -> list Instruction).
  Context (leak_ext_call: fun_info -> Z -> Z -> stmt Z -> list word -> list LeakageEvent).
  Context {word_ok: word.ok word}.
  Context {locals: map.map Z word}.
  Context {mem: map.map word byte}.
  Context {env: map.map String.string (list Z * list Z * stmt Z)}.
  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgramWithLeakage M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {ext_spec: Semantics.ExtSpec}.
  Context {word_riscv_ok: word.riscv_ok word}.
  Context {locals_ok: map.ok locals}.
  Context {mem_ok: map.ok mem}.
  Context {PR: MetricPrimitives PRParams}.

  Local Notation RiscvMachineL := MetricRiscvMachine.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Lemma reduce_eq_to_sub_and_lt: forall (y z: word),
      word.eqb y z = word.ltu (word.sub y z) (word.of_Z 1).
  Proof using BW word_ok.
    intros.
    rewrite word.unsigned_eqb.
    rewrite word.unsigned_ltu.
    rewrite word.unsigned_sub.
    rewrite word.unsigned_of_Z.
    pose proof (word.unsigned_range y) as Ry.
    pose proof (word.unsigned_range z) as Rz.
    remember (word.unsigned y) as a; clear Heqa.
    remember (word.unsigned z) as b; clear Heqb.
    assert (1 < 2 ^ width). {
      destruct width_cases as [E | E]; rewrite E; reflexivity.
    }
    destruct (Z.eqb_spec a b).
    - subst a. rewrite Z.sub_diag. unfold word.wrap. rewrite Z.mod_0_l by blia.
      rewrite Z.mod_small; [reflexivity|blia].
    - unfold word.wrap. rewrite (Z.mod_small 1) by blia.
      destruct (Z.ltb_spec ((a - b) mod 2 ^ width) 1); [exfalso|reflexivity].
      pose proof (Z.mod_pos_bound (a - b) (2 ^ width)).
      assert ((a - b) mod 2 ^ width = 0) as A by blia.
      apply Znumtheory.Zmod_divide in A; [|blia].
      unfold Z.divide in A.
      destruct A as [k A].
      assert (k <> 0); Lia.nia.
  Qed.

  (* Set Printing Projections.
     Prints some implicit arguments it shouldn't print :(
     COQBUG https://github.com/coq/coq/issues/9814 *)

  Ltac simulate''_step :=
    first (* not everyone wants these: *)
          [ eapply go_loadByte       ; [sidecondition..|]
          | eapply go_storeByte      ; [sidecondition..|]
          | eapply go_loadHalf       ; [sidecondition..|]
          | eapply go_storeHalf      ; [sidecondition..|]
          | eapply go_loadWord       ; [sidecondition..|]
          | eapply go_storeWord      ; [sidecondition..|]
          | eapply go_loadDouble     ; [sidecondition..|]
          | eapply go_storeDouble    ; [sidecondition..|]
          (* reuse defaults which everyone wants: *)
          | simulate_step
          | simpl_modu4_0 ].

  Ltac simulate'' := repeat simulate''_step.

  Context {BWM: bitwidth_iset width iset}.

  Lemma go_load: forall sz (x a ofs: Z) (addr v: word) (initialL: RiscvMachineL) post f,
      valid_register x ->
      valid_register a ->
      map.get initialL.(getRegs) a = Some addr ->
      Memory.load sz (getMem initialL) (word.add addr (word.of_Z ofs)) = Some v ->
      mcomp_sat (f tt)
                (withRegs (map.put initialL.(getRegs) x v) (updateMetrics (addMetricLoads 1) initialL)) post ->
      mcomp_sat (Bind (execute (compile_load iset sz x a ofs)) f) initialL post.
  Proof using word_ok PR BWM.
    clear word_riscv_ok mem_ok locals_ok leak_ext_call ext_spec.
    cbv [compile_load Memory.bytes_per Memory.bytes_per_word Memory.load]; intros *.
    destruct load_Z eqn:E; inversion_clear 4; intros Hpost.
    rewrite bitwidth_matches; destruct sz, width_cases as [-> | -> ]; intros; simulate'';
      cbv [MachineWidth_XLEN loadByte uInt8ToReg loadHalf uInt16ToReg loadWord uInt32ToReg int32ToReg loadDouble int64ToReg];
      try change (Z.to_nat ((32 + 7) / 8)) with 4%nat in *;
      try change (Z.to_nat ((64 + 7) / 8)) with 8%nat in *;
      rewrite ?E; trivial;
      try setoid_rewrite (tuple.to_list_of_list (le_split 1 z));
      try setoid_rewrite (tuple.to_list_of_list (le_split 2 z));
      try setoid_rewrite (tuple.to_list_of_list (le_split 4 z));
      try setoid_rewrite (tuple.to_list_of_list (le_split 8 z));
      rewrite ?LittleEndianList.le_combine_split; simpl_word_exprs word_ok;
      destruct initialL; eqapply Hpost; f_equal; f_equal.
      all: rewrite Z.mod_small; trivial; eapply load_Z_bound in E; blia.
  Qed.

  Lemma go_leak_load: forall sz (x a ofs: Z) (addr: word) (initialL: RiscvMachineL) post (f : option LeakageEvent -> M unit),
      valid_register a ->
      map.get initialL.(getRegs) a = Some addr ->
      mcomp_sat (f (Some (executeInstr (compile_load iset sz x a ofs) (leak_load iset sz addr)))) initialL post ->
      mcomp_sat (Bind (leakage_of_instr Machine.getRegister (compile_load iset sz x a ofs)) f) initialL post.
  Proof.
    unfold leakage_of_instr, leakage_of_instr_I, leak_load, compile_load, Memory.bytes_per, Memory.bytes_per_word.
    rewrite bitwidth_matches.
    destruct width_cases as [E | E];
      (* note: "rewrite E" does not work because "width" also appears in the type of "word",
         but we don't need to rewrite in the type of word, only in the type of the tuple,
         which works if we do it before intro'ing it *)
      (destruct (width =? 32));
      intros; destruct sz;
      simulate'';
      eassumption.
  Qed.

  Arguments invalidateWrittenXAddrs: simpl never.

  Local Arguments HList.tuple.to_list : simpl never.
  Local Arguments HList.tuple.of_list : simpl never.
  Local Arguments LittleEndianList.le_split : simpl never.
  Lemma go_store: forall sz (x a ofs: Z) (addr v: word) (initialL: RiscvMachineL) m' post f,
      valid_register x ->
      valid_register a ->
      map.get initialL.(getRegs) x = Some v ->
      map.get initialL.(getRegs) a = Some addr ->
      bedrock2.Memory.store sz (getMem initialL) (word.add addr (word.of_Z ofs)) v = Some m' ->
      mcomp_sat (f tt) (withXAddrs (invalidateWrittenXAddrs
                                      (@Memory.bytes_per width sz) (word.add addr (word.of_Z ofs))
                                      (getXAddrs initialL))
                       (withMem m' (updateMetrics (addMetricStores 1) initialL))) post ->
      mcomp_sat (Bind (execute (compile_store iset sz a x ofs)) f) initialL post.
  Proof using PR BWM mem_ok word_ok.
    clear -PR BWM mem_ok word_ok.
    cbv [compile_store Memory.bytes_per Memory.bytes_per_word bedrock2.Memory.store store_Z]; intros *.
    destruct coqutil.Map.Memory.store_bytes eqn:E; inversion 5; subst m'; intros Hpost.
    rewrite bitwidth_matches; destruct sz, width_cases as [-> | -> ]; intros; simulate'';
      cbv [MachineWidth_XLEN storeByte storeHalf storeWord storeDouble store_bytes];
      try change (Z.to_nat ((32 + 7) / 8)) with 4%nat in *;
      try change (Z.to_nat ((64 + 7) / 8)) with 8%nat in *; first
      [ setoid_rewrite (tuple.to_list_of_list (le_split 1 (word.unsigned v)))
      | setoid_rewrite (tuple.to_list_of_list (le_split 2 (word.unsigned v)))
      | setoid_rewrite (tuple.to_list_of_list (le_split 4 (word.unsigned v)))
      | setoid_rewrite (tuple.to_list_of_list (le_split 8 (word.unsigned v))) | idtac ];
      rewrite ?E; trivial.
  Qed.

  Lemma go_leak_store: forall sz (x a ofs: Z) (addr: word) (initialL: RiscvMachineL) post f,
    valid_register a ->
    map.get initialL.(getRegs) a = Some addr ->
    mcomp_sat (f (Some (executeInstr (compile_store iset sz a x ofs) (leak_store iset sz addr)))) initialL post ->
    mcomp_sat (Bind (leakage_of_instr Machine.getRegister (compile_store iset sz a x ofs)) f) initialL post.
  Proof.
    unfold leakage_of_instr, leakage_of_instr_I, leak_store, compile_store, Memory.bytes_per, Memory.bytes_per_word.
    rewrite bitwidth_matches.
    destruct width_cases as [E | E];
      (* note: "rewrite E" does not work because "width" also appears in the type of "word",
         but we don't need to rewrite in the type of word, only in the type of the tuple,
         which works if we do it before intro'ing it *)
      (destruct (width =? 32));
      intros; destruct sz;
      simulate'';
      eassumption.
  Qed.

  Lemma run_compile_load: forall sz: Syntax.access_size,
      run_Load_spec iset (@Memory.bytes_per width sz) (compile_load iset sz) id.
  Proof using word_ok mem_ok PR BWM.
    intro sz. destruct sz; unfold compile_load; simpl.
    - refine (run_Lbu iset).
    - refine (run_Lhu iset).
    - rewrite bitwidth_matches.
      destruct width_cases as [E | E]; rewrite E at 2; simpl.
      + refine (run_Lw_unsigned iset E).
      + refine (run_Lwu iset).
    - rewrite bitwidth_matches.
      destruct width_cases as [E | E]; rewrite E at 2 3; simpl.
      + refine (run_Lw_unsigned iset E).
      + refine (run_Ld_unsigned iset E).
  Qed.

  Lemma run_compile_store: forall sz: Syntax.access_size,
      run_Store_spec iset (@Memory.bytes_per width sz) (compile_store iset sz).
  Proof using word_ok mem_ok PR BWM.
    intro sz. destruct sz; unfold compile_store; simpl.
    - refine (run_Sb iset).
    - refine (run_Sh iset).
    - refine (run_Sw iset).
    - rewrite bitwidth_matches.
      destruct width_cases as [E | E]; rewrite E at 2 3; simpl.
      + refine (run_Sw iset).
      + refine (run_Sd iset).
  Qed.

  (* almost the same as run_compile_load, but not using tuples nor ptsto_bytes or
     Memory.bytes_per, but using ptsto_word instead *)
  Lemma run_load_word: forall (base addr v : word) (rd rs : Z) (ofs : Z)
                              (initialL : RiscvMachineL) (Exec R Rexec : mem -> Prop),
      valid_register rd ->
      valid_register rs ->
      getNextPc initialL = word.add (getPc initialL) (word.of_Z 4) ->
      map.get (getRegs initialL) rs = Some base ->
      addr = word.add base (word.of_Z ofs) ->
      subset (footpr Exec) (of_list initialL.(getXAddrs)) ->
      iff1 Exec (program iset initialL.(getPc)
                   [[compile_load iset Syntax.access_size.word rd rs ofs]] * Rexec)%sep ->
      (Exec * ptsto_word addr v * R)%sep (getMem initialL) ->
      valid_machine initialL ->
      mcomp_sat (run1 iset) initialL
         (fun finalL : RiscvMachineL =>
            getRegs finalL = map.put (getRegs initialL) rd v /\
            getLog finalL = getLog initialL /\
            getXAddrs finalL = getXAddrs initialL /\
            getMem finalL = getMem initialL /\
            getPc finalL = getNextPc initialL /\
            getNextPc finalL = word.add (getPc finalL) (word.of_Z 4) /\
            getMetrics finalL = addMetricInstructions 1 (addMetricLoads 2 (getMetrics initialL)) /\
            getTrace finalL = option_map (cons (executeInstr (compile_load iset Syntax.access_size.word rd rs ofs) (leak_load iset Syntax.access_size.word base))) (option_map (cons (fetchInstr initialL.(getPc))) initialL.(getTrace)) /\
            valid_machine finalL).
  Proof using word_ok mem_ok PR BWM.
    clear word_riscv_ok locals_ok leak_ext_call ext_spec.
    cbv [compile_load scalar truncated_word truncated_scalar]; rewrite bitwidth_matches; case BW as [ [ -> | -> ] ];
      try change (Z.eqb _ _) with true; try change (Z.eqb _ _) with false;
      try change (bytes_per _) with 4%nat; try change (bytes_per _) with 8%nat;
      cbv match; intros.
    { eapply mcomp_sat_weaken; cycle 1.
      1: eapply run_Lw_unsigned; cycle -3. { etransitivity. 1:eassumption. ecancel. }
      all : eassumption||trivial.
      1:erewrite (tuple.to_list_of_list (le_split 4 _)); ecancel_assumption.
      cbv beta. intros. simp. repeat split; try assumption.
      + etransitivity. 1: eassumption. unfold id.
        erewrite (tuple.to_list_of_list (le_split 4 _)), le_combine_split, word.wrap_unsigned, word.of_Z_unsigned; trivial.
      + etransitivity. 1: eassumption. cbv [final_trace concrete_leakage_of_instr compile_load leak_load].
        rewrite bitwidth_matches; simpl. rewrite Z.eqb_refl. reflexivity. }
    { eapply mcomp_sat_weaken; cycle 1.
      1: eapply run_Ld_unsigned; cycle -3. { etransitivity. 1:eassumption. ecancel. }
      all : eassumption||trivial.
      1:erewrite (tuple.to_list_of_list (le_split 8 _)); ecancel_assumption.
      cbv beta. intros. simp. repeat split; try assumption.
      + etransitivity. 1: eassumption. unfold id.
        erewrite (tuple.to_list_of_list (le_split 8 _)), le_combine_split, word.wrap_unsigned, word.of_Z_unsigned; trivial.
      + etransitivity. 1: eassumption. cbv [final_trace concrete_leakage_of_instr compile_load leak_load].
        rewrite bitwidth_matches; simpl. rewrite Z.eqb_refl. reflexivity. }
  Qed.

  (* almost the same as run_compile_store, but not using tuples nor ptsto_bytes or
     Memory.bytes_per, but using ptsto_word instead *)
  Lemma run_store_word: forall (base addr v_new : word) (v_old : word) (rs1 rs2 : Z)
              (ofs : Z) (initialL : RiscvMachineL) (Exec Rdata Rexec : mem -> Prop),
      valid_register rs1 ->
      valid_register rs2 ->
      getNextPc initialL = word.add (getPc initialL) (word.of_Z 4) ->
      map.get (getRegs initialL) rs1 = Some base ->
      map.get (getRegs initialL) rs2 = Some v_new ->
      addr = word.add base (word.of_Z ofs) ->
      subset (footpr Exec) (of_list initialL.(getXAddrs)) ->
      iff1 Exec (program iset (getPc initialL)
                         [[compile_store iset Syntax.access_size.word rs1 rs2 ofs]] * Rexec)%sep ->
      (Exec * ptsto_word addr v_old * Rdata)%sep (getMem initialL) ->
      valid_machine initialL ->
      mcomp_sat (run1 iset) initialL
        (fun finalL : RiscvMachineL =>
           getRegs finalL = getRegs initialL /\
           getLog finalL = getLog initialL /\
           subset (footpr Exec) (of_list finalL.(getXAddrs)) /\
           (Exec * ptsto_word addr v_new * Rdata)%sep (getMem finalL) /\
           getPc finalL = getNextPc initialL /\
           getNextPc finalL = word.add (getPc finalL) (word.of_Z 4) /\
           getMetrics finalL = addMetricInstructions 1 (addMetricStores 1 (addMetricLoads 1 (getMetrics initialL))) /\
           getTrace finalL = option_map (cons (executeInstr (compile_store iset Syntax.access_size.word rs1 rs2 ofs) (leak_store iset Syntax.access_size.word base))) (option_map (cons (fetchInstr initialL.(getPc))) initialL.(getTrace)) /\  
           valid_machine finalL).
  Proof using word_ok mem_ok PR BWM.
    clear word_riscv_ok locals_ok leak_ext_call ext_spec.
    cbv [compile_store scalar truncated_word truncated_scalar]; rewrite bitwidth_matches; case BW as [ [ -> | -> ] ];
      try change (Z.eqb _ _) with true; try change (Z.eqb _ _) with false;
      try change (bytes_per _) with 4%nat; try change (bytes_per _) with 8%nat;
      cbv match; intros.
    { eapply mcomp_sat_weaken; cycle 1.
      1: eapply run_Sw; cycle -3. { etransitivity. 1:eassumption. ecancel. }
      all : eassumption||trivial.
      1:erewrite (tuple.to_list_of_list (le_split 4 _)); ecancel_assumption.
      cbv beta. intros. simp. repeat split; try assumption.
      etransitivity. 1: eassumption.
      cbv [final_trace concrete_leakage_of_instr compile_load leak_store].
      rewrite bitwidth_matches; simpl. rewrite Z.eqb_refl. reflexivity. }
    { eapply mcomp_sat_weaken; cycle 1.
      1: eapply run_Sd; cycle -3. { etransitivity. 1:eassumption. ecancel. }
      all : eassumption||trivial.
      1:erewrite (tuple.to_list_of_list (le_split 8 _)); ecancel_assumption.
      cbv beta. intros. simp. repeat split; try assumption.
      etransitivity. 1: eassumption.
      cbv [final_trace concrete_leakage_of_instr compile_load leak_store].
      rewrite bitwidth_matches; simpl. rewrite Z.eqb_refl. reflexivity. }
  Qed.

  Lemma one_step: forall initialL P,
      mcomp_sat (run1 iset) initialL P ->
      runsTo initialL P.
  Proof using .
    intros.
    eapply runsToStep; [eassumption|].
    intros.
    apply runsToDone. assumption.
  Qed.

  Lemma runsTo_det_step_with_valid_machine: forall initialL midL (P : RiscvMachineL -> Prop),
      valid_machine initialL ->
      mcomp_sat (Run.run1 iset) initialL (eq midL) ->
      (valid_machine midL -> runsTo midL P) ->
      runsTo initialL P.
  Proof using PR.
 intros.
    eapply runsToStep with (midset := fun m' => m' = midL /\ valid_machine m').
    - eapply run1_get_sane; try eassumption.
      intros. subst. auto.
    - intros ? (? & ?). subst. eapply H1. assumption.
  Qed.

  Lemma store_bytes_preserves_footprint: forall n a v (m m': mem),
      riscv.Platform.Memory.store_bytes n m a v = Some m' ->
      map.same_domain m m'.
  Proof using word_ok mem_ok.
    intros; eapply riscv.Platform.Memory.store_bytes_preserves_domain; eauto.
  Qed.

  Lemma seplog_subst_eq{A B R: mem -> Prop} {mL mH: mem}
      (H: A mL)
      (H0: iff1 A (R * eq mH)%sep)
      (H1: B mH):
      (B * R)%sep mL.
  Proof using word_ok mem_ok.
    unfold iff1 in *.
    destruct (H0 mL) as [P1 P2]. specialize (P1 H).
    apply sep_comm.
    unfold sep in *.
    destruct P1 as (mR & mH' & P11 & P12 & P13). subst mH'. eauto.
  Qed.

  Lemma ptsto_instr_compile4bytes: forall l addr,
      word.unsigned addr mod 4 = 0 ->
      iff1 (ptsto_instr iset addr (compile4bytes l))
           (array ptsto (word.of_Z 1) addr
                  [nth 0 l Byte.x00; nth 1 l Byte.x00; nth 2 l Byte.x00; nth 3 l Byte.x00]).
  Proof using BW word_ok mem_ok.
    clear - BW word_ok mem_ok.
    intros. unfold compile4bytes, ptsto_instr, truncated_scalar.
    change 4%nat with (length [nth 0 l Byte.x00; nth 1 l Byte.x00; nth 2 l Byte.x00; nth 3 l Byte.x00]).
    rewrite LittleEndian.combine_of_list.
    cbn.
    unfold Encode.encode_Invalid.
    rewrite bitSlice_all_nonneg. 2: cbv; discriminate. 2: apply LittleEndianList.le_combine_bound.
    rewrite LittleEndianList.split_le_combine' by trivial.
    rewrite <-array1_iff_eq_of_list_word_at; trivial.
    2: { destruct BW as [ [ -> | -> ] ]; cbv; discriminate. }
    cbn.
    wcancel.
    cbn [seps].
    rewrite !sep_emp_emp.
    apply RunInstruction.iff1_emp; intuition idtac.
    unfold valid_InvalidInstruction.
    right.
    eexists. split. 2: reflexivity.
    apply LittleEndianList.le_combine_bound.
  Qed.

  Lemma program_compile_byte_list_array: forall instrs table addr,
      instrs = compile_byte_list table ->
      word.unsigned addr mod 4 = 0 ->
      exists padding,
        iff1 (program iset addr instrs)
             (array ptsto (word.of_Z 1) addr (table ++ padding)).
  Proof using BW word_ok mem_ok.
    clear -BW word_ok mem_ok.
    induction instrs; intros.
    - exists []. simpl. repeat (destruct table; try discriminate). reflexivity.
    - rename a into inst0.
      destruct table as [|b0 table]. 1: discriminate.
      destruct table as [|b1 table]. {
        destruct instrs. 2: discriminate. simpl in *. simp.
        exists [Byte.x00; Byte.x00; Byte.x00].
        rewrite ptsto_instr_compile4bytes by assumption. simpl.
        cancel.
      }
      destruct table as [|b2 table]. {
        destruct instrs. 2: discriminate. simpl in *. simp.
        exists [Byte.x00; Byte.x00].
        rewrite ptsto_instr_compile4bytes by assumption. simpl.
        cancel.
      }
      destruct table as [|b3 table]. {
        destruct instrs. 2: discriminate. simpl in *. simp.
        exists [Byte.x00].
        rewrite ptsto_instr_compile4bytes by assumption. simpl.
        cancel.
      }
      simpl in *. simp.
      specialize (IHinstrs _ (word.add addr (word.of_Z 4)) eq_refl).
      destruct IHinstrs as [padding IH]. 1: solve_divisibleBy4.
      exists padding.
      rewrite IH.
      rewrite ptsto_instr_compile4bytes by assumption.
      simpl.
      wcancel.
  Qed.

  Lemma array_to_of_list_word_at: forall l addr (m: mem),
      array ptsto (word.of_Z 1) addr l m ->
      m = OfListWord.map.of_list_word_at addr l.
  Proof using word_ok mem_ok.
    induction l; intros.
    - unfold OfListWord.map.of_list_word_at, OfListWord.map.of_list_word. simpl in *.
      unfold emp, MapKeys.map.map_keys in *. simp. rewrite map.fold_empty. reflexivity.
    - simpl in *. unfold sep in H. simp.
      specialize (IHl _ _ Hp2). unfold map.split in *. unfold ptsto in Hp1.
      subst. simp.
      apply map.map_ext. intro k.
      rewrite OfListWord.map.get_of_list_word_at.
      rewrite map.get_putmany_dec.
      rewrite OfListWord.map.get_of_list_word_at.
      rewrite map.get_put_dec.
      rewrite map.get_empty.
      unfold map.disjoint in *. rename Hp0p1 into D.
      specialize (D addr). rewrite map.get_put_same in D. specialize D with (1 := eq_refl).
      destr (word.eqb addr k).
      + ring_simplify (word.sub k k). rewrite word.unsigned_of_Z. simpl.
        destruct_one_match. 2: reflexivity.
        exfalso. eapply D.
        rewrite OfListWord.map.get_of_list_word_at. exact E.
      + replace (BinInt.Z.to_nat (word.unsigned (word.sub k addr))) with
            (S (BinInt.Z.to_nat (word.unsigned (word.sub k (word.add addr (word.of_Z 1)))))).
        * simpl. destruct_one_match; reflexivity.
        * destruct (BinInt.Z.to_nat (word.unsigned (word.sub k addr))) eqn: F.
          -- exfalso. apply E. apply (f_equal Z.of_nat) in F.
             rewrite Z2Nat.id in F. 2: {
               pose proof word.unsigned_range (word.sub k addr). blia.
             }
             apply (f_equal word.of_Z) in F.
             rewrite (word.of_Z_unsigned (word.sub k addr)) in F.
             rewrite <- word.add_0_r at 1. change (Z.of_nat 0) with 0 in F. rewrite <- F.
             ring.
          -- f_equal.
             pose proof word.unsigned_range (word.sub k addr).
             assert (Z.of_nat (S n) < 2 ^ width) by blia.
             apply (f_equal Z.of_nat) in F.
             rewrite Z2Nat.id in F by blia.
             apply (f_equal word.of_Z) in F.
             rewrite (word.of_Z_unsigned (word.sub k addr)) in F.
             ring_simplify (word.sub k (word.add addr (word.of_Z 1))).
             rewrite F.
             replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by blia.
             match goal with
             | |- Z.to_nat (word.unsigned ?x) = n => ring_simplify x
             end.
             rewrite word.unsigned_of_Z. unfold word.wrap.
             rewrite Z.mod_small by blia.
             blia.
  Qed.

  Lemma program_compile_byte_list: forall table addr,
      exists Padding,
        impl1 (program iset addr (compile_byte_list table))
              (Padding * (table$@addr)).
  Proof using BW word_ok mem_ok.
    clear - BW word_ok mem_ok.
    cbv [sepclause_of_map] in *.
    intros. destruct table as [|b0 bs].
    - simpl. exists (emp True).
      unfold OfListWord.map.of_list_word_at, OfListWord.map.of_list_word, MapKeys.map.map_keys.
      simpl. rewrite map.fold_empty.
      unfold impl1, sep, emp, map.split, map.disjoint. intros m H. simp.
      exists map.empty, map.empty. ssplit; auto.
      + rewrite map.putmany_empty_l. reflexivity.
      + intros. rewrite map.get_empty in H. discriminate.
    - destr (Z.eqb (word.unsigned addr mod 4) 0).
      + destruct (program_compile_byte_list_array (b0 :: bs) addr eq_refl E) as [padding P].
        exists (array ptsto (word.of_Z 1)
            (word.add addr (word.of_Z (word.unsigned (word.of_Z 1) * Z.of_nat (length (b0 :: bs))))) padding).
        rewrite P.
        rewrite array_append.
        rewrite sep_comm.
        unfold impl1.
        intros m A.
        unfold sep, map.split in *. simp. do 2 eexists. ssplit. 1: reflexivity. 1,2: assumption.
        symmetry. apply array_to_of_list_word_at. assumption.
      + exists (emp True).
        intros m C.
        replace (compile_byte_list (b0 :: bs))
           with (compile4bytes (b0 :: bs) :: compile_byte_list (tl (tl (tl bs)))) in C. 2: {
          destruct bs as [|b1 table]. 1: reflexivity.
          simpl in *.
          destruct table as [|b2 table]. 1: reflexivity.
          destruct table as [|b3 table]. 1: reflexivity.
          reflexivity.
        }
        simpl in C.
        apply invert_ptsto_instr in C. apply proj2 in C. congruence.
  Qed.

  Lemma shift_load_bytes_in_of_list_word: forall l (addr: word) n t index,
      coqutil.Map.Memory.load_bytes (map.of_list_word l) index n = Some t ->
      coqutil.Map.Memory.load_bytes (map.of_list_word_at addr l) (word.add addr index) n = Some t.
  Proof using word_ok mem_ok.
    cbv [coqutil.Map.Memory.load_bytes map.of_list_word_at Map.Memory.footprint]; intros.
    rewrite map_map in *; erewrite map_ext; [eassumption|].
    intros i; cbv beta.
    rewrite <-word.add_assoc, MapKeys.map.get_map_keys_always_invertible; trivial.
    intros k k' Hk.
    assert (word.sub (word.add addr k) addr = word.sub (word.add addr k') addr) as HH
      by (f_equal; assumption).
    ring_simplify in HH; exact HH.
  Qed.

  Lemma load_from_compile_byte_list: forall sz table index v R m addr,
    Memory.load sz (OfListWord.map.of_list_word table) index = Some v ->
    (program iset addr (compile_byte_list table) * R)%sep m ->
    Memory.load sz m (word.add addr index) = Some v.
  Proof using word_ok mem_ok BW.
    intros *. intros L M0.
    destruct (program_compile_byte_list table addr) as [Padding P].
    apply (Proper_sep_impl1 _ _ P R R) in M0; [|reflexivity]; clear P.
    revert L.
    unfold Memory.load, Memory.load_Z.
    destruct coqutil.Map.Memory.load_bytes eqn:E; inversion 1; subst.
    eapply shift_load_bytes_in_of_list_word in E.
    erewrite load_bytes_in_sep with (P:=(table$@addr)); try ecancel_assumption; trivial.
    intros ? <-; eassumption.
  Qed.

End FlatToRiscv1.

Ltac solve_valid_machine wordOk :=
  match goal with
  | H: valid_machine {| getMetrics := ?M |} |- valid_machine {| getMetrics := ?M |} =>
    eqexact H; f_equal; f_equal
  end;
  solve_word_eq wordOk.

Global Hint Resolve
     valid_FlatImp_var_implies_valid_register
     valid_FlatImp_vars_bcond_implies_valid_registers_bcond
: sidecondition_hints.

Ltac simulate'_step :=
  match goal with
  (* mentions definition only introduced in FlatToRiscvDef: *)
  | |- not_InvalidInstruction _ =>
    cbv [compile_load compile_store compile_bcond_by_inverting]; repeat destruct_one_match; exact I
  (* lemmas introduced only in this file: *)
  | |- mcomp_sat (Monads.Bind (Execute.execute (compile_load _ _ _ _ _)) _) _ _ =>
       eapply go_load; [ sidecondition.. | idtac ]
  | |- mcomp_sat (Monads.Bind (leakage_of_instr _ (compile_load _ _ _ _ _)) _) _ _ =>
       eapply go_leak_load; [ sidecondition.. | idtac ]                 
  | |- mcomp_sat (Monads.Bind (Execute.execute (compile_store _ _ _ _ _)) _) _ _ =>
       eapply go_store; [ sidecondition.. | idtac ]
  | |- mcomp_sat (Monads.Bind (leakage_of_instr _ (compile_store _ _ _ _ _)) _) _ _ =>
       eapply go_leak_store; [ sidecondition.. | idtac ]
  (* simulate_step from GoFlatToRiscv: *)
  | |- _ => simulate_step
  | |- _ => simpl_modu4_0
  end.

Ltac simulate' := repeat simulate'_step.

Ltac run1det :=
  eapply runsTo_det_step_with_valid_machine;
  [ assumption
  | simulate';
    match goal with
    | |- ?mid = ?RHS =>
      (* simpl RHS because mid will be instantiated to it and turn up again in the next step *)
      is_evar mid; simpl; reflexivity
    | |- _ => fail 10000 "simulate' did not go through completely"
    end
 | intros ].
