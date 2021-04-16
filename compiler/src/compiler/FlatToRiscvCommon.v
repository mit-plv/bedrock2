Require Import riscv.Utility.Monads. Require Import riscv.Utility.MonadNotations.
Require Import coqutil.Macros.unique.
Require Import coqutil.Tactics.ParamRecords.
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
Require Import compiler.FlatToRiscvDef.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.SeparationLogic.
Require Import bedrock2.Scalars.
Require Import coqutil.Tactics.Simp.
Require Export coqutil.Word.SimplWordExpr.
Require Import bedrock2.ptsto_bytes.
Require Import compiler.RiscvWordProperties.
Require Import compiler.eqexact.
Require Import compiler.on_hyp_containing.
Require Import coqutil.Z.bitblast.
Require Import coqutil.Z.prove_Zeq_bitwise.
Require Import compiler.RunInstruction.
Require Import compiler.DivisibleBy4.
Require Import compiler.MetricsToRiscv.

Require Import coqutil.Word.Interface.
Local Hint Mode Word.Interface.word - : typeclass_instances.

Import Utility.

Local Open Scope ilist_scope.
Local Open Scope Z_scope.

Set Implicit Arguments.

Export FlatToRiscvDef.FlatToRiscvDef.

Class parameters := {
  def_params :> FlatToRiscvDef.parameters;

  W :> Words;
  locals :> map.map Z word;
  mem :> map.map word byte;

  M: Type -> Type;
  MM :> Monad M;
  RVM :> RiscvProgram M word;
  PRParams :> PrimitivesParams M MetricRiscvMachine;

  ext_spec : list (mem * String.string * list word * (mem * list word)) ->
             mem -> String.string -> list word -> (mem -> list word -> Prop) -> Prop;
}.

Arguments Z.mul: simpl never.
Arguments Z.add: simpl never.
Arguments Z.of_nat: simpl never.
Arguments Z.modulo : simpl never.
Arguments Z.pow: simpl never.
Arguments Z.sub: simpl never.

Arguments run1: simpl never.

Arguments compile_store: simpl never.
Arguments compile_load: simpl never.

Section WithParameters.
  Context {p: parameters}.

  Instance Semantics_params: FlatImp.parameters Z := {|
    FlatImp.varname_eqb := Z.eqb;
    FlatImp.ext_spec := ext_spec;
  |}.

  Definition regs_initialized(regs: locals): Prop :=
    forall r : Z, 0 < r < 32 -> exists v : word, map.get regs r = Some v.

  Section WithLocalsOk.
    Context {locals_ok: map.ok locals}.

    Lemma regs_initialized_put: forall l x v,
        regs_initialized l ->
        regs_initialized (map.put l x v).
    Proof.
      unfold regs_initialized in *.
      intros.
      rewrite map.get_put_dec.
      destruct_one_match; eauto.
    Qed.

    Lemma preserve_regs_initialized_after_put: forall regs var val,
        regs_initialized regs ->
        regs_initialized (map.put regs var val).
    Proof.
      unfold regs_initialized. intros. specialize (H _ H0).
      rewrite map.get_put_dec. destruct_one_match; subst; eauto.
    Qed.

    Lemma preserve_regs_initialized_after_putmany_of_list_zip: forall vars vals (regs regs': locals),
        regs_initialized regs ->
        map.putmany_of_list_zip vars vals regs = Some regs' ->
        regs_initialized regs'.
    Proof.
      induction vars; intros.
      - simpl in H0. destruct vals; try discriminate.
        replace regs' with regs in * by congruence. assumption.
      - simpl in H0.
        destruct vals; try discriminate.
        eapply IHvars. 2: eassumption.
        eapply preserve_regs_initialized_after_put.
        eassumption.
    Qed.

  End WithLocalsOk.

  Definition runsTo: MetricRiscvMachine -> (MetricRiscvMachine -> Prop) -> Prop :=
    runsTo (mcomp_sat (run1 iset)).

  Definition function(base: word)(rel_positions: funname_env Z)
             (fname: String.string)(impl : list Z * list Z * stmt Z): mem -> Prop :=
    match map.get rel_positions fname with
    | Some pos => program iset (word.add base (word.of_Z pos)) (compile_function rel_positions pos impl)
    | _ => emp False
    end.

  (* Note: This definition would not be usable in the same way if we wanted to support
     recursive functions, because separation logic would prevent us from mentioning
     the snippet of code being run twice (once in [program initialL.(getPc) insts] and
     a second time inside [functions]).
     To avoid this double mentioning, we will remove the function being called from the
     list of functions before entering the body of the function. *)
  Definition functions(base: word)(rel_positions: funname_env Z): env -> mem -> Prop :=
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
  Definition framelength: list Z * list Z * stmt Z -> Z :=
    fun '(argvars, resvars, body) =>
      stackalloc_words body +
      let mod_vars := ListSet.list_union Z.eqb (modVars_as_list Z.eqb body) argvars in
      Z.of_nat (List.length argvars + List.length resvars + 1 + List.length mod_vars).

  (* "fits_stack M N env s" means that statement s will not run out of stack space
     if there are M words available before the stack pointer (in current frame),
     and there are N words available after the stack pointer (for the frames of the
     callees). Note:
     - This predicate cannot be proved for recursive functions
     - Measured in words, needs to be multiplied by 4 or 8 *)
  Inductive fits_stack: Z -> Z -> env -> stmt Z -> Prop :=
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
      fits_stack (stackalloc_words body)
                 (N - framelength (argnames, retnames, body))
                 (map.remove e fname) body ->
      fits_stack M N e (SCall binds fname args)
  | fits_stack_interact: forall M N e binds act args,
      0 <= M -> 0 <= N ->
      (* TODO it would be nice to allow external functions to use the stack too by requiring
         stack_needed act <= N *)
      fits_stack M N e (SInteract binds act args).

  Lemma stackalloc_words_nonneg: forall s,
      0 <= stackalloc_words s.
  Proof.
    assert (Memory.bytes_per_word (bitwidth iset) = 4 \/ Memory.bytes_per_word (bitwidth iset) = 8). {
      unfold Memory.bytes_per_word. destruct iset; cbv; auto.
    }
    induction s; simpl; Z.div_mod_to_equations; blia.
  Qed.

  Lemma framesize_nonneg: forall argvars resvars body,
      0 <= framelength (argvars, resvars, body).
  Proof.
    intros. unfold framelength.
    pose proof (stackalloc_words_nonneg body).
    assert (bytes_per_word = 4 \/ bytes_per_word = 8). {
      unfold bytes_per_word. destruct width_cases as [E | E]; rewrite E; cbv; auto.
    }
    Z.div_mod_to_equations.
    blia.
  Qed.

  Lemma fits_stack_nonneg: forall M N e s,
      fits_stack M N e s ->
      0 <= M /\ 0 <= N.
  Proof.
    induction 1; try blia. pose proof (@framesize_nonneg argnames retnames body). blia.
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
    p_sp: word;
    rem_stackwords: Z; (* remaining number of available stack words (not including those in current frame) *)
    rem_framewords: Z; (* remaining number of available stack words inside the current frame *)
    p_insts: word;
    insts: list Instruction;
    program_base: word;
    e_pos: funname_env Z;
    e_impl: env;
    dframe: mem -> Prop; (* data frame *)
    xframe: mem -> Prop; (* executable frame *)
  }.

  Definition goodMachine
      (* high-level state ... *)
      (t: list LogItem)(m: mem)(l: locals)
      (* ... plus ghost constants ... *)
      (g: GhostConsts)
      (* ... equals low-level state *)
      (lo: MetricRiscvMachine): Prop :=
    (* registers: *)
    map.extends lo.(getRegs) l /\
    (forall x v, map.get l x = Some v -> valid_FlatImp_var x) /\
    map.get lo.(getRegs) RegisterNames.sp = Some g.(p_sp) /\
    regs_initialized lo.(getRegs) /\
    (* pc: *)
    lo.(getNextPc) = word.add lo.(getPc) (word.of_Z 4) /\
    (* memory: *)
    subset (footpr (g.(xframe) *
                    program iset g.(p_insts) g.(insts) *
                    functions g.(program_base) g.(e_pos) g.(e_impl))%sep)
           (of_list lo.(getXAddrs)) /\
    (exists stack_trash,
        g.(rem_stackwords) = Z.of_nat (List.length stack_trash) - g.(rem_framewords) /\
        (g.(dframe) * g.(xframe) * eq m *
         word_array (word.sub g.(p_sp) (word.of_Z (bytes_per_word * g.(rem_stackwords)))) stack_trash *
         program iset g.(p_insts) g.(insts) *
         functions g.(program_base) g.(e_pos) g.(e_impl))%sep lo.(getMem)) /\
    (* trace: *)
    lo.(getLog) = t /\
    (* misc: *)
    valid_machine lo.

  Definition good_e_impl(e_impl: env)(e_pos: funname_env Z) :=
    forall f (fun_impl: list Z * list Z * stmt Z),
      map.get e_impl f = Some fun_impl ->
      valid_FlatImp_fun fun_impl /\
      exists pos, map.get e_pos f = Some pos /\ pos mod 4 = 0.

  Local Notation stmt := (stmt Z).

  (* note: [e_impl_reduced] and [funnames] will shrink one function at a time each time
     we enter a new function body, to make sure functions cannot call themselves, while
     [e_impl] and [e_pos] remain the same throughout because that's mandated by
     [FlatImp.exec] and [compile_stmt], respectively *)
  Definition compiles_FlatToRiscv_correctly
    (f: funname_env Z -> Z -> Z -> stmt -> list Instruction)
    (s: stmt): Prop :=
    forall e_impl_full initialTrace initialMH initialRegsH initialMetricsH postH,
    exec e_impl_full s initialTrace (initialMH: mem) initialRegsH initialMetricsH postH ->
    forall (g: GhostConsts) (initialL: MetricRiscvMachine) (pos: Z),
    map.extends e_impl_full g.(e_impl) ->
    good_e_impl g.(e_impl) g.(e_pos) ->
    fits_stack g.(rem_framewords) g.(rem_stackwords) g.(e_impl) s ->
    f g.(e_pos) pos (bytes_per_word * g.(rem_framewords)) s = g.(insts) ->
    stmt_not_too_big s ->
    valid_FlatImp_vars s ->
    pos mod 4 = 0 ->
    (word.unsigned g.(program_base)) mod 4 = 0 ->
    initialL.(getPc) = word.add g.(program_base) (word.of_Z pos) ->
    g.(p_insts)      = word.add g.(program_base) (word.of_Z pos) ->
    goodMachine initialTrace initialMH initialRegsH g initialL ->
    runsTo initialL (fun finalL => exists finalTrace finalMH finalRegsH finalMetricsH,
         postH finalTrace finalMH finalRegsH finalMetricsH /\
         finalL.(getPc) = word.add initialL.(getPc)
                                   (word.of_Z (4 * Z.of_nat (List.length g.(insts)))) /\
         map.only_differ initialL.(getRegs)
                 (union (of_list (modVars_as_list Z.eqb s)) (singleton_set RegisterNames.ra))
                 finalL.(getRegs) /\
         goodMachine finalTrace finalMH finalRegsH g finalL).

  Class assumptions: Prop := {
    bitwidth_matches: bitwidth iset = width;
    word_riscv_ok :> word.riscv_ok (@word W);
    locals_ok :> map.ok locals;
    mem_ok :> map.ok mem;
    funname_env_ok :> forall T, map.ok (funname_env T);
    PR :> MetricPrimitives PRParams;
  }.

End WithParameters.

Existing Instance Semantics_params.

Ltac simpl_g_get :=
  cbn [p_sp rem_framewords rem_stackwords p_insts insts program_base e_pos e_impl
            dframe xframe] in *.

Ltac solve_stmt_not_too_big :=
  lazymatch goal with
  | H: stmt_not_too_big _ |- stmt_not_too_big _ =>
    clear -H;
    unfold stmt_not_too_big in *;
    change (2 ^ 9)%Z with 512%Z in *;
    simpl stmt_size in H;
    repeat match goal with
           | s: stmt ?varname |- _ => unique pose proof (stmt_size_nonneg s)
           end;
    match goal with
    | |- ?SZ _ _ < _ => (* COQBUG https://github.com/coq/coq/issues/9268 *)
      change @stmt_size with SZ in *
    end;
    blia
  end.

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
  Context {p: unique! parameters}.
  Context {h: unique! assumptions}.

  Local Notation RiscvMachineL := MetricRiscvMachine.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Lemma reduce_eq_to_sub_and_lt: forall (y z: word),
      word.eqb y z = word.ltu (word.sub y z) (word.of_Z 1).
  Proof.
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

  Lemma go_load: forall sz (x a ofs: Z) (addr v: word) (initialL: RiscvMachineL) post f,
      valid_register x ->
      valid_register a ->
      map.get initialL.(getRegs) a = Some addr ->
      Memory.load sz (getMem initialL) (word.add addr (word.of_Z ofs)) = Some v ->
      mcomp_sat (f tt)
                (withRegs (map.put initialL.(getRegs) x v) (updateMetrics (addMetricLoads 1) initialL)) post ->
      mcomp_sat (Bind (execute (compile_load sz x a ofs)) f) initialL post.
  Proof.
    unfold compile_load, Memory.load, Memory.load_Z, Memory.bytes_per, Memory.bytes_per_word.
    rewrite bitwidth_matches.
    destruct width_cases as [E | E];
      (* note: "rewrite E" does not work because "width" also appears in the type of "word",
         but we don't need to rewrite in the type of word, only in the type of the tuple,
         which works if we do it before intro'ing it *)
      (destruct (width =? 32) eqn: E'; [apply Z.eqb_eq in E' | apply Z.eqb_neq in E']);
      try congruence;
      clear E';
      [set (nBytes := 4%nat) | set (nBytes := 8%nat)];
      replace (Z.to_nat ((width + 7) / 8)) with nBytes by (subst nBytes; rewrite E; reflexivity);
      subst nBytes;
      intros; destruct sz;
      try solve [
        unfold execute, ExecuteI.execute, ExecuteI64.execute, translate, DefaultRiscvState,
        Memory.load, Memory.load_Z in *;
        simp; simulate''; simpl; simpl_word_exprs word_ok; destruct initialL;
          try eassumption].
 Qed.

  Arguments invalidateWrittenXAddrs: simpl never.

  Lemma go_store: forall sz (x a ofs: Z) (addr v: word) (initialL: RiscvMachineL) m' post f,
      valid_register x ->
      valid_register a ->
      map.get initialL.(getRegs) x = Some v ->
      map.get initialL.(getRegs) a = Some addr ->
      Memory.store sz (getMem initialL) (word.add addr (word.of_Z ofs)) v = Some m' ->
      mcomp_sat (f tt) (withXAddrs (invalidateWrittenXAddrs
                                      (@Memory.bytes_per width sz) (word.add addr (word.of_Z ofs))
                                      (getXAddrs initialL))
                       (withMem m' (updateMetrics (addMetricStores 1) initialL))) post ->
      mcomp_sat (Bind (execute (compile_store sz a x ofs)) f) initialL post.
  Proof.
    unfold compile_store, Memory.store, Memory.store_Z, Memory.bytes_per, Memory.bytes_per_word.
    rewrite bitwidth_matches.
    destruct width_cases as [E | E];
      (* note: "rewrite E" does not work because "width" also appears in the type of "word",
         but we don't need to rewrite in the type of word, only in the type of the tuple,
         which works if we do it before intro'ing it *)
      (destruct (width =? 32) eqn: E'; [apply Z.eqb_eq in E' | apply Z.eqb_neq in E']);
      try congruence;
      clear E';
      [set (nBytes := 4%nat) | set (nBytes := 8%nat)];
      replace (Z.to_nat ((width + 7) / 8)) with nBytes by (subst nBytes; rewrite E; reflexivity);
      subst nBytes;
      intros; destruct sz;
        unfold execute, ExecuteI.execute, ExecuteI64.execute, translate, DefaultRiscvState,
        Memory.store, Memory.store_Z in *;
        simp; simulate''; simpl; simpl_word_exprs word_ok; try eassumption.
  Qed.

  Lemma run_compile_load: forall sz: Syntax.access_size,
      run_Load_spec iset (@Memory.bytes_per width sz) (compile_load sz) id.
  Proof.
    intro sz. destruct sz; unfold compile_load; simpl.
    - refine (run_Lbu iset).
    - refine (run_Lhu iset).
    - rewrite bitwidth_matches.
      destruct width_cases as [E | E]; rewrite E; simpl.
      + refine (run_Lw_unsigned iset E).
      + refine (run_Lwu iset).
    - rewrite bitwidth_matches.
      destruct width_cases as [E | E]; rewrite E; simpl.
      + refine (run_Lw_unsigned iset E).
      + refine (run_Ld_unsigned iset bitwidth_matches).
  Qed.

  Lemma run_compile_store: forall sz: Syntax.access_size,
      run_Store_spec iset (@Memory.bytes_per width sz) (compile_store sz).
  Proof.
    intro sz. destruct sz; unfold compile_store; simpl.
    - refine (run_Sb iset).
    - refine (run_Sh iset).
    - refine (run_Sw iset).
    - rewrite bitwidth_matches.
      destruct width_cases as [E | E]; rewrite E; simpl.
      + refine (run_Sw iset).
      + refine (run_Sd iset).
  Qed.

  (* almost the same as run_compile_load, but not using tuples nor ptsto_bytes or
     Memory.bytes_per, but using ptsto_word instead *)
  Lemma run_load_word: forall (base addr v : word) (rd rs : Z) (ofs : Z)
                              (initialL : RiscvMachineL) (R Rexec : mem -> Prop),
      valid_register rd ->
      valid_register rs ->
      getNextPc initialL = word.add (getPc initialL) (word.of_Z 4) ->
      map.get (getRegs initialL) rs = Some base ->
      addr = word.add base (word.of_Z ofs) ->
      subset (footpr (program iset initialL.(getPc) [[compile_load Syntax.access_size.word rd rs ofs]]
                      * Rexec)%sep)
             (of_list initialL.(getXAddrs)) ->
      (program iset initialL.(getPc) [[compile_load Syntax.access_size.word rd rs ofs]] * Rexec *
       ptsto_word addr v * R)%sep (getMem initialL) ->
      valid_machine initialL ->
      mcomp_sat (run1 iset) initialL
         (fun finalL : RiscvMachineL =>
            getRegs finalL = map.put (getRegs initialL) rd v /\
            getLog finalL = getLog initialL /\
            getXAddrs finalL = getXAddrs initialL /\
            getMem finalL = getMem initialL /\
            getPc finalL = getNextPc initialL /\
            getNextPc finalL = word.add (getPc finalL) (word.of_Z 4) /\
            valid_machine finalL).
  Proof.
    intros.
    eapply mcomp_sat_weaken; cycle 1.
    - eapply (run_compile_load Syntax.access_size.word); cycle -2; try eassumption.
    - cbv beta. intros. simp. repeat split; try assumption.
      etransitivity. 1: eassumption.
      unfold id.
      f_equal.
      rewrite LittleEndian.combine_split.
      replace (BinInt.Z.of_nat (Memory.bytes_per Syntax.access_size.word) * 8) with width.
      + rewrite word.wrap_unsigned. rewrite word.of_Z_unsigned. reflexivity.
      + clear. destruct width_cases as [E | E]; rewrite E; reflexivity.
  Qed.

  (* almost the same as run_compile_store, but not using tuples nor ptsto_bytes or
     Memory.bytes_per, but using ptsto_word instead *)
  Lemma run_store_word: forall (base addr v_new : word) (v_old : word) (rs1 rs2 : Z)
              (ofs : Z) (initialL : RiscvMachineL) (R Rexec : mem -> Prop),
      valid_register rs1 ->
      valid_register rs2 ->
      getNextPc initialL = word.add (getPc initialL) (word.of_Z 4) ->
      map.get (getRegs initialL) rs1 = Some base ->
      map.get (getRegs initialL) rs2 = Some v_new ->
      addr = word.add base (word.of_Z ofs) ->
      subset (footpr ((program iset initialL.(getPc)
                          [[compile_store Syntax.access_size.word rs1 rs2 ofs]]) * Rexec)%sep)
             (of_list initialL.(getXAddrs)) ->
      (program iset initialL.(getPc) [[compile_store Syntax.access_size.word rs1 rs2 ofs]] * Rexec
       * ptsto_word addr v_old * R)%sep (getMem initialL) ->
      valid_machine initialL ->
      mcomp_sat (run1 iset) initialL
        (fun finalL : RiscvMachineL =>
           getRegs finalL = getRegs initialL /\
           getLog finalL = getLog initialL /\
           subset (footpr (program iset initialL.(getPc)
                              [[compile_store Syntax.access_size.word rs1 rs2 ofs]] * Rexec)%sep)
             (of_list finalL.(getXAddrs)) /\
           (program iset initialL.(getPc) [[compile_store Syntax.access_size.word rs1 rs2 ofs]] * Rexec
            * ptsto_word addr v_new * R)%sep (getMem finalL) /\
           getPc finalL = getNextPc initialL /\
           getNextPc finalL = word.add (getPc finalL) (word.of_Z 4) /\
           valid_machine finalL).
  Proof.
    intros.
    eapply mcomp_sat_weaken; cycle 1.
    - eapply (run_compile_store Syntax.access_size.word); cycle -2; try eassumption.
    - cbv beta. intros. simp. repeat split; try assumption.
  Qed.

  Lemma one_step: forall initialL P,
      mcomp_sat (run1 iset) initialL P ->
      runsTo initialL P.
  Proof.
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
  Proof.
    intros.
    eapply runsToStep with (midset := fun m' => m' = midL /\ valid_machine m').
    - eapply run1_get_sane; try eassumption.
      intros. subst. auto.
    - intros ? (? & ?). subst. eapply H1. assumption.
  Qed.

  Lemma disjoint_putmany_preserves_store_bytes: forall n a vs (m1 m1' mq: mem),
      store_bytes n m1 a vs = Some m1' ->
      map.disjoint m1 mq ->
      store_bytes n (map.putmany m1 mq) a vs = Some (map.putmany m1' mq).
  Proof.
    intros.
    unfold store_bytes, load_bytes, unchecked_store_bytes in *. simp.
    erewrite map.getmany_of_tuple_in_disjoint_putmany by eassumption.
    f_equal.
    set (ks := (footprint a n)) in *.
    rename mq into m2.
    rewrite map.putmany_of_tuple_to_putmany.
    rewrite (map.putmany_of_tuple_to_putmany n m1 ks vs).
    apply map.disjoint_putmany_commutes.
    pose proof map.getmany_of_tuple_to_sub_domain _ _ _ _ E as P.
    apply map.sub_domain_value_indep with (vs2 := vs) in P.
    set (mp := (map.putmany_of_tuple ks vs map.empty)) in *.
    apply map.disjoint_comm.
    eapply map.sub_domain_disjoint; eassumption.
  Qed.

  Lemma store_bytes_preserves_footprint: forall n a v (m m': mem),
      Memory.store_bytes n m a v = Some m' ->
      map.same_domain m m'.
  Proof.
    intros. unfold store_bytes, load_bytes, unchecked_store_bytes in *. simp.
    eapply map.putmany_of_tuple_preserves_domain; eauto.
  Qed.

  Lemma seplog_subst_eq{A B R: mem -> Prop} {mL mH: mem}
      (H: A mL)
      (H0: iff1 A (R * eq mH)%sep)
      (H1: B mH):
      (B * R)%sep mL.
  Proof.
    unfold iff1 in *.
    destruct (H0 mL) as [P1 P2]. specialize (P1 H).
    apply sep_comm.
    unfold sep in *.
    destruct P1 as (mR & mH' & P11 & P12 & P13). subst mH'. eauto.
  Qed.

  Lemma subst_load_bytes_for_eq {sz} {mH mL: mem} {addr: word} {bs P R}:
      let n := @Memory.bytes_per width sz in
      bedrock2.Memory.load_bytes n mH addr = Some bs ->
      (P * eq mH * R)%sep mL ->
      exists Q, (P * ptsto_bytes n addr bs * Q * R)%sep mL.
  Proof.
    intros n H H0.
    apply sep_of_load_bytes in H; cycle 1. {
      subst n. clear. destruct sz; destruct width_cases as [C | C]; rewrite C; cbv; discriminate.
    }
    destruct H as [Q A]. exists Q.
    assert (((ptsto_bytes n addr bs * Q) * (P * R))%sep mL); [|ecancel_assumption].
    eapply seplog_subst_eq; [exact H0|..|exact A]. ecancel.
  Qed.

  Lemma store_bytes_frame: forall {n: nat} {m1 m1' m: mem} {a: word} {v: HList.tuple byte n} {F},
      Memory.store_bytes n m1 a v = Some m1' ->
      (eq m1 * F)%sep m ->
      exists m', (eq m1' * F)%sep m' /\ Memory.store_bytes n m a v = Some m'.
  Proof.
    intros.
    unfold sep in H0.
    destruct H0 as (mp & mq & A & B & C).
    subst mp.
    unfold map.split in A. destruct A as [A1 A2].
    eexists (map.putmany m1' mq).
    split.
    - unfold sep.
      exists m1', mq. repeat split; trivial.
      apply store_bytes_preserves_footprint in H.
      clear -H A2.
      unfold map.disjoint, map.same_domain, map.sub_domain in *. destruct H as [P Q].
      intros.
      edestruct Q; eauto.
    - subst m.
      eauto using disjoint_putmany_preserves_store_bytes.
  Qed.

  Lemma ptsto_instr_compile4bytes: forall l addr,
      word.unsigned addr mod 4 = 0 ->
      iff1 (ptsto_instr iset addr (compile4bytes l))
           (array ptsto (word.of_Z 1) addr
                  [nth 0 l Byte.x00; nth 1 l Byte.x00; nth 2 l Byte.x00; nth 3 l Byte.x00]).
  Proof.
    intros. unfold compile4bytes, ptsto_instr, truncated_scalar, littleendian. simpl.
    unfold Encode.encode_Invalid.
    rewrite bitSlice_all_nonneg. 2: cbv; discriminate. 2: apply (@LittleEndian.combine_bound 4).
    rewrite LittleEndian.split_combine.
    unfold ptsto_bytes.
    simpl.
    wcancel.
    cbn [seps].
    rewrite sep_emp_emp.
    apply RunInstruction.iff1_emp.
    split. 1: auto.
    intros _.
    unfold valid_InvalidInstruction.
    split. 2: assumption.
    right.
    eexists. split. 2: reflexivity.
    apply (@LittleEndian.combine_bound 4).
  Qed.

  Lemma program_compile_byte_list_array: forall instrs table addr,
      instrs = compile_byte_list table ->
      word.unsigned addr mod 4 = 0 ->
      exists padding,
        iff1 (program iset addr instrs)
             (array ptsto (word.of_Z 1) addr (table ++ padding)).
  Proof.
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
  Proof.
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
      + subst k. ring_simplify (word.sub addr addr). rewrite word.unsigned_of_Z. simpl.
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
             simpl_param_projections.
             rewrite (word.of_Z_unsigned (word.sub k addr)) in F.
             rewrite <- add_0_r at 1. change (Z.of_nat 0) with 0 in F. rewrite <- F.
             ring.
          -- f_equal.
             pose proof word.unsigned_range (word.sub k addr).
             assert (Z.of_nat (S n) < 2 ^ width) by blia.
             apply (f_equal Z.of_nat) in F.
             rewrite Z2Nat.id in F by blia.
             apply (f_equal word.of_Z) in F.
             simpl_param_projections.
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
              (Padding * eq (OfListWord.map.of_list_word_at addr table)).
  Proof.
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
      Memory.load_bytes n (OfListWord.map.of_list_word l) index = Some t ->
      Memory.load_bytes n (OfListWord.map.of_list_word_at addr l) (word.add addr index) = Some t.
  Proof.
    induction n; intros.
    - cbv in t. destruct t. etransitivity. 2: eassumption. reflexivity.
    - unfold Memory.load_bytes in *.
      eapply map.invert_getmany_of_tuple_Some in H. simp.
      eapply map.build_getmany_of_tuple_Some.
      + simpl in *.
        rewrite OfListWord.map.get_of_list_word_at.
        rewrite OfListWord.map.get_of_list_word in Hp0.
        etransitivity. 2: exact Hp0. do 3 f_equal. solve_word_eq word_ok.
      + simpl in *. specialize (IHn _ _ Hp1).
        etransitivity. 2: exact IHn. do 2 f_equal. solve_word_eq word_ok.
  Qed.

  Lemma load_from_compile_byte_list: forall sz table index v R m addr,
    Memory.load sz (OfListWord.map.of_list_word table) index = Some v ->
    (program iset addr (compile_byte_list table) * R)%sep m ->
    Memory.load sz m (word.add addr index) = Some v.
  Proof.
    intros *. intros L M.
    destruct (program_compile_byte_list table addr) as [Padding P].
    apply (Proper_sep_impl1 _ _ P R R) in M; [|reflexivity]; clear P.
    unfold Memory.load, Memory.load_Z in *. simp.
    eapply shift_load_bytes_in_of_list_word in E0.
    pose proof @subst_load_bytes_for_eq as P. cbv zeta in P.
    specialize P with (1 := E0) (2 := M).
    destruct P as [Q P].
    erewrite load_bytes_of_sep. 1: reflexivity.
    wcancel_assumption.
  Qed.

End FlatToRiscv1.

(* if we have valid_machine for the current machine, and need to prove a
   runsTo with valid_machine in the postcondition, this tactic can
   replace the valid_machine in the postcondition by True *)
Ltac get_run1valid_for_free :=
  let R := fresh "R" in
  evar (R: MetricRiscvMachine -> Prop);
  eapply runsTo_get_sane with (P := R);
  [ (* valid_machine *)
    assumption
  | (* the simpler runsTo goal, left open *)
    idtac
  | (* the impliciation, needs to replace valid_machine by True *)
    let mach' := fresh "mach'" in
    let D := fresh "D" in
    let Pm := fresh "Pm" in
    intros mach' D V Pm;
    match goal with
    | H: valid_machine mach' |- context C[valid_machine mach'] =>
      let G := context C[True] in
      let P := eval pattern mach' in G in
      lazymatch P with
      | ?F _ => instantiate (R := F)
      end
    end;
    subst R;
    clear -V Pm;
    cbv beta in *;
    simp;
    eauto 20
  ];
  subst R.

Ltac solve_valid_machine wordOk :=
  match goal with
  | H: valid_machine {| getMetrics := ?M |} |- valid_machine {| getMetrics := ?M |} =>
    eqexact H; f_equal; f_equal
  end;
  solve_word_eq wordOk.

Ltac subst_load_bytes_for_eq :=
  lazymatch goal with
  | Load: ?LB _ _ _ _ ?m _ = _ |- _ =>
    unify LB @Memory.load_bytes;
    let P := fresh "P" in
    epose proof (@subst_load_bytes_for_eq _ _ _ _ _ _ _ _ _ Load) as P;
    let Q := fresh "Q" in
    edestruct P as [Q ?]; clear P; [ecancel_assumption|]
  end.

Ltac simulate'_step :=
  match goal with
  (* lemmas introduced only in this file: *)
  | |- mcomp_sat (Monads.Bind (Execute.execute (compile_load _ _ _ _)) _) _ _ =>
       eapply go_load; [ sidecondition.. | idtac ]
  | |- mcomp_sat (Monads.Bind (Execute.execute (compile_store _ _ _ _)) _) _ _ =>
       eapply go_store; [ sidecondition.. | idtac ]
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
