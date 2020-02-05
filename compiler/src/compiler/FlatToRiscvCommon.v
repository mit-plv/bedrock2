Require Import riscv.Utility.Monads. Require Import riscv.Utility.MonadNotations.
Require Import coqutil.Macros.unique.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
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
Require Import riscv.Utility.div_mod_to_quot_rem.
Require Import compiler.util.Misc.
Require Import riscv.Utility.Utility.
Require Import coqutil.Z.BitOps.
Require Import compiler.util.Common.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.EmitsValid.
Require Import compiler.SeparationLogic.
Require Import bedrock2.Scalars.
Require Import compiler.Simp.
Require Import compiler.SimplWordExpr.
Require Import bedrock2.ptsto_bytes.
Require Import compiler.RiscvWordProperties.
Require Import compiler.eqexact.
Require Import compiler.on_hyp_containing.
Require Import coqutil.Z.bitblast.
Require Import riscv.Utility.prove_Zeq_bitwise.
Require Import compiler.RunInstruction.
Require Import compiler.DivisibleBy4.
Require Import compiler.MetricsToRiscv.

Import Utility.

Local Open Scope ilist_scope.
Local Open Scope Z_scope.

Set Implicit Arguments.

Export FlatToRiscvDef.FlatToRiscvDef.

Class parameters := {
  def_params :> FlatToRiscvDef.parameters;

  locals :> map.map Z word;
  mem :> map.map word byte;
  funname_env :> forall T: Type, map.map string T; (* abstract T for better reusability *)

  M: Type -> Type;
  MM :> Monad M;
  RVM :> RiscvProgram M word;
  PRParams :> PrimitivesParams M MetricRiscvMachine;

  ext_spec : list (mem * String.string * list word * (mem * list word)) ->
             mem -> String.string -> list word -> (mem -> list word -> Prop) -> Prop;
}.

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

  Class assumptions: Prop := {
    word_riscv_ok :> word.riscv_ok (@word W);
    locals_ok :> map.ok locals;
    mem_ok :> map.ok mem;
    funname_env_ok :> forall T, map.ok (funname_env T);

    PR :> MetricPrimitives PRParams;

    compile_ext_call_correct: forall (initialL: MetricRiscvMachine)
        action postH newPc insts (argvars resvars: list Z) initialMH R Rexec initialRegsH
        argvals mGive outcome p_sp,
      insts = compile_ext_call resvars action argvars ->
      newPc = word.add initialL.(getPc) (word.of_Z (4 * (Z.of_nat (List.length insts)))) ->
      map.extends initialL.(getRegs) initialRegsH ->
      Forall valid_FlatImp_var argvars ->
      Forall valid_FlatImp_var resvars ->
      subset (footpr (program initialL.(getPc) insts * Rexec)%sep)
             (of_list initialL.(getXAddrs)) ->
      (program initialL.(getPc) insts * eq initialMH * R)%sep initialL.(getMem) ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      map.get initialL.(getRegs) RegisterNames.sp = Some p_sp ->
      (forall x v, map.get initialRegsH x = Some v -> valid_FlatImp_var x) ->
      regs_initialized initialL.(getRegs) ->
      valid_machine initialL ->
      (* from FlatImp.exec/case interact, but for the case where no memory is exchanged *)
      map.getmany_of_list initialL.(getRegs) argvars = Some argvals ->
      ext_spec initialL.(getLog) mGive action argvals outcome ->
      (forall (resvals : list word),
          outcome map.empty resvals ->
          mGive = map.empty ->
          exists (finalRegsH: locals) finalMetricsH,
            map.putmany_of_list_zip resvars resvals initialRegsH = Some finalRegsH /\
            postH ((map.empty, action, argvals, (map.empty, resvals)) :: initialL.(getLog))
                  initialMH finalRegsH finalMetricsH) ->
      runsTo initialL
             (fun finalL =>
                exists (finalRegsH: locals) (rvs: list word)
                       (finalMetricsH : bedrock2.MetricLogging.MetricLog),
                  map.extends finalL.(getRegs) finalRegsH /\
                  map.putmany_of_list_zip resvars rvs initialL.(getRegs) = Some finalL.(getRegs) /\
                  map.get finalL.(getRegs) RegisterNames.sp = Some p_sp /\
                  (* external calls can't modify the memory for now *)
                  postH finalL.(getLog) initialMH finalRegsH finalMetricsH /\
                  finalL.(getPc) = newPc /\
                  finalL.(getNextPc) = add newPc (word.of_Z 4) /\
                  subset (footpr (program initialL.(getPc) insts * Rexec)%sep)
                         (of_list finalL.(getXAddrs)) /\
                  (program initialL.(getPc) insts * eq initialMH * R)%sep finalL.(getMem) /\
                  (forall x v, map.get finalRegsH x = Some v -> valid_FlatImp_var x) /\
                  regs_initialized finalL.(getRegs) /\
                  valid_machine finalL);
  }.

End WithParameters.

Existing Instance Semantics_params.

Arguments Z.mul: simpl never.
Arguments Z.add: simpl never.
Arguments Z.of_nat: simpl never.
Arguments Z.modulo : simpl never.
Arguments Z.pow: simpl never.
Arguments Z.sub: simpl never.

Arguments run1: simpl never.

Arguments compile_store: simpl never.
Arguments compile_load: simpl never.

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

  Lemma go_load: forall sz (x a: Z) (addr v: word) (initialL: RiscvMachineL) post f,
      valid_register x ->
      valid_register a ->
      map.get initialL.(getRegs) a = Some addr ->
      Memory.load sz (getMem initialL) addr = Some v ->
      mcomp_sat (f tt)
                (withRegs (map.put initialL.(getRegs) x v) (updateMetrics (addMetricLoads 1) initialL)) post ->
      mcomp_sat (Bind (execute (compile_load sz x a 0)) f) initialL post.
  Proof.
    unfold compile_load, Memory.load, Memory.load_Z, Memory.bytes_per.
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

  Lemma go_store: forall sz (x a: Z) (addr v: word) (initialL: RiscvMachineL) m' post f,
      valid_register x ->
      valid_register a ->
      map.get initialL.(getRegs) x = Some v ->
      map.get initialL.(getRegs) a = Some addr ->
      Memory.store sz (getMem initialL) addr v = Some m' ->
      mcomp_sat (f tt) (withXAddrs (invalidateWrittenXAddrs (@Memory.bytes_per width sz) addr
                                                            (getXAddrs initialL))
                       (withMem m' (updateMetrics (addMetricStores 1) initialL))) post ->
      mcomp_sat (Bind (execute (compile_store sz a x 0)) f) initialL post.
  Proof.
    unfold compile_store, Memory.store, Memory.store_Z, Memory.bytes_per;
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
      run_Load_spec (@Memory.bytes_per width sz) (compile_load sz) id.
  Proof.
    intro sz. destruct sz; unfold compile_load; simpl.
    - refine run_Lbu.
    - refine run_Lhu.
    - destruct width_cases as [E | E]; rewrite E; simpl.
      + refine (run_Lw_unsigned E).
      + refine run_Lwu.
    - destruct width_cases as [E | E]; rewrite E; simpl.
      + refine (run_Lw_unsigned E).
      + refine run_Ld_unsigned.
  Qed.

  Lemma run_compile_store: forall sz: Syntax.access_size,
      run_Store_spec (@Memory.bytes_per width sz) (compile_store sz).
  Proof.
    intro sz. destruct sz; unfold compile_store; simpl.
    - refine run_Sb.
    - refine run_Sh.
    - refine run_Sw.
    - destruct width_cases as [E | E]; rewrite E; simpl.
      + refine run_Sw.
      + refine run_Sd.
  Qed.

  (* almost the same as run_compile_load, but not using tuples nor ptsto_bytes or
     Memory.bytes_per, but using ptsto_word instead *)
  Lemma run_load_word: forall (base addr v : word) (rd rs : Z) (ofs : MachineInt)
                              (initialL : RiscvMachineL) (R Rexec : mem -> Prop),
      valid_register rd ->
      valid_register rs ->
      getNextPc initialL = word.add (getPc initialL) (word.of_Z 4) ->
      map.get (getRegs initialL) rs = Some base ->
      addr = word.add base (word.of_Z ofs) ->
      subset (footpr (program initialL.(getPc) [[compile_load Syntax.access_size.word rd rs ofs]]
                      * Rexec)%sep)
             (of_list initialL.(getXAddrs)) ->
      (program initialL.(getPc) [[compile_load Syntax.access_size.word rd rs ofs]] * Rexec *
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
              (ofs : MachineInt) (initialL : RiscvMachineL) (R Rexec : mem -> Prop),
      valid_register rs1 ->
      valid_register rs2 ->
      getNextPc initialL = word.add (getPc initialL) (word.of_Z 4) ->
      map.get (getRegs initialL) rs1 = Some base ->
      map.get (getRegs initialL) rs2 = Some v_new ->
      addr = word.add base (word.of_Z ofs) ->
      subset (footpr ((program initialL.(getPc)
                          [[compile_store Syntax.access_size.word rs1 rs2 ofs]]) * Rexec)%sep)
             (of_list initialL.(getXAddrs)) ->
      (program initialL.(getPc) [[compile_store Syntax.access_size.word rs1 rs2 ofs]] * Rexec
       * ptsto_word addr v_old * R)%sep (getMem initialL) ->
      valid_machine initialL ->
      mcomp_sat (run1 iset) initialL
        (fun finalL : RiscvMachineL =>
           getRegs finalL = getRegs initialL /\
           getLog finalL = getLog initialL /\
           subset (footpr (program initialL.(getPc)
                              [[compile_store Syntax.access_size.word rs1 rs2 ofs]] * Rexec)%sep)
             (of_list finalL.(getXAddrs)) /\
           (program initialL.(getPc) [[compile_store Syntax.access_size.word rs1 rs2 ofs]] * Rexec
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
    pose proof map.getmany_of_tuple_to_sub_domain as P.
    specialize P with (1 := E).
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
    eauto using map.putmany_of_tuple_preserves_domain.
  Qed.

  Lemma iset_is_supported: supported_iset iset.
  Proof.
    unfold iset. destruct_one_match; constructor.
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
