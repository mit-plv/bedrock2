From Coq Require Import ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Z.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Decode.
Require Import riscv.Platform.Memory.
Require Import riscv.Spec.Machine.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.MetricPrimitives.
Require Import riscv.Platform.Run.
Require Import riscv.Spec.Execute.
Require Import riscv.Proofs.DecodeEncode.
Require Import coqutil.Tactics.Tactics.
Require Import compiler.SeparationLogic.
Require Import bedrock2.ptsto_bytes.
Require Import bedrock2.Scalars.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.RegisterNames.
Require Import riscv.Proofs.EncodeBound.
Require Import coqutil.Decidable.
Require Import compiler.GoFlatToRiscv.
Require Import riscv.Utility.InstructionCoercions. Local Open Scope ilist_scope.
Require Export coqutil.Word.SimplWordExpr.
Require Import coqutil.Tactics.Simp.
Require Import compiler.DivisibleBy4.
Require Import compiler.ZLemmas.
Import Utility.

Notation Register0 := 0%Z (only parsing).

(* R: evar to be instantiated to goal but with valid_machine replaced by True *)
Ltac replace_valid_machine_by_True R :=
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
  solve [eauto 30].

(* if we have valid_machine for the current machine, and need to prove a
   run1 with valid_machine in the postcondition, this tactic can
   replace the valid_machine in the postcondition by True *)
Ltac get_run1_valid_for_free :=
  let R := fresh "R" in
  evar (R: MetricRiscvMachine -> Prop);
  eapply run1_get_sane with (P := R);
  [ (* valid_machine *)
    assumption
  | (* the simpler run1 goal, left open *)
    idtac
  | (* the implication, needs to replace valid_machine by True *)
    replace_valid_machine_by_True R
  ];
  subst R.


(* if we have valid_machine for the current machine, and need to prove a
   runsTo with valid_machine in the postcondition, this tactic can
   replace the valid_machine in the postcondition by True *)
Ltac get_runsTo_valid_for_free :=
  let R := fresh "R" in
  evar (R: MetricRiscvMachine -> Prop);
  eapply runsTo_get_sane with (P := R);
  [ (* valid_machine *)
    assumption
  | (* the simpler runsTo goal, left open *)
    idtac
  | (* the implication, needs to replace valid_machine by True *)
    replace_valid_machine_by_True R
  ];
  subst R.

Section Run.

  Context {width} {BW: Bitwidth width} {word: word.word width} {word_ok: word.ok word}.
  Context {Registers: map.map Z word}.
  Context {mem: map.map word byte}.
  Context {mem_ok: map.ok mem}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Local Notation RiscvMachineL := MetricRiscvMachine.

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {PR: MetricPrimitives PRParams}.

  Ltac simulate'_step :=
    first [ eapply go_loadByte_sep ; simpl; [sidecondition..|]
          | eapply go_storeByte_sep; simpl; [sidecondition..|intros]
          | eapply go_loadHalf_sep ; simpl; [sidecondition..|]
          | eapply go_storeHalf_sep; simpl; [sidecondition..|intros]
          | eapply go_loadWord_sep ; simpl; [sidecondition..|]
          | eapply go_storeWord_sep; simpl; [sidecondition..|intros]
          | eapply go_loadDouble_sep ; simpl; [sidecondition..|]
          | eapply go_storeDouble_sep; simpl; [sidecondition..|intros]
          | simpl_modu4_0
          | simulate_step ].

  Ltac simulate' := repeat simulate'_step.

  Context (iset: InstructionSet).

  Definition run_Jalr0_spec :=
    forall (rs1: Z) (oimm12: Z) (initialL: RiscvMachineL) (Exec R Rexec: mem -> Prop)
           (dest: word),
      (* [verify] (and decode-encode-id) only enforces divisibility by 2 because there could be
         compressed instructions, but we don't support them so we require divisibility by 4: *)
      oimm12 mod 4 = 0 ->
      (word.unsigned dest) mod 4 = 0 ->
      (* valid_register almost follows from verify (or decode-encode-id) except for when
         the register is Register0 *)
      valid_register rs1 ->
      map.get initialL.(getRegs) rs1 = Some dest ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      subset (footpr Exec) (of_list (initialL.(getXAddrs))) ->
      iff1 Exec (program iset initialL.(getPc) [[Jalr RegisterNames.zero rs1 oimm12]] * Rexec)%sep ->
      (Exec * R)%sep initialL.(getMem) ->
      valid_machine initialL ->
      mcomp_sat (run1 iset) initialL (fun (finalL: RiscvMachineL) =>
        finalL.(getRegs) = initialL.(getRegs) /\
        finalL.(getLog) = initialL.(getLog) /\
        finalL.(getMem) = initialL.(getMem) /\
        finalL.(getXAddrs) = initialL.(getXAddrs) /\
        finalL.(getPc) = word.add dest (word.of_Z oimm12) /\
        finalL.(getNextPc) = word.add finalL.(getPc) (word.of_Z 4) /\
        finalL.(getMetrics) = addMetricInstructions 1 (addMetricJumps 1 (addMetricLoads 1 initialL.(getMetrics))) /\
        valid_machine finalL).

  Definition run_Jal_spec :=
    forall (rd: Z) (jimm20: Z) (initialL: RiscvMachineL) (Exec R Rexec: mem -> Prop),
      jimm20 mod 4 = 0 ->
      valid_register rd ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      subset (footpr Exec) (of_list (initialL.(getXAddrs))) ->
      iff1 Exec (program iset initialL.(getPc) [[Jal rd jimm20]] * Rexec)%sep ->
      (Exec * R)%sep initialL.(getMem) ->
      valid_machine initialL ->
      mcomp_sat (run1 iset) initialL (fun finalL =>
        finalL.(getRegs) = map.put initialL.(getRegs) rd initialL.(getNextPc) /\
        finalL.(getLog) = initialL.(getLog) /\
        finalL.(getMem) = initialL.(getMem) /\
        finalL.(getXAddrs) = initialL.(getXAddrs) /\
        finalL.(getPc) = word.add initialL.(getPc) (word.of_Z jimm20) /\
        finalL.(getNextPc) = word.add finalL.(getPc) (word.of_Z 4) /\
        finalL.(getMetrics) = addMetricInstructions 1 (addMetricJumps 1 (addMetricLoads 1 initialL.(getMetrics))) /\
        valid_machine finalL).

  Definition run_Jal0_spec :=
    forall (jimm20: Z) (initialL: RiscvMachineL) (Exec R Rexec: mem -> Prop),
      jimm20 mod 4 = 0 ->
      subset (footpr Exec) (of_list (initialL.(getXAddrs))) ->
      iff1 Exec (program iset initialL.(getPc) [[Jal Register0 jimm20]] * Rexec)%sep ->
      (Exec * R)%sep initialL.(getMem) ->
      valid_machine initialL ->
      mcomp_sat (run1 iset) initialL (fun finalL =>
        finalL.(getRegs) = initialL.(getRegs) /\
        finalL.(getLog) = initialL.(getLog) /\
        finalL.(getMem) = initialL.(getMem) /\
        finalL.(getXAddrs) = initialL.(getXAddrs) /\
        finalL.(getPc) = word.add initialL.(getPc) (word.of_Z jimm20) /\
        finalL.(getNextPc) = word.add finalL.(getPc) (word.of_Z 4) /\
        finalL.(getMetrics) = addMetricInstructions 1 (addMetricJumps 1 (addMetricLoads 1 initialL.(getMetrics))) /\
        valid_machine finalL).

  Definition run_ImmReg_spec(Op: Z -> Z -> Z -> Instruction)
                            (f: word -> word -> word): Prop :=
    forall (rd rs: Z) rs_val imm (initialL: RiscvMachineL) (Exec R Rexec: mem -> Prop),
      valid_register rd ->
      valid_register rs ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      map.get initialL.(getRegs) rs = Some rs_val ->
      subset (footpr Exec) (of_list (initialL.(getXAddrs))) ->
      iff1 Exec (program iset initialL.(getPc) [[Op rd rs imm]] * Rexec)%sep ->
      (Exec * R)%sep initialL.(getMem) ->
      valid_machine initialL ->
      mcomp_sat (run1 iset) initialL (fun finalL =>
        finalL.(getRegs) = map.put initialL.(getRegs) rd (f rs_val (word.of_Z imm)) /\
        finalL.(getLog) = initialL.(getLog) /\
        finalL.(getMem) = initialL.(getMem) /\
        finalL.(getXAddrs) = initialL.(getXAddrs) /\
        finalL.(getPc) = initialL.(getNextPc) /\
        finalL.(getNextPc) = word.add finalL.(getPc) (word.of_Z 4) /\
        finalL.(getMetrics) = addMetricInstructions 1 (addMetricLoads 1 initialL.(getMetrics)) /\
        valid_machine finalL).

  Definition run_Load_spec(n: nat)(L: Z -> Z -> Z -> Instruction)
             (opt_sign_extender: Z -> Z): Prop :=
    forall (base addr: word) (v: HList.tuple byte n) (rd rs: Z) (ofs: Z)
           (initialL: RiscvMachineL) (Exec R Rexec: mem -> Prop),
      (* valid_register almost follows from verify except for when the register is Register0 *)
      valid_register rd ->
      valid_register rs ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      map.get initialL.(getRegs) rs = Some base ->
      addr = word.add base (word.of_Z ofs) ->
      subset (footpr Exec) (of_list (initialL.(getXAddrs))) ->
      iff1 Exec (program iset initialL.(getPc) [[L rd rs ofs]] * Rexec)%sep ->
      (Exec * ptsto_bytes n addr v * R)%sep initialL.(getMem) ->
      valid_machine initialL ->
      mcomp_sat (run1 iset) initialL (fun finalL =>
        finalL.(getRegs) = map.put initialL.(getRegs) rd
                  (word.of_Z (opt_sign_extender (LittleEndian.combine n v))) /\
        finalL.(getLog) = initialL.(getLog) /\
        finalL.(getMem) = initialL.(getMem) /\
        finalL.(getXAddrs) = initialL.(getXAddrs) /\
        finalL.(getPc) = initialL.(getNextPc) /\
        finalL.(getNextPc) = word.add finalL.(getPc) (word.of_Z 4) /\
        finalL.(getMetrics) = addMetricInstructions 1 (addMetricLoads 2 initialL.(getMetrics)) /\
        valid_machine finalL).

  Definition run_Store_spec(n: nat)(S: Z -> Z -> Z -> Instruction): Prop :=
    forall (base addr v_new: word) (v_old: HList.tuple byte n) (rs1 rs2: Z)
           (ofs: Z) (initialL: RiscvMachineL) (Exec R Rexec: mem -> Prop),
      (* valid_register almost follows from verify except for when the register is Register0 *)
      valid_register rs1 ->
      valid_register rs2 ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      map.get initialL.(getRegs) rs1 = Some base ->
      map.get initialL.(getRegs) rs2 = Some v_new ->
      addr = word.add base (word.of_Z ofs) ->
      subset (footpr Exec) (of_list (initialL.(getXAddrs))) ->
      iff1 Exec (program iset initialL.(getPc) [[S rs1 rs2 ofs]] * Rexec)%sep ->
      (Exec * ptsto_bytes n addr v_old * R)%sep initialL.(getMem) ->
      valid_machine initialL ->
      mcomp_sat (run1 iset) initialL (fun finalL =>
        finalL.(getRegs) = initialL.(getRegs) /\
        finalL.(getLog) = initialL.(getLog) /\
        subset (footpr Exec) (of_list (finalL.(getXAddrs))) /\
        (Exec * ptsto_bytes n addr (LittleEndian.split n (word.unsigned v_new)) * R)%sep
          finalL.(getMem) /\
        finalL.(getPc) = initialL.(getNextPc) /\
        finalL.(getNextPc) = word.add finalL.(getPc) (word.of_Z 4) /\
        finalL.(getMetrics) = addMetricInstructions 1 (addMetricStores 1 (addMetricLoads 1 initialL.(getMetrics))) /\
        valid_machine finalL).

  Ltac inline_iff1 :=
    match goal with
    | H: iff1 ?x _ |- _ => is_var x; apply iff1ToEq in H; subst x
    end.

  Ltac t0 :=
    match goal with
    | initialL: RiscvMachineL |- _ => destruct_RiscvMachine initialL
    end;
    simpl in *; subst;
    simulate';
    simpl;
    repeat match goal with
           | |- _ /\ _ => split
           | |- _ => solve [auto]
           | |- _ => ecancel_assumption
           | |- _ => solve_MetricLog
           end.

  Ltac t := repeat intro; inline_iff1; get_run1_valid_for_free; t0.

  Lemma run_Jalr0: run_Jalr0_spec.
  Proof.
    repeat intro.
    inline_iff1.
    get_run1_valid_for_free.
    match goal with
    | H: (?P * ?Q * ?R)%sep ?m |- _ =>
      assert ((P * (Q * R))%sep m) as A by ecancel_assumption
    end.
    destruct (invert_ptsto_program1 iset A) as (DE & ?). clear A.
    (* execution of Jalr clears lowest bit *)
    assert (word.and (word.add dest (word.of_Z oimm12))
                     (word.xor (word.of_Z 1) (word.of_Z (2 ^ width - 1))) =
            word.add dest (word.of_Z oimm12)) as A. {
      assert (word.unsigned (word.add dest (word.of_Z oimm12)) mod 4 = 0) as C by
            solve_divisibleBy4.
      generalize dependent (word.add dest (word.of_Z oimm12)). clear -BW word_ok.
      intros.
      apply word.unsigned_inj.
      rewrite word.unsigned_and, word.unsigned_xor, !word.unsigned_of_Z. unfold word.wrap.
      assert (0 <= width) by (destruct width_cases as [E | E]; rewrite E; blia).
      replace (2 ^ width - 1) with (Z.ones width); cycle 1. {
        rewrite Z.ones_equiv. reflexivity.
      }
      change 1 with (Z.ones 1).
      transitivity (word.unsigned r mod (2 ^ width)); cycle 1. {
        rewrite word.wrap_unsigned. reflexivity.
      }
      rewrite <-! Z.land_ones by assumption.
      change 4 with (2 ^ 2) in C.
      prove_Zeq_bitwise.Zbitwise.
    }
    assert (word.unsigned
              (word.and (word.add dest (word.of_Z oimm12))
                        (word.xor (word.of_Z 1) (word.of_Z (2 ^ width - 1)))) mod 4 = 0) as B. {
      rewrite A. solve_divisibleBy4.
    }
    t0.
  Qed.

  Lemma run_Jal: run_Jal_spec.
  Proof.
    repeat intro.
    inline_iff1.
    get_run1_valid_for_free.
    match goal with
    | H: (?P * ?Q * ?R)%sep ?m |- _ =>
      assert ((P * (Q * R))%sep m) as A by ecancel_assumption
    end.
    destruct (invert_ptsto_program1 iset A) as (DE & ?).
    t0.
  Qed.

  Local Arguments Z.pow: simpl never.
  Local Arguments Z.opp: simpl never.

  Lemma run_Jal0: run_Jal0_spec.
  Proof.
    repeat intro.
    inline_iff1.
    get_run1_valid_for_free.
    match goal with
    | H: (?P * ?Q * ?R)%sep ?m |- _ =>
      assert ((P * (Q * R))%sep m) as A by ecancel_assumption
    end.
    destruct (invert_ptsto_program1 iset A) as (DE & ?).
    t0.
  Qed.

  Lemma run_Addi: run_ImmReg_spec Addi word.add.
  Proof. t. Qed.

  Lemma run_Lb: run_Load_spec 1 Lb (signExtend 8).
  Proof. t. Qed.

  Lemma run_Lbu: run_Load_spec 1 Lbu id.
  Proof. t. Qed.

  Lemma run_Lh: run_Load_spec 2 Lh (signExtend 16).
  Proof. t. Qed.

  Lemma run_Lhu: run_Load_spec 2 Lhu id.
  Proof. t. Qed.

  Lemma run_Lw: run_Load_spec 4 Lw (signExtend 32).
  Proof. t. Qed.

  Lemma run_Lw_unsigned: width = 32 -> run_Load_spec 4 Lw id.
  Proof.
    change width with (id width).
    t. rewrite sextend_width_nop; [reflexivity|symmetry;assumption].
  Qed.

  Lemma run_Lwu: run_Load_spec 4 Lwu id.
  Proof. t. Qed.

  Lemma run_Ld: run_Load_spec 8 Ld (signExtend 64).
  Proof. t. Qed.

  (* Note: there's no Ldu instruction, because Ld does the same *)
  Lemma run_Ld_unsigned: width = 64 -> run_Load_spec 8 Ld id.
  Proof.
    change width with (id width).
    t. rewrite sextend_width_nop; [reflexivity|symmetry;assumption].
  Qed.

  Lemma iff1_emp: forall P Q,
      (P <-> Q) ->
      @iff1 mem (emp P) (emp Q).
  Proof. unfold iff1, emp. clear. firstorder idtac. Qed.

  Lemma removeXAddr_diff: forall (a1 a2: word) xaddrs,
      a1 <> a2 ->
      isXAddr1 a1 xaddrs ->
      isXAddr1 a1 (removeXAddr a2 xaddrs).
  Proof.
    unfold isXAddr1, removeXAddr.
    intros.
    apply filter_In.
    split; [assumption|].
    rewrite word.eqb_ne by congruence.
    reflexivity.
  Qed.

  Lemma removeXAddr_bw: forall (a1 a2: word) xaddrs,
      isXAddr1 a1 (removeXAddr a2 xaddrs) ->
      isXAddr1 a1 xaddrs.
  Proof.
    unfold isXAddr1, removeXAddr.
    intros.
    eapply filter_In.
    eassumption.
  Qed.

  Lemma sep_ptsto_to_addr_neq: forall a1 v1 a2 v2 (m : mem) R,
      (ptsto a1 v1 * ptsto a2 v2 * R)%sep m ->
      a1 <> a2.
  Proof.
    intros. intro E. subst a2. unfold ptsto in *.
    destruct H as (? & ? & ? & (? & ? & ? & ? & ?) & ?).
    subst.
    destruct H0 as [? D].
    unfold map.disjoint in D.
    eapply D; apply map.get_put_same.
  Qed.

  Local Arguments invalidateWrittenXAddrs: simpl never.

  Lemma run_Sb: run_Store_spec 1 Sb.
  Proof. t. Qed.

  Lemma run_Sh: run_Store_spec 2 Sh.
  Proof. t. Qed.

  Lemma run_Sw: run_Store_spec 4 Sw.
  Proof. t. Qed.

  Lemma run_Sd: run_Store_spec 8 Sd.
  Proof. t. Qed.

End Run.
