Require Import Coq.Lists.List.
Require Import coqutil.Z.Lia.
Import ListNotations.
Require Import coqutil.Word.Properties.
Require Import riscv.Utility.Monads.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.MetricPrimitives.
Require Import riscv.Spec.Machine.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.Memory.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.MkMachineWidth.
Require Import coqutil.Map.Interface.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.SeparationLogic.
Require Import compiler.FlatToRiscvDef.
Require Export coqutil.Word.SimplWordExpr.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import coqutil.Tactics.Simp.
Import Utility Decode.

Open Scope Z_scope.
Open Scope ilist_scope.

Definition x1: Z := 1.
Definition x2: Z := 2.

(* average of register x1 and x2 put into x2 *)
Definition asm_prog_1: list Instruction := [[
  Add x2 x1 x2;
  Srai x2 x2 1
]].

Definition input_ptr: Z := 0x400.
Definition output_ptr: Z := 0x500.

(* a program with memory operations *)
Definition asm_prog_2: list Instruction := [[
  Lw x1 Register0 input_ptr;
  Lw x2 Register0 (input_ptr+4)
]] ++
asm_prog_1 ++ [[
  Sw Register0 x2 output_ptr
]].

Import Separation.
Local Notation ptsto_bytes :=
  (fun n addr v => OfListWord.map.of_list_word_at addr (HList.tuple.to_list (n:=n) v))
  (only parsing).

Section Verif.

  Context {width} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {Registers: map.map Register word}.
  Context {Registers_ok: map.ok Registers}.
  Context {mem: map.map word byte}.
  Context {mem_ok: map.ok mem}.
  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgramWithLeakage M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {PR: MetricPrimitives PRParams}.

  Definition iset := if width =? 32 then RV32I else RV64I.

  Add Ring wring : (Zmod.ring_theory (2 ^ width))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (width := width)),
       constants [word_cst]).

  Ltac simulate'_step :=
    first [ eapply go_loadWord_sep ; simpl in *; simpl_word_exprs; [ecancel_assumption||sidecondition..|]
          | eapply go_storeWord_sep; simpl in *; simpl_word_exprs; [ecancel_assumption||sidecondition..|intros]
          | simulate_step ].

  Ltac simulate' := repeat simulate'_step.

  Ltac run1det :=
    eapply runsTo_det_step;
    [ simulate';
      match goal with
      | |- ?mid = ?RHS =>
        (* simpl RHS because mid will be instantiated to it and turn up again in the next step *)
        is_evar mid; simpl; reflexivity
      | |- _ => fail 10000 "simulate' did not go through completely"
      end
    | ].

  Definition gallina_prog_1(v1 v2: word): word :=
    Zmod.srs (Zmod.add v1 v2) 1.

  Lemma asm_prog_1_correct: forall (initial: MetricRiscvMachine) newPc R Rexec (v1 v2: word),
      map.get initial.(getRegs) x1 = Some v1 ->
      map.get initial.(getRegs) x2 = Some v2 ->
      newPc = Zmod.add initial.(getPc) (bits.of_Z width (4 * (Z.of_nat (List.length asm_prog_1)))) ->
      subset (footpr (program iset initial.(getPc) asm_prog_1 * Rexec)%sep)
             (of_list initial.(getXAddrs)) ->
      (program iset initial.(getPc) asm_prog_1 * Rexec * R)%sep initial.(getMem) ->
      initial.(getNextPc) = Zmod.add initial.(getPc) (bits.of_Z width 4) ->
      runsTo (mcomp_sat (run1 iset)) initial
             (fun final =>
                final.(getPc) = newPc /\
                final.(getNextPc) = add newPc (bits.of_Z width 4) /\
                subset (footpr (program iset initial.(getPc) asm_prog_1 * Rexec)%sep)
                       (of_list final.(getXAddrs)) /\
                (program iset initial.(getPc) asm_prog_1 * Rexec * R)%sep final.(getMem) /\
                map.get final.(getRegs) x2 = Some (gallina_prog_1 v1 v2)).
  Proof.
    intros.
    assert (valid_register x1). { unfold valid_register, x1. blia. }
    assert (valid_register x2). { unfold valid_register, x2. blia. }
    destruct_RiscvMachine initial.
    unfold asm_prog_1 in *.
    simpl in *. simp.
    subst.
    run1det.
    run1det.
    eapply runsToDone.
    simpl.
    repeat split; first [ solve_word_eq | assumption | idtac ].
    apply map.get_put_same.
  Qed.

  Opaque asm_prog_1.

  Definition gallina_prog_2(v1 v2: w32): word :=
    gallina_prog_1 (bits.of_Z width (BitOps.signExtend 32 (LittleEndian.combine 4 v1)))
                   (bits.of_Z width (BitOps.signExtend 32 (LittleEndian.combine 4 v2))).

  Arguments LittleEndian.combine: simpl never.

  Axiom fix_updated_mem_TODO: False.
  Axiom fix_footpr_TODO: False.

  Arguments Z.add: simpl never.
  Arguments Z.mul: simpl never.
  Arguments Z.of_nat: simpl never.

  Lemma asm_prog_2_correct: forall (initial: MetricRiscvMachine) newPc
                                  (argvars resvars: list Register) R Rexec (v1 v2 dummy: w32),
      newPc = Zmod.add initial.(getPc) (bits.of_Z width (4 * Z.of_nat (List.length asm_prog_2))) ->
      subset (footpr (program iset initial.(getPc) asm_prog_2 * Rexec)%sep)
             (of_list initial.(getXAddrs)) ->
      (program iset initial.(getPc) asm_prog_2 * Rexec *
       ptsto_bytes 4%nat (bits.of_Z width input_ptr) v1 *
       ptsto_bytes 4%nat (bits.of_Z width (input_ptr+4)) v2 *
       ptsto_bytes 4%nat (bits.of_Z width output_ptr) dummy * R)%sep initial.(getMem) ->
      initial.(getNextPc) = Zmod.add initial.(getPc) (bits.of_Z width 4) ->
      runsTo (mcomp_sat (run1 iset)) initial
             (fun final =>
                final.(getPc) = newPc /\
                final.(getNextPc) = add newPc (bits.of_Z width 4) /\
                subset (footpr (program iset initial.(getPc) asm_prog_2 * Rexec)%sep)
                       (of_list final.(getXAddrs)) /\
                (program iset initial.(getPc) asm_prog_2 * Rexec * R)%sep final.(getMem) /\
                map.get final.(getRegs) x2 = Some (gallina_prog_2 v1 v2)).
  Proof.
    intros.
    assert (valid_register x1). { unfold valid_register, x1. blia. }
    assert (valid_register x2). { unfold valid_register, x2. blia. }
    destruct_RiscvMachine initial.
    unfold asm_prog_2 in *.
    simpl in *.
    unfold program in *.
    subst.
    simpl.

    run1det.
    run1det.

(* TODO integrate changes into GoFlatToRiscv *)
Ltac sidecondition ::=
  simpl; simpl_MetricRiscvMachine_get_set;
  match goal with
  (* these branches are allowed to instantiate evars in a controlled manner: *)
  | H: map.get _ _ = Some _ |- _ => exact H
  | |- map.get _ _ = Some _ =>
    simpl;
    match goal with
    | |- map.get (map.put _ ?x _) ?y = Some _ =>
      constr_eq x y; apply map.get_put_same
    end
  | |- @sep ?K ?V ?M ?P ?Q ?m => simpl in *;
                                 simpl_MetricRiscvMachine_get_set;
                                 wcancel_assumption
  | H: subset (footpr _) _ |- subset (footpr ?F) _ =>
    tryif is_evar F then
      eassumption
    else
      (simpl in H |- *; eapply rearrange_footpr_subset; [ exact H | solve [wwcancel] ])
  | |- _ => reflexivity
  | A: map.get ?lH ?x = Some _, E: map.extends ?lL ?lH |- map.get ?lL ?x = Some _ =>
    eapply (map.extends_get A E)
  (* but we don't have a general "eassumption" branch, only "assumption": *)
  | |- _ => solve [auto using valid_FlatImp_var_implies_valid_register,
                              valid_FlatImp_vars_bcond_implies_valid_registers_bcond]
  | |- Memory.store ?sz ?m ?addr ?val = Some ?m' => eassumption
  | |- _ => sidecondition_hook
  end.


    eapply runsTo_trans. {
      eapply asm_prog_1_correct; simpl; try sidecondition.
      rewrite map.get_put_diff by (unfold x1, x2; blia).
      apply map.get_put_same.
    }
    simpl.
    intros middle (? & ? & ? & ? & ?).
    destruct_RiscvMachine middle. simpl in *.
    subst. simp.

    (* TODO matching up addresses should work automatically *)
    replace (Zmod.add
              (Zmod.add (Zmod.add initial_pc (bits.of_Z width 4)) (bits.of_Z width 4))
              (bits.of_Z width
                 (Zmod.unsigned (bits.of_Z width 4) *
                  BinInt.Z.of_nat (@Datatypes.length Instruction asm_prog_1))))
      with (Zmod.add
        (Zmod.add (Zmod.add initial_pc (bits.of_Z width 4)) (bits.of_Z width 4))
        (Zmod.mul (bits.of_Z width 4)
           (bits.of_Z width (Z.of_nat (@Datatypes.length Instruction asm_prog_1)))))
      in H1; cycle 1. {
      clear.
      change BinInt.Z.of_nat with Z.of_nat in *.
      f_equal.
      apply Zmod.unsigned_inj.
      rewrite Zmod.unsigned_mul.
      rewrite bits.unsigned_of_Z at 2.
      rewrite (bits.unsigned_of_Z (4 mod 2 ^ width * Z.of_nat (Datatypes.length asm_prog_1))).
      rewrite! bits.unsigned_of_Z.
      apply Zmult_mod_idemp_r.
    }

    run1det.
    eapply runsToDone.
    simpl.
    repeat split.
    - solve_word_eq.
    - solve_word_eq.
    - (* TODO *) case fix_footpr_TODO.
    - (* TODO *) case fix_updated_mem_TODO.
    - assumption.
  Qed.

End Verif.

(* Print Assumptions asm_prog_2_correct. *)
