Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import lib.LibTactics.
Require Import bbv.Word.
Require Import compiler.StateMonad.

(* allows inifinite number of registers *)
Definition Reg := nat.

Definition R0: Reg := 0.

Definition Regs := Reg -> option (word 32).

Inductive Instruction: Set :=
  | Addi(rd: Reg)(rs1: Reg)(imm12: word 12): Instruction
  | Add(rd: Reg)(rs1: Reg)(rs2: Reg): Instruction
  | Mul(rd: Reg)(rs1: Reg)(rs2: Reg): Instruction
  | Halt: Instruction.

Definition Nop := Addi R0 R0 $0. (* NOP encoding as per RISC-V, does nothing except pc++ *)

Record MachineState := mkMachineState {
  (* instruction memory, immutable *)
  imem: list Instruction;
  pc: nat;
  regs: Regs
}.

Definition update(regs: Regs)(reg: Reg)(v: word 32): Regs :=
  fun (r: Reg) =>
    if beq_nat r 0 then Some ($ 0) else (* register 0 is read-only 0 *)
    if beq_nat r reg then Some v else regs r.

Definition step(s: MachineState): option MachineState :=
  let (imem, pc, regs) := s in
  inst <- nth_error imem pc;
  match inst with
  | Addi rd rs1 imm12 =>
      v1 <- regs rs1;
      let v2 := zext imm12 20 in
      let v3 := v1 ^+ v2 in
      Return (mkMachineState imem (S pc) (update regs rd v3))
  | Add rd rs1 rs2 =>
      v1 <- regs rs1;
      v2 <- regs rs2;
      let v3 := v1 ^+ v2 in
      Return (mkMachineState imem (S pc) (update regs rd v3))
  | Mul rd rs1 rs2 =>
      v1 <- regs rs1;
      v2 <- regs rs2;
      let v3 := v1 ^* v2 in
      Return (mkMachineState imem (S pc) (update regs rd v3))
  | Halt => Some s (* does not do anything, not even increase pc *)
  end.

Definition isDone(s: MachineState): bool :=
  match nth_error s.(imem) s.(pc) with
  | Some Halt => true
  | _ => false
  end.

(* None means failure, out of fuel is considered success *)
Fixpoint run(fuel: nat)(s: MachineState): option MachineState :=
  match fuel with
  | 0 => Some s
  | S n => s' <- step s; run n s'
  end.


(* arithmetic expressions *)
Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Fixpoint interp(e: aexp): nat :=
  match e with
  | ANum x => x
  | APlus x y => (interp x) + (interp y)
  | AMult x y => (interp x) * (interp y)
  end.

(* returns register into which result is saved, and that's the highest used register *)
Fixpoint compile(firstFree: Reg)(e: aexp): (list Instruction * Reg) :=
  match e with
  | ANum n => ([Addi firstFree R0 $n], firstFree)
  | APlus x y =>
      let (p1, r1) := compile firstFree x in
      let (p2, r2) := compile (S r1) y in
      (p1 ++ p2 ++ [Add (S r2) r1 r2], S r2)
  | AMult x y =>
      let (p1, r1) := compile firstFree x in
      let (p2, r2) := compile (S r1) y in
      (p1 ++ p2 ++ [Mul (S r2) r1 r2], S r2)
  end.


Definition initialState(prog: list Instruction): MachineState := {|
  imem := prog;
  pc := 0;
  regs := fun (r: Reg) => if beq_nat r 0 then Some ($ 0) else None
|}.

Definition aboutToRun(im0 prog: list Instruction)(regs: Regs): MachineState := {|
  imem := im0 ++ prog;
  pc := length im0;
  regs := fun (r: Reg) => if beq_nat r 0 then Some ($ 0) else regs r
|}.

Lemma imem_readonly_step: forall s1 s2,
  step s1 = Some s2 ->
  s1.(imem) = s2.(imem).
Proof.
  introv E.
  destruct s1 as [imem1 pc1 regs1].
  destruct s2 as [imem2 pc2 regs2].
  unfold step in E.
  destruct (nth_error imem1 pc1); [|inversion E].
  destruct i; simpl in *; try destruct (regs1 rs1); inversion E; try reflexivity;
  try destruct (regs1 rs2); inversion E; reflexivity.
Qed.

Lemma run_snoc_inv: forall f s1 s3,
  run (S f) s1 = Some s3 ->
  exists s2, run f s1 = Some s2 /\ step s2 = Some s3.
Proof.
  induction f; introv E.
  - eexists. apply (conj eq_refl). simpl in E. destruct (step s1); assumption.
  - remember (S f) as Sf. simpl in E. destruct (step s1) as [s2|] eqn: E2; [|inversion E].
    subst Sf.
    specialize (IHf _ _ E). destruct IHf as [s29 [R St29]].
    exists s29.
    refine (conj _ St29).
    simpl. rewrite E2. exact R.
Qed.

Lemma imem_readonly_run: forall f s1 s2,
  run f s1 = Some s2 ->
  s1.(imem) = s2.(imem).
Proof.
  induction f; introv E.
  - simpl in E. inversion E. subst. reflexivity.
  - apply run_snoc_inv in E. destruct E as [s19 [R St19]].
    specialize (IHf _ _ R). rewrite IHf.
    apply imem_readonly_step. exact St19.
Qed.

(* TODO only holds if n not too big *)
Axiom zext_bounds: forall n sz1 sz2,
  zext (natToWord sz1 n) sz2 = natToWord (sz1 + sz2) n.

(* TODO doesn't hold *)
Axiom reg0: forall rs: Regs,
  rs = fun r : Reg => if r =? 0 then Some $ (0) else rs r.

Lemma double_reg0: forall (rs0: Regs),
  (fun r : Reg => if r =? 0 then Some $ (0)
                 else if r =? 0 then Some $ (0) else rs0 r)
  = (fun r : Reg => if r =? 0 then Some $ (0) else rs0 r).
Proof.
  intros. extensionality r. destruct (r =? 0) eqn: E; reflexivity.
Qed.

(* TODO only if within bounds *)
Axiom distrib_plus_over_natToWord: forall n1 n2 sz,
  (natToWord sz n1) ^+ (natToWord sz n2) = (natToWord sz (n1 + n2)).

(* TODO only if within bounds *)
Axiom distrib_mult_over_natToWord: forall n1 n2 sz,
  (natToWord sz n1) ^* (natToWord sz n2) = (natToWord sz (n1 * n2)).

Lemma destruct_run_S: forall f s1 s3,
  run (S f) s1 = Some s3 ->
  exists s2, step s1 = Some s2 /\ run f s2 = Some s3.
Proof.
  intros. simpl in H. destruct (step s1) as [s2|].
  - eauto.
  - inversion H.
Qed.

Lemma concat_run: forall f12 f23 s1 s2 s3,
  run f12 s1 = Some s2 ->
  run f23 s2 = s3 ->
  run (f12 + f23) s1 = s3.
Proof.
  induction f12; introv R1 R2.
  - simpl in *. inversions R1. reflexivity.
  - apply destruct_run_S in R1. destruct R1 as [s1' [St R1']].
    simpl. rewrite St.
    eapply IHf12; eauto.
Qed.

Lemma run_snoc: forall f12 s1 s2 s3,
  run f12 s1 = Some s2 ->
  step s2 = s3 ->
  run (S f12) s1 = s3.
Proof.
  intros. replace (S f12) with (f12 + 1) by omega.
  eapply concat_run; [ eassumption | ]. subst s3. simpl. destruct (step s2); reflexivity.
Qed.

Lemma compile_correct_aux: forall e lastUsed im0 prog im1 resReg rs,
  compile (S lastUsed) e = (prog, resReg) ->
  rs 0 = Some $0 ->
  exists fuel final,
    run fuel (aboutToRun im0 (prog ++ im1) rs) = Some final /\
    final.(pc) = length (im0 ++ prog) /\
    final.(regs) resReg = Some $(interp e) /\
    resReg > lastUsed /\
    forall r, r <= lastUsed \/ r > resReg -> rs r = final.(regs) r.
Proof.
  intro e. induction e; introv CEq Rs0.
  - simpl in CEq. inversions CEq.
    exists 1. simpl.
    rewrite nth_error_app2 by omega.
    replace (length im0 - length im0) with 0 by omega.
    simpl.
    eexists. apply (conj eq_refl). simpl. rewrite app_length.
    simpl. split; [omega|]. repeat split.
    + unfold update. simpl.
      rewrite Nat.eqb_refl. f_equal.
      rewrite wplus_unit. rewrite zext_bounds. reflexivity.
    + omega.
    + introv B. unfold update. destruct r.
      * rewrite <- beq_nat_refl. assumption.
      * destruct (S r =? 0) eqn: E; [ apply beq_nat_true in E; omega |].
        destruct (S r =? S lastUsed) eqn: E2;
          [ apply beq_nat_true in E2 | apply beq_nat_false in E2].
        { inversions E2. omega. }
        { reflexivity. }
  - simpl in CEq.
    destruct (compile (S lastUsed) e1) as [p1 r1] eqn: E1.
    destruct (compile (S r1) e2) as [p2 r2] eqn: E2.
    inversions CEq.
    specialize (IHe1 _ im0 p1 (p2 ++ [Add (S r2) r1 r2] ++ im1) _ rs E1 Rs0).
    destruct IHe1 as [fuel1 [final1 [Run1 [Pc1 [Regs1 [B1 U1]]]]]].
    destruct final1 as [im pc1 rs1].
    lets Ei1: (imem_readonly_run _ _ _ Run1). simpl in Ei1. subst im.
    simpl in U1.
    lets Rs1: (U1 0). specializes Rs1; [omega|]. symmetry in Rs1. rewrite Rs0 in Rs1.
    specialize (IHe2 _ (im0 ++ p1) p2 ([Add (S r2) r1 r2] ++ im1) _ rs1 E2 Rs1).
    destruct IHe2 as [fuel2 [final2 [Run2 [Pc2 [Regs2 [B2 U2]]]]]].
    destruct final2 as [im pc2 rs2].
    lets Ei2: (imem_readonly_run _ _ _ Run2). simpl in Ei2. subst im.
    simpl in Pc1, Pc2. subst pc1 pc2.
    simpl in Regs1, Regs2, U2.
    unfold aboutToRun in Run2.
    repeat rewrite <- app_assoc in Run2.
    rewrite (reg0 rs1) in Run1. simpl in Run2.
    lets R12: (concat_run _ _ _ _ _ Run1 Run2).
    evar (iF: list Instruction). evar (pF: nat). evar (rF: Regs).
    exists (S (fuel1 + fuel2)).
    exists (mkMachineState iF pF rF).
    subst iF pF rF.
    repeat rewrite <- app_assoc.
    split.
    + eapply run_snoc; [ eapply R12 |].
      simpl.
      replace (nth_error (im0 ++ p1 ++ p2 ++ Add (S r2) r1 r2 :: im1)
                         (length (im0 ++ p1 ++ p2)))
         with (Some (Add (S r2) r1 r2)).
      * rewrite Regs2.
        specialize (U2 r1). specializes U2; [omega|].
        rewrite <- U2. rewrite Regs1.
        reflexivity.
      * replace (im0 ++ p1 ++ p2 ++ Add (S r2) r1 r2 :: im1)
           with ((im0 ++ p1 ++ p2) ++ Add (S r2) r1 r2 :: im1).
        { rewrite nth_error_app2 by omega.
          replace (length (im0 ++ p1 ++ p2) - length (im0 ++ p1 ++ p2)) with 0 by omega.
          simpl. reflexivity. }
        { repeat rewrite <- app_assoc. reflexivity. }
    + simpl. repeat split.
      * replace (im0 ++ p1 ++ p2 ++ [Add (S r2) r1 r2])
           with ((im0 ++ p1 ++ p2) ++ [Add (S r2) r1 r2]).
        { remember (im0 ++ p1 ++ p2) as l.
          rewrite app_length. simpl. omega. }
        { repeat rewrite <- app_assoc. reflexivity. }
      * unfold update. clear.
        destruct (S r2 =? 0) eqn: E.
        { symmetry in E. apply beq_nat_eq in E. omega. }
        { rewrite <- beq_nat_refl.
          f_equal. apply distrib_plus_over_natToWord. }
      * omega.
      * introv B. unfold update.
        destruct (r =? 0) eqn: E;
          [apply beq_nat_true in E; subst; assumption | apply beq_nat_false in E].
        destruct r; [omega|].
        clear E.
        destruct (S r =? S r2) eqn: E;
          [apply beq_nat_true in E | apply beq_nat_false in E].
        { inversions E. omega. (* contradiction *) }
        { rewrite U1 by omega. rewrite U2 by omega. reflexivity. }
  - (* TODO code duplication alert! *)
    simpl in CEq.
    destruct (compile (S lastUsed) e1) as [p1 r1] eqn: E1.
    destruct (compile (S r1) e2) as [p2 r2] eqn: E2.
    inversions CEq.
    specialize (IHe1 _ im0 p1 (p2 ++ [Mul (S r2) r1 r2] ++ im1) _ rs E1 Rs0).
    destruct IHe1 as [fuel1 [final1 [Run1 [Pc1 [Regs1 [B1 U1]]]]]].
    destruct final1 as [im pc1 rs1].
    lets Ei1: (imem_readonly_run _ _ _ Run1). simpl in Ei1. subst im.
    simpl in U1.
    lets Rs1: (U1 0). specializes Rs1; [omega|]. symmetry in Rs1. rewrite Rs0 in Rs1.
    specialize (IHe2 _ (im0 ++ p1) p2 ([Mul (S r2) r1 r2] ++ im1) _ rs1 E2 Rs1).
    destruct IHe2 as [fuel2 [final2 [Run2 [Pc2 [Regs2 [B2 U2]]]]]].
    destruct final2 as [im pc2 rs2].
    lets Ei2: (imem_readonly_run _ _ _ Run2). simpl in Ei2. subst im.
    simpl in Pc1, Pc2. subst pc1 pc2.
    simpl in Regs1, Regs2, U2.
    unfold aboutToRun in Run2.
    repeat rewrite <- app_assoc in Run2.
    rewrite (reg0 rs1) in Run1. simpl in Run2.
    lets R12: (concat_run _ _ _ _ _ Run1 Run2).
    evar (iF: list Instruction). evar (pF: nat). evar (rF: Regs).
    exists (S (fuel1 + fuel2)).
    exists (mkMachineState iF pF rF).
    subst iF pF rF.
    repeat rewrite <- app_assoc.
    split.
    + eapply run_snoc; [ eapply R12 |].
      simpl.
      replace (nth_error (im0 ++ p1 ++ p2 ++ Mul (S r2) r1 r2 :: im1)
                         (length (im0 ++ p1 ++ p2)))
         with (Some (Mul (S r2) r1 r2)).
      * rewrite Regs2.
        specialize (U2 r1). specializes U2; [omega|].
        rewrite <- U2. rewrite Regs1.
        reflexivity.
      * replace (im0 ++ p1 ++ p2 ++ Mul (S r2) r1 r2 :: im1)
           with ((im0 ++ p1 ++ p2) ++ Mul (S r2) r1 r2 :: im1).
        { rewrite nth_error_app2 by omega.
          replace (length (im0 ++ p1 ++ p2) - length (im0 ++ p1 ++ p2)) with 0 by omega.
          simpl. reflexivity. }
        { repeat rewrite <- app_assoc. reflexivity. }
    + simpl. repeat split.
      * replace (im0 ++ p1 ++ p2 ++ [Mul (S r2) r1 r2])
           with ((im0 ++ p1 ++ p2) ++ [Mul (S r2) r1 r2]).
        { remember (im0 ++ p1 ++ p2) as l.
          rewrite app_length. simpl. omega. }
        { repeat rewrite <- app_assoc. reflexivity. }
      * unfold update. clear.
        destruct (S r2 =? 0) eqn: E.
        { symmetry in E. apply beq_nat_eq in E. omega. }
        { rewrite <- beq_nat_refl.
          f_equal. apply distrib_mult_over_natToWord. }
      * omega.
      * introv B. unfold update.
        destruct (r =? 0) eqn: E;
          [apply beq_nat_true in E; subst; assumption | apply beq_nat_false in E].
        destruct r; [omega|].
        clear E.
        destruct (S r =? S r2) eqn: E;
          [apply beq_nat_true in E | apply beq_nat_false in E].
        { inversions E. omega. (* contradiction *) }
        { rewrite U1 by omega. rewrite U2 by omega. reflexivity. }
Qed.

Lemma compile_correct: forall e prog resReg,
  compile 1 e = (prog, resReg) ->
  exists fuel final,
    run fuel (initialState prog) = Some final /\ final.(regs) resReg = Some $(interp e).
Proof.
  introv C.
  lets E: (compile_correct_aux _ _ [] prog [] _ (initialState prog).(regs) C eq_refl).
  destruct E as [fuel [final [R [Pc [Regs [B U]]]]]].
  exists fuel final.
  unfold aboutToRun in R.
  rewrite app_nil_l, app_nil_r in *.
  unfold initialState.
  simpl in R.
  rewrite double_reg0 in R.
  apply (conj R Regs).
Qed.
