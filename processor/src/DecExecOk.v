Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Kami.Lib.Word.
Require Import riscv.Spec.Decode.
Require Import coqutil.Map.Interface.

Require Import processor.KamiWord.
Require Import riscv.Utility.Utility.

Require Import Kami.Syntax Kami.Semantics Kami.Tactics.
Require Import Kami.Ex.MemTypes.
Require Import Kami.Ex.IsaRv32.

Require Import processor.KamiProc.

Local Open Scope Z_scope.

Section DecExecOk.

  Instance W: Utility.Words := @KamiWord.WordsKami width width_cases.

  Variables (instrMemSizeLg: Z).
  Hypothesis (HinstrMemBound: instrMemSizeLg <= width - 2).

  Local Definition kamiProc := @KamiProc.proc instrMemSizeLg.
  Local Definition KamiSt := @KamiProc.st instrMemSizeLg.

  (** * Register file mapping *)

  Context {Registers: map.map Register word}.

  Definition convertRegs (rf: kword 5 -> kword width): Registers :=
    let kkeys := HList.tuple.unfoldn (wplus (natToWord 5 1)) 31 (natToWord 5 1) in
    let values := HList.tuple.map rf kkeys in
    let keys := HList.tuple.map (@wordToZ 5) kkeys in
    map.putmany_of_tuple keys values map.empty.

  Lemma convertRegs_get:
    forall rf r v,
      map.get (convertRegs rf) (Word.wordToZ r) = Some v ->
      v = rf r.
  Proof.
  Admitted.

  Lemma convertRegs_put:
    forall rf r v,
      convertRegs (fun w => if weq w r then v else rf w) =
      map.put (convertRegs rf) (Word.wordToZ r) v.
  Proof.
    intros.
    eapply map.map_ext.
    intros k.
  Admitted.

  Lemma invert_Kami_execNm:
    forall km1 kt1 kupd klbl,
      KamiProc.RegsToT km1 = Some kt1 ->
      Step kamiProc km1 kupd klbl ->
      klbl.(annot) = Some (Some "execNm"%string) ->
      exists kt2: KamiSt,
        klbl.(calls) = FMap.M.empty _ /\
        KamiProc.RegsToT (FMap.M.union kupd km1) = Some kt2 /\
        exists curInst npc prf dst exec_val,
          curInst = (KamiProc.pgm kt1) (split2 _ _ (KamiProc.pc kt1)) /\
          npc = evalExpr (rv32NextPc
                            _ _
                            (KamiProc.rf kt1) (KamiProc.pc kt1)
                            curInst) /\
          prf = KamiProc.rf kt1 /\
          dst = evalExpr (rv32GetDst _ curInst) /\
          exec_val = evalExpr
                       (rv32Exec
                          _ _
                          (KamiProc.rf kt1 (evalExpr (rv32GetSrc1 _ curInst)))
                          (KamiProc.rf kt1 (evalExpr (rv32GetSrc2 _ curInst)))
                          (KamiProc.pc kt1)
                          curInst) /\
          kt2 = {| KamiProc.pc := npc;
                   KamiProc.rf :=
                     evalExpr
                       (UpdateVector
                          (Var _ (SyntaxKind (Vector (Bit (Z.to_nat width))
                                                     rv32RfIdx)) prf)
                          (Var _ (SyntaxKind (Bit rv32RfIdx)) dst)
                          (Var _ (SyntaxKind (Bit (Z.to_nat width))) exec_val));
                   KamiProc.pgm := KamiProc.pgm kt1;
                   KamiProc.mem := KamiProc.mem kt1 |}.
  Proof.
    intros.
    kinvert; try (repeat
                    match goal with
                    | [H: annot ?klbl = Some _ |- _] => rewrite H in *
                    | [H: (_ :: _)%struct = (_ :: _)%struct |- _] =>
                      inversion H; subst; clear H
                    end; discriminate).

    Opaque evalExpr.
    kinv_action_dest.
    unfold KamiProc.RegsToT in *.
    kregmap_red.
    destruct x1; try discriminate.
    destruct (FMap.M.find "mem"%string km1)
      as [[[kind|] memv]|]; try discriminate.
    destruct (decKind kind (Vector (Bit (Z.to_nat width)) (Z.to_nat width)));
      try discriminate.
    kregmap_red.
    inversion_clear H.
    eexists; split; [|split].
    - assumption.
    - reflexivity.
    - do 5 eexists.
      repeat (split; [reflexivity|]).
      reflexivity.
      Transparent evalExpr.

  Qed.

  Ltac lets_in_hyp_to_eqs :=
    repeat lazymatch goal with
           | |- (let x := ?a in ?b) = ?c -> ?Q =>
             change (let x := a in b = c -> Q); intro
           | x := bitSlice _ 25 26 |- _ =>
            (* shamtHi is the only field which another field depends on *)
             subst x
           | x := ?t : ?T |- _ =>
             pose proof (eq_refl t : x = t); clearbody x
           end.

  Ltac invert_decode_if_true G :=
    first [ apply Bool.andb_true_iff in G;
            let G1 := fresh G in let G2 := fresh G in destruct G as [G1 G2];
            invert_decode_if_true G1; invert_decode_if_true G2
          | apply Z.eqb_eq in G
          | idtac ].

  (* TODO rather than stating this as a lemma, write a tactic which
     infers & poses the conclusion *)
  Lemma invert_decode_Add: forall inst rd rs1 rs2: Z,
      decode RV32IM inst = IInstruction (Decode.Add rd rs1 rs2) ->
      bitSlice inst 0 7 = opcode_OP /\
      bitSlice inst 7 12 = rd /\
      bitSlice inst 12 15 = funct3_ADD /\
      bitSlice inst 15 20 = rs1 /\
      bitSlice inst 20 25 = rs2 /\
      bitSlice inst 25 32 = funct7_ADD.
  Proof.
    intros *.
    cbv beta delta [decode].
    lets_in_hyp_to_eqs.
    subst
      resultI
      resultM
      resultA
      resultF
      resultI64
      resultM64
      resultA64
      resultF64
      resultCSR.
    repeat match type of H with
    | context C [if ?a then ?b else ?c] =>
      ((let P := context C [ b ] in change P in H) ||
       (let P := context C [ c ] in change P in H))
    end.
    subst results.
    destruct (isValidI decodeI) eqn: VI;
    destruct (isValidM decodeM) eqn: VM;
    destruct (isValidCSR decodeCSR) eqn: VCSR.
    all: try (clear; simpl; discriminate).
    simpl.
    intro E.
    injection E. clear E.
    subst decodeI.
    intro E.
    repeat match type of E with
    | (if ?a then ?b else ?c) = ?d => destruct a; [discriminate E|]
    end.
    match type of E with
    | (if ?a then ?b else ?c) = ?d => destruct a eqn: G; cycle 1
    end.
    { (* more invalid cases *)
      repeat match type of E with
             | (if ?a then ?b else ?c) = ?d => destruct a; [discriminate E|]
             end.
      discriminate E.
    }
    (* the only valid case remains *)
    subst rd0 rs4 rs0.
    invert_decode_if_true G.
    assert (bitSlice inst 0 7 = opcode_OP) as R1 by congruence; revert R1.
    assert (bitSlice inst 12 15 = funct3_ADD) as R2 by congruence; revert R2.
    assert (bitSlice inst 25 32 = funct7_ADD) as R3 by congruence; revert R3.
    injection E.
    clear.
    (* if we automate this further, we might be able to infer the conclusion with a tactic
       rather than having to state it manually *)
    intros. auto.
  Qed.

  Lemma kami_split_bitSlice_consistent_1:
    forall (i: nat) kinst,
      wordToZ (split1 i (32 - i) kinst) =
      bitSlice (wordToZ kinst) 0 (Z.of_nat i).
  Proof.
  Admitted.

  Lemma kami_split_bitSlice_consistent_2:
    forall (i j: nat) kinst,
      wordToZ (split2 i j kinst) =
      bitSlice (wordToZ kinst) (Z.of_nat i) (Z.of_nat (i + j)).
  Proof.
  Admitted.

  Lemma kami_split_bitSlice_consistent_3:
    forall (i j: nat) kinst,
      wordToZ
        (split2 i j (split1 (i + j) (32 - (i + j)) kinst)) =
      bitSlice (wordToZ kinst) (Z.of_nat i) (Z.of_nat (i + j)).
  Proof.
  Admitted.

  Lemma kami_getOpcode_ok:
    forall kinst,
      wordToZ
        (evalExpr
           (getOpcodeE (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) =
      bitSlice (wordToZ kinst) 0 7.
  Proof.
    intros.
    unfold getOpcodeE.
    unfold evalExpr; fold evalExpr.
    unfold evalUniBit.
    rewrite kami_split_bitSlice_consistent_1.
    reflexivity.
  Qed.

  Lemma kami_getFunct7_ok:
    forall kinst,
      wordToZ
        (evalExpr
           (getFunct7E (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) =
      bitSlice (wordToZ kinst) 25 32.
  Proof.
    intros.
    unfold getFunct7E.
    unfold evalExpr; fold evalExpr.
    unfold evalUniBit.
    rewrite kami_split_bitSlice_consistent_2.
    reflexivity.
  Qed.

  Lemma kami_getFunct3_ok:
    forall kinst,
      wordToZ
        (evalExpr
           (getFunct3E (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) =
      bitSlice (wordToZ kinst) 12 15.
  Proof.
    intros.
    unfold getFunct3E.
    unfold evalExpr; fold evalExpr.
    unfold evalUniBit.
    rewrite kami_split_bitSlice_consistent_3.
    reflexivity.
  Qed.

  Lemma kami_getRdE_ok:
    forall kinst,
      wordToZ
        (evalExpr (getRdE (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) =
      bitSlice (wordToZ kinst) 7 12.
  Proof.
    intros.
    unfold getRdE.
    unfold evalExpr; fold evalExpr.
    unfold evalUniBit.
    rewrite kami_split_bitSlice_consistent_3.
    reflexivity.
  Qed.

  Lemma kami_rv32GetDst_ok:
    forall kinst,
      bitSlice (wordToZ kinst) 0 7 = opcode_OP ->
      Word.wordToZ (evalExpr (rv32GetDst type kinst)) =
      bitSlice (wordToZ kinst) 7 12.
  Proof.
    intros.
    unfold rv32GetDst.
    unfold evalExpr; fold evalExpr.
    destruct (isEq _ _) as [Heq|Hne].
    - exfalso.
      pose proof (kami_getOpcode_ok kinst).
      rewrite Heq, H in H0; discriminate.
    - rewrite kami_getRdE_ok; reflexivity.
  Qed.

  Lemma kami_rv32GetSrc1_ok:
    forall kinst,
      Word.wordToZ (evalExpr (rv32GetSrc1 type kinst)) =
      bitSlice (wordToZ kinst) 15 20.
  Proof.
    intros.
    unfold rv32GetSrc1, getRs1E.
    unfold evalExpr; fold evalExpr.
    unfold evalUniBit.
    rewrite kami_split_bitSlice_consistent_3.
    reflexivity.
  Qed.

  Lemma kami_rv32GetSrc2_ok:
    forall kinst,
      Word.wordToZ (evalExpr (rv32GetSrc2 type kinst)) =
      bitSlice (wordToZ kinst) 20 25.
  Proof.
    intros.
    unfold rv32GetSrc2, getRs2E.
    unfold evalExpr; fold evalExpr.
    unfold evalUniBit.
    rewrite kami_split_bitSlice_consistent_3.
    reflexivity.
  Qed.

  (** TODO @joonwonc: ditto [invert_decode_Add]; better to have a tactic. *)
  Lemma kami_rv32Exec_Add_ok:
    forall v1 v2 pc kinst,
      wordToZ
        (evalExpr
           (getOpcodeE (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) =
      opcode_OP ->
      wordToZ
        (evalExpr (getFunct7E (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) =
      funct7_ADD ->
      wordToZ
        (evalExpr (getFunct3E (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) =
      funct3_ADD ->
      evalExpr (rv32Exec (Z.to_nat instrMemSizeLg) type v1 v2 pc kinst) =
      v1 ^+ v2.
  Proof.
    intros.
    unfold rv32Exec.
    unfold evalExpr; fold evalExpr.
    do 5 (destruct (isEq _ _); [rewrite e in H; discriminate|clear n]).
    do 3 (destruct (isEq _ _); [|exfalso; elim n; apply wordToZ_inj; assumption]).
    reflexivity.
  Qed.

  Lemma kami_rv32NextPc_op_ok:
    forall rf pc kinst,
      wordToZ
        (evalExpr
           (getOpcodeE (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) =
      opcode_OP ->
      evalExpr (rv32NextPc (Z.to_nat instrMemSizeLg) type rf pc kinst) =
      pc ^+ $4.
  Proof.
    intros.
    unfold rv32NextPc.
    unfold evalExpr; fold evalExpr.
    do 3 (destruct (isEq _ _); [rewrite e in H; discriminate|clear n]).
    unfold evalBinBit.
    unfold evalConstT.
    f_equal.
  Admitted.

End DecExecOk.
