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

Set Implicit Arguments.

Local Open Scope Z_scope.

Axiom TODO_joonwon: False.

Lemma unsigned_wordToZ n z : Z.of_N (wordToN (ZToWord n z)) = z mod 2^(Z.of_nat n).
Admitted.

Lemma unsigned_inj n x y : Z.of_N (@wordToN n x) = Z.of_N (@wordToN n y) -> x = y.
Admitted.

Lemma sumbool_rect_weq {T} a b n x y :
  sumbool_rect (fun _ => T) (fun _ => a) (fun _ => b) (@weq n x y) = if weqb x y then a else b.
Proof.
  cbv [sumbool_rect].
  destruct (weq _ _), (weqb _ _) eqn:?;
  try match goal with H : _ |- _ => eapply weqb_true_iff in H end;
  trivial; congruence.
Qed.

Lemma sumbool_rect_bool_weq n x y :
  sumbool_rect (fun _ => bool) (fun _ => true) (fun _ => false) (@weq n x y) = weqb x y.
Proof. rewrite sumbool_rect_weq; destruct (weqb x y); trivial. Qed.

Lemma unsigned_eqb n x y : Z.eqb (Z.of_N (wordToN x)) (Z.of_N (wordToN y)) = @weqb n x y.
Admitted.

Lemma unsigned_split1_as_bitSlice a b x :
  Z.of_N (wordToN (split1 a b x)) = bitSlice (Z.of_N (wordToN x)) 0 (Z.of_nat a).
Admitted.

Lemma unsigned_split2_as_bitSlice a b x :
  Z.of_N (wordToN (split2 a b x)) = bitSlice (Z.of_N (wordToN x)) (Z.of_nat a) (Z.of_nat a + Z.of_nat b).
Admitted.

Lemma unsigned_split2_split1_as_bitSlice a b c x :
  Z.of_N (wordToN (split2 a b (split1 (a+b) c x))) = bitSlice (Z.of_N (wordToN x)) (Z.of_nat a) (Z.of_nat a + Z.of_nat b).
Admitted.

Section DecExecOk.

  Instance W: Utility.Words := @KamiWord.WordsKami width width_cases.

  Variables (instrMemSizeLg: Z).
  Hypothesis (HinstrMemBound: 3 <= instrMemSizeLg <= width - 2).

  Local Definition kamiProc := @KamiProc.proc instrMemSizeLg.
  Local Definition KamiSt := @KamiProc.st instrMemSizeLg.

  (** * Register file mapping *)

  Context {Registers: map.map Register word}
          (Registers_ok : map.ok Registers).
  
  Definition regs_related (krf: kword 5 -> kword width)
             (rrf: Registers): Prop :=
    forall w, w <> $0 -> map.get rrf (Z.of_N (wordToN w)) = Some (krf w).

  Lemma regs_related_get:
    forall krf (Hkrf0: forall idx, idx = $0 -> krf idx = $0) rrf,
      regs_related krf rrf ->
      forall w z,
        Z.of_N (wordToN w) = z ->
        krf w =
        (if Z.eq_dec z 0 then word.of_Z 0
         else
           match map.get rrf z with
           | Some x => x
           | None => word.of_Z 0
           end).
  Proof.
    intros.
    destruct (Z.eq_dec _ _).
    - subst; rewrite Hkrf0; auto.
      rewrite <-N2Z.inj_0 in e.
      apply N2Z.inj in e.
      apply wordToN_inj; assumption.
    - subst; rewrite H; [reflexivity|].
      intro; subst; auto.
  Qed.

  Lemma regs_related_put krf rrf kv rv kk rk
        (Hrf: regs_related krf rrf)
        (Hk: Z.of_N (wordToN kk) = rk)
        (Hv: kv = rv):
    regs_related
      (fun w : Word.word rv32RfIdx => if weq w kk then kv else krf w)
      (map.put rrf rk rv).
  Proof.
    rewrite <-Hv.
    cbv [regs_related].
    intros i Hi.
    destruct (weq (sz:= rv32RfIdx) i kk).
    - subst; apply map.get_put_same.
    - rewrite map.get_put_diff.
      + apply Hrf; auto.
      + subst; intro.
        apply N2Z.inj, wordToN_inj in H; auto.
  Qed.

  (** * Inversion for decoding *)

  (* Ltac lets_in_hyp_to_eqs := *)
  (*   repeat lazymatch goal with *)
  (*          | |- (let x := ?a in ?b) = ?c -> ?Q => *)
  (*            change (let x := a in b = c -> Q); intro *)
  (*          | x := bitSlice _ 25 26 |- _ => *)
  (*           (* shamtHi is the only field which another field depends on *) *)
  (*            subst x *)
  (*          | x := ?t : ?T |- _ => *)
  (*            pose proof (eq_refl t : x = t); clearbody x *)
  (*          end. *)

  (* Ltac invert_decode_if_true G := *)
  (*   first [ apply Bool.andb_true_iff in G; *)
  (*           let G1 := fresh G in let G2 := fresh G in destruct G as [G1 G2]; *)
  (*           invert_decode_if_true G1; invert_decode_if_true G2 *)
  (*         | apply Z.eqb_eq in G *)
  (*         | idtac ]. *)

  (* (* TODO rather than stating this as a lemma, write a tactic which *)
  (*    infers & poses the conclusion *) *)
  (* Lemma invert_decode_Add: forall inst rd rs1 rs2: Z, *)
  (*     decode RV32IM inst = IInstruction (Decode.Add rd rs1 rs2) -> *)
  (*     bitSlice inst 0 7 = opcode_OP /\ *)
  (*     bitSlice inst 7 12 = rd /\ *)
  (*     bitSlice inst 12 15 = funct3_ADD /\ *)
  (*     bitSlice inst 15 20 = rs1 /\ *)
  (*     bitSlice inst 20 25 = rs2 /\ *)
  (*     bitSlice inst 25 32 = funct7_ADD. *)
  (* Proof. *)
  (*   intros *. *)
  (*   cbv beta delta [decode]. *)
  (*   lets_in_hyp_to_eqs. *)
  (*   subst *)
  (*     resultI *)
  (*     resultM *)
  (*     resultA *)
  (*     resultF *)
  (*     resultI64 *)
  (*     resultM64 *)
  (*     resultA64 *)
  (*     resultF64 *)
  (*     resultCSR. *)
  (*   repeat match type of H with *)
  (*   | context C [if ?a then ?b else ?c] => *)
  (*     ((let P := context C [ b ] in change P in H) || *)
  (*      (let P := context C [ c ] in change P in H)) *)
  (*   end. *)
  (*   subst results. *)
  (*   destruct (isValidI decodeI) eqn: VI; *)
  (*   destruct (isValidM decodeM) eqn: VM; *)
  (*   destruct (isValidCSR decodeCSR) eqn: VCSR. *)
  (*   all: try (clear; simpl; discriminate). *)
  (*   simpl. *)
  (*   intro E. *)
  (*   injection E. clear E. *)
  (*   subst decodeI. *)
  (*   intro E. *)
  (*   repeat match type of E with *)
  (*   | (if ?a then ?b else ?c) = ?d => destruct a; [discriminate E|] *)
  (*   end. *)
  (*   match type of E with *)
  (*   | (if ?a then ?b else ?c) = ?d => destruct a eqn: G; cycle 1 *)
  (*   end. *)
  (*   { (* more invalid cases *) *)
  (*     repeat match type of E with *)
  (*            | (if ?a then ?b else ?c) = ?d => destruct a; [discriminate E|] *)
  (*            end. *)
  (*     discriminate E. *)
  (*   } *)
  (*   (* the only valid case remains *) *)
  (*   subst rd0 rs4 rs0. *)
  (*   invert_decode_if_true G. *)
  (*   assert (bitSlice inst 0 7 = opcode_OP) as R1 by congruence; revert R1. *)
  (*   assert (bitSlice inst 12 15 = funct3_ADD) as R2 by congruence; revert R2. *)
  (*   assert (bitSlice inst 25 32 = funct7_ADD) as R3 by congruence; revert R3. *)
  (*   injection E. *)
  (*   clear. *)
  (*   (* if we automate this further, we might be able to infer the conclusion with a tactic *)
  (*      rather than having to state it manually *) *)
  (*   intros. auto. *)
  (* Qed. *)

  (* Lemma invert_decode_Lw: *)
  (*   forall inst (rd rs1: Register) (oimm12: Utility.Utility.MachineInt), *)
  (*     decode RV32IM inst = IInstruction (Decode.Lw rd rs1 oimm12) -> *)
  (*     bitSlice inst 0 7 = opcode_LOAD /\ *)
  (*     bitSlice inst 7 12 = rd /\ *)
  (*     bitSlice inst 12 15 = funct3_LW /\ *)
  (*     bitSlice inst 15 20 = rs1 /\ *)
  (*     bitSlice inst 20 32 = oimm12. *)
  (* Proof. *)
  (*   intros *. *)
  (*   cbv beta delta [decode]. *)
  (*   lets_in_hyp_to_eqs. *)
  (*   subst *)
  (*     resultI *)
  (*     resultM *)
  (*     resultA *)
  (*     resultF *)
  (*     resultI64 *)
  (*     resultM64 *)
  (*     resultA64 *)
  (*     resultF64 *)
  (*     resultCSR. *)
  (*   repeat match type of H with *)
  (*   | context C [if ?a then ?b else ?c] => *)
  (*     ((let P := context C [ b ] in change P in H) || *)
  (*      (let P := context C [ c ] in change P in H)) *)
  (*   end. *)
  (*   subst results. *)
  (*   destruct (isValidI decodeI) eqn: VI; *)
  (*   destruct (isValidM decodeM) eqn: VM; *)
  (*   destruct (isValidCSR decodeCSR) eqn: VCSR. *)
  (*   all: try (clear; simpl; discriminate). *)
  (*   simpl. *)
  (*   intro E. *)
  (*   injection E. clear E. *)
  (*   subst decodeI. *)
  (*   intro E. *)
  (*   repeat match type of E with *)
  (*   | (if ?a then ?b else ?c) = ?d => destruct a; [discriminate E|] *)
  (*   end. *)
  (*   match type of E with *)
  (*   | (if ?a then ?b else ?c) = ?d => destruct a eqn: G; cycle 1 *)
  (*   end. *)
  (*   { (* more invalid cases *) *)
  (*     repeat match type of E with *)
  (*            | (if ?a then ?b else ?c) = ?d => destruct a; [discriminate E|] *)
  (*            end. *)
  (*     discriminate E. *)
  (*   } *)
  (*   (* the only valid case remains *) *)
  (*   subst rd0 rs0 oimm0. *)
  (*   invert_decode_if_true G. *)
  (*   assert (bitSlice inst 0 7 = opcode_LOAD) as R1 by congruence; revert R1. *)
  (*   assert (bitSlice inst 12 15 = funct3_LW) as R2 by congruence; revert R2. *)
  (*   injection E. *)
  (*   clear. *)
  (*   (* if we automate this further, we might be able to infer the conclusion with a tactic *)
  (*      rather than having to state it manually *) *)
  (*   intros. *)
  (*   erewrite signExtend_nop in H. *)
  (*   - auto. *)
  (*   - case TODO_joonwon. *)
  (*   - case TODO_joonwon. *)
  (*   Unshelve. case TODO_joonwon. *)
  (* Qed. *)

  (* Lemma kami_getOpcode_ok: *)
  (*   forall kinst, *)
  (*     wordToNat *)
  (*       (evalExpr *)
  (*          (getOpcodeE (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) = *)
  (*     Z.to_nat (bitSlice (wordToZ kinst) 0 7). *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold getOpcodeE. *)
  (*   unfold evalExpr; fold evalExpr. *)
  (*   unfold evalUniBit. *)
  (*   rewrite kami_split_bitSlice_consistent_1 by blia. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma kami_getFunct7_ok: *)
  (*   forall kinst, *)
  (*     wordToNat *)
  (*       (evalExpr *)
  (*          (getFunct7E (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) = *)
  (*     Z.to_nat (bitSlice (wordToZ kinst) 25 32). *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold getFunct7E. *)
  (*   unfold evalExpr; fold evalExpr. *)
  (*   unfold evalUniBit. *)
  (*   rewrite kami_split_bitSlice_consistent_2. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma kami_getFunct3_ok: *)
  (*   forall kinst, *)
  (*     wordToNat *)
  (*       (evalExpr *)
  (*          (getFunct3E (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) = *)
  (*     Z.to_nat (bitSlice (wordToZ kinst) 12 15). *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold getFunct3E. *)
  (*   unfold evalExpr; fold evalExpr. *)
  (*   unfold evalUniBit. *)
  (*   rewrite kami_split_bitSlice_consistent_3. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma kami_getRdE_ok: *)
  (*   forall kinst, *)
  (*     wordToNat *)
  (*       (evalExpr (getRdE (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) = *)
  (*     Z.to_nat (bitSlice (wordToZ kinst) 7 12). *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold getRdE. *)
  (*   unfold evalExpr; fold evalExpr. *)
  (*   unfold evalUniBit. *)
  (*   rewrite kami_split_bitSlice_consistent_3. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma kami_rv32GetDst_ok: *)
  (*   forall kinst, *)
  (*     bitSlice (wordToZ kinst) 0 7 = opcode_OP -> *)
  (*     wordToNat (evalExpr (rv32GetDst type kinst)) = *)
  (*     Z.to_nat (bitSlice (wordToZ kinst) 7 12). *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold rv32GetDst. *)
  (*   unfold evalExpr; fold evalExpr. *)
  (*   destruct (isEq _ _) as [Heq|Hne]. *)
  (*   - exfalso. *)
  (*     pose proof (kami_getOpcode_ok kinst). *)
  (*     rewrite Heq, H in H0; discriminate. *)
  (*   - rewrite kami_getRdE_ok; reflexivity. *)
  (* Qed. *)

  (* Lemma kami_rv32GetSrc1_ok: *)
  (*   forall kinst, *)
  (*     wordToNat (evalExpr (rv32GetSrc1 type kinst)) = *)
  (*     Z.to_nat (bitSlice (wordToZ kinst) 15 20). *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold rv32GetSrc1, getRs1E. *)
  (*   unfold evalExpr; fold evalExpr. *)
  (*   unfold evalUniBit. *)
  (*   rewrite kami_split_bitSlice_consistent_3. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma kami_rv32GetSrc2_ok: *)
  (*   forall kinst, *)
  (*     wordToNat (evalExpr (rv32GetSrc2 type kinst)) = *)
  (*     Z.to_nat (bitSlice (wordToZ kinst) 20 25). *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold rv32GetSrc2, getRs2E. *)
  (*   unfold evalExpr; fold evalExpr. *)
  (*   unfold evalUniBit. *)
  (*   rewrite kami_split_bitSlice_consistent_3. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma kami_rv32GetLdSrc_ok: *)
  (*   forall kinst, *)
  (*     wordToNat (evalExpr (rv32GetLdSrc type kinst)) = *)
  (*     Z.to_nat (bitSlice (wordToZ kinst) 15 20). *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold rv32GetLdSrc, getRs1E. *)
  (*   unfold evalExpr; fold evalExpr. *)
  (*   unfold evalUniBit. *)
  (*   rewrite kami_split_bitSlice_consistent_3. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* (** TODO @joonwonc: ditto [invert_decode_Add]; better to have a tactic. *) *)
  (* Lemma kami_rv32DoExec_Add_ok: *)
  (*   forall v1 v2 pc kinst, *)
  (*     wordToNat *)
  (*       (evalExpr *)
  (*          (getOpcodeE (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) = *)
  (*     Z.to_nat opcode_OP -> *)
  (*     wordToNat *)
  (*       (evalExpr (getFunct7E (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) = *)
  (*     Z.to_nat funct7_ADD -> *)
  (*     wordToNat *)
  (*       (evalExpr (getFunct3E (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) = *)
  (*     Z.to_nat funct3_ADD -> *)
  (*     evalExpr (rv32DoExec (Z.to_nat instrMemSizeLg) type v1 v2 pc kinst) = *)
  (*     v1 ^+ v2. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold rv32DoExec. *)
  (*   unfold evalExpr; fold evalExpr. *)
  (*   do 5 (destruct (isEq _ _); [rewrite e in H; discriminate|clear n]). *)
  (*   do 3 (destruct (isEq _ _); [|exfalso; elim n; apply wordToNat_inj; assumption]). *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma kami_rv32NextPc_op_ok: *)
  (*   forall rf pc kinst, *)
  (*     wordToNat *)
  (*       (evalExpr *)
  (*          (getOpcodeE (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) = *)
  (*     Z.to_nat opcode_OP -> *)
  (*     evalExpr (rv32NextPc (Z.to_nat instrMemSizeLg) type rf pc kinst) = *)
  (*     pc ^+ $4. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold rv32NextPc. *)
  (*   unfold evalExpr; fold evalExpr. *)
  (*   do 3 (destruct (isEq _ _); [rewrite e in H; discriminate|clear n]). *)
  (*   unfold evalBinBit. *)
  (*   unfold evalConstT. *)
  (*   f_equal. *)
  (*   case TODO_joonwon. *)
  (* Qed. *)

  (* Lemma kami_rv32NextPc_load_ok: *)
  (*   forall rf pc kinst, *)
  (*     wordToZ *)
  (*       (evalExpr *)
  (*          (getOpcodeE (Var type (SyntaxKind (Data rv32InstBytes)) kinst))) = *)
  (*     opcode_LOAD -> *)
  (*     evalExpr (rv32NextPc (Z.to_nat instrMemSizeLg) type rf pc kinst) = *)
  (*     pc ^+ $4. *)
  (* Proof. *)
  (*   case TODO_joonwon. *)
  (* Qed. *)

End DecExecOk.
