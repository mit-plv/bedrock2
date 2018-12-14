Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import bbv.ZLib.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import riscv.Decode.
Require Import riscv.Run.
Require Import riscv.Memory.
Require Import coqutil.Decidable.
Require compiler.Memory.
Require Import Coq.Program.Tactics.
Require Import riscv.InstructionCoercions.
Require Import riscv.AxiomaticRiscv.
Require Import Coq.micromega.Lia.
Require Import riscv.Utility.
Require Import compiler.FlatToRiscvBitWidthSpecifics.

Local Open Scope ilist_scope.
Local Open Scope Z_scope.

Set Implicit Arguments.

Local Unset Universe Polymorphism. (* for Add Ring *)

Section ContainsProgram.

  Context {byte: word 8} {width: Z} {mword: word width} {bound: 0 <= width} {ok: word.ok mword}.
  Context {Mem: map.map mword byte}.
  Context {BWS: FlatToRiscvBitWidthSpecifics mword}.

  Ltac mword_cst w :=
    match w with
    | ZToReg ?x => let b := isZcst x in
                  match b with
                  | true => x
                  | _ => constr:(NotConstant)
                  end
    | _ => constr:(NotConstant)
  end.

  (*
  Hint Rewrite
    ZToReg_morphism.(morph_add)
    ZToReg_morphism.(morph_sub)
    ZToReg_morphism.(morph_mul)
    ZToReg_morphism.(morph_opp)
  : rew_ZToReg_morphism.

  Add Ring mword_ring : (@regRing mword MW)
      (preprocess [autorewrite with rew_ZToReg_morphism],
       morphism (@ZToReg_morphism mword MW),
       constants [mword_cst]).
   *)
  Add Ring mword_ring: (@word.ring_theory _ _ _ bound).

  (* load and decode Inst *)
  Definition ldInst(m: Mem)(a: mword): option Instruction :=
    match Memory.loadWord m a with
    | Some w => Some (decode (@RV_wXLEN_IM BitWidth) (LittleEndian.combine 4 w))
    | None => None
    end.

  (*
  Definition decode_prog(prog: list (word 32)): list Instruction :=
    List.map (fun w => decode (@RV_wXLEN_IM BitWidth) (uwordToZ w)) prog.
   *)

  Definition containsProgram(m: Mem)(program: list Instruction)(offset: mword) :=
(*    regToZ_unsigned offset + 4 * Zlength program <= Memory.memSize m /\*)
    forall i inst, Znth_error program i = Some inst ->
      ldInst m (add offset (ZToReg (4 * i))) = Some inst.

  (*
  Definition containsProgram'(m: Mem mword)(program: list Instruction)(offset: mword) :=
    regToZ_unsigned offset + 4 * Zlength program <= Memory.memSize m /\
    decode_prog (Memory.load_word_list m offset (Zlength program)) = program.

  Lemma containsProgram_alt: forall m program offset,
      containsProgram m program offset <-> containsProgram' m program offset.
  Proof.
    intros. unfold containsProgram, containsProgram', decode_prog.
    intuition idtac.
    - apply list_elementwise_same_Z. intros i B. specialize (H1 i).
      assert (0 <= i < Zlength program \/ Zlength program <= i) as C by omega.
      destruct C as [C | C].
      + destruct (Znth_error_Some _ program i) as [_ P].
        specialize (P C).
        destruct (Znth_error program i) as [inst|] eqn: E; try contradiction.
        specialize (H1 _ eq_refl). unfold ldInst in H1.
        erewrite map_Znth_error.
        * f_equal. eassumption.
        * apply Znth_error_load_word_list; try assumption.
      + pose proof (Znth_error_ge_None _ _ C) as P.
        rewrite P.
        apply Znth_error_ge_None.
        rewrite map_Zlength.
        rewrite Zlength_load_word_list by (apply Zlength_nonneg).
        assumption.
    - unfold ldInst. rewrite <- H1 in H.
      pose proof (map_Znth_error') as P.
      specialize P with (1 := H).
      destruct P as [inst' [P Q] ].
      subst inst.
      do 2 f_equal.
      rewrite Znth_error_load_word_list in P.
      + congruence.
      + edestruct (Znth_error_Some _ (Memory.load_word_list m offset (Zlength program)))
          as [Q _].
        rewrite Zlength_load_word_list in Q by (apply Zlength_nonneg).
        apply Q. congruence.
  Qed.
  *)

  (* Note: containsProgram for one single [[inst]] could be simplified, but for automation,
     it's better not to simplify.
  Lemma containsProgram_cons_inv_old: forall m inst insts offset,
    containsProgram m (inst :: insts) offset ->
    containsProgram m [[inst]] offset /\
    containsProgram m insts (add offset ZToReg 4).
  Proof.
    intros *. intro Cp. unfold containsProgram in *. cbn [length] in *.
    intuition (try omega).
    + specialize (H0 0). specialize H0 with (1 := eq_refl).
      intros. destruct i; inverts H1.
      - assumption.
      - exfalso. eauto using nth_error_nil_Some.
    + nat_rel_with_words.
    + rename H0 into Cp. specialize (Cp (S i)). simpl in Cp.
      specialize (Cp _ H1).
      rewrite <- Cp. f_equal.
      solve_word_eq.
  Qed.
  *)

  Definition containsProgram_app_will_work(insts1 insts2: list Instruction)(offset: mword) :=
    (regToZ_unsigned (mul (add offset (ZToReg 4)) (ZToReg (Zlength insts1))) = 0 ->
     insts1 = nil \/ insts2 = nil).

  Lemma containsProgram_app_inv0: forall s insts1 insts2 offset,
    containsProgram s (insts1 ++ insts2) offset ->
    containsProgram s insts1 offset /\
    containsProgram s insts2 (add offset (ZToReg (4 * Zlength insts1))) /\
    containsProgram_app_will_work insts1 insts2 offset.
  Proof.
  (*
    intros *. intro Cp. unfold containsProgram, containsProgram_app_will_work in *.
    rewrite app_length in Cp.
    intuition (try nat_rel_with_words).
    + apply H0. rewrite nth_error_app1; [assumption|].
      apply nth_error_Some. intro E. rewrite E in H1. discriminate.
    + rewrite <- (H0 (length insts1 + i)).
      - f_equal. solve_word_eq.
      - rewrite nth_error_app2 by omega.
        replace (length insts1 + i - length insts1) with i by omega.
        assumption.
    + destruct insts2; [solve [auto]|].
      destruct insts1; [solve [auto]|].
      exfalso.
      simpl (length _) in *.
      rewrite Nat.mul_add_distr_l in H.
      rewrite Nat.add_assoc in H.
      rewrite wordToNat_wplus in H1.
      rewrite? wordToNat_wmult in *.
      rewrite? wordToNat_natToWord_eqn in *.
      pose proof pow2_wXLEN_4.
      rewrite Nat.add_mod in H1 by omega.
      rewrite <- Nat.mul_mod in * by omega.
      rewrite Nat.add_mod_idemp_r in H1 by omega.
      rewrite <- Nat.add_mod in H1 by omega.
      pose proof (Memory.memSize_bound s).
      rewrite Nat.mod_small in H1 by omega.
      clear -H1. omega.
  Qed.
   *)
  Admitted.

  Lemma containsProgram_app_inv: forall s insts1 insts2 offset,
    containsProgram s (insts1 ++ insts2) offset ->
    containsProgram s insts1 offset /\
    containsProgram s insts2 (add offset (mul (ZToReg 4) (ZToReg (Zlength insts1)))) /\
    containsProgram_app_will_work insts1 insts2 offset.
  Proof.
    intros.
    destruct (containsProgram_app_inv0 _ _ H) as [H1 H2].
    unfold add, ZToReg, MkMachineWidth.MachineWidth_XLEN in *.
    rewrite (@word.ring_morph width mword ok bound).(morph_mul) in H2.
    auto.
  Qed.

  Lemma containsProgram_cons_inv: forall m inst insts offset,
    containsProgram m (inst :: insts) offset ->
    containsProgram m [[inst]] offset /\
    containsProgram m insts (add offset (ZToReg 4)) /\
    containsProgram_app_will_work [[inst]] insts offset.
  Proof.
    intros.
    pose proof containsProgram_app_inv as P.
    specialize P with (insts1 := [[inst]]) (insts2 := insts).
    (* TODO how to automate this nicely? "match" and equate? *)
    replace (add offset (ZToReg 4)) with (add offset (mul (ZToReg 4) (ZToReg (Zlength [[inst]])))); auto.
    rewrite Zlength_cons. rewrite Zlength_nil.
    change (0 + 1) with 1.
    unfold add, mul, ZToReg, MkMachineWidth.MachineWidth_XLEN in *.
    ring.
  Qed.

  Lemma containsProgram_app: forall m insts1 insts2 offset,
      containsProgram_app_will_work insts1 insts2 offset ->
      containsProgram m insts1 offset ->
      containsProgram m insts2 (add offset (mul (ZToReg 4) (ZToReg (Zlength insts1)))) ->
      containsProgram m (insts1 ++ insts2) offset.
  Proof.
    (*
    unfold containsProgram, containsProgram_app_will_work.
    intros *. intro A. intros. rewrite app_length.
    intuition idtac.
    - clear H2 H3.
      repeat match goal with
             | IsMem: Memory.Memory ?M _, m: ?M |- _ =>
               unique pose proof (@Memory.memSize_bound M _ IsMem m)
             end.
      pose proof pow2_wXLEN_4.
      assert (let x := regToZ_unsigned  (offset ^+ $ (4) ^* $ (length insts1)) in x = 0 \/ x > 0) as C
        by (cbv zeta; omega).
      destruct C as [C | C].
      + specialize (A C). destruct A as [A | A].
        * subst insts1.
          change (length [[]]) with 0 in *.
          rewrite Nat.add_0_l.
          replace (offset ^+ $ (4) ^* $ (0)) with offset in C by solve_word_eq.
          apply wordToNat_zero in C. subst offset.
          rewrite roundTrip_0 in *.
          match goal with
          | H: regToZ_unsigned ?b + 4 * length insts2 <= _ |- _ =>
            replace 0 with (regToZ_unsigned b) at 1; [assumption|]
          end.
          rewrite <- roundTrip_0 at 4.
          f_equal.
          solve_word_eq.
        * subst insts2.
          change (length [[]]) with 0.
          rewrite Nat.add_0_r.
          assumption.
      + repeat match goal with
             | IsMem: Memory.Memory ?M _, m: ?M |- _ =>
               unique pose proof (@Memory.memSize_bound M _ IsMem m)
             end.
        pose proof pow2_wXLEN_4.
        rewrite? wordToNat_wplus in *.
        rewrite? wordToNat_natToWord_eqn in *.
        rewrite? wordToNat_wmult in *.
        rewrite? wordToNat_natToWord_eqn in *.
        rewrite <- Nat.mul_mod in * by omega.
        rewrite Nat.add_mod_idemp_r in * by omega.
        nat_div_mod_to_quot_rem.
        assert (q = 0 \/ q > 0) as D by omega.
        destruct D as [D | D]; nia.
    - assert (i < length insts1 \/ length insts1 <= i) as E by omega.
      destruct E as [E | E].
      + rewrite nth_error_app1 in H0 by assumption. eauto.
      + rewrite nth_error_app2 in H0 by assumption.
        erewrite <- H3; [|exact H0].
        f_equal.
        replace i with (i - length insts1 + length insts1) at 1 by omega.
        forget (i - length insts1) as i'.
        solve_word_eq.
  Qed.*)
  Admitted.

  Lemma containsProgram_cons: forall m inst insts offset,
    containsProgram_app_will_work [[inst]] insts offset ->
    containsProgram m [[inst]] offset ->
    containsProgram m insts (add offset (ZToReg 4)) ->
    containsProgram m (inst :: insts) offset.
  Proof.
    intros. change (inst :: insts) with ([[inst]] ++ insts).
    apply containsProgram_app; [assumption..|].
    rewrite Zlength_cons, Zlength_nil.
    unfold add, mul, ZToReg, MkMachineWidth.MachineWidth_XLEN in *.
    change (0 + 1) with 1.
    repeat match goal with
           | H: containsProgram _ _ ?x |- _ => progress (ring_simplify x in H)
           | |-  containsProgram _ _ ?x     => progress (ring_simplify x)
           end.
    assumption.
  Qed.

End ContainsProgram.
