Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import riscv.Decode.
Require Import riscv.Encode.
Require Import coqutil.Word.LittleEndian.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Utility.
Require Import riscv.Primitives.
Require Import riscv.RiscvMachine.
Require Import riscv.Program.
Require riscv.Memory.
Require Import riscv.PseudoInstructions.
Require Import riscv.proofs.EncodeBound.
Require Import riscv.proofs.DecodeEncode.
Require Import riscv.Run.
Require Import riscv.util.BitWidths.
Require Import riscv.MkMachineWidth.
Require Import riscv.util.Monads.


Local Open Scope Z_scope.

Section Equiv.

  (* TODO not sure if we want to use ` or rather a parameter record *)
  Context `{Pr: Primitives}.
  Context {RVS: RiscvState M word}.

  Definition NOP: w32 := LittleEndian.split 4 (encode (IInstruction Nop)).

  Record FakeProcessor := {
    counter: word;
  }.

  Definition fakeStep: FakeProcessor -> FakeProcessor :=
    fun '(Build_FakeProcessor c) => Build_FakeProcessor (word.add c (word.of_Z 4)).

  Definition from_Fake(f: FakeProcessor): RiscvMachine Register Action := {|
    getRegs := initialRegs;
    getPc := f.(counter);
    getNextPc := word.add f.(counter) (word.of_Z 4);
    getMem := Memory.store_bytes 4 map.empty f.(counter) NOP;
    getLog := nil;
  |}.

  Definition to_Fake(m: RiscvMachine Register Action): FakeProcessor := {|
    counter := m.(getPc);
  |}.

  Definition BW: BitWidths := if width =? 32 then BW32 else BW64.

  Arguments Memory.store_bytes: simpl never.

  Lemma combine_split: forall (n: nat) (z: Z),
      0 <= z < 2 ^ (Z.of_nat n * 8) ->
      combine n (split n z) = z.
  Proof.
    induction n; intros.
    - simpl in *. lia.
    - unfold combine. (* TODO *)
  Admitted.

  Hypothesis assume_no_MMIO: forall mach addr post, ~ nonmem_loadWord_sat mach addr post.

  Lemma simulate_step_fw: forall (initial: RiscvMachine Register Action)
                                 (post: RiscvMachine Register Action -> Prop),
      (* begin additional hypotheses which should be deleted in a real proof *)
      Memory.loadWord initial.(getMem) initial.(getPc) = Some NOP ->
      (forall machine1 machine2,
          post machine1 ->
          machine1.(getPc) = machine2.(getPc) ->
          machine1.(getNextPc) = machine2.(getNextPc) ->
          post machine2) ->
      (* end hypotheses to be deleted *)
      initial.(getNextPc) = word.add initial.(getPc) (word.of_Z 4) ->
      mcomp_sat (run1 (B := BW)) initial (fun _ => post) ->
      post (from_Fake (fakeStep (to_Fake initial))).
  Proof.
    intros *. intros AllNOPs postOnlyLooksAtPc EqPC H.
    destruct initial as [r pc npc m l].
    unfold to_Fake, fakeStep, from_Fake.
    simpl.
    unfold run1 in H.
    apply spec_Bind in H. destruct_products.
    apply spec_getPC in Hl. simpl in Hl.
    specialize Hr with (1 := Hl). clear Hl.
    apply spec_Bind in Hr. destruct_products.
    apply spec_loadWord in Hrl.
    destruct Hrl as [A | [_ A]]; [|exfalso; eapply assume_no_MMIO; exact A].
    destruct_products.
    simpl in Al, AllNOPs. rewrite AllNOPs in Al. inversion Al. subst v. clear Al.
    specialize Hrr with (1 := Ar). clear Ar.
    apply spec_Bind in Hrr. destruct_products.
    unfold NOP in Hrrl.
    rewrite combine_split in Hrrl by apply (encode_range (IInstruction Nop)).
    rewrite decode_encode in Hrrl by (cbv; clear; intuition congruence).
    simpl in Hrrl.
    apply spec_Bind in Hrrl. destruct_products.
    apply spec_getRegister in Hrrll.
    destruct Hrrll as [[[A _] _] | [_ A]]; [ cbv in A; discriminate A | ].
    specialize Hrrlr with (1 := A). clear A.
    apply spec_setRegister in Hrrlr.
    destruct Hrrlr as [[[A _] _] | [_ A]]; [ cbv in A; discriminate A | ].
    specialize Hrrr with (1 := A). clear A.
    apply spec_step in Hrrr. unfold withPc, withNextPc in Hrrr. simpl in Hrrr.
    simpl in EqPC. subst npc.
    eapply postOnlyLooksAtPc; [eassumption|reflexivity..].
  Qed.

  Ltac det_step :=
    match goal with
    | |- exists (_: ?A -> ?Mach -> Prop), _ =>
      let a := fresh "a" in evar (a: A);
      let m := fresh "m" in evar (m: Mach);
      exists (fun a0 m0 => a0 = a /\ m0 = m);
      subst a m
    end.

  Lemma loadWord_store_bytes_same: forall m w addr,
      Memory.loadWord (Memory.store_bytes 4 m addr w) addr = Some w.
  Admitted. (* TODO once we have a good map solver and word solver, this should be easy *)

  Lemma simulate_step_bw: forall (m m': FakeProcessor),
      fakeStep m = m' ->
      mcomp_sat (run1 (B := BW)) (from_Fake m) (fun _ final => to_Fake final = m').
  Proof.
    intros. subst m'. destruct m as [c]. unfold from_Fake, to_Fake, fakeStep, run1.
    apply spec_Bind.
    det_step. split.
    { simpl. apply spec_getPC. simpl. split; reflexivity. }
    intros. destruct_products. subst.
    apply spec_Bind.
    det_step. split.
    { apply spec_loadWord.
      left.
      exists NOP.
      repeat split. (* also invokes reflexivity *)
      simpl.
      apply loadWord_store_bytes_same. }
    intros. destruct_products. subst.
    apply spec_Bind.
    det_step. split.
    { unfold NOP at 1.
      rewrite combine_split by apply (encode_range (IInstruction Nop)).
      rewrite decode_encode by (cbv; clear; intuition congruence).
      simpl.
      apply spec_Bind.
      det_step. split.
      { apply spec_getRegister.
        simpl.
        right.
        repeat split. }
      intros. destruct_products. subst.
      apply spec_setRegister.
      right.
      repeat split. }
    intros. destruct_products. subst.
    apply spec_step. simpl. reflexivity.
  Qed.

  Lemma to_Fake_from_Fake: forall (m: FakeProcessor),
      to_Fake (from_Fake m) = m.
  Proof.
    intros. destruct m as [c]. reflexivity.
  Qed.

  Lemma step_equiv: forall (m m': FakeProcessor),
      fakeStep m = m' <->
      mcomp_sat (run1 (B := BW)) (from_Fake m) (fun _ final => to_Fake final = m').
  Proof.
    intros. split.
    - apply simulate_step_bw.
    - intros.
      pose proof (simulate_step_fw (from_Fake m) (fun final => to_Fake final = m')) as P.
      simpl in P.
      do 2 rewrite to_Fake_from_Fake in P.
      apply P; clear P.
      + intros. apply loadWord_store_bytes_same.
      + intros. destruct machine1, machine2. unfold to_Fake in *; simpl in *. congruence.
      + reflexivity.
      + assumption.
  Qed.

End Equiv.
