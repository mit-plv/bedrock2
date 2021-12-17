From Coq Require Import ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Z.Lia.
Require Import coqutil.Z.div_mod_to_equations.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.Memory.
Require Import riscv.Spec.Machine.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.MetricPrimitives.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Platform.Run.
Require Import riscv.Spec.Execute.
Require Import coqutil.Tactics.Tactics.
Require Import compiler.SeparationLogic.
Require Export coqutil.Word.SimplWordExpr.
Require Import compiler.DivisibleBy4.
Require Import bedrock2.ptsto_bytes.
Require Import bedrock2.Scalars.
Require Import riscv.Utility.Encode.
Require Import riscv.Proofs.EncodeBound.
Require Import riscv.Proofs.DecodeEncode.
Require Import riscv.Platform.MetricSane.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.Simp.
Require Import riscv.Utility.runsToNonDet.
Require Import coqutil.Datatypes.ListSet.
Import Utility.

Section Go.
  Context {width} {BW: Bitwidth width} {word: word.word width} {word_ok: word.ok word}.
  Context {Registers: map.map Z word}.
  Context {mem: map.map word byte}.
  Context {mem_ok: map.ok mem}.

  Local Notation RiscvMachineL := MetricRiscvMachine.

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {PR: MetricPrimitives PRParams}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Lemma spec_Bind_det{A B: Type}: forall (initialL: RiscvMachineL)
       (post: B -> RiscvMachineL -> Prop) (m: M A) (f : A -> M B) (a: A) (mid: RiscvMachineL),
      mcomp_sat m initialL (fun a' mid' => a' = a /\ mid' = mid) ->
      mcomp_sat (f a) mid post ->
      mcomp_sat (Bind m f) initialL post.
  Proof.
    intros. eapply spec_Bind. eexists. split; [exact H|]. intros. simpl in *.
    destruct H1. subst. assumption.
  Qed.

  (* redefine mcomp_sat to simplify for the case where no answer is returned *)
  Definition mcomp_sat(m: M unit)(initialL: RiscvMachineL)(post: RiscvMachineL -> Prop): Prop :=
    mcomp_sat m initialL (fun (_: unit) => post).

  Lemma mcomp_sat_weaken: forall initialL m (post1 post2: RiscvMachineL -> Prop),
      (forall mach, post1 mach -> post2 mach) ->
      mcomp_sat m initialL post1 ->
      mcomp_sat m initialL post2.
  Proof.
    intros. eapply mcomp_sat_weaken; [|eassumption].
    simpl. intros _. assumption.
  Qed.

  (* nicer version of mcomp_sat_weaken which gives you two more hypotheses while proving P -> Q *)
  Lemma run1_get_sane: forall iset (P Q: RiscvMachineL -> Prop) mach,
      valid_machine mach ->
      mcomp_sat (run1 iset) mach P ->
      (forall mach': RiscvMachineL,
          (exists diff, mach'.(getLog) = diff ++ mach.(getLog)) ->
          valid_machine mach' ->
          P mach' ->
          Q mach') ->
      mcomp_sat (run1 iset) mach Q.
  Proof.
    intros.
    pose proof run1_sane as A.
    unfold mcomp_sane in A.
    specialize A with (1 := H) (2 := H0).
    apply proj2 in A.
    eapply mcomp_sat_weaken. 2: exact A. cbv beta.
    intros. destruct H2 as ((? & (diff & ?)) & ?).
    eapply H1; eauto.
  Qed.

  Lemma runsTo_sane: forall iset (P: RiscvMachineL -> Prop) mach,
      runsTo (mcomp_sat (run1 iset)) mach P ->
      valid_machine mach ->
      runsTo (mcomp_sat (run1 iset)) mach (fun mach' =>
        (P mach' /\ exists diff, mach'.(getLog) = diff ++ mach.(getLog)) /\ valid_machine mach').
  Proof.
    induction 1; intros.
    - eapply runsToDone. ssplit; try assumption. exists nil. reflexivity.
    - pose proof run1_sane as A.
      unfold mcomp_sane in A.
      specialize A with (1 := H2) (2 := H).
      apply proj2 in A.
      eapply runsToStep. 1: exact A.
      cbv beta.
      intros. destruct H3 as ((? & (diff & ?)) & ?). eapply runsTo_weaken.
      + eapply H1; eassumption.
      + cbv beta. intros. destruct H6 as ((? & (diff' & ?)) & ?).
        ssplit; try eassumption.
        rewrite H7. rewrite H4. rewrite app_assoc. eexists. reflexivity.
  Qed.

  (* a nicer version of runsTo_weaken which gives you two more hypotheses while proving P -> Q *)
  Lemma runsTo_get_sane: forall iset (P Q: RiscvMachineL -> Prop) mach,
      valid_machine mach ->
      runsTo (mcomp_sat (run1 iset)) mach P ->
      (forall mach': RiscvMachineL,
          (exists diff, mach'.(getLog) = diff ++ mach.(getLog)) ->
          valid_machine mach' ->
          P mach' ->
          Q mach') ->
      runsTo (mcomp_sat (run1 iset)) mach Q.
  Proof.
    intros.
    eapply runsTo_weaken.
    - eapply runsTo_sane; eassumption.
    - cbv beta. intros. destruct H2 as ((? & ?) & ?).
      eapply H1; assumption.
  Qed.

  Lemma spec_Bind_unit: forall (initialL: RiscvMachineL)
       (mid post: RiscvMachineL -> Prop) (m1: M unit) (m2 : M unit),
      mcomp_sat m1 initialL mid ->
      (forall middle, mid middle -> mcomp_sat m2 middle post) ->
      mcomp_sat (Bind m1 (fun _ => m2)) initialL post.
  Proof.
    intros. eapply spec_Bind. eexists. split; [exact H|]. intros. simpl in *.
    apply H0. assumption.
  Qed.

  Lemma ExecuteFetchP: forall (addr: word) xAddrs, Execute = Fetch -> isXAddr4 addr xAddrs.
  Proof. intros. discriminate. Qed.

  Ltac t lem :=
    intros;
    try (eapply spec_Bind_det; [|eassumption]); (* try because go_step doesn't need Bind *)
    apply lem;
    rewrite_match;
    eauto 10 using ExecuteFetchP.

  Lemma go_getRegister: forall (initialL: RiscvMachineL) (x: Z) v post (f: word -> M unit),
      valid_register x ->
      map.get initialL.(getRegs) x = Some v ->
      mcomp_sat (f v) initialL post ->
      mcomp_sat (Bind (getRegister x) f) initialL post.
  Proof. t spec_getRegister. Qed.

  Lemma go_getRegister0: forall (initialL: RiscvMachineL) post (f: word -> M unit),
      mcomp_sat (f (ZToReg 0)) initialL post ->
      mcomp_sat (Bind (getRegister Register0) f) initialL post.
  Proof. t spec_getRegister. Qed.

  Lemma go_setRegister: forall (initialL: RiscvMachineL) x v post (f: unit -> M unit),
      valid_register x ->
      mcomp_sat (f tt) (withRegs (map.put initialL.(getRegs) x v) initialL) post ->
      mcomp_sat (Bind (setRegister x v) f) initialL post.
  Proof. t spec_setRegister. Qed.

  Lemma go_setRegister0: forall (initialL: RiscvMachineL) v post (f: unit -> M unit),
      mcomp_sat (f tt) initialL post ->
      mcomp_sat (Bind (setRegister Register0 v) f) initialL post.
  Proof. t spec_setRegister. Qed.

  Lemma go_loadByte: forall (initialL: RiscvMachineL) addr (v: w8) (f: w8 -> M unit) post,
      Memory.loadByte initialL.(getMem) addr = Some v ->
      mcomp_sat (f v) (updateMetrics (addMetricLoads 1) initialL) post ->
      mcomp_sat (Bind (Machine.loadByte Execute addr) f) initialL post.
  Proof. t spec_loadByte. Qed.

  Lemma go_loadHalf: forall (initialL: RiscvMachineL) addr (v: w16) (f: w16 -> M unit) post,
      Memory.loadHalf initialL.(getMem) addr = Some v ->
      mcomp_sat (f v) (updateMetrics (addMetricLoads 1) initialL) post ->
      mcomp_sat (Bind (Machine.loadHalf Execute addr) f) initialL post.
  Proof. t spec_loadHalf. Qed.

  Lemma go_loadWord: forall (initialL: RiscvMachineL) addr (v: w32) (f: w32 -> M unit) post,
      Memory.loadWord initialL.(getMem) addr = Some v ->
      mcomp_sat (f v) (updateMetrics (addMetricLoads 1) initialL) post ->
      mcomp_sat (Bind (Machine.loadWord Execute addr) f) initialL post.
  Proof. t spec_loadWord. Qed.

  Lemma go_loadWord_Fetch: forall (initialL: RiscvMachineL) addr (v: w32) (f: w32 -> M unit) post,
      isXAddr4 addr initialL.(getXAddrs) ->
      Memory.loadWord initialL.(getMem) addr = Some v ->
      mcomp_sat (f v) (updateMetrics (addMetricLoads 1) initialL) post ->
      mcomp_sat (Bind (Machine.loadWord Fetch addr) f) initialL post.
  Proof. t spec_loadWord. Qed.

  Lemma go_loadDouble: forall (initialL: RiscvMachineL) addr (v: w64) (f: w64 -> M unit) post,
      Memory.loadDouble initialL.(getMem) addr = Some v ->
      mcomp_sat (f v) (updateMetrics (addMetricLoads 1) initialL) post ->
      mcomp_sat (Bind (Machine.loadDouble Execute addr) f) initialL post.
  Proof. t spec_loadDouble. Qed.

  Lemma go_storeByte: forall (initialL: RiscvMachineL) kind addr v m' post (f: unit -> M unit),
        Memory.storeByte initialL.(getMem) addr v = Some m' ->
        mcomp_sat (f tt) (withXAddrs (invalidateWrittenXAddrs 1 addr initialL.(getXAddrs))
                         (withMem m' (updateMetrics (addMetricStores 1) initialL))) post ->
        mcomp_sat (Bind (Machine.storeByte kind addr v) f) initialL post.
  Proof. t spec_storeByte. Qed.

  Lemma go_storeHalf: forall (initialL: RiscvMachineL) kind addr v m' post (f: unit -> M unit),
        Memory.storeHalf initialL.(getMem) addr v = Some m' ->
        mcomp_sat (f tt) (withXAddrs (invalidateWrittenXAddrs 2 addr initialL.(getXAddrs))
                         (withMem m' (updateMetrics (addMetricStores 1) initialL))) post ->
        mcomp_sat (Bind (Machine.storeHalf kind addr v) f) initialL post.
  Proof. t spec_storeHalf. Qed.

  Lemma go_storeWord: forall (initialL: RiscvMachineL) kind addr v m' post (f: unit -> M unit),
        Memory.storeWord initialL.(getMem) addr v = Some m' ->
        mcomp_sat (f tt) (withXAddrs (invalidateWrittenXAddrs 4 addr initialL.(getXAddrs))
                         (withMem m' (updateMetrics (addMetricStores 1) initialL))) post ->
        mcomp_sat (Bind (Machine.storeWord kind addr v) f) initialL post.
  Proof. t spec_storeWord. Qed.

  Lemma go_storeDouble: forall (initialL: RiscvMachineL) kind addr v m' post (f: unit -> M unit),
        Memory.storeDouble initialL.(getMem) addr v = Some m' ->
        mcomp_sat (f tt) (withXAddrs (invalidateWrittenXAddrs 8 addr initialL.(getXAddrs))
                         (withMem m' (updateMetrics (addMetricStores 1) initialL))) post ->
        mcomp_sat (Bind (Machine.storeDouble kind addr v) f) initialL post.
  Proof. t spec_storeDouble. Qed.

  Lemma go_getPC: forall (initialL: RiscvMachineL) (f: word -> M unit) post,
        mcomp_sat (f initialL.(getPc)) initialL post ->
        mcomp_sat (Bind getPC f) initialL post.
  Proof. t spec_getPC. Qed.

  Lemma go_setPC: forall (initialL: RiscvMachineL) v post (f: unit -> M unit),
        mcomp_sat (f tt) (withNextPc v (updateMetrics (addMetricJumps 1) initialL)) post ->
        mcomp_sat (Bind (setPC v) f) initialL post.
  Proof.
    intros.
    t (spec_setPC initialL v (fun a' mid' => a' = tt /\
      mid' = withNextPc v (updateMetrics (addMetricJumps 1) initialL))).
  Qed.

  Lemma go_endCycleNormal: forall (initialL: RiscvMachineL) (post: RiscvMachineL -> Prop),
      post (withPc initialL.(getNextPc)
           (withNextPc (word.add initialL.(getNextPc) (word.of_Z 4))
           (updateMetrics (addMetricInstructions 1) initialL))) ->
      mcomp_sat endCycleNormal initialL post.
  Proof. t spec_endCycleNormal. Qed.

  Lemma go_done: forall (initialL: RiscvMachineL) (post: RiscvMachineL -> Prop),
      post initialL ->
      mcomp_sat (Return tt) initialL post.
  Proof. intros. apply spec_Return. exact H. Qed.

  Lemma go_left_identity{A: Type}: forall (initialL: RiscvMachineL) post a
         (f : A -> M unit),
      mcomp_sat (f a) initialL post ->
      mcomp_sat (Bind (Return a) f) initialL post.
  Proof.
    intros. rewrite left_identity. assumption.
  Qed.

  Lemma go_right_identity: forall (initialL: RiscvMachineL) post
         (m: M unit),
      mcomp_sat m initialL post ->
      mcomp_sat (Bind m Return) initialL post.
  Proof.
    intros. rewrite right_identity. assumption.
  Qed.

  Lemma go_associativity{A B: Type}: forall (initialL: RiscvMachineL) post
         (m: M A)
         (f : A -> M B) (g : B -> M unit),
      mcomp_sat (Bind m (fun x : A => Bind (f x) g)) initialL post ->
      mcomp_sat (Bind (Bind m f) g) initialL post.
  Proof.
    intros. rewrite associativity. assumption.
  Qed.

  Local Arguments Z.of_nat: simpl never.
  Local Arguments Z.mul: simpl never.
  Local Arguments Z.add: simpl never.

  Definition unchecked_store_program(addr: word)(p: list Decode.Instruction)(m: mem): mem :=
    unchecked_store_byte_list addr (Z32s_to_bytes (List.map encode p)) m.

  Lemma unchecked_store_byte_list_None: forall (l: list byte) (z: Z) m (addr: word),
      0 < z ->
      z + Z.of_nat (length l) < 2 ^ width ->
      map.get m addr = None ->
      map.get (unchecked_store_byte_list (word.add addr (word.of_Z z)) l m) addr = None.
  Proof.
    intros. unfold unchecked_store_byte_list, unchecked_store_bytes.
    apply putmany_of_footprint_None; try assumption; try blia.
  Qed.

  Fixpoint in_tuple{T: Type}(a: T){n: nat}: HList.tuple T n -> Prop :=
    match n with
    | O => fun _ => False
    | S n' => fun '(PrimitivePair.pair.mk t ts) => a = t \/ in_tuple a ts
    end.

  Lemma ptsto_bytes_putmany_of_tuple: forall n addr vs (R: mem -> Prop) m,
      Z.of_nat n < 2 ^ width ->
      R m ->
      (forall k, in_tuple k (footprint addr n) -> map.get m k = None) ->
      (ptsto_bytes n addr vs * R)%sep (map.putmany_of_tuple (footprint addr n) vs m).
  Proof.
    assert (2 ^ width > 0) as Gz. {
      destruct width_cases as [E | E]; rewrite E; reflexivity.
    }
    induction n; intros.
    - simpl. unfold ptsto_bytes. destruct vs. simpl. apply sep_emp_l. auto.
    - simpl. unfold ptsto_bytes. destruct vs as [v vs].
      simpl.
      replace (Z.of_nat (S n)) with (1 + Z.of_nat n) in H by blia.
      match goal with
      | |- (?A * ?B * ?C)%sep ?m => assert ((A * (B * C))%sep m); [|ecancel_assumption]
      end.
      eapply sep_on_undef_put.
      + apply putmany_of_footprint_None; try blia.
        eapply H1.
        simpl. left. reflexivity.
      + apply IHn; blia || assumption || idtac.
        intros. eapply H1.
        simpl. right. assumption.
  Qed.

  Lemma ptsto_bytes_putmany_of_tuple_empty: forall n (addr: word) vs,
      Z.of_nat n < 2 ^ width ->
      ptsto_bytes n addr vs (map.putmany_of_tuple (footprint addr n) vs map.empty).
  Proof.
    induction n; intros.
    - cbv. auto.
    - simpl. unfold ptsto_bytes. destruct vs as [v vs].
      simpl.
      replace (Z.of_nat (S n)) with (1 + Z.of_nat n) in H by blia.
      eapply sep_on_undef_put.
      + apply putmany_of_footprint_None; try blia.
        apply map.get_empty.
      + apply IHn. blia.
  Qed.

  Lemma ptsto_bytes_array: forall (l: list byte) (addr: word),
      iff1 (array ptsto (word.of_Z 1) addr l)
           (ptsto_bytes (length l) addr (HList.tuple.of_list l)).
  Proof.
    induction l; intros.
    - simpl. reflexivity.
    - simpl. unfold ptsto_bytes. simpl. apply iff1_sep_cancel. apply IHl.
  Qed.

  Lemma array_on_undef_store_byte_list: forall addr l (R: mem -> Prop) m,
      Z.of_nat (length l) < 2 ^ width ->
      R m ->
      (forall k, in_tuple k (footprint addr (length l)) -> map.get m k = None) ->
      (array ptsto (word.of_Z 1) addr l * R)%sep (unchecked_store_byte_list addr l m).
  Proof.
    intros.
    seprewrite ptsto_bytes_array.
    apply ptsto_bytes_putmany_of_tuple; assumption.
  Qed.

  Lemma mod_eq_to_diff: forall e1 e2 m,
      m <> 0 ->
      e1 mod m = e2 mod m ->
      (e1 - e2) mod m = 0.
  Proof.
    intros. rewrite !Z.mod_eq in H0 by assumption.
    replace (e1 - e2) with (m * (e1 / m) - m * (e2 / m)) by blia.
    rewrite Z.mod_eq by assumption.
    rewrite <- Z.mul_sub_distr_l.
    rewrite (Z.mul_comm m (e1 / m - e2 / m)).
    rewrite Z.div_mul by assumption.
    rewrite Z.mul_comm.
    apply Z.sub_diag.
  Qed.

  Ltac word_simpl :=
    rewrite <-? word.add_assoc;
    rewrite <-? word.ring_morph.(morph_add);
    simpl.

  Lemma pow2width_nonzero: 2 ^ width <> 0.
  Proof.
    destruct width_cases as [E | E]; rewrite E; cbv; discriminate.
  Qed.

  Lemma ptsto_subset_to_isXAddr1: forall (a : word) (v : Init.Byte.byte) xAddrs,
      subset (footpr (ptsto a v)) (of_list xAddrs) ->
      isXAddr1 a xAddrs.
  Proof.
    unfold subset, footpr, footprint_underapprox, ptsto, elem_of, of_list, isXAddr1.
    intros.
    eapply H.
    intros.
    subst.
    eexists.
    apply map.get_put_same.
  Qed.

  Context (iset: Decode.InstructionSet).

  Lemma ptsto_instr_subset_to_isXAddr4: forall (a: word) i xAddrs,
      subset (footpr (ptsto_instr iset a i)) (of_list xAddrs) ->
      isXAddr4 a xAddrs.
  Proof.
    unfold isXAddr4, ptsto_instr, truncated_scalar, littleendian, ptsto_bytes, array. simpl.
    intros.
    ssplit; eapply ptsto_subset_to_isXAddr1;
      (eapply shrink_footpr_subset; [eassumption|wcancel]).
  Qed.

  Definition not_InvalidInstruction(inst: Decode.Instruction): Prop :=
    match inst with
    | Decode.InvalidInstruction _ => False
    | _ => True
    end.

  Lemma go_fetch_inst{initialL: RiscvMachineL} {inst pc0 R Rexec} (post: RiscvMachineL -> Prop):
      pc0 = initialL.(getPc) ->
      subset (footpr (program iset pc0 [inst] * Rexec)%sep) (of_list initialL.(getXAddrs)) ->
      (program iset pc0 [inst] * Rexec * R)%sep initialL.(getMem) ->
      not_InvalidInstruction inst ->
      mcomp_sat (Bind (execute inst) (fun _ => endCycleNormal))
                (updateMetrics (addMetricLoads 1) initialL) post ->
      mcomp_sat (run1 iset) initialL post.
  Proof.
    intros. subst.
    unfold run1.
    apply go_getPC.
    unfold program in *.
    unfold array, ptsto_instr in H1.
    match goal with
    | H: (?T * ?P1 * ?P2 * emp True * Rexec * R)%sep ?m |- _ =>
      assert ((T * R * Rexec * P1 * P2)%sep m) as A by ecancel_assumption; clear H
    end.
    do 2 (apply sep_emp_r in A; destruct A as [A ?]).
    eapply go_loadWord_Fetch.
    - eapply ptsto_instr_subset_to_isXAddr4.
      eapply shrink_footpr_subset. 1: eassumption. simpl. ecancel.
    - unfold Memory.loadWord.
      unfold truncated_scalar, littleendian, Memory.bytes_per in A.
      eapply load_bytes_of_sep with (n:=(length (LittleEndianList.le_split 4 (encode inst)))).
      (* TODO here it would be useful if seplog unfolded Memory.bytes_per for me,
         ie. did more than just syntactic unify *)
      ecancel_assumption.
    - change 4%nat with (length (LittleEndianList.le_split 4 (encode inst))).
      rewrite LittleEndian.combine_eq, HList.tuple.to_list_of_list, LittleEndianList.le_combine_split.
      assert (0 <= encode inst < 2 ^ width) as F. {
        pose proof (encode_range inst) as P.
        destruct width_cases as [E | E]; rewrite E; split. all: blia.
      }
      rewrite Z.mod_small; try assumption; try apply encode_range.
      destruct H1.
      + rewrite decode_encode; assumption.
      + exfalso. unfold not_InvalidInstruction, valid_InvalidInstruction in *. simp. contradiction.
  Qed.

  (* go_load/storeXxx lemmas phrased in terms of separation logic instead of
     Memory.load/storeXxx *)

  Lemma go_loadByte_sep:
    forall (initialL : RiscvMachineL) (addr : word) (v : w8)
           (f : w8 -> M unit) (post : RiscvMachineL -> Prop) (R: mem -> Prop),
      (ptsto_bytes 1 addr v * R)%sep initialL.(getMem) ->
      mcomp_sat (f v) (updateMetrics (addMetricLoads 1) initialL) post ->
      mcomp_sat (Bind (loadByte Execute addr) f) initialL post.
  Proof.
    intros.
    eapply go_loadByte; [|eassumption].
    eapply load_bytes_of_sep. eassumption.
  Qed.

  Lemma preserve_subset_of_xAddrs: forall m Rexec n (R: mem -> Prop) (xAddrs: list word) addr v,
      subset (footpr Rexec) (of_list xAddrs) ->
      (ptsto_bytes n addr v * R * Rexec)%sep m ->
      subset (footpr Rexec) (of_list (invalidateWrittenXAddrs n addr xAddrs)).
  Proof.
    induction n; intros.
    - simpl. assumption.
    - destruct v as [v vs]. unfold ptsto_bytes in *. simpl in *.
      assert (exists R',
                 (array ptsto (word.of_Z 1) (word.add addr (word.of_Z 1)) (HList.tuple.to_list vs)
                  * R' * Rexec)%sep m) as F by (eexists; ecancel_assumption).
      destruct F as [R' F].
      specialize IHn with (2 := F).
      change removeXAddr with (@List.removeb word word.eqb).
      rewrite ListSet.of_list_removeb.
      unfold subset.
      intros x Hx.
      destr (word.eqb x addr).
      + subst. exfalso. clear F IHn.
        unfold sep, map.split in H0.
        simp.
        unfold elem_of, footpr, footprint_underapprox in Hx.
        specialize (Hx _ H0p2).
        destruct Hx as [w Hx].
        rename H0p1p1p1 into B.
        unfold ptsto in B.
        subst.
        unfold map.disjoint in *.
        eapply H0p0p1. 2: exact Hx.
        rewrite map.get_putmany_left; cycle 1. {
          destr (map.get mq0 addr); [exfalso|reflexivity].
          eapply H0p1p0p1. 2: exact E.
          rewrite map.get_putmany_left; cycle 1. {
            destr (map.get mq1 addr); [exfalso|reflexivity].
            eapply H0p1p1p0p1. 2: exact E0.
            rewrite map.get_put_same. reflexivity.
          }
          rewrite map.get_put_same. reflexivity.
        }
        rewrite map.get_putmany_left; cycle 1. {
          destr (map.get mq1 addr); [exfalso|reflexivity].
          eapply H0p1p1p0p1. 2: exact E.
          rewrite map.get_put_same. reflexivity.
        }
        rewrite map.get_put_same. reflexivity.
      + unfold diff, elem_of, singleton_set. split; [|congruence].
        eapply IHn; assumption.
  Qed.

  Lemma go_storeByte_sep:
    forall (initialL : RiscvMachineL) (addr : word) (v_old v_new : w8)
           (post : RiscvMachineL -> Prop) (f : unit -> M unit) (R Rexec: mem -> Prop),
      subset (footpr Rexec) (of_list initialL.(getXAddrs)) ->
      (ptsto_bytes 1 addr v_old * R * Rexec)%sep initialL.(getMem) ->
      (forall m': mem,
          subset (footpr Rexec) (of_list (invalidateWrittenXAddrs 1 addr initialL.(getXAddrs))) ->
          (ptsto_bytes 1 addr v_new * R * Rexec)%sep m' ->
          mcomp_sat (f tt) (withXAddrs (invalidateWrittenXAddrs 1 addr initialL.(getXAddrs))
                           (withMem m' (updateMetrics (addMetricStores 1) initialL))) post) ->
      mcomp_sat (Bind (storeByte Execute addr v_new) f) initialL post.
  Proof.
    intros.
    pose proof (store_bytes_of_sep (mem_ok := mem_ok)) as P.
    edestruct P as [m' [P1 P2]]; cycle 2.
    - eapply go_storeByte.
      + exact P1.
      + exact P2.
    - ecancel_assumption.
    - cbv beta. intros m' Hm'.
      eapply H1. 2: ecancel_assumption.
      eapply preserve_subset_of_xAddrs; eassumption.
  Qed.

  Lemma go_loadHalf_sep:
    forall (initialL : RiscvMachineL) (addr : word) (v : w16)
           (f : w16 -> M unit) (post : RiscvMachineL -> Prop) (R: mem -> Prop),
      (ptsto_bytes 2 addr v * R)%sep initialL.(getMem) ->
      mcomp_sat (f v) (updateMetrics (addMetricLoads 1) initialL) post ->
      mcomp_sat (Bind (loadHalf Execute addr) f) initialL post.
  Proof.
    intros.
    eapply go_loadHalf; [|eassumption].
    eapply load_bytes_of_sep. eassumption.
  Qed.

  Lemma go_storeHalf_sep:
    forall (initialL : RiscvMachineL) (addr : word) (v_old v_new : w16)
           (post : RiscvMachineL -> Prop) (f : unit -> M unit) (R Rexec: mem -> Prop),
      subset (footpr Rexec) (of_list initialL.(getXAddrs)) ->
      (ptsto_bytes 2 addr v_old * R * Rexec)%sep initialL.(getMem) ->
      (forall m': mem,
          subset (footpr Rexec) (of_list (invalidateWrittenXAddrs 2 addr initialL.(getXAddrs))) ->
          (ptsto_bytes 2 addr v_new * R * Rexec)%sep m' ->
          mcomp_sat (f tt) (withXAddrs (invalidateWrittenXAddrs 2 addr initialL.(getXAddrs))
                           (withMem m' (updateMetrics (addMetricStores 1) initialL))) post) ->
      mcomp_sat (Bind (storeHalf Execute addr v_new) f) initialL post.
  Proof.
    intros.
    pose proof (store_bytes_of_sep (mem_ok := mem_ok)) as P.
    edestruct P as [m' [P1 P2]]; cycle 2.
    - eapply go_storeHalf.
      + exact P1.
      + exact P2.
    - ecancel_assumption.
    - cbv beta. intros m' Hm'.
      eapply H1. 2: ecancel_assumption.
      eapply preserve_subset_of_xAddrs; eassumption.
  Qed.

  Lemma go_loadWord_sep:
    forall (initialL : RiscvMachineL) (addr : word) (v : w32)
           (f : w32 -> M unit) (post : RiscvMachineL -> Prop) (R: mem -> Prop),
      (ptsto_bytes 4 addr v * R)%sep initialL.(getMem) ->
      mcomp_sat (f v) (updateMetrics (addMetricLoads 1) initialL) post ->
      mcomp_sat (Bind (loadWord Execute addr) f) initialL post.
  Proof.
    intros.
    eapply go_loadWord; [|eassumption].
    eapply load_bytes_of_sep. eassumption.
  Qed.

  Lemma go_storeWord_sep:
    forall (initialL : RiscvMachineL) (addr : word) (v_old v_new : w32)
           (m': mem) (post : RiscvMachineL -> Prop) (f : unit -> M unit) (R: mem -> Prop),
      (ptsto_bytes 4 addr v_old * R)%sep initialL.(getMem) ->
      (ptsto_bytes 4 addr v_new * R)%sep m' ->
      mcomp_sat (f tt) (withXAddrs (invalidateWrittenXAddrs 4 addr initialL.(getXAddrs))
                       (withMem m' (updateMetrics (addMetricStores 1) initialL))) post ->
      mcomp_sat (Bind (storeWord Execute addr v_new) f) initialL post.
  Proof.
    intros.
    eapply go_storeWord; [|eassumption].
    unfold Memory.storeWord.
    pose proof (unchecked_store_bytes_of_sep (mem_ok := mem_ok)) as P.
    specialize P with (1 := H). specialize (P v_new).
    (* Does not hold because if R does not completely determine the contents of the memory,
       initialL.(getMem) and m' could change in locations other than at addr,
       and post could check for that, so if the post in the hyp requires some specific value
       in m', this value might not be present in initialL.(getMem), and still not be present
       after the storeWord operation, so the conclusion would not hold. *)
  Abort.

  Lemma go_storeWord_sep:
    forall (initialL : RiscvMachineL) (addr : word) (v_old v_new : w32)
           (post : RiscvMachineL -> Prop) (f : unit -> M unit) (R Rexec: mem -> Prop),
      subset (footpr Rexec) (of_list initialL.(getXAddrs)) ->
      (ptsto_bytes 4 addr v_old * R * Rexec)%sep initialL.(getMem) ->
      (let m' := Memory.unchecked_store_bytes 4 (getMem initialL) addr v_new in
       let xaddrs' := invalidateWrittenXAddrs 4 addr initialL.(getXAddrs) in
          subset (footpr Rexec) (of_list xaddrs') ->
          (ptsto_bytes 4 addr v_new * R * Rexec)%sep m' ->
          mcomp_sat (f tt) (withXAddrs xaddrs'
                           (withMem m' (updateMetrics (addMetricStores 1) initialL))) post) ->
      mcomp_sat (Bind (storeWord Execute addr v_new) f) initialL post.
  Proof.
    intros.
    pose proof (unchecked_store_bytes_of_sep (mem_ok := mem_ok)) as P.
    assert ((ptsto_bytes 4 addr v_old * (R * Rexec))%sep initialL.(getMem)) as H0'
        by ecancel_assumption.
    specialize P with (1 := H0'). specialize (P v_new).
    cbv zeta in H1.
    assert ((ptsto_bytes 4 addr v_new * R * Rexec)%sep
                (Memory.unchecked_store_bytes 4 (getMem initialL) addr v_new)) as P'
        by ecancel_assumption.
    specialize H1 with (2 := P').
    eapply go_storeWord; cycle 1. {
      eapply H1.
      eapply preserve_subset_of_xAddrs; eassumption.
    }
    unfold Memory.storeWord, store_bytes.
    erewrite load_bytes_of_sep; eauto using unchecked_store_bytes_of_sep.
  Qed.

  Lemma go_storeWord_sep_holds_but_results_in_evars_out_of_scope:
    forall (initialL : RiscvMachineL) (addr : word) (v_old v_new : w32)
           (post : RiscvMachineL -> Prop) (f : unit -> M unit) (R: mem -> Prop),
      (ptsto_bytes 4 addr v_old * R)%sep initialL.(getMem) ->
      (forall m': mem,
          (ptsto_bytes 4 addr v_new * R)%sep m' ->
          mcomp_sat (f tt) (withXAddrs (invalidateWrittenXAddrs 4 addr initialL.(getXAddrs))
                           (withMem m' (updateMetrics (addMetricStores 1) initialL))) post) ->
      mcomp_sat (Bind (storeWord Execute addr v_new) f) initialL post.
  Proof.
    intros.
    pose proof (store_bytes_of_sep (mem_ok := mem_ok)) as P.
    specialize P with (1 := H) (2 := H0).
    destruct P as (m' & P & Q).
    eapply go_storeWord; eassumption.
  Qed.

  Lemma go_loadDouble_sep:
    forall (initialL : RiscvMachineL) (addr : word) (v : w64)
           (f : w64 -> M unit) (post : RiscvMachineL -> Prop) (R: mem -> Prop),
      (ptsto_bytes 8 addr v * R)%sep initialL.(getMem) ->
      mcomp_sat (f v) (updateMetrics (addMetricLoads 1) initialL) post ->
      mcomp_sat (Bind (loadDouble Execute addr) f) initialL post.
  Proof.
    intros.
    eapply go_loadDouble; [|eassumption].
    eapply load_bytes_of_sep. eassumption.
  Qed.

  Lemma go_storeDouble_sep:
    forall (initialL : RiscvMachineL) (addr : word) (v_old v_new : w64)
           (post : RiscvMachineL -> Prop) (f : unit -> M unit) (R Rexec: mem -> Prop),
      subset (footpr Rexec) (of_list initialL.(getXAddrs)) ->
      (ptsto_bytes 8 addr v_old * R * Rexec)%sep initialL.(getMem) ->
      (forall m': mem,
          subset (footpr Rexec) (of_list (invalidateWrittenXAddrs 8 addr initialL.(getXAddrs))) ->
          (ptsto_bytes 8 addr v_new * R * Rexec)%sep m' ->
          mcomp_sat (f tt) (withXAddrs (invalidateWrittenXAddrs 8 addr initialL.(getXAddrs))
                           (withMem m' (updateMetrics (addMetricStores 1) initialL))) post) ->
      mcomp_sat (Bind (storeDouble Execute addr v_new) f) initialL post.
  Proof.
    intros.
    pose proof (store_bytes_of_sep (mem_ok := mem_ok)) as P.
    edestruct P as [m' [P1 P2]]; cycle 2.
    - eapply go_storeDouble.
      + exact P1.
      + exact P2.
    - ecancel_assumption.
    - cbv beta. intros m' Hm'.
      eapply H1. 2: ecancel_assumption.
      eapply preserve_subset_of_xAddrs; eassumption.
  Qed.

End Go.

Ltac simpl_MetricRiscvMachine_get_set :=
  cbn [
     withMetrics
     updateMetrics
     getMachine
     getMetrics
     getRegs
     getPc
     getNextPc
     getMem
     getXAddrs
     getLog
     withRegs
     withPc
     withNextPc
     withMem
     withXAddrs
     withLog
     withLogItem
     withLogItems
     RiscvMachine.withRegs
     RiscvMachine.withPc
     RiscvMachine.withNextPc
     RiscvMachine.withMem
     RiscvMachine.withXAddrs
     RiscvMachine.withLog
     RiscvMachine.withLogItem
     RiscvMachine.withLogItems
  ].

Ltac simpl_MetricRiscvMachine_mem :=
  unfold getPc, getMem in *;
  simpl RiscvMachine.getPc in *;
  simpl RiscvMachine.getMem in *.

Ltac sidecondition_hook := idtac.

#[export] Hint Resolve Forall_impl : sidecondition_hints.

Ltac subst_if_not_in x t :=
  lazymatch t with
  | context[x] => fail
  | _ => progress subst x
  end.

Ltac subst_sep_var_only_in_lhs lhs rhs :=
  match lhs with
  | context[sep ?x _] => is_var x; subst_if_not_in x rhs
  | context[sep _ ?x] => is_var x; subst_if_not_in x rhs
  end.

Ltac subst_sep_vars :=
  match goal with
  | |- iff1 ?LHS ?RHS =>
    repeat (subst_sep_var_only_in_lhs LHS RHS);
    repeat (subst_sep_var_only_in_lhs RHS LHS)
  end.

Ltac sidecondition :=
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
                                 use_sep_assumption;
                                 wwcancel
  | |- iff1 ?x _ =>
    simpl_MetricRiscvMachine_get_set;
    (tryif is_var x then
       lazymatch goal with
       | H: iff1 x _ |- _ => etransitivity; [exact H|]
       end
     else idtac);
    subst_sep_vars;
    wwcancel
  | H: subset (footpr _) _ |- subset (footpr ?F) _ =>
    tryif is_evar F then
      eassumption
    else
      (simpl in H |- *;
       eapply rearrange_footpr_subset; [ exact H | solve [sidecondition] ])
  | |- _ => reflexivity
  | A: map.get ?lH ?x = Some _, E: map.extends ?lL ?lH |- map.get ?lL ?x = Some _ =>
    eapply (map.extends_get A E)
  (* but we don't have a general "eassumption" branch, only "assumption": *)
  | |- _ => solve [auto with sidecondition_hints]
  | |- ?G => assert_fails (has_evar G); solve [eauto with sidecondition_hints]
  | |- Memory.load ?sz ?m ?addr = Some ?v =>
    unfold Memory.load, Memory.load_Z in *;
    simpl_MetricRiscvMachine_mem;
    erewrite load_bytes_of_sep; [ reflexivity | ecancel_assumption ]
  | |- Memory.load ?sz ?m ?addr = Some ?v => eassumption
  | |- Memory.store ?sz ?m ?addr ?val = Some ?m' => eassumption
  | |- _ => sidecondition_hook
  end.

(* eapply and rapply don't always work (they failed in compiler.MMIO), so we use refine below
   Trick to test if right number of underscores:
          let c := open_constr:(go_associativity _ _ _ _ _ _) in
          let t := type of c in idtac t. *)

Ltac simulate_step :=
  first (* lemmas packing multiple primitives need to go first: *)
        [ refine (go_fetch_inst _ _ _ _ _ _ _);    [sidecondition..|]
        (* single-primitive lemmas: *)
        (* lemmas about Register0 need to go before lemmas about other Registers *)
        | refine (go_getRegister0 _ _ _ _);        [sidecondition..|]
        | refine (go_setRegister0 _ _ _ _ _);      [sidecondition..|]
        | refine (go_getRegister _ _ _ _ _ _ _ _); [sidecondition..|]
        | refine (go_setRegister _ _ _ _ _ _ _);   [sidecondition..|]
        (* Note: One might not want these, but the separation logic version, or
           the version expressed in terms of compile_load/store, so they're commented out
        | eapply go_loadByte       ; [sidecondition..|]
        | eapply go_storeByte      ; [sidecondition..|]
        | eapply go_loadHalf       ; [sidecondition..|]
        | eapply go_storeHalf      ; [sidecondition..|]
        | eapply go_loadWord       ; [sidecondition..|]
        | eapply go_storeWord      ; [sidecondition..|]
        | eapply go_loadDouble     ; [sidecondition..|]
        | eapply go_storeDouble    ; [sidecondition..|]
        *)
        | refine (go_getPC _ _ _ _);               [sidecondition..|]
        | refine (go_setPC _ _ _ _ _);             [sidecondition..|]
        | refine (go_endCycleNormal _ _ _);        [sidecondition..|]
        (* monad law lemmas: *)
        | refine (go_left_identity _ _ _ _ _);     [sidecondition..|]
        | refine (go_right_identity _ _ _ _);      [sidecondition..|]
        | refine (go_associativity _ _ _ _ _ _);   [sidecondition..|] ].

Ltac simulate := repeat simulate_step.
