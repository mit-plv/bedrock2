From Coq Require Import ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Z.Lia.
Require Import coqutil.Z.div_mod_to_equations.
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
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.MetricPrimitives.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Platform.Run.
Require Import riscv.Spec.Execute.
Require Import coqutil.Tactics.Tactics.
Require Import compiler.SeparationLogic.
Require Import compiler.SimplWordExpr.
Require Import compiler.DivisibleBy4.
Require Import bedrock2.ptsto_bytes.
Require Import bedrock2.Scalars.
Require Import riscv.Utility.Encode.
Require Import riscv.Proofs.EncodeBound.
Require Import riscv.Proofs.DecodeEncode.
Require Import riscv.Platform.MetricSane.
Require Import coqutil.Decidable.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.Simp.
Require Import riscv.Utility.runsToNonDet.
Import Utility.

Section Go.

  Context {W: Words}.
  Context {Registers: map.map Register word}.
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

  Lemma ExecuteFetchP: forall addr xAddrs, Execute = Fetch -> isXAddr4 addr xAddrs.
  Proof. intros. discriminate. Qed.

  Ltac t lem :=
    intros;
    try (eapply spec_Bind_det; [|eassumption]); (* try because go_step doesn't need Bind *)
    apply lem;
    rewrite_match;
    eauto 10 using ExecuteFetchP.

  Lemma go_getRegister: forall (initialL: RiscvMachineL) (x: Register) v post (f: word -> M unit),
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

  Lemma go_step: forall (initialL: RiscvMachineL) (post: RiscvMachineL -> Prop),
      post (withPc initialL.(getNextPc)
           (withNextPc (word.add initialL.(getNextPc) (word.of_Z 4))
           (updateMetrics (addMetricInstructions 1) initialL))) ->
      mcomp_sat step initialL post.
  Proof. t spec_step. Qed.

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

  Axiom TODO_sam: False.

  Definition iset := if Utility.width =? 32 then RV32IM else RV64IM.

  (* contains all the conditions needed to successfully execute instr, except
     that addr needs to be in the set of executable addresses, which is dealt with elsewhere *)
  Definition ptsto_instr(addr: word)(instr: Instruction): mem -> Prop :=
    (truncated_scalar Syntax.access_size.four addr (encode instr) *
     emp (verify instr iset) *
     emp ((word.unsigned addr) mod 4 = 0))%sep.

  Definition program(addr: word)(prog: list Instruction): mem -> Prop :=
    array ptsto_instr (word.of_Z 4) addr prog.

  Lemma invert_ptsto_instr: forall {addr instr R m},
    (ptsto_instr addr instr * R)%sep m ->
     verify instr iset /\
     (word.unsigned addr) mod 4 = 0.
  Proof.
    intros.
    unfold array, ptsto_instr in *.
    match goal with
    | H: (?T * ?P1 * ?P2 * R)%sep ?m |- _ =>
      assert ((T * R * P1 * P2)%sep m) as A by ecancel_assumption; clear H
    end.
    do 2 (apply sep_emp_r in A; destruct A as [A ?]).
    auto.
  Qed.

  Lemma invert_ptsto_program1: forall {addr instr R m},
    (program addr [instr] * R)%sep m ->
     verify instr iset /\
     (word.unsigned addr) mod 4 = 0.
  Proof.
    unfold program. intros. simpl in *. eapply invert_ptsto_instr.
    ecancel_assumption.
  Qed.

  Arguments Z.of_nat: simpl never.
  Arguments Z.mul: simpl never.
  Arguments Z.add: simpl never.

  Definition unchecked_store_program(addr: word)(p: list Instruction)(m: mem): mem :=
    unchecked_store_byte_list addr (Z32s_to_bytes (List.map encode p)) m.

  Lemma putmany_of_footprint_None: forall n (vs: HList.tuple byte n) (addr: word) (z: Z) (m: mem),
      0 < z ->
      z + Z.of_nat n < 2 ^ width ->
      map.get m addr = None ->
      map.get (map.putmany_of_tuple (footprint (word.add addr (word.of_Z z)) n) vs m)
              addr = None.
  Proof.
    induction n; intros.
    - simpl. assumption.
    - destruct vs as [v vs]. simpl.
      assert (2 ^ width > 0) as Gz. {
        destruct width_cases as [E | E]; rewrite E; reflexivity.
      }
      rewrite map.get_put_diff; cycle 1. {
        clear -H H0 Gz. intro C.
        apply (f_equal word.unsigned) in C.
        rewrite word.unsigned_add in C. unfold word.wrap in C.
        rewrite word.unsigned_of_Z in C. unfold word.wrap in C.
        pose proof (word.unsigned_range addr) as R.
        remember (word.unsigned addr) as w.
        rewrite Z.add_mod_idemp_r in C by bomega.
        rewrite Z.mod_eq in C by bomega.
        assert (z = 2 ^ width * ((w + z) / 2 ^ width)) by bomega.
        remember ((w + z) / 2 ^ width) as k.
        assert (k < 0 \/ k = 0 \/ 0 < k) as D by bomega. destruct D as [D | [D | D]]; Lia.nia.
      }
      rewrite <- word.add_assoc.
      replace ((word.add (word.of_Z (word := @word W) z) (word.of_Z 1)))
        with (word.of_Z (word := @word W) (z + 1)); cycle 1. {
        apply word.unsigned_inj.
        rewrite word.unsigned_add.
        rewrite! word.unsigned_of_Z.
        apply Z.add_mod.
        destruct width_cases as [E | E]; rewrite E; cbv; discriminate.
      }
      eapply IHn; try blia.
      assumption.
  Qed.

  Lemma putmany_of_footprint_None'': forall n (vs: HList.tuple byte n) (a1 a2: word) (m: mem),
      0 < word.unsigned (word.sub a1 a2) ->
      word.unsigned (word.sub a1 a2) + Z.of_nat n < 2 ^ width ->
      map.get m a2 = None ->
      map.get (map.putmany_of_tuple (footprint a1 n) vs m) a2 = None.
  Proof.
    intros.
    pose proof putmany_of_footprint_None as P.
    specialize P with (1 := H) (2 := H0) (3 := H1).
    specialize (P vs).
    replace (word.add a2 (word.of_Z (word.unsigned (word.sub a1 a2)))) with a1 in P; [exact P|].
    apply word.unsigned_inj.
    rewrite word.unsigned_add. unfold word.wrap.
    rewrite word.of_Z_unsigned.
    rewrite word.unsigned_sub. unfold word.wrap.
    rewrite Z.add_mod_idemp_r by (destruct width_cases as [E | E]; rewrite E; cbv; discriminate).
    rewrite <- (word.of_Z_unsigned a1) at 1.
    rewrite word.unsigned_of_Z. unfold word.wrap.
    f_equal.
    bomega.
  Qed.

  Lemma putmany_of_footprint_None': forall n (vs: HList.tuple byte n) (a1 a2: word) (m: mem),
      a1 <> a2 ->
      word.unsigned (word.sub a1 a2) + Z.of_nat n < 2 ^ width ->
      map.get m a2 = None ->
      map.get (map.putmany_of_tuple (footprint a1 n) vs m) a2 = None.
  Proof.
    intros.
    apply putmany_of_footprint_None''; try assumption.
    pose proof (word.unsigned_range (word.sub a1 a2)).
    assert (word.unsigned (word.sub a1 a2) = 0 \/ 0 < word.unsigned (word.sub a1 a2)) as C
        by bomega. destruct C as [C | C].
    - exfalso. apply H.
      rewrite word.unsigned_sub in C.
      apply word.unsigned_inj.
      apply Z.div_exact in C; [|(destruct width_cases as [E | E]; rewrite E; cbv; discriminate)].
      remember ((word.unsigned a1 - word.unsigned a2) / 2 ^ width) as k.
      pose proof (word.unsigned_range a1).
      pose proof (word.unsigned_range a2).
      assert (k < 0 \/ k = 0 \/ 0 < k) as D by bomega. destruct D as [D | [D | D]]; try Lia.nia.
      (* LIABUG if primitive projections are on, we need this:
      rewrite D in C.
      rewrite Z.mul_0_r in C.
      bomega.
      *)
    - assumption.
  Qed.

  Lemma unchecked_store_byte_list_None: forall (l: list byte) (z: Z) m (addr: word),
      0 < z ->
      z + Z.of_nat (length l) < 2 ^ width ->
      map.get m addr = None ->
      map.get (unchecked_store_byte_list (word.add addr (word.of_Z z)) l m)
              addr = None.
  Proof.
    intros. unfold unchecked_store_byte_list, unchecked_store_bytes.
    apply putmany_of_footprint_None; try assumption.
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
      + exact word.eqb_spec.
      + apply putmany_of_footprint_None; try bomega.
        eapply H1.
        simpl. left. reflexivity.
      + apply IHn; bomega || assumption || idtac.
        intros. eapply H1.
        simpl. right. assumption.
  Qed.

  Lemma ptsto_bytes_putmany_of_tuple_empty: forall n addr vs,
      Z.of_nat n < 2 ^ width ->
      ptsto_bytes n addr vs (map.putmany_of_tuple (footprint addr n) vs map.empty).
  Proof.
    induction n; intros.
    - cbv. auto.
    - simpl. unfold ptsto_bytes. destruct vs as [v vs].
      simpl.
      replace (Z.of_nat (S n)) with (1 + Z.of_nat n) in H by blia.
      eapply sep_on_undef_put.
      + exact word.eqb_spec.
      + apply putmany_of_footprint_None; try bomega.
        apply map.get_empty.
      + apply IHn. bomega.
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

  Lemma length_flat_map: forall {A B: Type} (f: A -> list B) n (l: list A),
      (forall (a: A), length (f a) = n) ->
      length (flat_map f l) = (n * length l)%nat.
  Proof.
    induction l; intros.
    - simpl. blia.
    - simpl. rewrite app_length. rewrite H. rewrite IHl; assumption || blia.
  Qed.

  Lemma mod_eq_to_diff: forall e1 e2 m,
      m <> 0 ->
      e1 mod m = e2 mod m ->
      (e1 - e2) mod m = 0.
  Proof.
    intros. rewrite !Z.mod_eq in H0 by assumption.
    replace (e1 - e2) with (m * (e1 / m) - m * (e2 / m)) by bomega.
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

  (* proves goals of the form
  addr <> word.add (word.add (word.add addr (word.of_Z 1)) (word.of_Z 1)) (word.of_Z 1)
  (any number of +1s)
   *)
  Ltac word_neq_add :=
    word_simpl;
    let C := fresh in
    intro C;
    apply (f_equal word.unsigned) in C;
    match type of C with
    | word.unsigned ?addr = _ => rewrite <- (word.of_Z_unsigned addr) in C at 1
    end;
    unfold word.wrap in C;
    rewrite !word.unsigned_add in C; unfold word.wrap in C;
    rewrite !word.unsigned_of_Z in C; unfold word.wrap in C;
    rewrite ?Z.add_mod_idemp_r in C by (apply pow2width_nonzero);
    rewrite ?Z.mod_mod in C by (apply pow2width_nonzero);
    (apply mod_eq_to_diff in C; [|apply pow2width_nonzero]);
    match type of C with
    | ?x mod _ = 0 => ring_simplify x in C
    end;
    destruct width_cases as [E | E]; rewrite E in C;
    cbv in C; discriminate C.

  Lemma store_program_empty: forall prog addr,
      4 * Z.of_nat (length prog) < 2 ^ width ->
      (word.unsigned addr) mod 4 = 0 ->
      Forall (fun instr => verify instr iset) prog ->
      program addr prog (unchecked_store_program addr prog map.empty).
  Proof.
    induction prog; intros.
    - cbv. auto.
    - unfold unchecked_store_program, Z32s_to_bytes. simpl.
      rewrite! unchecked_store_byte_list_cons.
      unfold ptsto_instr, truncated_scalar, littleendian, Memory.bytes_per, ptsto_bytes. simpl.
      match goal with
      | |- (?A1 * (?A2 * (?A3 * (?A4 * emp True))) * ?P1 * ?P2 * ?B)%sep ?m =>
        assert ((A1 * (A2 * (A3 * (A4 * (P1 * (P2 * B))))))%sep m); [|ecancel_assumption]
      end.
      eapply sep_on_undef_put; try exact word.eqb_spec. {
        rewrite !map.get_put_diff by word_neq_add.
        word_simpl.
        apply unchecked_store_byte_list_None; try reflexivity; try apply map.get_empty.
        erewrite length_flat_map by (intro; simpl; reflexivity).
        rewrite map_length.
        change (Z.of_nat (length (a :: prog))) with (Z.of_nat (1 + length prog)) in H.
        blia.
      }
      eapply sep_on_undef_put; try exact word.eqb_spec. {
        rewrite !map.get_put_diff by word_neq_add.
        remember (word.add addr (word.of_Z 1)) as addr'.
        word_simpl.
        apply unchecked_store_byte_list_None; try reflexivity; try apply map.get_empty.
        erewrite length_flat_map by (intro; simpl; reflexivity).
        rewrite map_length.
        change (Z.of_nat (length (a :: prog))) with (Z.of_nat (1 + length prog)) in H.
        blia.
      }
      eapply sep_on_undef_put; try exact word.eqb_spec. {
        rewrite !map.get_put_diff by word_neq_add.
        remember (word.add (word.add addr (word.of_Z 1)) (word.of_Z 1)) as addr'.
        word_simpl.
        apply unchecked_store_byte_list_None; try reflexivity; try apply map.get_empty.
        erewrite length_flat_map by (intro; simpl; reflexivity).
        rewrite map_length.
        change (Z.of_nat (length (a :: prog))) with (Z.of_nat (1 + length prog)) in H.
        blia.
      }
      eapply sep_on_undef_put; try exact word.eqb_spec. {
        apply unchecked_store_byte_list_None; try reflexivity; try apply map.get_empty.
        erewrite length_flat_map by (intro; simpl; reflexivity).
        rewrite map_length.
        change (Z.of_nat (length (a :: prog))) with (Z.of_nat (1 + length prog)) in H.
        blia.
      }
      word_simpl.
      destruct H0. inversion H1. subst.
      apply sep_emp_l; split; [assumption|].
      apply sep_emp_l; split; [reflexivity|].
      apply IHprog.
      + change (Z.of_nat (length (a :: prog))) with (Z.of_nat (1 + length prog)) in H. blia.
      + clear. rewrite word.unsigned_add. rewrite word.unsigned_of_Z.
        unfold word.wrap.
        pose proof (word.unsigned_range addr).
        forget (word.unsigned addr) as a.
        rewrite Zplus_mod_idemp_r.
        Z.div_mod_to_equations.
        destruct width_cases as [E | E]; rewrite E in *; blia.
      + assumption.
  Qed.

  Lemma array_map: forall {T1 T2: Type} sz (f: T1 -> T2) elem (l: list T1) (addr: word),
      iff1 (array elem                                (word.of_Z sz) addr (List.map f l))
           (array (fun addr0 v0 => elem addr0 (f v0)) (word.of_Z sz) addr l).
  Proof.
    induction l; intros.
    - simpl. reflexivity.
    - simpl. apply iff1_sep_cancel. apply IHl.
  Qed.

  Lemma ptsto_subset_to_isXAddr1: forall a v xAddrs,
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

  Lemma ptsto_instr_subset_to_isXAddr4: forall a i xAddrs,
      subset (footpr (ptsto_instr a i)) (of_list xAddrs) ->
      isXAddr4 a xAddrs.
  Proof.
    unfold isXAddr4, ptsto_instr, truncated_scalar, littleendian, ptsto_bytes, array. simpl.
    intros.
    ssplit; eapply ptsto_subset_to_isXAddr1;
      (eapply shrink_footpr_subset; [eassumption|wcancel word_ok]).
  Qed.

  Lemma go_fetch_inst_NEW: forall {initialL: RiscvMachineL} {inst pc0 R} (post: RiscvMachineL -> Prop),
      pc0 = initialL.(getPc) ->
      subset (footpr (program pc0 [inst])) (of_list initialL.(getXAddrs)) ->
      (program pc0 [inst] * R)%sep initialL.(getMem) ->
      mcomp_sat (Bind (execute inst) (fun _ => step))
                (updateMetrics (addMetricLoads 1) initialL) post ->
      mcomp_sat (run1 iset) initialL post.
  Proof.
    intros. subst.
    unfold run1.
    apply go_getPC.
    unfold program in *.
    unfold array, ptsto_instr in H1.
    match goal with
    | H: (?T * ?P1 * ?P2 * emp True * R)%sep ?m |- _ =>
      assert ((T * R * P1 * P2)%sep m) as A by ecancel_assumption; clear H
    end.
    do 2 (apply sep_emp_r in A; destruct A as [A ?]).
    eapply go_loadWord_Fetch.
    - eapply ptsto_instr_subset_to_isXAddr4.
      eapply shrink_footpr_subset. 1: eassumption. simpl. ecancel.
    - unfold Memory.loadWord.
      eapply load_bytes_of_sep.
      unfold truncated_scalar, littleendian, Memory.bytes_per in A.
      (* TODO here it would be useful if seplog unfolded Memory.bytes_per for me,
         ie. did more than just syntactic unify *)
      ecancel_assumption.
    - rewrite LittleEndian.combine_split.
      assert (0 <= encode inst < 2 ^ width) as F. {
        pose proof (encode_range inst) as P.
        destruct width_cases as [E | E]; rewrite E; split.
        (* TODO if https://github.com/coq/coq/pull/9291 makes it into 8.9.1,
           bomega can be replaced *)
        + bomega.
        + bomega.
        + bomega.
        + let r := eval cbv in (2 ^ 32) in change (2 ^ 32) with r in *.
          let r := eval cbv in (2 ^ 64) in change (2 ^ 64) with r in *.
          bomega.
      }
      rewrite Z.mod_small; try assumption; try apply encode_range.
      rewrite decode_encode; assumption.
  Qed.

  Lemma go_fetch_inst: forall {initialL: RiscvMachineL} {inst pc0 R} (post: RiscvMachineL -> Prop),
      pc0 = initialL.(getPc) ->
      (program pc0 [inst] * R)%sep initialL.(getMem) ->
      mcomp_sat (Bind (execute inst) (fun _ => step))
                (updateMetrics (addMetricLoads 1) initialL) post ->
      mcomp_sat (run1 iset) initialL post.
  Proof.
    intros. eapply go_fetch_inst_NEW; try eassumption.
    case TODO_sam.
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
      change removeXAddr with (@ListLib.removeb word word.eqb).
      rewrite ListLib.of_list_removeb.
      2: apply word.eqb_spec. (* TODO why is this not automatic? *)
      unfold subset.
      intros x Hx.
      destr (word.eqb x addr).
      + subst. exfalso. clear F IHn.
        unfold sep, map.split in H0.
        simp.
        unfold elem_of, footpr, footprint_underapprox in Hx.
        specialize (Hx _ H0rr).
        destruct Hx as [w Hx].
        rename H0rlrlrl into B.
        unfold ptsto in B.
        subst.
        unfold map.disjoint in *.
        eapply H0lr. 2: exact Hx.
        rewrite map.get_putmany_left; cycle 1. {
          destr (map.get mq0 addr); [exfalso|reflexivity].
          eapply H0rllr. 2: exact E.
          rewrite map.get_putmany_left; cycle 1. {
            destr (map.get mq1 addr); [exfalso|reflexivity].
            eapply H0rlrllr. 2: exact E0.
            rewrite map.get_put_same. reflexivity.
          }
          rewrite map.get_put_same. reflexivity.
        }
        rewrite map.get_putmany_left; cycle 1. {
          destr (map.get mq1 addr); [exfalso|reflexivity].
          eapply H0rlrllr. 2: exact E.
          rewrite map.get_put_same. reflexivity.
        }
        rewrite map.get_put_same. reflexivity.
      + unfold diff, elem_of, singleton_set. split; [|congruence].
        eapply IHn; assumption.
  Qed.

  Lemma go_storeByte_sep:
    forall (initialL : RiscvMachineL) (addr : word) (v_old v_new : w8)
           (post : RiscvMachineL -> Prop) (f : unit -> M unit) (R: mem -> Prop),
      (ptsto_bytes 1 addr v_old * R)%sep initialL.(getMem) ->
      (forall m': mem,
          (ptsto_bytes 1 addr v_new * R)%sep m' ->
          mcomp_sat (f tt) (withXAddrs (invalidateWrittenXAddrs 1 addr initialL.(getXAddrs))
                           (withMem m' (updateMetrics (addMetricStores 1) initialL))) post) ->
      mcomp_sat (Bind (storeByte Execute addr v_new) f) initialL post.
  Proof.
    intros.
    pose proof (store_bytes_of_sep (mem_ok := mem_ok)) as P.
    specialize P with (1 := H) (2 := H0).
    destruct P as (m' & P & Q).
    eapply go_storeByte; eassumption.
  Qed.

  Lemma go_storeByte_sep_NEW:
    forall (initialL : RiscvMachineL) (addr : word) (v_old v_new : w8)
           (post : RiscvMachineL -> Prop) (f : unit -> M unit) (R Rexec: mem -> Prop),
      subset (footpr Rexec) (of_list (initialL.(getXAddrs))) ->
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
           (post : RiscvMachineL -> Prop) (f : unit -> M unit) (R: mem -> Prop),
      (ptsto_bytes 2 addr v_old * R)%sep initialL.(getMem) ->
      (forall m': mem,
          (ptsto_bytes 2 addr v_new * R)%sep m' ->
          mcomp_sat (f tt) (withXAddrs (invalidateWrittenXAddrs 2 addr initialL.(getXAddrs))
                           (withMem m' (updateMetrics (addMetricStores 1) initialL))) post) ->
      mcomp_sat (Bind (storeHalf Execute addr v_new) f) initialL post.
  Proof.
    intros.
    pose proof (store_bytes_of_sep (mem_ok := mem_ok)) as P.
    specialize P with (1 := H) (2 := H0).
    destruct P as (m' & P & Q).
    eapply go_storeHalf; eassumption.
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
           (post : RiscvMachineL -> Prop) (f : unit -> M unit) (R: mem -> Prop),
      (ptsto_bytes 4 addr v_old * R)%sep initialL.(getMem) ->
      (let m' := Memory.unchecked_store_bytes 4 (getMem initialL) addr v_new in
          (ptsto_bytes 4 addr v_new * R)%sep m' ->
          mcomp_sat (f tt) (withXAddrs (invalidateWrittenXAddrs 4 addr initialL.(getXAddrs))
                           (withMem m' (updateMetrics (addMetricStores 1) initialL))) post) ->
      mcomp_sat (Bind (storeWord Execute addr v_new) f) initialL post.
  Proof.
    intros.
    pose proof (unchecked_store_bytes_of_sep (mem_ok := mem_ok)) as P.
    specialize P with (1 := H). specialize (P v_new).
    simpl in *.
    specialize (H0 P).
    eapply go_storeWord; [|eassumption].
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
           (post : RiscvMachineL -> Prop) (f : unit -> M unit) (R: mem -> Prop),
      (ptsto_bytes 8 addr v_old * R)%sep initialL.(getMem) ->
      (forall m': mem,
          (ptsto_bytes 8 addr v_new * R)%sep m' ->
          mcomp_sat (f tt) (withXAddrs (invalidateWrittenXAddrs 8 addr initialL.(getXAddrs))
                           (withMem m' (updateMetrics (addMetricStores 1) initialL))) post) ->
      mcomp_sat (Bind (storeDouble Execute addr v_new) f) initialL post.
  Proof.
    intros.
    pose proof (store_bytes_of_sep (mem_ok := mem_ok)) as P.
    specialize P with (1 := H) (2 := H0).
    destruct P as (m' & P & Q).
    eapply go_storeDouble; eassumption.
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
  | |- sep ?P ?Q ?m => simpl in *; simpl_MetricRiscvMachine_get_set; solve [seplog]
  | |- _ => reflexivity
  | A: map.get ?lH ?x = Some _, E: map.extends ?lL ?lH |- map.get ?lL ?x = Some _ =>
    eapply (map.extends_get A E)
  (* but we don't have a general "eassumption" branch, only "assumption": *)
  | |- _ => solve [auto using valid_FlatImp_var_implies_valid_register,
                              valid_FlatImp_vars_bcond_implies_valid_registers_bcond]
  | |- ?G => assert_fails (has_evar G);
             solve [eauto using valid_FlatImp_var_implies_valid_register,
                                valid_FlatImp_vars_bcond_implies_valid_registers_bcond,
                                Forall_impl]
  (* TODO eventually remove this case and dependency on FlatToRiscvDef *)
  | V: FlatToRiscvDef.valid_instructions _ _ |- Encode.verify ?inst ?iset =>
    assert_fails (is_evar inst);
    apply V;
    repeat match goal with
           | H: _ |- _ => clear H
           end;
    eauto 30 using in_cons, in_or_app, in_eq
  | |- Memory.load ?sz ?m ?addr = Some ?v =>
    unfold Memory.load, Memory.load_Z in *;
    simpl_MetricRiscvMachine_mem;
    erewrite load_bytes_of_sep; [ reflexivity | ecancel_assumption ]
  | |- Memory.store ?sz ?m ?addr ?val = Some ?m' => eassumption
  | |- _ => sidecondition_hook
  end.

(* eapply and rapply don't always work (they failed in compiler.MMIO), so we use refine below
   Trick to test if right number of underscores:
          let c := open_constr:(go_associativity _ _ _ _ _ _) in
          let t := type of c in idtac t. *)

Ltac simulate_step :=
  first (* lemmas packing multiple primitives need to go first: *)
        [ refine (go_fetch_inst _ _ _ _);          [sidecondition..|]
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
        | refine (go_step _ _ _);                  [sidecondition..|]
        (* monad law lemmas: *)
        | refine (go_left_identity _ _ _ _ _);     [sidecondition..|]
        | refine (go_right_identity _ _ _ _);      [sidecondition..|]
        | refine (go_associativity _ _ _ _ _ _);   [sidecondition..|] ].

Ltac simulate := repeat simulate_step.
