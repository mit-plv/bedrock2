Require Import lib.LibTacticsMin.
Require Import bbv.ZLib.
Require Import riscv.util.Monads.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import compiler.Op.
Require Import riscv.Program.
Require Import riscv.Decode.
Require Import riscv.PseudoInstructions.
Require Import riscv.RiscvMachine.
Require Import riscv.Execute.
Require Import riscv.Run.
Require Import riscv.Memory.
Require Import riscv.util.PowerFunc.
Require Export compiler.FlatToRiscvBitWidthSpecifics.
Require Export compiler.FlatToRiscvInvariants.
Require Export compiler.FlatToRiscvBitWidthSpecificProofs.
Require Import compiler.Decidable.
Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import riscv.InstructionCoercions.
Require Import riscv.AxiomaticRiscv.
Require Import Coq.micromega.Lia.
Require Import riscv.util.div_mod_to_quot_rem.
Require Import compiler.util.Misc.
Require Import riscv.Utility.
Require Import riscv.util.ZBitOps.
Require Import compiler.util.Common.
Require Import riscv.Utility.

(* TODO remove these three *)
Require Import riscv.MachineWidth_XLEN.
Require Import riscv.MachineWidth32.
Require Import riscv.MachineWidth64.

Local Open Scope ilist_scope.
Local Open Scope Z_scope.

Set Implicit Arguments.


(* State_is_RegisterFile gets its own section so that destructing Bw later does
   not lead to ill-typed terms *)
Section RegisterFile.

  Context {mword: Set}.
  Context {MW: MachineWidth mword}.
  Context {stateMap: MapFunctions Register mword}.
  Notation state := (map Register mword).

  Instance State_is_RegisterFile: RegisterFile state Register mword := {|
    getReg rf r := match get rf r with
                   | Some v => v
                   | None => ZToReg 0
                   end;
    setReg := put;
    initialRegs := empty_map;
  |}.

End RegisterFile.

Existing Instance State_is_RegisterFile.


Section FlatToRiscv.

  Context {mword: Set}.
  Context {MW: MachineWidth mword}.

  Ltac mword_cst w :=
    match w with
    | ZToReg ?x => let b := isZcst x in
                  match b with
                  | true => x
                  | _ => constr:(NotConstant)
                  end
    | _ => constr:(NotConstant)
  end.

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

  Hint Rewrite @Zlength_nil @Zlength_cons @Zlength_app: rew_Zlength.

  Ltac solve_word_eq :=
    match goal with
    | |- @eq mword _ _ => idtac
    | _ => fail 1 "wrong shape of goal"
    end;
    subst;
    clear;
    simpl;
    repeat (autorewrite with rew_Zlength; simpl);
    try ring.

  (* put here so that rem picks up the MachineWidth for wXLEN *)

  (*
  Lemma four_divides_Npow2_wXLEN:
      exists k : N, (wordToN (natToWord wXLEN 4) * k)%N = Npow2 wXLEN.
  Proof.
    unfold wXLEN, bitwidth in *.
    destruct Bw.
    - exists (Npow2 30). reflexivity.
    - exists (Npow2 62). reflexivity.
  Qed.
   *)

  (* check lower two bits approach: how to connect to remu? or replace remu in spec? *)


  Axiom euclid_unsigned: forall a b, a = add (mul (divu a b) b) (remu a b).
  Axiom remu_range: forall (a b: mword), 0 <= regToZ_unsigned (remu a b) < regToZ_unsigned b.

  Axiom unique: forall a b q r,
      a = add (mul b q) r ->
      0 <= regToZ_unsigned r < regToZ_unsigned b ->
      q = divu a b /\ r = remu a b.

  Definition divisibleBy4(a: mword): Prop := exists q, mul (ZToReg 4) q = a.

  Lemma remu40_divisibleBy4: forall (a: mword),
      remu a (ZToReg 4) = ZToReg 0 ->
      divisibleBy4 a.
  Proof.
    intros.
    unfold divisibleBy4.
    exists (divu a (ZToReg 4)).
    pose proof (euclid_unsigned a (ZToReg 4)) as P.
    rewrite P at 2.
    rewrite H.
    ring.
  Qed.

  Lemma divisibleBy4_remu40: forall (a: mword),
      divisibleBy4 a ->
      remu a (ZToReg 4) = ZToReg 0.
  Proof.
    intros.
    unfold divisibleBy4 in *.
    destruct H as [q H].
    destruct (@unique a (ZToReg 4) q (ZToReg 0)).
    - subst a. ring.
    - pose proof pow2_sz_4.
      rewrite regToZ_ZToReg_unsigned by omega.
      rewrite regToZ_ZToReg_unsigned by omega.
      omega.
    - congruence.
  Qed.

  Lemma remu_four_undo: forall a, remu (mul (ZToReg 4) a) (ZToReg 4) = ZToReg 0.
  Proof.
    intros.
    rewrite remu_def.
    f_equal.
    pose proof pow2_sz_4.
    rewrite mul_def_unsigned.
    rewrite regToZ_ZToReg_unsigned_mod.
    rewrite (regToZ_ZToReg_unsigned 4) by omega.
    pose proof XLEN_lbound.
    apply Z.rem_mod_eq_0; [omega|].
    replace XLEN with (2 + (XLEN - 2)) by omega.
    rewrite Z.pow_add_r by omega.
    change (2 ^ 2) with 4.
    pose proof (pow2_pos (XLEN - 2)).
    div_mod_to_quot_rem. nia.
  Qed.

  Lemma remu_four_four: remu (ZToReg 4) (ZToReg 4) = ZToReg 0.
  Proof.
    intros.
    apply divisibleBy4_remu40. unfold divisibleBy4.
    exists (ZToReg 1). ring.
  Qed.

  Lemma remu_four_zero_distrib_plus: forall a b,
      remu a (ZToReg 4) = ZToReg 0 ->
      remu b (ZToReg 4) = ZToReg 0 ->
      remu (add a b) (ZToReg 4) = ZToReg 0.
  Proof.
    intros.
    apply divisibleBy4_remu40.
    apply remu40_divisibleBy4 in H.  destruct H  as [q1 H1].
    apply remu40_divisibleBy4 in H0. destruct H0 as [q2 H2].
    unfold divisibleBy4 in *.
    subst.
    exists (add q1 q2).
    ring.
  Qed.

  (* TODO is there a principled way of writing such proofs? *)
  Lemma reduce_eq_to_sub_and_lt: forall (y z: mword) {T: Type} (thenVal elseVal: T),
    (if ltu (sub y  z) (fromImm 1) then thenVal else elseVal) =
    (if reg_eqb y z        then thenVal else elseVal).
  Proof. (*
    intros. destruct (weq y z).
    - subst z. unfold wminus. rewrite wminus_inv.
      destruct (wlt_dec (wzero wXLEN) $1); [reflexivity|].
      change (wzero wXLEN) with (natToWord wXLEN 0) in n. unfold wlt in n.
      exfalso. apply n.
      do 2 rewrite wordToN_nat. rewrite roundTrip_0.
      clear.
      destruct wXLEN as [|w1] eqn: E.
      + unfold wXLEN in *. destruct bitwidth; discriminate.
      + rewrite roundTrip_1. simpl. constructor.
    - destruct (@wlt_dec wXLEN (y ^- z) $ (1)) as [E|NE]; [|reflexivity].
      exfalso. apply n. apply sub_0_eq.
      unfold wlt in E.
      do 2 rewrite wordToN_nat in E.
      clear -E.
      destruct wXLEN as [|w1] eqn: F.
      + unfold wXLEN in *. destruct bitwidth; discriminate.
      + rewrite roundTrip_1 in E.
        simpl in E. apply N.lt_1_r in E. change 0%N with (N.of_nat 0) in E.
        apply Nnat.Nat2N.inj in E. rewrite <- (roundTrip_0 (S w1)) in E.
        apply wordToNat_inj in E.
        exact E.
  Qed.
*)
  Admitted.

  (*
  Lemma wlshift_bitSlice_plus: forall (sz1 sz2: Z) v,
      (0 <= sz1)%Z ->
      (0 <= sz2)%Z ->
      wlshift (ZToWord wXLEN (bitSlice v sz1 (sz1 + sz2))) (Z.to_nat sz1)
      ^+ ZToWord wXLEN (bitSlice v 0 sz1)
      = ZToWord wXLEN (bitSlice v 0 (sz1 + sz2)).
  Proof.
    intros. rewrite wlshift_alt.
    rewrite wlshift_mul_Zpow2 by assumption.
    rewrite <- ZToWord_mult.
    rewrite <- ZToWord_plus.
    f_equal.
    apply bitSlice_split; assumption.
  Qed.
  *)

  (*
  Context {Name: NameWithEq}.

  (* If we made it a definition instead, destructing an if on "@dec (@eq (@var Name) x x0)"
     (from this file), where a "@dec (@eq (@Reg Name) x x0)" (from another file, Riscv.v)
     is in the context, will not recognize that these two are the same (they both reduce to
     "@dec (@eq var x x0)", which is annoying. *)
  Notation var := var.
  Existing Instance eq_name_dec.
   *)

  Context {stateMap: MapFunctions Register mword}.
  Notation state := (map Register mword).

  Notation stmt := (stmt Z Empty_set).

  Context {funcMap: MapFunctions Empty_set (list Z * list Z * stmt)}. (* TODO meh *)

  Context {mem: Set}.
  Context {IsMem: Memory.Memory mem mword}.
  Context {BWS: FlatToRiscvBitWidthSpecifics mword mem}.
  Context {BWSP: FlatToRiscvBitWidthSpecificProofs mword mem}.

  Local Notation RiscvMachine := (@RiscvMachine mword mem state).
  Context {RVM: RiscvProgram (OState RiscvMachine) mword}.

  (* assumes generic translate and raiseException functions *)
  Context {RVS: @RiscvState (OState RiscvMachine) mword _ _ RVM}.

  Context {RVAX: @AxiomaticRiscv mword _ state State_is_RegisterFile mem _ RVM}.

  Ltac state_calc0 := map_solver Z mword.

  Hypothesis translate_id_if_aligned_4: forall a mode,
      (regToZ_unsigned a) mod 4 = 0 ->
      translate mode (ZToReg 4) a = Return a.

  Hypothesis translate_id_if_aligned_8: forall a mode,
      (regToZ_unsigned a) mod 8 = 0 ->
      translate mode (ZToReg 8) a = Return a.

  (* This phase assumes that register allocation has already been done on the FlatImp
     level, and expects the following to hold: *)

  Fixpoint valid_registers_bcond (cond: bcond Register) : Prop :=
    match cond with
    | CondBinary _ x y => valid_register x /\ valid_register y
    | CondNez x => valid_register x
    end.

  Fixpoint valid_registers(s: stmt): Prop :=
    match s with
    | SLoad x a => valid_register x /\ valid_register a
    | SStore a x => valid_register a /\ valid_register x
    | SLit x _ => valid_register x
    | SOp x _ y z => valid_register x /\ valid_register y /\ valid_register z
    | SSet x y => valid_register x /\ valid_register y
    | SIf c s1 s2 => valid_registers_bcond c /\ valid_registers s1 /\ valid_registers s2
    | SLoop s1 c s2 => valid_registers_bcond c /\ valid_registers s1 /\ valid_registers s2
    | SSeq s1 s2 => valid_registers s1 /\ valid_registers s2
    | SSkip => True
    | SCall binds _ args => Forall valid_register binds /\ Forall valid_register args (* untested *)
    end.

  (*
  Variable var2Register: var -> Register. (* TODO register allocation *)
  Hypothesis no_var_mapped_to_Register0: forall (x: var), x <> Register0.
  Hypothesis var2Register_inj: forall x1 x2, x1 = x2 -> x1 = x2.
   *)

  (* Set Printing Projections.
     Uncaught anomaly when stepping through proofs :(
     https://github.com/coq/coq/issues/6257 *)

  Variable LwXLEN: Register -> Register -> Z -> Instruction.

  Variable SwXLEN: Register -> Register -> Z -> Instruction.

  Definition compile_op(rd: Register)(op: bopname)(rs1 rs2: Register): list Instruction :=
    match op with
    | bopname.add => [[Add rd rs1 rs2]]
    | bopname.sub => [[Sub rd rs1 rs2]]
    | bopname.mul => [[Mul rd rs1 rs2]]
    | bopname.and => [[And rd rs1 rs2]]
    | bopname.or  => [[Or  rd rs1 rs2]]
    | bopname.xor => [[Xor rd rs1 rs2]]
    | bopname.sru => [[Srl rd rs1 rs2]]
    | bopname.slu => [[Sll rd rs1 rs2]]
    | bopname.srs => [[Sra rd rs1 rs2]]
    | bopname.lts => [[Slt rd rs1 rs2]]
    | bopname.ltu => [[Sltu rd rs1 rs2]]
    | bopname.eq  => [[Sub rd rs1 rs2; Seqz rd rd]]
    end.

  Fixpoint compile_lit_rec(byteIndex: nat)(rd rs: Register)(v: Z): list Instruction :=
    let byte := bitSlice v ((Z.of_nat byteIndex) * 8) ((Z.of_nat byteIndex + 1) * 8) in
    [[ Addi rd rs byte ]] ++
    match byteIndex with
    | S b => [[ Slli rd rd 8]] ++ (compile_lit_rec b rd rd v)
    | O => [[]]
    end.

  Fixpoint compile_lit_rec'(byteIndex: nat)(rd rs: Register)(v: Z): list Instruction :=
    let d := (2 ^ ((Z.of_nat byteIndex) * 8))%Z in
    let hi := (v / d)%Z in
    let v' := (v - hi * d)%Z in
    [[ Addi rd rs hi ]] ++
    match byteIndex with
    | S b => [[ Slli rd rd 8]] ++ (compile_lit_rec b rd rd v')
    | O => [[]]
    end.

  (*
  Variable rd: Register.
  Eval cbv -[Register0] in (compile_lit_rec 7 rd Register0 10000).
  *)

  Definition compile_lit(rd: Register)(v: Z): list Instruction :=
    compile_lit_rec 7 rd Register0 v.

  Definition compile_lit_32(rd: Register)(v: word 32): list Instruction :=
    let h0 := wsplit_lo 16 16 v in
    let h1 := wsplit_hi 16 16 v in
    [[Addi rd Register0 (uwordToZ h1); Slli rd rd 16; Addi rd rd (uwordToZ h0)]].

  Definition compile_lit_64(rd: Register)(v: word 64): list Instruction :=
    let w0 := wsplit_lo 32 32 v in
    let w1 := wsplit_hi 32 32 v in
    let h0 := wsplit_lo 16 16 w0 in
    let h1 := wsplit_hi 16 16 w0 in
    let h2 := wsplit_lo 16 16 w1 in
    let h3 := wsplit_hi 16 16 w1 in
    [[Addi rd Register0 (uwordToZ h3);
      Slli rd rd 16; Addi rd rd (uwordToZ h2);
      Slli rd rd 16; Addi rd rd (uwordToZ h1);
      Slli rd rd 16; Addi rd rd (uwordToZ h0)]].

  (* The problem with the primed version is that we have to destruct the bitwidth to expose
     the indivdual commands (on which the proof machinery of compile_stmt_correct_aux works),
     but the proof machinery stops working when the bitwidth is destructed because typeclass
     search stops working as it should, and destructing the bitwidth only works after unfolding
     all definitions involving mword.
  Definition compile_lit'(rd: Register)(v: mword): list Instruction.
    clear -Bw rd v. unfold wXLEN, bitwidth in *. destruct Bw.
    - exact (compile_lit_32 rd v).
    - exact (compile_lit_64 rd v).
  Defined.

  (* Very stupid workaround: *)
  Definition make_64_bit(v: mword): word 64.
    clear -Bw v. unfold wXLEN, bitwidth in *. destruct Bw.
    - exact (zext v 32).
    - exact v.
  Defined.

  Definition compile_lit''(rd: Register)(v: mword): list Instruction :=
    compile_lit_64 rd (make_64_bit v).

  (* store the n lowest halves (1 half = 16bits) of v into rd *)
  Fixpoint compile_halves(n: nat)(rd: Register)(v: Z): list Instruction :=
    if dec (- 2^19 <= v < 2^19)%Z then
      [[Addi rd Register0 v]]
    else
      match n with
      | O => [[]] (* will not happen because we choose n big enough *)
      | S n' =>
        let upper := (v / 2^16)%Z in
        let lower := (v - upper * 2^16)%Z in
        (compile_halves n' rd upper) ++ [[Slli rd rd 16; Addi rd rd lower]]
      end.

  Fixpoint interp_compiled_halves(l: list Instruction)(acc: Z): Z :=
    match l with
    | (Addi _ _ v) :: l' => interp_compiled_halves l' (acc + v)
    | (Slli _ _ _) :: l' => interp_compiled_halves l' (acc * 16)
    | _ => acc
    end.

  Lemma compile_halves_correct: forall n rd v acc,
      v <=2^(16 * n)
      interp_compiled_halves (compile_halves n rd v) acc = (acc + v)%Z.
  Proof.
    induction n; intros.
    - simpl.
  Qed.

  Definition compile_lit_old(rd: Register)(v: Z): list Instruction :=
    compile_halves (wXLEN / 16) rd v.

  Definition add_lit_20(rd rs: Register)(v: word 20): list Instruction :=
    [[Addi rd rs (wordToZ v)]].

  Definition add_lit_32(rd rs: Register)(v: word 32): list Instruction :=
    let lobits := split1 20 12 v in
    let hibits := split2 20 12 v in [[]].

  Definition embed_words(l: list (word 32)): list Instruction :=
    [[J (Z.of_nat (length l))]] ++ (map (fun w => InvalidInstruction (wordToZ w)) l).

  Definition wXLEN_to_word_list(v: mword): list (word 32).
    clear -Bw v. unfold wXLEN, bitwidth in *. destruct Bw.
    - exact [v].
    - exact [split1 32 32 v; split2 32 32 v].
  Defined.

  Definition embed_word(v: mword): list Instruction :=
    List.map (fun w => InvalidInstruction (wordToZ w)) (wXLEN_to_word_list v).

  Definition compile_lit_old1(rd: Register)(v: mword): list Instruction :=
    let l := embed_word v in
    [[Auipc rd 0; LwXLEN rd rd 8; J (Z.of_nat (length l))]] ++ l.

  Definition add_lit_20'(rd rs: Register)(v: Z): list Instruction :=
    [[Addi rd rs v]].

  Definition add_lit_32'(rd rs: Register)(v: Z): list Instruction :=
    (if dec (- 2^19 <= v < 2^19)%Z then [[]] else (
         let '(hibits, lobits) := (1%Z, 1%Z) in
         let maybe1 := 1%Z in
         ([[ Lui rd hibits ]] ++ (add_lit_20' rd rs (lobits + maybe1))))).

  Definition compile_lit_32(rd: Register)(v: Z): list Instruction :=
      let lobits := (v mod (2 ^ 20))%Z in
      if dec (lobits = v)
      then [[Addi rd Register0 lobits]]
      else
        let hibits := (v - lobits)%Z in
        if Z.testbit v 20
        (* Xori will sign-extend lobits with 1s, therefore Z.lnot *)
        then [[Lui rd (Z.lnot hibits); Xori rd rd lobits]]
        (* Xori will sign-extend lobits with 0s *)
        else [[Lui rd hibits; Xori rd rd lobits]].

  Definition compile_lit_old'(rd: Register)(v: mword): list Instruction.
    clear -Bw rd v. unfold wXLEN, bitwidth in *. destruct Bw.
    - exact (compile_lit_32 rd v).
    - exact (compile_lit_64 rd v).
  Defined.
  *)

  (* Inverts the branch condition. *)
  Definition compile_bcond_by_inverting
             (cond: bcond Register) (amt: Z) : Instruction:=
    match cond with
    | CondBinary op x y =>
        match op with
        | BEq  => Bne x y amt
        | BNe  => Beq x y amt
        | BLt  => Bge x y amt
        | BGe  => Blt x y amt
        | BLtu => Bgeu x y amt
        | BGeu => Bltu x y amt
        end
    | CondNez x =>
        Beq x Register0 amt
    end.
 
  Fixpoint compile_stmt(s: stmt): list (Instruction) :=
    match s with
    | SLoad x y => [[LwXLEN x y 0]]
    | SStore x y => [[SwXLEN x y 0]]
    | SLit x v => compile_lit x v
    | SOp x op y z => compile_op x op y z
    | SSet x y => [[Add x Register0 y]]
    | SIf cond bThen bElse =>
        let bThen' := compile_stmt bThen in
        let bElse' := compile_stmt bElse in
        (* only works if branch lengths are < 2^12 *)
        [[compile_bcond_by_inverting cond ((Zlength bThen' + 2) * 4)]] ++
        bThen' ++
        [[Jal Register0 ((Zlength bElse' + 1) * 4)]] ++
        bElse'
    | SLoop body1 cond body2 =>
        let body1' := compile_stmt body1 in
        let body2' := compile_stmt body2 in
        (* only works if branch lengths are < 2^12 *)
        body1' ++
        [[compile_bcond_by_inverting cond ((Zlength body2' + 2) * 4)]] ++
        body2' ++
        [[Jal Register0 (- (Zlength body1' + 1 + Zlength body2') * 4)]]
    | SSeq s1 s2 => compile_stmt s1 ++ compile_stmt s2
    | SSkip => nil
    | SCall _ _ _ => nil (* unsupported *)
    end.

  (*
  Lemma embed_lit_size: forall v,
    length (embed_lit v) <= 3.
  Proof.
    intros. clear.
    unfold wXLEN, bitwidth, embed_lit, embed_lit_32, embed_lit_64 in *.
    destruct Bw; simpl; omega.
  Qed.
  *)
  Lemma compile_stmt_size: forall s,
    (length (compile_stmt s) <= 2 * (stmt_size _ _ s))%nat.
  Proof.
    induction s; simpl; try destruct op; simpl;
    repeat (rewrite app_length; simpl); try omega.
  Qed.

  (* load and decode Inst *)
  Definition ldInst(m: mem)(a: mword): Instruction :=
    decode (@RV_wXLEN_IM BitWidth) (uwordToZ (Memory.loadWord m a)).

  Definition decode_prog(prog: list (word 32)): list Instruction :=
    List.map (fun w => decode (@RV_wXLEN_IM BitWidth) (uwordToZ w)) prog.

  Definition mem_inaccessible(m: Memory.mem)(start len: Z): Prop :=
    forall a w, Memory.read_mem a m = Some w -> not_in_range a XLEN_in_bytes start len.

  Definition containsProgram(m: mem)(program: list Instruction)(offset: mword) :=
    regToZ_unsigned offset + 4 * Zlength program <= Memory.memSize m /\
    forall i inst, Znth_error program i = Some inst ->
      ldInst m (add offset (ZToReg (4 * i))) = inst.

  Definition containsProgram'(m: mem)(program: list Instruction)(offset: mword) :=
    regToZ_unsigned offset + 4 * Zlength program <= Memory.memSize m /\
    decode_prog (Memory.load_word_list m offset (Zlength program)) = program.

  Lemma containsProgram_alt: forall m program offset,
      containsProgram m program offset <-> containsProgram' m program offset.
  Proof.
    intros. unfold containsProgram, containsProgram', decode_prog.
    clear LwXLEN SwXLEN.
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

  Lemma nth_error_nil_Some: forall {A} i (a: A), nth_error nil i = Some a -> False.
  Proof.
    intros. destruct i; simpl in *; discriminate.
  Qed.

  Ltac ensure_is_nat_rel R :=
    match R with
    | ?P /\ ?Q => ensure_is_nat_rel P; ensure_is_nat_rel Q
    | ?P \/ ?Q => ensure_is_nat_rel P; ensure_is_nat_rel Q
    | @eq nat _ _  => idtac (* can't use %nat here because = is polymorphic *)
    | (_ <  _)%nat => idtac
    | (_ <= _)%nat => idtac
    | (_ >  _)%nat => idtac
    | (_ >= _)%nat => idtac
    end.

  Definition pow2_wXLEN_4 := pow2_sz_4.

  Ltac nat_rel_with_words_pre :=
    match goal with
    | |- ?P => ensure_is_nat_rel P
    end(*;
    repeat match goal with
           | IsMem: Memory.Memory ?M _, m: ?M |- _ =>
             unique pose proof (@Memory.memSize_bound M _ IsMem m)
           end;
    pose proof pow2_wXLEN_4;
    rewrite? wordToNat_wplus in *;
    rewrite? wordToNat_natToWord_eqn in * *).

  Ltac nat_rel_with_words :=
    nat_rel_with_words_pre(*;
    nat_div_mod_to_quot_rem;
    nia *).

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
    rewrite ZToReg_morphism.(morph_mul) in H2.
    rewrite <- regToZ_unsigned_four in H2.
    rewrite ZToReg_regToZ_unsigned in H2.
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
    simpl.
    rewrite <- regToZ_unsigned_one.
    rewrite ZToReg_regToZ_unsigned.
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
    repeat match goal with
           | H: containsProgram _ _ ?x |- _ => progress (ring_simplify x in H)
           | |-  containsProgram _ _ ?x     => progress (ring_simplify x)
           end.
    assumption.
  Qed.

  Arguments containsProgram: simpl never.

  Ltac destruct_containsProgram :=
    repeat match goal with
           | Cp: containsProgram _ ?l _ |- _ =>
             let Cp' := fresh Cp in
             let W := fresh "W" in
             match l with
             | [[]] => clear Cp
             | [[?inst]] => fail 1
             | ?h :: ?t => apply containsProgram_cons_inv in Cp;
                          destruct Cp as [ W [Cp' Cp] ]
             | ?insts0 ++ ?insts1 => apply containsProgram_app_inv in Cp;
                                    destruct Cp as [ W [Cp' Cp] ]
             end
           end.

  Ltac solve_containsProgram :=
    match goal with
    | |- containsProgram _ _ _ => subst
    end;
    repeat match goal with
    | |- context [?a :: ?b :: ?t] => change (a :: b :: t) with ((a :: nil) ++ (b :: t)) in *
    end;
    rewrite? app_nil_r in *;
    rewrite? app_nil_l in *;
    repeat match goal with
    | W: containsProgram_app_will_work ?i1 ?i2 ?p |- containsProgram ?m (?i1 ++ ?i2) ?p =>
      apply (containsProgram_app W)
    | Cp: containsProgram ?m ?i ?p |- containsProgram ?m ?i ?p => exact Cp
    | Cp: containsProgram ?m ?i ?p |- containsProgram ?m ?i ?p' =>
          replace p' with p; [exact Cp|try solve_word_eq]
    end;
    try assumption.

  (*
  Lemma containsState_put: forall initialH initialRegs x v1 v2,
    containsState initialRegs initialH ->
    v1 = v2 ->
    containsState
      (fun reg2 =>
               if dec (x = reg2)
               then v1
               else initialRegs reg2)
     (put initialH x v2).
  Proof.
    unfold containsState. intros.
    rewrite get_put in H1.
    destruct_one_match_hyp.
    - clear E. subst. inverts H1.
      destruct_one_match; [reflexivity|].
      exfalso.
      apply n.
      reflexivity.
    - destruct_one_match.
      * clear E0. apply var2Register_inj in e. contradiction.
      * apply H. assumption.
  Qed.
  *)

  Definition runsTo_onerun(initial: RiscvMachine)(P: RiscvMachine -> Prop): Prop :=
    exists fuel,
      match run (B := BitWidth) fuel initial with
      | (Some _, final) => P final
      | (None  , final) => False
      end.

  Inductive runsTo: RiscvMachine -> (RiscvMachine -> Prop) -> Prop :=
    | runsToDone: forall (initial: RiscvMachine) (P: RiscvMachine -> Prop),
        P initial ->
        runsTo initial P
    | runsToStep: forall (initial middle: RiscvMachine) (P: RiscvMachine -> Prop),
        run1 (B := BitWidth) initial = (Some tt, middle) ->
        runsTo middle P ->
        runsTo initial P.

  Lemma runsTo_to_onerun: forall initial (P: RiscvMachine -> Prop),
      runsTo initial P ->
      runsTo_onerun initial P.
  Proof.
    unfold runsTo_onerun. induction 1.
    - exists O. simpl. assumption.
    - destruct IHrunsTo as [fuel IH].
      exists (S fuel). unfold run, power_func.
      match goal with
      | |- context [?t] =>
           match t with
           | Bind _  _ =>
             match t with
             | ?B _ _ => let B' := eval cbv in B in change B with B'
             end
           end
      end.
      cbv beta.
      rewrite H.
      exact IH.
  Qed.

  Lemma runsTo_from_onerun: forall initial (P: RiscvMachine -> Prop),
      runsTo_onerun initial P ->
      runsTo initial P.
  Proof.
    unfold runsTo_onerun. intros. destruct H as [fuel H].
    revert H. revert P. revert initial.
    induction fuel; intros.
    - apply runsToDone. exact H.
    - unfold run, power_func, Bind, OState_Monad in H.
      match type of H with
      | context [?t] =>
        match t with
        | run1 initial =>  destruct t as [ [u1 | ] s1 ] eqn: E1; [|contradiction]
        end
      end.
      destruct u1.
      eapply runsToStep; [exact E1|].
      apply IHfuel.
      exact H.
  Qed.

  Lemma runsTo_alt_equiv: forall initial (P: RiscvMachine -> Prop),
      runsTo_onerun initial P <-> runsTo initial P.
  Proof.
    intros. split.
    - apply runsTo_from_onerun.
    - apply runsTo_to_onerun.
  Qed.

  Lemma runsToSatisfying_trans: forall P Q initial,
    runsTo initial P ->
    (forall middle, P middle -> runsTo middle Q) ->
    runsTo initial Q.
  Proof.
    introv R1. induction R1; introv R2; [solve [auto]|].
    eapply runsToStep; [eassumption|]. apply IHR1. apply R2.
  Qed.

  Lemma runsToSatisfying_imp: forall (P Q : RiscvMachine -> Prop) initial,
    runsTo initial P ->
    (forall final, P final -> Q final) ->
    runsTo initial Q.
  Proof using .
    introv R1 R2. eapply runsToSatisfying_trans; [eassumption|].
    intros final Pf. apply runsToDone. auto.
  Qed.

  Definition runsToSatisfying: RiscvMachine -> (RiscvMachine -> Prop) -> Prop := runsTo.

  Ltac simpl_run1 :=
    cbv [run1 execState Monads.put Monads.gets Monads.get Return Bind State_Monad OState_Monad
         execute ExecuteI.execute ExecuteM.execute ExecuteI64.execute ExecuteM64.execute
         core machineMem registers pc nextPC exceptionHandlerAddr
         getPC setPC getRegister setRegister gets].

  Tactic Notation "log_solved" tactic(t) :=
    match goal with
    | |- ?G => let H := fresh in assert G as H by t; idtac "solved" G; exact H
    | |- ?G => idtac "did not solve" G
    end.

  (* TODO is 2^9 really the best we can get? *)
  Definition stmt_not_too_big(s: stmt): Prop := (Z.of_nat (stmt_size _ _ s) < 2 ^ 9)%Z.

  Local Ltac solve_stmt_not_too_big :=
    lazymatch goal with
    | H: stmt_not_too_big _ |- stmt_not_too_big _ =>
        unfold stmt_not_too_big in *;
        change (2 ^ 9)%Z with 512%Z in *;
        simpl stmt_size in H;
        lia
    end.

  (* Needed because simpl will unfold (4 * ...) which is unreadable *)
  Local Ltac simpl_pow2 := idtac. (*
    repeat match goal with
    | |- context [1 + ?a] => change (1 + a) with (S a)
    | |- context [pow2 (S ?a)] => change (pow2 (S a)) with (2 * pow2 a)
    | |- context [pow2 0] => change (pow2 0) with 1
    end.
*)

  Lemma simpl_with_registers: forall (rs1 rs2: state) p npc eh (m: mem),
    with_registers (mword := mword) rs2 (mkRiscvMachine (mkRiscvMachineCore rs1 p npc eh) m) =
                                        (mkRiscvMachine (mkRiscvMachineCore rs2 p npc eh) m).
  Proof. intros. reflexivity. Qed.

  Lemma simpl_with_pc: forall (rs: state) pc1 pc2 npc eh (m: mem),
    with_pc (mword := mword) pc2 (mkRiscvMachine (mkRiscvMachineCore rs pc1 npc eh) m) =
                                 (mkRiscvMachine (mkRiscvMachineCore rs pc2 npc eh) m).
  Proof. intros. reflexivity. Qed.

  Lemma simpl_with_nextPC: forall (rs: state) p npc1 npc2 eh (m: mem),
    with_nextPC (mword := mword) npc2 (mkRiscvMachine (mkRiscvMachineCore rs p npc1 eh) m) =
                                      (mkRiscvMachine (mkRiscvMachineCore rs p npc2 eh) m).
  Proof. intros. reflexivity. Qed.

  Lemma simpl_with_machineMem: forall (c: @RiscvMachineCore _ state) (m1 m2: mem),
    with_machineMem (mword := mword) m2 (mkRiscvMachine c m1) =
                                        (mkRiscvMachine c m2).
  Proof. intros. reflexivity. Qed.

  Lemma simpl_registers: forall (rs: state) p npc eh,
    registers (mword := mword) (mkRiscvMachineCore rs p npc eh) = rs.
  Proof. intros. reflexivity. Qed.

  Lemma simpl_pc: forall (rs: state) p npc eh,
    pc (mword := mword) (mkRiscvMachineCore rs p npc eh) = p.
  Proof. intros. reflexivity. Qed.

  Lemma simpl_nextPC: forall (rs: state) p npc eh,
    nextPC (mword := mword) (mkRiscvMachineCore rs p npc eh) = npc.
  Proof. intros. reflexivity. Qed.

  Lemma simpl_core: forall (c: @RiscvMachineCore _ state) (m: mem),
    core (mword := mword) (mkRiscvMachine c m) = c.
  Proof. intros. reflexivity. Qed.

  Lemma simpl_machineMem: forall (c: @RiscvMachineCore mword state) (m: mem),
    machineMem (mkRiscvMachine c m) = m.
  Proof. intros. reflexivity. Qed.

  Hint Rewrite
      simpl_with_registers
      simpl_with_pc
      simpl_with_nextPC
      simpl_with_machineMem
      simpl_registers
      simpl_pc
      simpl_nextPC
      simpl_core
      simpl_machineMem
  : rew_RiscvMachine_get_set.

  Ltac simpl_RiscvMachine_get_set := autorewrite with rew_RiscvMachine_get_set in *.

  Ltac destruct_RiscvMachine m :=
    let t := type of m in
    unify t RiscvMachine;
    let r := fresh m "_regs" in
    let p := fresh m "_pc" in
    let n := fresh m "_npc" in
    let e := fresh m "_eh" in
    let me := fresh m "_mem" in
    destruct m as [ [r p n e] me ];
    simpl_RiscvMachine_get_set.

  Arguments Z.modulo : simpl never.

  Lemma run1_simpl: forall {inst initialL pc0},
      containsProgram initialL.(machineMem) [[inst]] pc0 ->
      pc0 = initialL.(core).(pc) ->
      run1 (B := BitWidth) initialL = (execute inst;; step) initialL.
  Proof.
    intros. subst *.
    unfold run1.
    destruct_RiscvMachine initialL.
    rewrite Bind_getPC.
    simpl_RiscvMachine_get_set.
    rewrite Bind_loadWord.
    unfold containsProgram in H. apply proj2 in H.
    specialize (H 0 _ eq_refl). subst inst.
    unfold ldInst.
    simpl_RiscvMachine_get_set.
    repeat match goal with
           | |- context[?x] => progress (ring_simplify x)
           end.
    reflexivity.
  Qed.

  Inductive AllInsts: list Instruction -> Prop :=
    mkAllInsts: forall l, AllInsts l.

  Ltac head_of_app e :=
    match e with
    | ?f ?a => head_of_app f
    | _ => e
    end.

  Notation K := Z.
  Notation V := mword.

  (* only strictly needed if we want to export the goal into a map_solver-only environment,
     but might result in a speed up if used anyways *)
  Ltac prepare_for_map_solver :=
    clear translate_id_if_aligned_4 translate_id_if_aligned_8 BWSP RVAX;
    repeat match goal with
             | IH: forall (s : stmt), _ |- _ => clear IH
             | H: context [FlatImp.modVars ?var ?func ?s] |- _ =>
               let n := fresh "mv" s in
               forget (FlatImp.modVars var func s) as n
             | H: Memory.read_mem _ _ = _ |- _ => clear H
             | H: ?P |- _ =>
               let h := head_of_app P in
               match h with
               | @stmt_not_too_big => clear H
               | @valid_register => clear H
               | @valid_registers => clear H
               | @divisibleBy4 => clear H
               | @containsMem => clear H
               | @containsProgram => clear H
               | @mem_inaccessible => clear H
               | @containsProgram_app_will_work => clear H
               | @AllInsts => clear H
               end
             | H: @eq ?T _ _ |- _ =>
               match T with
            (* | option Semantics.word => don't clear because we have maps of Semantics.word *)
               | option (map Z mword * Memory.mem) => clear H
               | option Memory.mem => clear H
               | list _ => clear H
               | nat => clear H
               end
           end;
    repeat match goal with
           | H: ?P |- _ =>
             progress
               tryif (let T := type of P in unify T Prop)
               then revert H
               else (match P with
                     | _ => clear H
                     end)
           end;
    repeat match goal with
           | x: ?T |- _ =>
             lazymatch T with
             | MachineWidth _  => fail
             | MapFunctions _ _  => fail
             | SetFunctions _ => fail
             | DecidableEq _ => fail
             | _ => revert x
             end
           end.

  Ltac state_calc_with_logging :=
    prepare_for_map_solver;
    idtac "map_solver goal:";
    match goal with
    | |- ?G => idtac G
    end;
    time state_calc0.

  Ltac state_calc_with_timing :=
    prepare_for_map_solver;
    time state_calc0.

  Ltac state_calc_without_logging :=
    prepare_for_map_solver;
    state_calc0.

  Ltac state_calc := state_calc_without_logging.


  Hint Rewrite
      (@associativity  _ (OState_Monad RiscvMachine))
      (@left_identity  _ (OState_Monad RiscvMachine))
      (@right_identity _ (OState_Monad RiscvMachine))
      (@Bind_getRegister _ _ _ _ _ _ _)
      (@Bind_getRegister0 _ _ _ _ _ _ _)
      (@Bind_setRegister _ _ _ _ _ _ _)
      (@Bind_setRegister0 _ _ _ _ _ _ _)
      (@Bind_getPC _ _ _ _ _ _ _)
      (@Bind_setPC _ _ _ _ _ _ _)
  using assumption : rew_get_set_Register.

  Ltac do_get_set_Register := autorewrite with rew_get_set_Register.

  Arguments Z.mul: simpl never.
  Arguments Z.add: simpl never.
  Arguments run1: simpl never.

  (* requires destructed RiscvMachine and containsProgram *)
  Ltac fetch_inst :=
      match goal with
      | Cp: containsProgram _ [[?inst]] ?pc0 |- ?E = (Some tt, _) =>
        match E with
        | run1 ?initialL =>
          let Eqpc := fresh in
          assert (pc0 = initialL.(core).(pc)) as Eqpc by solve_word_eq;
            replace E with ((execute inst;; step) initialL) by
              (symmetry; eapply run1_simpl; [ exact Cp | exact Eqpc ]);
            clear Eqpc
        end
      end.

  Ltac rewrite_reg_value :=
    match goal with
    | |- context [getReg _ _] => idtac
    | |- context [get    _ _] => idtac
    | _ => fail 1 "wrong shape of goal"
    end;
    let G1 := fresh "G1" in
    match goal with
    | G2: get ?st2 ?x = ?v, E: extends ?st1 ?st2 |- context [@getReg ?RF ?R ?V ?TC ?st1 ?x] =>
      let gg := constr:(@getReg RF R V TC st1 x) in
      let gg' := eval unfold getReg, State_is_RegisterFile in gg in
      progress change gg with gg';
      match gg' with
      | match ?gg'' with | _ => _ end => assert (G1: gg'' = v) by state_calc
      end
    | G2: get ?st2 ?x = ?v, E: extends ?st1 ?st2 |- context [?gg'] =>
      match gg' with
      | match ?gg'' with | _ => _ end => assert (G1: gg'' = v) by state_calc
      end
    end;
    rewrite G1;
    clear G1.

  Ltac rewrite_getReg :=
    match goal with
    | |- context [@getReg ?RF ?R ?V ?TC ?st1 ?x] =>
      let gg := constr:(@getReg RF R V TC st1 x) in
      let gg' := eval unfold getReg, State_is_RegisterFile in gg in
          progress change gg with gg'
    end.

  Ltac rewrite_setReg :=
    match goal with
    | |- context [@setReg ?RF ?R ?V ?TC ?st1 ?x ?v] =>
      let gg := constr:(@setReg RF R V TC st1 x v) in
      let gg' := eval unfold setReg, State_is_RegisterFile in gg in
          progress change gg with gg'
    end.

  Ltac solve_valid_registers :=
    match goal with
    | |- valid_registers _ => solve [simpl; auto]
    end.

  Lemma add_to_instsBefore: forall (before insts1 insts2 after: list Instruction),
      before ++ (insts1 ++ insts2) ++ after = (before ++ insts1) ++ insts2 ++ after.
  Proof. intros. rewrite <-? app_assoc. reflexivity. Qed.

  Lemma add_to_instsAfter: forall (before insts1 insts2 after: list Instruction),
      before ++ (insts1 ++ insts2) ++ after = before ++ insts1 ++ (insts2 ++ after).
  Proof. intros. rewrite <-? app_assoc. reflexivity. Qed.

  (* Solves an equality of the form
        before ++ insts ++ after = evarForBefore ++ subseqOfInsts ++ evarForAfter
     instantiating evarForBefore and evarForAfter appropriately.
     Works by first shoveling instructions from "insts" into "before" until "subseqOfInsts"
     is found, and then shoveling the remaining instructions from "insts" into "after". *)
  Ltac solve_imem :=
    repeat match goal with
           | H: _ |- _ => clear H
           end;
    let targetInsts := fresh "targetInsts" in
    lazymatch goal with
    | |- ?lhs = _ ++ ?insts ++ _ =>
      match lhs with
      | context [insts] => remember insts as targetInsts
      end
    end;
    repeat match goal with
           | |- context [?h :: ?t] =>
             tryif (unify t [[]])
             then fail
             else (change (h :: t) with ([h] ++ t))
           end;
    repeat match goal with
           | |- ?before ++ (targetInsts ++ ?insts2) ++ ?after = _ => fail 1 (* success/quit loop *)
           | |- ?before ++ (?insts1 ++ ?insts2) ++ ?after = _ =>
             rewrite (add_to_instsBefore before insts1 insts2 after)
           end;
    repeat match goal with
           | |- ?before ++ (?insts1 ++ ?insts2) ++ ?after = _ =>
             rewrite (add_to_instsAfter before insts1 insts2 after)
           end;
    subst targetInsts;
    reflexivity.

  Lemma write_mem_preserves_mem_accessibility:
    forall {initialMem finalMem: Memory.mem} {a0 w: mword},
      Memory.write_mem a0 w initialMem = Some finalMem ->
      forall a, Memory.read_mem a initialMem = None <-> Memory.read_mem a finalMem = None.
  Proof.
    intros. unfold Memory.write_mem in *.
    destruct_one_match_hyp; [|discriminate].
    inversions H.
    unfold Memory.read_mem in *.
    split; intros.
    - repeat destruct_one_match. subst.
      + apply reg_eqb_true in E1. subst. rewrite E0 in E. rewrite E in H. discriminate.
      + assumption.
      + reflexivity.
    - repeat destruct_one_match_hyp; subst; reflexivity || discriminate || assumption.
  Qed.

  Lemma mem_accessibility_trans:
    forall {initialMem middleMem finalMem: Memory.mem} {a: mword},
      (Memory.read_mem a initialMem = None <-> Memory.read_mem a middleMem = None) ->
      (Memory.read_mem a middleMem  = None <-> Memory.read_mem a finalMem  = None) ->
      (Memory.read_mem a initialMem = None <-> Memory.read_mem a finalMem  = None).
  Proof. intros. tauto. Qed.

  Lemma eval_stmt_preserves_mem_accessibility:  forall {fuel: nat} {initialMem finalMem: Memory.mem}
      {s: stmt} {initialRegs finalRegs: state},
      eval_stmt _ _ empty_map fuel initialRegs initialMem s = Some (finalRegs, finalMem) ->
      forall a, Memory.read_mem a initialMem = None <-> Memory.read_mem a finalMem = None.
  Proof.
    induction fuel; intros; try (simpl in *; discriminate).
    destruct s; simpl in *;
      repeat (destruct_one_match_hyp; [|discriminate]);
      inversions H;
      try reflexivity.
    - eauto using write_mem_preserves_mem_accessibility.
    - destruct_one_match_hyp; eauto.
    - destruct p.
      repeat (destruct_one_match_hyp; try discriminate).
      + inversions H1. eauto.
      + eapply mem_accessibility_trans; [ eauto | ].
        eapply mem_accessibility_trans; [ eauto | ].
        eauto.
    - destruct p.
      eapply mem_accessibility_trans; eauto.
    - rewrite empty_is_empty in E. discriminate E.
  Qed.

  Lemma eval_stmt_preserves_mem_inaccessible: forall {fuel: nat} {initialMem finalMem: Memory.mem}
      {s: stmt} {initialRegs finalRegs: state},
      eval_stmt _ _ empty_map fuel initialRegs initialMem s = Some (finalRegs, finalMem) ->
      forall start len,
        mem_inaccessible initialMem start len -> mem_inaccessible finalMem start len.
  Proof.
    unfold mem_inaccessible. intros.
    destruct (Memory.read_mem a initialMem) eqn: E.
    - eapply H0. exact E.
    - pose proof (eval_stmt_preserves_mem_accessibility H a) as P.
      destruct P as [P _]. specialize (P E). exfalso. congruence.
  Qed.

  Ltac prove_remu_four_zero :=
    match goal with
    | |- remu _ (ZToReg 4) = ZToReg 0 => idtac
    | |- ZToReg 0 = remu _ (ZToReg 4) => symmetry
    | _ => fail 1 "wrong shape of goal"
    end;
    rewrite <-? (Z.mul_comm 4);
    autorewrite with rew_ZToReg_morphism;
    repeat (apply remu_four_zero_distrib_plus);
    rewrite? remu_four_undo;
    rewrite? remu_four_four;
    repeat match goal with
           | H: divisibleBy4 _ |- _ => apply divisibleBy4_remu40 in H; rewrite H
           end;
    ring.

  Ltac solve_mem_inaccessible :=
    eapply eval_stmt_preserves_mem_inaccessible; [|eassumption];
    try eassumption;
    let Eq := fresh "Eq" in
    match goal with
    | E1: eval_stmt _ _ ?env ?f ?r1 ?m1 ?s1 = Some (?r2, ?m2),
      E2: eval_stmt _ _ ?env ?f ?r2 ?m2 ?s2 = Some (?r3, ?m3)
      |-   eval_stmt _ _ ?env _ _ ?m1 _ = Some (_, ?m3)
      => assert (eval_stmt _ _ env (S f) r1 m1 (SSeq s1 s2) = Some (r3, m3)) as Eq
          by (simpl; rewrite E1; exact E2); exact Eq
    end.

  Ltac spec_IH originalIH IH stmt1 :=
    pose proof originalIH as IH;
    match goal with
    | |- runsTo ?st _ => specialize IH with (initialL := st); simpl in IH
    end;
    specialize IH with (s := stmt1);
    specializes IH;
    first
      [ reflexivity
      | solve_imem
      | solve_stmt_not_too_big
      | solve_valid_registers
      | solve_containsProgram
      | solve_word_eq
      | eassumption
      | solve_mem_inaccessible
      | idtac ].

  Ltac simpl_remu4_test :=
    match goal with
    | |- context [reg_eqb ?r ?expectZero] =>
      match expectZero with
      | ZToReg 0 => idtac
      end;
      match r with
      | remu ?a (ZToReg 4) => replace r with expectZero by prove_remu_four_zero
      end
    end;
    rewrite reg_eqb_eq by reflexivity;
    simpl.

  Hint Rewrite reg_eqb_ne reg_eqb_eq using congruence : rew_reg_eqb.

  Hint Rewrite
      elim_then_true_else_false
      (@left_identity _ (OState_Monad RiscvMachine))
      @get_put_same
  : rew_run1step.

  Ltac run1step'' :=
    fetch_inst;
    autounfold with unf_pseudo in *;
    cbn [execute ExecuteI.execute ExecuteM.execute ExecuteI64.execute ExecuteM64.execute];
    repeat (
        autorewrite with
            rew_get_set_Register
            rew_RiscvMachine_get_set
            rew_reg_eqb
            rew_run1step ||
        rewrite_getReg ||
        rewrite_setReg ||
        simpl_remu4_test ||
        rewrite_reg_value).

  Ltac run1step' :=
    (eapply runsToStep; simpl in *; subst *); [ run1step'' | ].

  Ltac run1step :=
    run1step';
    [ rewrite execState_step;
      simpl_RiscvMachine_get_set;
      reflexivity
    | ].

  Ltac run1done :=
    apply runsToDone;
    simpl_RiscvMachine_get_set;
    (* note: less aggressive than "repeat split" because it does not unfold *)
    repeat match goal with
           | |- _ /\ _ => split
           end;
    first
      [ assumption
      | eapply containsMem_write; eassumption
      | match goal with
        | |- extends _ _ => state_calc
        end
      | solve [solve_containsProgram]
      | solve_word_eq
      | idtac ].

  Ltac IH_done IH :=
    eapply runsToSatisfying_imp; [ exact IH | ];
    subst;
    clear;
    simpl;
    intros;
    destruct_products;
    repeat match goal with
           | |- _ /\ _ => split
           end;
    try assumption;
    try match goal with
        | H: ?m.(core).(pc) = _ |- ?m.(core).(pc) = _ => rewrite H
        end;
    solve_word_eq.

  Ltac destruct_everything :=
    destruct_products;
    try destruct_pair_eqs;
    destruct_conjs;
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end;
    subst *;
    destruct_containsProgram.

  Lemma execute_load: forall {A: Type} (x a: Register) (addr v: mword) (initialMH: Memory.mem)
           (f:unit -> OState RiscvMachine A) (initialL: RiscvMachine) initialRegsH,
      valid_register x ->
      valid_register a ->
      Memory.read_mem addr initialMH = Some v ->
      containsMem initialL.(machineMem) initialMH ->
      get initialRegsH a = Some addr ->
      extends initialL.(core).(registers) initialRegsH ->
      (Bind (execute (LwXLEN x a 0)) f) initialL =
      (f tt) (with_registers (setReg initialL.(core).(registers) x v) initialL).
  Proof. (*
    intros.
    pose proof (@Bind_getRegister _ _ _ _ _ _ _) as Bind_getRegister.
    pose proof (@Bind_setRegister _ _ _ _ _ _ _) as Bind_setRegister.
    pose proof (@State_is_RegisterFile _ _) as State_is_RegisterFile.
    pose proof (@Bind_loadWord _ _ _ _ _ _ _) as Bind_loadWord.
    pose proof (@Bind_loadDouble _ _ _ _ _ _ _) as Bind_loadDouble.
    unfold containsMem, Memory.read_mem, wXLEN_in_bytes, wXLEN, bitwidth in *.
    unfold LwXLEN, bitwidth, loadWordwXLEN in *.
    destruct Bw eqn: EBw;
      simpl in H2;
      specialize H2 with (1 := H1);
      (destruct_one_match_hyp; [|discriminate]);
      simpl in H2; inversions H2;
      cbn [execute ExecuteI.execute ExecuteM.execute ExecuteI64.execute ExecuteM64.execute];
      rewrite associativity;
      rewrite Bind_getRegister by assumption;
      rewrite associativity;
      unfold add, fromImm, MachineWidthInst, bitwidth, MachineWidth32, MachineWidth64;
      rewrite_reg_value;
      rewrite ZToWord_0;
      rewrite wplus_comm;
      rewrite wplus_unit;
      [ rewrite translate_id_if_aligned_4 by assumption |
        rewrite translate_id_if_aligned_8 by assumption ];
      rewrite left_identity;
      rewrite associativity;
      [ rewrite Bind_loadWord | rewrite Bind_loadDouble ];
      rewrite Bind_setRegister;
      first [reflexivity | assumption].
  Qed.
          *)
  Admitted.

  Lemma execute_store: forall {A: Type} (ra rv: Register) (a v: mword)
                         (initialMH finalMH: Memory.mem)
                         (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine) initialRegsH,
      valid_register ra ->
      valid_register rv ->
      Memory.write_mem a v initialMH = Some finalMH ->
      containsMem initialL.(machineMem) initialMH ->
      get initialRegsH ra = Some a ->
      get initialRegsH rv = Some v ->
      extends initialL.(core).(registers) initialRegsH ->
      (Bind (execute (SwXLEN ra rv 0)) f) initialL =
      (f tt) (with_machineMem (storeWordwXLEN initialL.(machineMem) a v) initialL).
  Proof.
    (*
    intros.
    pose proof (@Bind_getRegister _ _ _ _ _ _ _) as Bind_getRegister.
    pose proof (@Bind_setRegister _ _ _ _ _ _ _) as Bind_setRegister.
    pose proof (@State_is_RegisterFile _ _) as State_is_RegisterFile.
    pose proof (@Bind_storeWord _ _ _ _ _ _ _) as Bind_storeWord.
    pose proof (@Bind_storeDouble _ _ _ _ _ _ _) as Bind_storeDouble.
    intros.
    unfold containsMem, Memory.write_mem, Memory.read_mem,
      wXLEN_in_bytes in *.
    unfold SwXLEN, bitwidth, loadWordwXLEN, storeWordwXLEN in *.
    destruct Bw eqn: EBw;
      simpl in H2;
      (destruct_one_match_hyp; [|discriminate]);
      inversions H1;
      (destruct_one_match_hyp; [|discriminate]);
      cbn [execute ExecuteI.execute ExecuteM.execute ExecuteI64.execute ExecuteM64.execute];
      rewrite associativity;
      rewrite Bind_getRegister by assumption;
      rewrite associativity;
      unfold add, fromImm, MachineWidthInst, bitwidth, MachineWidth32, MachineWidth64;
      rewrite ZToWord_0;
      rewrite wplus_comm;
      rewrite wplus_unit;
      unfold wXLEN, bitwidth in *;
      rewrite_reg_value;
      [ rewrite translate_id_if_aligned_4 by assumption |
        rewrite translate_id_if_aligned_8 by assumption ];
      rewrite left_identity;
      rewrite associativity;
      rewrite Bind_getRegister by assumption;
      [ rewrite Bind_storeWord   |
        rewrite Bind_storeDouble ];
      rewrite_reg_value;
      reflexivity.
  Qed.*)
  Admitted.

  Arguments Bind: simpl never.
  Arguments Return: simpl never.
  Arguments app: simpl never. (* don't simpl ([[ oneInst ]] ++ rest) into oneInst :: rest
    because otherwise solve_imem doesn't recognize "middle" any more *)

  (* otherwise simpl takes forever:
  Arguments split1: simpl never.
  Arguments split2: simpl never.
  Arguments ZToWord: simpl never.
  Arguments Nat.pow: simpl never.
*)
  Lemma in_range0_valid_addr: forall (a: mword) al l,
      in_range a al 0 l ->
      Memory.valid_addr a al l.
  Proof.
    unfold in_range, Memory.valid_addr. intuition idtac.
  Qed.

  Lemma store_preserves_containsProgram: forall initialL_mem insts imemStart a v,
      containsProgram initialL_mem insts imemStart ->
      not_in_range a XLEN_in_bytes (regToZ_unsigned imemStart) (4 * (Zlength insts)) ->
      in_range a XLEN_in_bytes 0 (Memory.memSize initialL_mem) ->
      (* better than using $4 ^* imemStart because that prevents overflow *)
      divisibleBy4 imemStart ->
      containsProgram (storeWordwXLEN initialL_mem a v) insts imemStart.
  Proof.
    (*
    unfold containsProgram.
    intros. rename H2 into A. destruct H.
    clear -H H0 H1 H2 A.
    pose proof pow2_wXLEN_4 as X.
    assert (forall (a: mword), a = a ^+ $ (4) ^- $ (4)) as helper4 by (intros; solve_word_eq).
    rename H1 into IR.
    pose proof (in_range0_valid_addr IR) as H1.
    unfold storeWordwXLEN, ldInst, wXLEN_in_bytes, wXLEN, bitwidth in *;
      destruct Bw; simpl in *;
        split;
        rewrite? Memory.storeWord_preserves_memSize;
        rewrite? Memory.storeDouble_preserves_memSize;
        try assumption;
        intros;
        specialize H2 with (1 := H3).
    - pose proof (Memory.memSize_bound initialL_mem) as B.
      assert (nth_error insts i <> None) as F by congruence.
      apply nth_error_Some in F.
      pose proof (@wordToNat_natToWord_idempotent' 32 (4 * i)) as D.
      rewrite Memory.loadStoreWord_ne; try assumption.
      + unfold Memory.valid_addr. split.
        * rewrite wordToNat_wplus'; omega.
        * rewrite wordToNat_wplus' by omega.
          rewrite D by omega.
          rewrite Nat.add_mod by omega.
          rewrite Nat.mul_comm. rewrite Nat.mod_mul by omega.
          rewrite A.
          reflexivity.
      + intro C. subst a. rename H0 into R.
        unfold not_in_range in *.
        rewrite wordToNat_wplus' in R; omega.
    - pose proof (Memory.memSize_bound initialL_mem) as B.
      assert (nth_error insts i <> None) as F by congruence.
      apply nth_error_Some in F.
      pose proof (@wordToNat_natToWord_idempotent' 64 (4 * i)) as D.
      rewrite loadWord_storeDouble_ne'; try assumption.
      + unfold in_range in *.
        rewrite wordToNat_wplus' by omega.
        rewrite D by omega.
        rewrite Nat.add_mod by omega.
        rewrite Nat.mul_comm. rewrite Nat.mod_mul by omega.
        rewrite A.
        intuition (omega || reflexivity).
      + clear H1 H2.
        unfold not_in_range, in_range in *.
        rewrite wordToNat_wplus' by omega.
        rewrite D by omega.
        omega.
  Qed.*)
  Admitted.

  Lemma mem_inaccessible_read:  forall a initialMH w start len,
      Memory.read_mem a initialMH = Some w ->
      mem_inaccessible initialMH start len ->
      not_in_range a XLEN_in_bytes start len.
  Proof.
    intros. unfold mem_inaccessible in *. eapply H0. eassumption.
  Qed.

  Lemma mem_inaccessible_write:  forall a v initialMH finalMH start len,
      Memory.write_mem a v initialMH = Some finalMH ->
      mem_inaccessible initialMH start len ->
      not_in_range a XLEN_in_bytes start len.
  Proof.
    intros. unfold Memory.write_mem, mem_inaccessible in *.
    destruct_one_match_hyp; [|discriminate].
    eapply H0. eassumption.
  Qed.

  Lemma read_mem_in_range: forall a0 initialMH initialML w,
      Memory.read_mem a0 initialMH = Some w ->
      containsMem initialML initialMH ->
      in_range a0 XLEN_in_bytes 0 (Memory.memSize initialML).
  Proof.
    intros. unfold in_range, containsMem in *.
    specialize H0 with (1 := H). destruct H0 as [A B0].
    unfold Memory.read_mem in *.
    destruct_one_match_hyp; try discriminate.
    Admitted. (*
    omega.
  Qed.*)

  Lemma write_mem_in_range: forall a0 v0 initialMH finalMH initialML,
      Memory.write_mem a0 v0 initialMH = Some finalMH ->
      containsMem initialML initialMH ->
      in_range a0 XLEN_in_bytes 0 (Memory.memSize initialML).
  Proof.
    intros. unfold Memory.write_mem in *.
    destruct_one_match_hyp; try discriminate.
    inversion H. clear H. subst finalMH.
    eapply read_mem_in_range; eassumption.
  Qed.

  (*
  Lemma wordToZ_size'': forall (w : mword),
      (- Z.of_nat (pow2 (wXLEN - 1)) <= wordToZ w < Z.of_nat (pow2 (wXLEN - 1)))%Z.
  Proof.
    clear. unfold wXLEN, bitwidth. destruct Bw; intros; apply  wordToZ_size'.
  Qed.

  Lemma wordToZ_ZToWord': forall (z : Z),
      (- Z.of_nat (pow2 (wXLEN - 1)) <= z < Z.of_nat (pow2 (wXLEN - 1)))%Z ->
      wordToZ (ZToWord wXLEN z) = z.
  Proof.
    clear. unfold wXLEN, bitwidth. destruct Bw; intros; apply wordToZ_ZToWord; assumption.
  Qed.
  *)

  Definition load_lit_semantics(v: Z): mword :=
    add (sll (add (sll (add (sll (add (sll (add (sll (add (sll (add (sll (add
      (ZToReg 0)
      (ZToReg (bitSlice v (7 * 8) (8 * 8)))) 8)
      (ZToReg (bitSlice v (6 * 8) (7 * 8)))) 8)
      (ZToReg (bitSlice v (5 * 8) (6 * 8)))) 8)
      (ZToReg (bitSlice v (4 * 8) (5 * 8)))) 8)
      (ZToReg (bitSlice v (3 * 8) (4 * 8)))) 8)
      (ZToReg (bitSlice v (2 * 8) (3 * 8)))) 8)
      (ZToReg (bitSlice v (1 * 8) (2 * 8)))) 8)
      (ZToReg (bitSlice v (0 * 8) (1 * 8))).

  Lemma compile_lit_correct: forall v: Z,
      load_lit_semantics v = ZToReg v.
  Proof using .
  Admitted.

  Lemma signed_lt_lemma: forall x0 x1 b,
    signed_less_than x1 x0 || reg_eqb x1 x0 = b ->
    signed_less_than x0 x1 = negb b.
  Proof.
  Admitted.

  Lemma ltu_lemma: forall x0 x1 b,
    ltu x1 x0 || reg_eqb x1 x0 = b ->
    ltu x0 x1 = negb b.
  Proof.
  Admitted.

  Lemma setPC_lemma: forall l m,
    setPC l m = (Some tt, with_nextPC l m).
  Proof.
  Admitted.

  Ltac cleanup :=
    repeat match goal with
    | H : negb ?x = true |- _ =>
        let H' := fresh in
        assert (x = false) as H' by (eapply negb_true_iff; eauto);
        clear H
    | H : negb ?x = false |- _ =>
        let H' := fresh in
        assert (x = true) as H' by (eapply negb_false_iff; eauto);
        clear H
    | H : ?x = false |- _ =>
        progress (rewrite H in *)
    | H : ?x = true |- _ =>
        progress (rewrite H in *)
    | H : None = Some _ |- _ =>
        inversion H
    | H : Return _ = Some _ |- _ =>
        inversion H; clear H
    end.

  Ltac tac1 :=
    (match goal with
    | |- context[@Bind _ _ _ _ _ _ ] =>
        first [rewrite Bind_getRegister0 |
               rewrite Bind_getRegister  | 
               rewrite Bind_getPC]
    | H: eval_bcond _ _ _ = Some _ |- _ =>
        inversion H; clear H
    | H : valid_registers_bcond _ |- _ =>
        destruct H
    | H: context[@Bind _ option_Monad _ _ _ _] |- _ =>
        unfold Bind, option_Monad in H; repeat destruct_one_match_of_hyp H
    | |- (Return ?a) _ = (Some ?a, _) =>
        apply execState_Return
    | |- context[remu ?x (ZToReg 4)] =>
        let H' := fresh in
        assert (remu x (ZToReg 4) = ZToReg 0) as H' by (prove_remu_four_zero);
        rewrite H'
    | H1: extends ?initialL_regs ?initialH,
      H2: @get _ ?mword ?stateMap ?initialH ?x = Some ?mx |- _ =>
        let H' := fresh in
        assert (@get Register mword stateMap initialL_regs x = Some mx) as H' by
                (apply (H1 x mx H2));
        rewrite H'
    | H : signed_less_than ?x1 ?x0 || reg_eqb ?x1 ?x0 = ?b |- _ =>
        rewrite (signed_lt_lemma x0 x1 H)
    | H : ltu ?x1 ?x0 || reg_eqb ?x1 ?x0 = ?b |- _ =>
        rewrite (ltu_lemma x0 x1 H)
    | |- setPC _ _ = _ =>
        rewrite setPC_lemma
    | |- context[reg_eqb ?x ?x] =>
        let H' := fresh in
        assert (reg_eqb x x = true) as H' by (rewrite reg_eqb_spec; eauto);
        rewrite H'
  end; simpl; cleanup; simpl; eauto).

  Lemma sequence_lemma:  forall (t1 t2: OState RiscvMachine unit) m1 m2 m3,
    t1 m1 = (Some tt, m2) ->
    t2 m2 = (Some tt, m3) ->
    (t1;;t2) m1 = (Some tt, m3).
  Proof.
    intros. simpl_run1. rewrite H. eauto.
  Qed.

  Lemma compile_stmt_correct_aux:
    forall allInsts imemStart fuelH s insts initialH  initialMH finalH finalMH initialL
      instsBefore instsAfter,
    compile_stmt s = insts ->
    allInsts = instsBefore ++ insts ++ instsAfter ->
    stmt_not_too_big s ->
    valid_registers s ->
    divisibleBy4 imemStart ->
    eval_stmt _ _ empty_map fuelH initialH initialMH s = Some (finalH, finalMH) ->
    extends initialL.(core).(registers) initialH ->
    containsMem initialL.(machineMem) initialMH ->
    containsProgram initialL.(machineMem) allInsts imemStart ->
    initialL.(core).(pc) = add imemStart (mul (ZToReg 4) (ZToReg (Zlength instsBefore))) ->
    initialL.(core).(nextPC) = add initialL.(core).(pc) (ZToReg 4) ->
    mem_inaccessible initialMH (regToZ_unsigned imemStart) (4 * Zlength allInsts) ->
    runsToSatisfying initialL (fun finalL =>
       extends finalL.(core).(registers) finalH /\
       containsMem finalL.(machineMem) finalMH /\
       containsProgram finalL.(machineMem) allInsts imemStart /\
       finalL.(core).(pc) = add initialL.(core).(pc) (mul (ZToReg 4) (ZToReg (Zlength insts))) /\
       finalL.(core).(nextPC) = add finalL.(core).(pc) (ZToReg 4)).
  Proof.
    intros allInsts imemStart. pose proof (mkAllInsts allInsts).
    induction fuelH; [intros; discriminate |].
    intros.
    unfold runsToSatisfying in *.
    invert_eval_stmt;
      try match goal with
          | o: bopname |- _ => destruct o (* do this before destruct_containsProgram *)
          end;
      simpl in *; unfold compile_lit, compile_lit_rec in *;
      destruct_everything.

    - (* SLoad *)
      clear IHfuelH.
      eapply runsToStep; simpl in *; subst *.
      + fetch_inst.
        erewrite execute_load; [|eassumption..].
        simpl_RiscvMachine_get_set.
        simpl.
        rewrite execState_step.
        simpl_RiscvMachine_get_set.
        reflexivity.
      + run1done.

    - (* SStore *)
      clear IHfuelH.
      eapply runsToStep; simpl in *; subst *.
      + fetch_inst.
        erewrite execute_store; [|eassumption..].
        simpl_RiscvMachine_get_set.
        rewrite execState_step.
        simpl_RiscvMachine_get_set.
        reflexivity.
      + run1done.
        apply store_preserves_containsProgram.
        * solve_containsProgram.
        * eapply mem_inaccessible_write; eassumption.
        * eapply write_mem_in_range; eassumption.
        * assumption.

    - (* SLit *)
      clear IHfuelH.
      Time run1step.
      Time run1step.
      Time run1step.
      Time run1step.
      Time run1step.
      Time run1step.
      Time run1step.
      Time run1step.
      Time run1step.
      Time run1step.
      Time run1step.
      Time run1step.
      Time run1step.
      Time run1step.
      Time run1step.
      run1done.
      f_equal.
      apply compile_lit_correct.

      (* SOp *)
    - run1step. run1done.
    - run1step. run1done.
    - run1step. run1done.
    - run1step. run1done.
    - run1step. run1done.
    - run1step. run1done.
    - run1step. run1done.
    - run1step. run1done.
    - run1step. run1done.
    - run1step. run1done.
    - run1step. run1done.
    - run1step. run1step. run1done.
      rewrite reduce_eq_to_sub_and_lt.
      auto.

    - (* SSet *)
      clear IHfuelH.
      run1step.
      run1done.
      f_equal.
      ring.

    - (* SIf/Then *)
      (* branch if cond = false (will not branch *)
      eapply runsToStep; simpl in *; subst *.
      fetch_inst. eapply sequence_lemma.
      destruct cond; repeat tac1.
      apply execState_step.
      (*run1step.*)
      (* use IH for then-branch *)
      spec_IH IHfuelH IH s1.
      apply (runsToSatisfying_trans IH). clear IH.
      (* jump over else-branch *)
      intros.
      destruct_everything.
      run1step.
      run1done.

    - (* SIf/Else *)
      (* branch if cond = 0 (will  branch) *)
      eapply runsToStep; simpl in *; subst *.
      fetch_inst.
      eapply sequence_lemma.
      destruct cond; repeat tac1. 
      apply execState_step.
      (*run1step.*)
      (* use IH for else-branch *)
      spec_IH IHfuelH IH s2.
      IH_done IH.
    - (* SLoop/done *)
      (* We still have to run part 1 of the loop body which is before the break *)
      spec_IH IHfuelH IH s1.
      apply (runsToSatisfying_trans IH). clear IH.
      intros.
      destruct_everything.
      eapply runsToStep; simpl in *; subst *.
      fetch_inst.
      eapply sequence_lemma.
      destruct cond; repeat tac1.
      apply execState_step.
      run1done.

    - (* SLoop/again *)
      (* 1st application of IH: part 1 of loop body *)
      spec_IH IHfuelH IH s1.
      apply (runsToSatisfying_trans IH). clear IH.
      intros.
      destruct_everything.
      (*run1step.
      (* 2nd application of IH: part 2 of loop body *)*)
      eapply runsToStep; simpl in *; subst *.
      fetch_inst. eapply sequence_lemma.
      destruct cond; repeat tac1.
      apply execState_step.

      (*run1step.*)
      (* 2nd application of IH: part 2 of loop body *)      
      spec_IH IHfuelH IH s2.
      apply (runsToSatisfying_trans IH). clear IH.
      intros.
      destruct_everything.
      run1step.
      (* 3rd application of IH: run the whole loop again *)
      spec_IH IHfuelH IH (SLoop s1 cond s2).
      IH_done IH.

    - (* SSeq *)
      spec_IH IHfuelH IH s1.
      apply (runsToSatisfying_trans IH). clear IH.
      intros.
      destruct_everything.
      spec_IH IHfuelH IH s2.
      IH_done IH.

    - (* SSkip *)
      run1done.

    - (* SCall *)
      match goal with H: _ |- _ => solve [rewrite empty_is_empty in H; inversion H] end.
  Qed.

  Lemma compile_stmt_correct:
    forall imemStart fuelH s insts initialMH finalH finalMH initialL,
    compile_stmt s = insts ->
    stmt_not_too_big s ->
    valid_registers s ->
    divisibleBy4 imemStart ->
    eval_stmt _ _ empty_map fuelH empty_map initialMH s = Some (finalH, finalMH) ->
    containsMem initialL.(machineMem) initialMH ->
    containsProgram initialL.(machineMem) insts imemStart ->
    initialL.(core).(pc) = imemStart ->
    initialL.(core).(nextPC) = add initialL.(core).(pc) (ZToReg 4) ->
    mem_inaccessible initialMH (regToZ_unsigned imemStart) (4 * Zlength insts) ->
    exists fuelL,
      let finalL := execState (run (B := BitWidth) fuelL) initialL in
      extends finalL.(core).(registers) finalH /\
      containsMem finalL.(machineMem) finalMH.
  Proof.
    intros.
    pose proof runsTo_to_onerun as Q.
    specialize (Q initialL
                  (fun finalL => extends (registers (core finalL)) finalH /\
                                 containsMem (machineMem finalL) finalMH)).
    cbv beta zeta in *.
    unfold runsTo_onerun in Q.
    destruct Q as [fuel Q].
    {
    eapply runsToSatisfying_imp.
    - eapply @compile_stmt_correct_aux with (s := s) (initialH := empty_map)
        (fuelH := fuelH) (finalH := finalH) (instsBefore := nil) (instsAfter := nil).
      + reflexivity.
      + reflexivity.
      + assumption.
      + assumption.
      + eassumption.
      + eassumption.
      + clear. unfold extends. intros. rewrite empty_is_empty in H. discriminate.
      + assumption.
      + rewrite app_nil_r. rewrite app_nil_l. subst *. assumption.
      + simpl. subst imemStart.
        rewrite Zlength_nil.
        ring.
      + assumption.
      + rewrite app_nil_r. rewrite app_nil_l. subst *. assumption.
    - intros.
      rename H9 into A.
      cbv beta in A. tauto.
    }
    {
      match type of Q with
      | context [?r] =>
          match r with
          | run fuel initialL => destruct r as [ [ u | ] final ] eqn: E; [|contradiction]
          end
      end.
      exists fuel. unfold execState.
      change Register with Z in *.
      rewrite E.
      exact Q.
    }
  Qed.

  Print Assumptions compile_stmt_correct.
End FlatToRiscv.