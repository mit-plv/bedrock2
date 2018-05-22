Require Import lib.LibTacticsMin.
Require Import riscv.util.Monads.
Require Import compiler.Common.
Require Import compiler.FlatImp.
Require Import compiler.StateCalculus.
Require Import bbv.DepEqNat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import compiler.Op.
Require Import compiler.ResMonad.
Require Import riscv.Program.
Require Import riscv.Decode.
Require Import riscv.PseudoInstructions.
Require Import riscv.RiscvMachine.
Require Import riscv.Execute.
Require Import riscv.Run.
Require riscv.Memory.
Require Import compiler.runsToSatisfying.
Require Import riscv.RiscvBitWidths.
Require Import compiler.NameWithEq.
Require Import Coq.Program.Tactics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import riscv.InstructionCoercions.
Require Import riscv.Utility.
Require Import compiler.StateCalculus.
Require Import riscv.AxiomaticRiscv.
Require Import riscv.encode.Encode.

Local Open Scope ilist_scope.

Set Implicit Arguments.

Section put_put.

  Context {var: Type}.
  Context {val: Type}.
  Context {state: Type}.
  Context {stateMap: Map state var val}.

  Lemma put_put_same: forall s x v1 v2,
      put (put s x v1) x v2 = put s x v2.
  Admitted.

End put_put.

(* needed below for ring automation *)  
Lemma Z4four: forall sz, ZToWord sz 4 = $4.
Proof.
  intros. change 4%Z with (Z.of_nat 4).
  apply ZToWord_Z_of_nat.
Qed.

(* State_is_RegisterFile gets its own section so that destructing Bw later does
   not lead to ill-typed terms *)
Section RegisterFile.

  Context {Bw: RiscvBitWidths}.
  Context {state: Type}.
  Context {stateMap: Map state Register (word wXLEN)}.

  Instance State_is_RegisterFile: RegisterFile state Register (word wXLEN) := {|
    getReg rf r := match get rf r with
                   | Some v => v
                   | None => $0
                   end;
    setReg := put;
    initialRegs := empty;
  |}.

End RegisterFile.

Existing Instance State_is_RegisterFile.


Section FlatToRiscv.

  Context {Bw: RiscvBitWidths}.

  (* put here so that rem picks up the MachineWidth for wXLEN *)

  Lemma remu_four_distrib_plus: forall a b, remu (a ^+ b) four = (remu a four) ^+ (remu b four).
  Proof. Admitted.

  Lemma remu_four_undo: forall a, remu ($4 ^* a) four = $0.
  Proof. Admitted.

  Lemma remu_four_four: remu $4 four = $0.
  Proof. Admitted.

  Lemma wlshift_distr_plus: forall sz n (a b: word sz),
      wlshift (a ^+ b) n = wlshift a n ^+ wlshift b n.
  Admitted.
  
  Lemma wlshift_iter: forall sz n1 n2 (a: word sz),
      wlshift (wlshift a n1) n2 = wlshift a (n1 + n2).
  Admitted.
  
  Lemma wlshift_bitSlice_plus: forall (sz1 sz2: Z) v,
      wlshift (ZToWord wXLEN (bitSlice v sz1 (sz1 + sz2))) (Z.to_nat sz1)
      ^+ ZToWord wXLEN (bitSlice v 0 sz1)
      = ZToWord wXLEN (bitSlice v 0 (sz1 + sz2)).
  Admitted.
  
  Lemma wlshift_zero: forall sz n, wlshift $0 n = natToWord sz 0.
  Admitted.
  
  Lemma bitSlice_wordToZ_all: forall sz1 sz2 (v: word sz1),
      sz1 <= Z.to_nat sz2 ->
      bitSlice (wordToZ v) 0 sz2 = wordToZ v.
  Admitted.

  (*
  Context {Name: NameWithEq}.

  (* If we made it a definition instead, destructing an if on "@dec (@eq (@var Name) x x0)"
     (from this file), where a "@dec (@eq (@Reg Name) x x0)" (from another file, Riscv.v)
     is in the context, will not recognize that these two are the same (they both reduce to
     "@dec (@eq (@name Name) x x0)", which is annoying. *)
  Notation var := (@name Name).
  Existing Instance eq_name_dec.
   *)

  Context {state: Type}.
  Context {stateMap: Map state Register (word wXLEN)}.

  Context {mem: nat -> Set}.
  Context {IsMem: Memory.Memory (mem wXLEN) wXLEN}.
  
  Local Notation RiscvMachine := (@RiscvMachine Bw (mem wXLEN) state).
  Context {RVM: RiscvProgram (OState RiscvMachine) (word wXLEN)}.

  (* assumes generic translate and raiseException functions *)
  Context {RVS: @RiscvState (OState RiscvMachine) (word wXLEN) _ _ RVM}.  

  Context {RVAX: @AxiomaticRiscv Bw state State_is_RegisterFile (mem wXLEN) _ RVM}.
  
  Ltac state_calc := state_calc_generic (@name TestFlatImp.ZName) (word wXLEN).

  (* This phase assumes that register allocation has already been done on the FlatImp
     level, and expects the following to hold: *)
  Fixpoint valid_registers(s: stmt): Prop :=
    match s with
    | SLoad x a => valid_register x /\ valid_register a
    | SStore a x => valid_register a /\ valid_register x
    | SLit x _ => valid_register x
    | SOp x _ y z => valid_register x /\ valid_register y /\ valid_register z
    | SSet x y => valid_register x /\ valid_register y
    | SIf c s1 s2 => valid_register c /\ valid_registers s1 /\ valid_registers s2
    | SLoop s1 c s2 => valid_register c /\ valid_registers s1 /\ valid_registers s2
    | SSeq s1 s2 => valid_registers s1 /\ valid_registers s2
    | SSkip => True
    end.

  (*
  Variable var2Register: var -> Register. (* TODO register allocation *)
  Hypothesis no_var_mapped_to_Register0: forall (x: var), x <> Register0.
  Hypothesis var2Register_inj: forall x1 x2, x1 = x2 -> x1 = x2.
   *)
  
  (* Set Printing Projections.
     Uncaught anomaly when stepping through proofs :(
     https://github.com/coq/coq/issues/6257 *)

  Definition LwXLEN: Register -> Register -> Z -> Instruction :=
    match bitwidth with
    | Bitwidth32 => Lw
    | Bitwidth64 => Ld
    end.
  
  Definition SwXLEN: Register -> Register -> Z -> Instruction :=
    match bitwidth with
    | Bitwidth32 => Sw
    | Bitwidth64 => Sd
    end.

  Definition compile_op(rd: Register)(op: binop)(rs1 rs2: Register): list Instruction :=
    match op with
    | OPlus => [[Add rd rs1 rs2]]
    | OMinus => [[Sub rd rs1 rs2]]
    | OTimes => [[Mul rd rs1 rs2]]
    | OEq => [[Sub rd rs1 rs2; Seqz rd rd]]
    | OLt => [[Sltu rd rs1 rs2]]
    | OAnd => [[And rd rs1 rs2]]
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
  
  Definition compile_lit(rd: Register)(v: word wXLEN): list Instruction :=
    compile_lit_rec 7 rd Register0 (wordToZ v).
  
  Definition compile_lit_32(rd: Register)(v: word 32): list Instruction :=
    let h0 := split1 16 16 v in
    let h1 := split2 16 16 v in
    [[Addi rd Register0 (wordToZ h1); Slli rd rd 16; Addi rd rd (wordToZ h0)]].

  Definition compile_lit_64(rd: Register)(v: word 64): list Instruction :=
    let w0 := split1 32 32 v in
    let w1 := split2 32 32 v in
    let h0 := split1 16 16 w0 in
    let h1 := split2 16 16 w0 in
    let h2 := split1 16 16 w1 in
    let h3 := split2 16 16 w1 in
    [[Addi rd Register0 (wordToZ h3);
      Slli rd rd 16; Addi rd rd (wordToZ h2);
      Slli rd rd 16; Addi rd rd (wordToZ h1);
      Slli rd rd 16; Addi rd rd (wordToZ h0)]].

  (* The problem with the primed version is that we have to destruct the bitwidth to expose
     the indivdual commands (on which the proof machinery of compile_stmt_correct_aux works),
     but the proof machinery stops working when the bitwidth is destructed because typeclass
     search stops working as it should, and destructing the bitwidth only works after unfolding
     all definitions involving (word wXLEN). *)
  Definition compile_lit'(rd: Register)(v: word wXLEN): list Instruction.
    clear -Bw rd v. unfold wXLEN, bitwidth in *. destruct Bw.
    - exact (compile_lit_32 rd v).
    - exact (compile_lit_64 rd v).
  Defined.

  (* Very stupid workaround: *)
  Definition make_64_bit(v: word wXLEN): word 64.
    clear -Bw v. unfold wXLEN, bitwidth in *. destruct Bw.
    - exact (zext v 32).
    - exact v.
  Defined.

  Definition compile_lit''(rd: Register)(v: word wXLEN): list Instruction :=
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

  (*
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
  *)
  
  Definition compile_lit_old(rd: Register)(v: Z): list Instruction :=
    compile_halves (wXLEN / 16) rd v.

  (*
  Definition add_lit_20(rd rs: Register)(v: word 20): list Instruction :=
    [[Addi rd rs (wordToZ v)]].
  
  Definition add_lit_32(rd rs: Register)(v: word 32): list Instruction :=
    let lobits := split1 20 12 v in
    let hibits := split2 20 12 v in [[]].

  Definition embed_words(l: list (word 32)): list Instruction :=
    [[J (Z.of_nat (length l))]] ++ (map (fun w => InvalidInstruction (wordToZ w)) l).
  *)

  Definition wXLEN_to_word_list(v: word wXLEN): list (word 32).
    clear -Bw v. unfold wXLEN, bitwidth in *. destruct Bw.
    - exact [v].
    - exact [split1 32 32 v; split2 32 32 v].
  Defined.

  Definition embed_word(v: word wXLEN): list Instruction :=
    map (fun w => InvalidInstruction (wordToZ w)) (wXLEN_to_word_list v).

  Definition compile_lit_old1(rd: Register)(v: word wXLEN): list Instruction :=
    let l := embed_word v in
    [[Auipc rd 0; LwXLEN rd rd 8; J (Z.of_nat (length l))]] ++ l.

  (*
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
   *)

  Definition compile_lit_old'(rd: Register)(v: word wXLEN): list Instruction.
    clear -Bw rd v. unfold wXLEN, bitwidth in *. destruct Bw.
    - exact (compile_lit_32 rd v).
    - exact (compile_lit_64 rd v).
  Defined.

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
        [[Beq cond Register0 ((Z.of_nat (length bThen' + 2)) * 4)]] ++
        bThen' ++
        [[Jal Register0 ((Z.of_nat (length bElse' + 1)) * 4)]] ++
        bElse'
    | SLoop body1 cond body2 =>
        let body1' := compile_stmt body1 in
        let body2' := compile_stmt body2 in
        (* only works if branch lengths are < 2^12 *)
        body1' ++
        [[Beq cond Register0 ((Z.of_nat (length body2' + 2)) * 4)]] ++
        body2' ++
        [[Jal Register0 ((- Z.of_nat (length body1' + 1 + length body2')) * 4)]]
    | SSeq s1 s2 => compile_stmt s1 ++ compile_stmt s2
    | SSkip => nil
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
    length (compile_stmt s) <= 2 * (stmt_size s).
  Proof.
    induction s; simpl; try destruct op; simpl;
    repeat (rewrite app_length; simpl); try omega.
    (* pose proof (embed_lit_size v). TODO adapt stmt_size *)
  Admitted.

  Add Ring word_wXLEN_ring : (wring wXLEN).

  Ltac ringify :=
    repeat match goal with
           | |- context [natToWord ?sz (S ?x)] =>
             tryif (unify x O)
             then fail
             else (progress rewrite (natToWord_S sz x))
           | |- _ => change $1 with (wone wXLEN)
                   || change $0 with (wzero wXLEN)
                   || rewrite! natToWord_plus
                   || rewrite! Nat2Z.inj_add
                   || rewrite <-! Z.sub_0_l
                   || rewrite! Z.mul_sub_distr_r
                   || rewrite! Z.mul_add_distr_r
                   || rewrite! ZToWord_minus
                   || rewrite! ZToWord_plus
                   || rewrite! ZToWord_mult
                   || rewrite! ZToWord_Z_of_nat
                   || rewrite! Z4four
                   || rewrite! ZToWord_0
                   || rewrite! wzero'_def
           end.
  
  Ltac solve_word_eq :=
    match goal with
    | |- @eq (word _) _ _ => idtac
    | _ => fail 1 "wrong shape of goal"
    end;
    subst;
    clear;
    simpl;
    repeat (rewrite app_length; simpl);
    ringify;
    try ring.    

  Goal forall (a b c: word wXLEN), ((a ^+ b) ^- b) ^* c ^* $1 = a ^* c ^* $1.
  Proof. intros. ring. Qed.

  (* load and decode Inst *)
  Definition ldInst(m: mem wXLEN)(a: word wXLEN): Instruction :=
    decode RV_wXLEN_IM (wordToZ (Memory.loadWord m a)).

  Definition words_inaccessible(m: Memory.mem)(start: word wXLEN)(len: nat): Prop :=
    forall i, 0 <= i < len -> Memory.read_mem (start ^+ $4 ^* $i) m = None.

  Definition mem_inaccessible(m: Memory.mem)(start: word wXLEN)(len: nat): Prop :=
    forall a w, Memory.read_mem a m = Some w ->
           ~ wordToNat start <= wordToNat a < wordToNat start + len.

  Definition containsProgram(m: mem wXLEN)(program: list Instruction)(offset: word wXLEN) :=
    forall i inst, nth_error program i = Some inst ->
      ldInst m (offset ^+ $4 ^* $i) = inst.

  Definition containsProgram2(m: mem wXLEN)(program: list Instruction)(offset: word wXLEN) :=
    #offset + 4 * length program <= Memory.memSize m /\
    forall i inst, nth_error program i = Some inst ->
      encode inst = wordToZ (Memory.loadWord m (offset ^+ $(4 * i))).

  (* TODO doesn't hold but use containsProgram2 everywhere *)
  Axiom containsProgram_alt: containsProgram = containsProgram2.
  
  (*
  Definition containsProgram'(m: mem wXLEN)(program: list Instruction)(offset: word wXLEN) :=
    forall i inst, nth_error program i = Some inst ->
      encode inst = wordToZ (Memory.loadWord m (offset ^+ $4 ^* $i)).

  (* TODO doesn't hold but something similar enough should hold hopefully *)
  Axiom containsProgram_alt: containsProgram = containsProgram'.
  *)
(*  
  Definition containsState(regs: Register -> word wXLEN)(s: state) :=
    forall x v, get s x = Some v -> regs x = v.
*)
  Lemma wmult_neut_r: forall (sz : nat) (x : word sz), x ^* $0 = $0.
  Proof.
    intros. unfold wmult. unfold wordBin. do 2 rewrite wordToN_nat.
    rewrite <- Nnat.Nat2N.inj_mul. rewrite roundTrip_0.
    rewrite Nat.mul_0_r. simpl. rewrite wzero'_def. reflexivity.
  Qed.

  Lemma nth_error_nil_Some: forall {A} i (a: A), nth_error nil i = Some a -> False.
  Proof.
    intros. destruct i; simpl in *; discriminate.
  Qed.

  (* Note: containsProgram for one single [[inst]] could be simplified, but for automation,
     it's better not to simplify. *)
  Lemma containsProgram_cons_inv: forall m inst insts offset,
    containsProgram m (inst :: insts) offset ->
    containsProgram m [[inst]] offset /\
    containsProgram m insts (offset ^+ $4).
  Proof.
    intros *. intro Cp. unfold containsProgram. split.
    + specialize (Cp 0). specialize Cp with (1 := eq_refl).
      intros. destruct i; inverts H.
      - assumption.
      - exfalso. eauto using nth_error_nil_Some.
    + intros i inst0 E. specialize (Cp (S i)). simpl in Cp.
      specialize (Cp _ E).
      rewrite <- Cp. f_equal.
      rewrite (natToWord_S wXLEN i).
      change $1 with (wone wXLEN).
      ring.
  Qed.

  (* less general than natToWord_S, but more useful for automation because it does
     not rewrite [$1] into [$1 ^+ $0] infinitely.
     But not so useful because it does not apply to (S x) where x is a variable. *)
  Lemma natToWord_S_S: forall sz n,
      natToWord sz (S (S n)) = (wone sz) ^+ (natToWord sz (S n)).
  Proof. intros. apply natToWord_S. Qed.
  
  Lemma containsProgram_cons_inv_old: forall m inst insts offset,
    containsProgram m (inst :: insts) offset ->
    ldInst m offset = inst /\
    containsProgram m insts (offset ^+ $4).
  Proof.
    intros *. intro Cp. unfold containsProgram in Cp. split.
    + specialize (Cp 0). specializes Cp; [reflexivity|].
      rewrite wmult_neut_r in Cp.
      rewrite wplus_comm in Cp. rewrite wplus_unit in Cp.
      assumption.
    + unfold containsProgram.
      intros i inst0 E. specialize (Cp (S i)). simpl in Cp.
      specialize (Cp _ E).
      rewrite <- Cp. f_equal.
      rewrite (natToWord_S wXLEN i).
      change $1 with (wone wXLEN).
      ring.
      (*
      match goal with
      | |- @eq (word _) ?a ?b => ring_simplify a b
      end.
      *)
  Qed.

  Lemma containsProgram_app_inv: forall s insts1 insts2 offset,
    containsProgram s (insts1 ++ insts2) offset ->
    containsProgram s insts1 offset /\
    containsProgram s insts2 (offset ^+ $4 ^* $(length insts1)).
  Proof.
    intros *. intro Cp. unfold containsProgram in *. split.
    + intros. apply Cp. rewrite nth_error_app1; [assumption|].
      apply nth_error_Some. intro E. rewrite E in H. discriminate.
    + intros. rewrite <- wplus_assoc.
      do 2 rewrite (wmult_comm $4).
      rewrite <- wmult_plus_distr. rewrite <- wmult_comm.
      rewrite <- natToWord_plus.
      apply Cp.
      rewrite nth_error_app2 by omega.
      replace (length insts1 + i - length insts1) with i by omega.
      assumption.
  Qed.
  
  Lemma containsProgram_app: forall m insts1 insts2 offset,
      containsProgram m insts1 offset ->
      containsProgram m insts2 (offset ^+ $4 ^* $(length insts1)) ->
      containsProgram m (insts1 ++ insts2) offset.
  Proof.
    unfold containsProgram. intros.
    assert (i < length insts1 \/ length insts1 <= i) as E by omega.
    destruct E as [E | E].
    - rewrite nth_error_app1 in H1 by assumption. eauto.
    - rewrite nth_error_app2 in H1 by assumption.
      specialize H0 with (1 := H1). subst inst.
      f_equal. rewrite <- wplus_assoc.
      f_equal.
      match goal with
      | |- _ = ?x => match x with
                   | $4 ^* ?a ^+ $4 ^* ?b => replace x with ($4 ^* (a ^+ b)) by ring
                   end
      end.
      rewrite <- natToWord_plus.
      f_equal. f_equal. omega.
  Qed.

  Lemma containsProgram_cons: forall m inst insts offset,
    containsProgram m [[inst]] offset ->
    containsProgram m insts (offset ^+ $4) ->
    containsProgram m (inst :: insts) offset.
  Proof.
    unfold containsProgram. intros. destruct i.
    - simpl in H1. inverts H1. eauto.
    - simpl in H1.
      replace (offset ^+ $ (4) ^* $ (S i)) with (offset ^+ $4 ^+ $4 ^* $i); [eauto|].
      rewrite (natToWord_S _ i).
      change (natToWord wXLEN 1) with (wone wXLEN).
      ring.
  Qed.

  Lemma containsProgram_nil: forall m offset,
      containsProgram m [[]] offset.
  Proof.
    unfold containsProgram. intros. exfalso. eauto using nth_error_nil_Some.
  Qed.
  
  Arguments containsProgram: simpl never.
  
  Ltac destruct_containsProgram :=
    repeat match goal with
           | Cp: containsProgram _ ?l _ |- _ =>
             let Cp' := fresh Cp in
             match l with
             | [[]] => clear Cp
             | [[?inst]] => fail 1
             | ?h :: ?t => apply containsProgram_cons_inv in Cp;
                          destruct Cp as [Cp' Cp]
             | ?insts0 ++ ?insts1 => apply containsProgram_app_inv in Cp;
                                    destruct Cp as [Cp' Cp]
             end
           end.

  Ltac solve_containsProgram :=
    match goal with
    | |- containsProgram _ _ _ => subst
    end;
    repeat match goal with
           (* to make sure (b :: x) is not nil *)
           | |- context [(?a :: ?b :: ?x) ++ ?y] => rewrite <- (app_comm_cons (b :: x) y a)
           | |- _ => rewrite <- app_assoc
           end;
    (*
    repeat match goal with
           | H: ?P |- _ => match P with
                         | containsProgram _ _ _ => fail 1
                         | mem_inaccessible _ _ _ => fail 1
                         | containsMem _ _ => fail 1
                         | _ => clear H
                         end
           end;
    *)
    repeat match goal with
           | |- containsProgram _ [[]] _ => apply containsProgram_nil
           | |- containsProgram _ (_ ++ _) _ => apply containsProgram_app
           | |- containsProgram _ (_ :: ?t) _ =>
             tryif (unify t [[]])
             then fail
             else (apply containsProgram_cons)
           | Cp: containsProgram ?m ?i ?p |- containsProgram ?m ?i ?p => exact Cp
           | Cp: containsProgram ?m ?i ?p |- containsProgram ?m ?i ?p' =>
             replace p' with p; [exact Cp|try solve_word_eq]
           end.

  Lemma mul_div_undo: forall i c,
    c <> 0 ->
    c * i / c = i.
  Proof.
    intros.
    pose proof (Nat.div_mul_cancel_l i 1 c) as P.
    rewrite Nat.div_1_r in P.
    rewrite Nat.mul_1_r in P.
    apply P; auto.
  Qed.

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

  Lemma distr_if_over_app: forall T U P1 P2 (c: sumbool P1 P2) (f1 f2: T -> U) (x: T),
    (if c then f1 else f2) x = if c then f1 x else f2 x.
  Proof. intros. destruct c; reflexivity. Qed.

  Lemma pair_eq_acc: forall T1 T2 (a: T1) (b: T2) t,
    t = (a, b) -> a = fst t /\ b = snd t.
  Proof. intros. destruct t. inversionss. auto. Qed.

  Definition runsToSatisfying:
    RiscvMachine -> (RiscvMachine -> Prop) -> Prop :=
    runsTo RiscvMachine (execState run1).

  Lemma execState_compose{S A: Type}: forall (m1 m2: OState S A) (initial: S),
    execState m2 (execState m1 initial) = execState (m1 ;; m2) initial.
  Proof.
    intros. unfold execState. unfold Bind, Return, OState_Monad.
    destruct (m1 initial). simpl. destruct o; try reflexivity.
  Abort.

  Lemma runsToSatisfying_exists_fuel_old: forall initial P,
    runsToSatisfying initial P ->
    exists fuel, P (execState (run fuel) initial).
  Proof.
    introv R. induction R.
    - exists 0. exact H.
    - destruct IHR as [fuel IH]. exists (S fuel).
      unfold run in *.
      (*
      rewrite execState_compose in IH.
      apply IH.
      *)
  Abort.

  Lemma runsToSatisfying_exists_fuel: forall initial P,
    runsToSatisfying initial P ->
    exists fuel, P (execState (run fuel) initial).
  Proof.
    intros *. intro R.
    pose proof (runsToSatisfying_exists_fuel _ _ initial P R) as F.
    unfold run.
    destruct F as [fuel F]. exists fuel.
    replace
      (execState (power_func (fun m => run1;; m) fuel (Return tt)) initial)
    with
      (power_func (execState run1) fuel initial);
    [assumption|clear].
    revert initial.
    induction fuel; intros; simpl; [reflexivity|].
    unfold execState. f_equal.
    (* TODO does that hold? What if optional answer is None and it aborts? *)
  Admitted.

  (* not needed any more because we keep the instruction memory external: 
  Lemma execute_preserves_instructionMem: forall inst initial,
    (snd (execute inst initial)).(instructionMem) = initial.(instructionMem).
  Proof.
    intros. destruct initial as [machine imem]. unfold execute.
    unfold ExecuteI.execute, ExecuteM.execute, ExecuteI64.execute, ExecuteM64.execute.

  Qed.

  Lemma run1_preserves_instructionMem: forall initial,
    (execState run1 initial).(instructionMem) = initial.(instructionMem).
  Proof.
    intros.
    destruct initial as [initialProg initialRegs initialPc]. simpl.
    unfold execState, StateMonad.put. simpl.
    rewrite execute_preserves_instructionMem.
    reflexivity.
  Qed.

  Lemma runsTo_preserves_instructionMem: forall P initial,
    runsToSatisfying initial P ->
    runsToSatisfying initial
       (fun final => P final /\ final.(instructionMem) = initial.(instructionMem)).
  Proof.
    intros. induction H.
    - apply runsToDone. auto.
    - apply runsToStep. rewrite run1_preserves_instructionMem in IHrunsTo. assumption.
  Qed.

  Lemma regs_overwrite: forall x v1 v2 (initialRegs: var -> word wXLEN),
      (fun reg2 : var => if dec (x = reg2) then v2 else
                         if dec (x = reg2) then v1 else
                         initialRegs reg2)
    = (fun reg2 : var => if dec (x = reg2) then v2 else initialRegs reg2).
  Proof.
    intros.
    extensionality reg2. destruct_one_match; reflexivity.
  Qed.
*)

  (* TODO is there a principled way of writing such proofs? *)
  Lemma reduce_eq_to_sub_and_lt: forall (y z: word wXLEN) {T: Type} (thenVal elseVal: T),
    (if wlt_dec (y ^- z) $1 then thenVal else elseVal) =
    (if weq y z             then thenVal else elseVal).
  Proof.
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

  Lemma reduce_eq_to_sub_and_lt': forall (y z: word wXLEN),
    wltb (y ^- z) $1 = weqb y z.
  Proof.
    intros.
    pose proof (reduce_eq_to_sub_and_lt y z true false) as P.
    destruct (weq y z); simpl in *; destruct_one_match_hyp; subst; try discriminate.
    - rewrite ((proj2 (weqb_true_iff z z)) eq_refl).
      unfold wltb. unfold wlt in w.
      apply N.ltb_lt.
      assumption.
    - unfold wltb.
      destruct (weqb y z) eqn: F.
      + apply ((proj1 (weqb_true_iff y z))) in F. contradiction.
      + apply N.ltb_ge.
        unfold wlt in n0.
        apply N.le_ngt.
        assumption.
  Qed.

  Ltac simpl_run1 :=
    cbv [run1 execState Monads.put Monads.gets Monads.get Return Bind State_Monad OState_Monad
         execute ExecuteI.execute ExecuteM.execute ExecuteI64.execute ExecuteM64.execute
         core machineMem registers pc nextPC exceptionHandlerAddr
         getPC setPC getRegister setRegister gets].

  Ltac solve_word_eq_old :=
    clear;
    repeat match goal with
    | v: word _ |- _ =>
       rewrite <- (natToWord_wordToNat v);
       let v' := fresh v in forget (# v) as v';
       clear v
    end;
    repeat (rewrite app_length; simpl);
    repeat (rewrite <- natToWord_mult || rewrite <- natToWord_plus);
    match goal with
    | |- $ _ = $ _ => f_equal
    end;
    (repeat rewrite wordToNat_natToWord_idempotent'; [omega|..]).

  Tactic Notation "log_solved" tactic(t) :=
    match goal with
    | |- ?G => let H := fresh in assert G as H by t; idtac "solved" G; exact H
    | |- ?G => idtac "did not solve" G
    end.
  
  Lemma sext_natToWord_nat_cast: forall sz2 sz1 sz n (e: sz1 + sz2 = sz),
    2 * n < pow2 sz1 ->
    nat_cast word e (sext (natToWord sz1 n) sz2) = natToWord sz n.
  Proof.
    intros. rewrite nat_cast_eq_rect. apply sext_natToWord. assumption.
  Qed.

  Lemma sext_neg_natToWord_nat_cast: forall sz2 sz1 sz n (e: sz1 + sz2 = sz),
    2 * n < pow2 sz1 ->
    nat_cast word e (sext (wneg (natToWord sz1 n)) sz2) = wneg (natToWord sz n).
  Proof.
    intros. rewrite nat_cast_eq_rect. apply sext_wneg_natToWord. assumption.
  Qed.

  Lemma sext0: forall sz0 sz (v: word sz) (e: sz0 = 0),
    sext v sz0 = nat_cast word (eq_ind_r (fun sz0 : nat => sz = sz + sz0) (plus_n_O sz) e) v.
  Proof.
    intros. subst.
    unfold sext.
    destruct_one_match;
      simpl; rewrite combine_n_0; rewrite <- nat_cast_eq_rect; apply nat_cast_proof_irrel.
  Qed.
(*
  Lemma reassemble_literal_ext0: forall wup1 wlo1 wup2 wlo2 wlo3 wAll (v: word wAll)
    e1 e2 e3 e4,
    wup1 = wup2 ->
    wlo1 = wlo2 ->
    wlo2 = wlo3 ->
    wmsb (split_lower wup2 wlo2 (nat_cast word e3 v)) false = false ->
    wxor (nat_cast word e1 (extz (split_upper wup1 wlo1 (nat_cast word e4 v)) wlo3))
         (nat_cast word e2 (sext (split_lower wup2 wlo2 (nat_cast word e3 v)) wup2)) = v.
  Proof.
    intros.
    unfold extz, sext, wxor.
    rewrite H2.
    subst wlo3 wlo2 wup2.
    rewrite nat_cast_proof_irrel with (e1 := e2) (e2 := e1). clear e2.
    rewrite nat_cast_eq_rect with (e := e1).
    rewrite nat_cast_eq_rect with (e := e1).
    rewrite <- eq_rect_bitwp'.
    rewrite <- combine_bitwp.
    fold wxor. rewrite wxor_wzero. rewrite wxor_comm. rewrite wxor_wzero.
    rewrite nat_cast_proof_irrel with (e1 := e4) (e2 := e3). clear e4.
    unfold split_lower, split_upper.
    rewrite Word.combine_split.
    destruct e1. simpl.
    rewrite nat_cast_proof_irrel with (e1 := e3) (e2 := eq_refl).
    apply nat_cast_same.
  Qed.

  Lemma reassemble_literal_ext1: forall wup1 wlo1 wup2 wlo2 wlo3 wAll (v: word wAll)
    e1 e2 e3 e4,
    wup1 = wup2 ->
    wlo1 = wlo2 ->
    wlo2 = wlo3 ->
    wmsb (split_lower wup2 wlo2 (nat_cast word e3 v)) false = true ->
    wxor (nat_cast word e1 (extz (wnot (split_upper wup1 wlo1 (nat_cast word e4 v))) wlo3))
         (nat_cast word e2 (sext (split_lower wup2 wlo2 (nat_cast word e3 v)) wup2)) = v.
  Proof.
    intros.
    unfold extz, sext, wxor.
    rewrite H2.
    subst wlo3 wlo2 wup2.
    rewrite nat_cast_proof_irrel with (e1 := e2) (e2 := e1). clear e2.
    rewrite nat_cast_eq_rect with (e := e1).
    rewrite nat_cast_eq_rect with (e := e1).
    rewrite <- eq_rect_bitwp'.
    rewrite <- combine_bitwp.
    fold wxor. rewrite wxor_wzero. rewrite wxor_comm.
    rewrite <- wxor_wones.
    rewrite wxor_assoc.
    rewrite wxor_wones.
    rewrite wnot_ones.
    rewrite wxor_wzero.
    rewrite nat_cast_proof_irrel with (e1 := e4) (e2 := e3). clear e4.
    unfold split_lower, split_upper.
    rewrite Word.combine_split.
    destruct e1. simpl.
    rewrite nat_cast_proof_irrel with (e1 := e3) (e2 := eq_refl).
    apply nat_cast_same.
  Qed.*)

  (* separate definition to better guide automation: don't simpl 16, but keep it as a 
     constant to stay in linear arithmetic *)
  Local Definition stmt_not_too_big(s: stmt): Prop := stmt_size s * 16 < pow2 20.

  Local Ltac solve_stmt_not_too_big :=
    lazymatch goal with
    | H: stmt_not_too_big _ |- stmt_not_too_big _ =>
        unfold stmt_not_too_big in *;
        simpl stmt_size in H;
        omega
    end.

  Local Ltac solve_length_compile_stmt :=
    repeat match goal with
    | s: stmt |- _ => unique pose proof (compile_stmt_size s)
    end;
    lazymatch goal with
    | H: stmt_not_too_big _ |- _ =>
        unfold stmt_not_too_big in *;
        simpl stmt_size in H;
        unfold pow2; fold pow2;
        omega
    end.

  (* Needed because simpl will unfold (4 * ...) which is unreadable *)
  Local Ltac simpl_pow2 :=
    repeat match goal with
    | |- context [1 + ?a] => change (1 + a) with (S a)
    | |- context [pow2 (S ?a)] => change (pow2 (S a)) with (2 * pow2 a)
    | |- context [pow2 0] => change (pow2 0) with 1
    end.

  (*
  Local Ltac solve_pc_update :=
    rewrite? extz_is_mult_pow2;
    rewrite? sext_natToWord_nat_cast;
    simpl_pow2;
    [ solve_word_eq | solve_length_compile_stmt ].
   *)

  (*
  Definition loadWordH(memH: Memory.mem wXLEN)(addr: word wXLEN): option (word wXLEN).
    clear -addr memH.
    unfold wXLEN in *.
    destruct bitwidth; exact (compiler.Memory.read_mem addr memH).
  Defined.
   *)

  Lemma simpl_with_registers: forall (rs1 rs2: state) p npc eh (m: mem wXLEN),
    with_registers rs2 (mkRiscvMachine (mkRiscvMachineCore rs1 p npc eh) m) =
                       (mkRiscvMachine (mkRiscvMachineCore rs2 p npc eh) m).
  Proof. intros. reflexivity. Qed.

  Lemma simpl_with_pc: forall (rs: state) pc1 pc2 npc eh (m: mem wXLEN),
    with_pc pc2 (mkRiscvMachine (mkRiscvMachineCore rs pc1 npc eh) m) =
                (mkRiscvMachine (mkRiscvMachineCore rs pc2 npc eh) m).
  Proof. intros. reflexivity. Qed.

  Lemma simpl_with_nextPC: forall (rs: state) p npc1 npc2 eh (m: mem wXLEN),
    with_nextPC npc2 (mkRiscvMachine (mkRiscvMachineCore rs p npc1 eh) m) =
                     (mkRiscvMachine (mkRiscvMachineCore rs p npc2 eh) m).
  Proof. intros. reflexivity. Qed.

  Lemma simpl_with_machineMem: forall (c: @RiscvMachineCore _ state) (m1 m2: mem wXLEN),
    with_machineMem m2 (mkRiscvMachine c m1) =
                       (mkRiscvMachine c m2).
  Proof. intros. reflexivity. Qed.  

  Lemma simpl_registers: forall (rs: state) p npc eh,
    registers (mkRiscvMachineCore rs p npc eh) = rs.
  Proof. intros. reflexivity. Qed.

  Lemma simpl_pc: forall (rs: state) p npc eh,
    pc (mkRiscvMachineCore rs p npc eh) = p.
  Proof. intros. reflexivity. Qed.

  Lemma simpl_nextPC: forall (rs: state) p npc eh,
    nextPC (mkRiscvMachineCore rs p npc eh) = npc.
  Proof. intros. reflexivity. Qed.
  
  Lemma simpl_core: forall (c: @RiscvMachineCore _ state) (m: mem wXLEN),
    core (mkRiscvMachine c m) = c.
  Proof. intros. reflexivity. Qed.  

  Lemma simpl_machineMem: forall (c: @RiscvMachineCore _ state) (m: mem wXLEN),
    machineMem (mkRiscvMachine c m) = m.
  Proof. intros. reflexivity. Qed.  

  Ltac simpl_RiscvMachine_get_set :=
    repeat (rewrite simpl_with_registers in *
            || rewrite simpl_with_pc in *
            || rewrite simpl_with_nextPC in *
            || rewrite simpl_with_machineMem in *
            || rewrite simpl_registers in *
            || rewrite simpl_pc in *
            || rewrite simpl_nextPC in *
            || rewrite simpl_core in *
            || rewrite simpl_machineMem in * ).
            
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

  (*
  Definition loadWordL(memL: mem wXLEN)(addr: word wXLEN): option (word wXLEN).
    clear -addr memL IsMem.
    unfold wXLEN in *.
    destruct bitwidth; apply Some.
    - exact (Memory.loadWord memL addr).
    - exact (Memory.loadDouble memL addr).
  Defined.

  Definition storeWordL(memL: mem wXLEN)(addr v: word wXLEN): option (mem wXLEN).
    clear -addr v memL IsMem.
    unfold wXLEN in *.
    destruct bitwidth; apply Some.
    - exact (Memory.storeWord memL addr v).
    - exact (Memory.storeDouble memL addr v).
  Defined.
  *)

  (* same as loadWordL but without option *)
  Definition loadWordwXLEN(memL: mem wXLEN)(addr: word wXLEN): word wXLEN.
    clear -addr memL IsMem.
    unfold wXLEN in *.
    destruct bitwidth.
    - exact (Memory.loadWord memL addr).
    - exact (Memory.loadDouble memL addr).
  Defined.
  
  (* same as storeWordL but without option *)
  Definition storeWordwXLEN(m: mem wXLEN)(a v: word wXLEN): mem wXLEN.
    unfold wXLEN, bitwidth in *.
    clear - m a v IsMem.
    destruct Bw.
    - exact (Memory.storeWord m a v).
    - exact (Memory.storeDouble m a v).
  Defined.

  Definition containsMem(memL: mem wXLEN)(memH: compiler.Memory.mem): Prop :=
    forall addr v, compiler.Memory.read_mem addr memH = Some v ->
              loadWordwXLEN memL addr = v /\ #addr + wXLEN_in_bytes <= Memory.memSize memL.

  Arguments Nat.modulo : simpl never.

  Lemma containsMem_write: forall initialL initialH finalH a v,
    containsMem initialL initialH ->
    Memory.write_mem a v initialH = Some finalH ->
    containsMem (storeWordwXLEN initialL a v) finalH.
  Proof.
    unfold containsMem, Memory.write_mem, Memory.read_mem, storeWordwXLEN,
      loadWordwXLEN, wXLEN, bitwidth in *.
    intros; destruct Bw; simpl in *;
    (destruct_one_match_hyp; [|discriminate]);
    (destruct_one_match_hyp; [|discriminate]);
    inversions H0;
    destruct_one_match_hyp.
    - inversion H1; subst; clear H1 E1.
      specialize H with (1 := E0). destruct H as [A B].
      split.
      * apply Memory.loadStoreWord_eq; try reflexivity.
        unfold Memory.valid_addr.
        auto.
      * rewrite Memory.storeWord_preserves_memSize. assumption.
    - pose proof H as G.
      specialize H with (1 := E0). destruct H as [A B].
      specialize (G addr v0).
      rewrite E in G. rewrite H1 in G. specialize (G eq_refl). destruct G as [C D].
      subst.
      destruct_one_match_hyp; try discriminate.
      split.
      * apply @Memory.loadStoreWord_ne; try congruence; unfold Memory.valid_addr; auto.
      * rewrite Memory.storeWord_preserves_memSize. assumption.
    - inversion H1; subst; clear H1 E1.
      specialize H with (1 := E0). destruct H as [A B].
      split.
      * apply Memory.loadStoreDouble_eq; try reflexivity.
        unfold Memory.valid_addr.
        auto.
      * rewrite Memory.storeDouble_preserves_memSize. assumption.
    - pose proof H as G.
      specialize H with (1 := E0). destruct H as [A B].
      specialize (G addr v0).
      rewrite E in G. rewrite H1 in G. specialize (G eq_refl). destruct G as [C D].
      subst.
      destruct_one_match_hyp; try discriminate.
      split.
      * apply @Memory.loadStoreDouble_ne; try congruence; unfold Memory.valid_addr; auto.
      * rewrite Memory.storeDouble_preserves_memSize. assumption.
  Qed.

  (* TODO might not hold if a = 0, but we only use it with a = 4 *)
  Lemma wzero_div: forall sz a, wzero sz ^/ a = wzero sz. Admitted.

  (* TODO might not hold if a = 0, but we only use it with a = 4 *)  
  Lemma mul_div_undo_word: forall {sz} (a b: word sz), a ^* b ^/ a = b. Admitted.

  Lemma let_pair_rhs_eq: forall {A B R} (c1 c2: A * B) (f: A -> B -> R),
      c1 = c2 ->
      (let (a, b) := c1 in f a b) = (let (a, b) := c2 in f a b).
  Proof. intros. subst. reflexivity. Qed.

  Lemma run1_simpl: forall {inst initialL pc0},
      containsProgram initialL.(machineMem) [[inst]] pc0 ->
      pc0 = initialL.(core).(pc) ->
      execState run1 initialL = execState (execute inst;; step) initialL.
  Proof.
    intros. subst.
    unfold run1.
    destruct_RiscvMachine initialL.
    rewrite Bind_getPC.
    simpl_RiscvMachine_get_set.
    rewrite Bind_loadWord.
    unfold containsProgram in H.
    specialize (H 0 _ eq_refl). subst inst.
    unfold ldInst.
    simpl_RiscvMachine_get_set.
    replace (initialL_pc ^+ $4 ^* $0) with initialL_pc by solve_word_eq.
    reflexivity.
  Qed. 

  (* Not sure if typechecking this ever finishes:
  Definition load_wXLEN: word wXLEN -> OState RiscvMachine (word wXLEN) :=
    match Bw with
    | Bitwidth32 => loadWord
    | Bitwidth64 => loadDouble
    end. *)

  (* not needed -- proving that loadWord or loadDouble equals load_wXLEN is too cumbersome
     to make it worth
  Definition load_wXLEN: word wXLEN -> OState RiscvMachine (word wXLEN).
    set (lw := loadWord).
    set (ld := loadDouble).
    unfold State_is_RegisterFile in *.
    unfold RiscvBitWidths in *.
    unfold wXLEN in *.
    unfold bitwidth in *.
    destruct Bw.
    - exact lw.
    - exact ld.
  Defined.
  *)

  Ltac do_get_set_Register :=
    repeat (
        rewrite? associativity;
        rewrite? left_identity;
        rewrite? right_identity;
        rewrite? Bind_getRegister by assumption;
        rewrite? Bind_getRegister0;
        rewrite? Bind_setRegister by assumption;
        rewrite? Bind_setRegister0;
        rewrite? Bind_getPC;
        rewrite? Bind_setPC
      ).

  Ltac prove_alu_def :=
    intros; clear; unfold wXLEN in *; unfold MachineWidthInst;
    destruct bitwidth; [unfold MachineWidth32 | unfold MachineWidth64]; reflexivity.

  Lemma fromImm_def: forall (a: Z),
      fromImm a = ZToWord wXLEN a.
  Proof. unfold fromImm. prove_alu_def. Qed.

  Lemma zero_def:
      zero = $0.
  Proof. unfold zero. prove_alu_def. Qed.
  
  Lemma one_def:
      one = $1.
  Proof. unfold one. prove_alu_def. Qed.
  
  Lemma add_def: forall (a b: word wXLEN),
      add a b = wplus a b.
  Proof. unfold add. prove_alu_def. Qed.
  
  Lemma sub_def: forall (a b: word wXLEN),
      sub a b = wminus a b.
  Proof. unfold sub. prove_alu_def. Qed.
  
  Lemma mul_def: forall (a b: word wXLEN),
      mul a b = wmult a b.
  Proof. unfold mul. prove_alu_def. Qed.
  
  Lemma div_def: forall (a b: word wXLEN),
      div a b = ZToWord wXLEN (wordToZ a / wordToZ b).
  Proof. unfold div. prove_alu_def. Qed.

  Lemma rem_def: forall (a b: word wXLEN),
      rem a b = ZToWord wXLEN (wordToZ a mod wordToZ b).
  Proof. unfold rem. prove_alu_def. Qed.

  Lemma signed_less_than_def: forall (a b: word wXLEN),
      signed_less_than a b = if wslt_dec a b then true else false.
  Proof. unfold signed_less_than. prove_alu_def. Qed.
  
  Lemma signed_eqb_def: forall (a b: word wXLEN),
      signed_eqb a b = weqb a b.
  Proof. unfold signed_eqb. prove_alu_def. Qed.
  
  Lemma xor_def: forall (a b: word wXLEN),
      xor a b = wxor a b.
  Proof. unfold xor. prove_alu_def. Qed.
  
  Lemma or_def: forall (a b: word wXLEN),
      or a b = wor a b.
  Proof. unfold or. prove_alu_def. Qed.
  
  Lemma and_def: forall (a b: word wXLEN),
      and a b = wand a b.
  Proof. unfold and. prove_alu_def. Qed.
  
  Lemma sll_def: forall (a: word wXLEN) (b: Z),
      sll a b = wlshift a (Z.to_nat b).
  Proof. unfold sll. prove_alu_def. Qed.
  
  Lemma srl_def: forall (a: word wXLEN) (b: Z),
      srl a b = wrshift a (Z.to_nat b).
  Proof. unfold srl. prove_alu_def. Qed.
  
  Lemma sra_def: forall (a: word wXLEN) (b: Z),
      sra a b = wrshift a (Z.to_nat b).
  Proof. unfold sra. prove_alu_def. Qed.
  
  Lemma ltu_def: forall (a b: word wXLEN),
      ltu a b = if wlt_dec a b then true else false.
  Proof. unfold ltu. prove_alu_def. Qed.
  
  Lemma divu_def: forall (a b: word wXLEN),
      divu a b = wdiv a b.
  Proof. unfold divu. prove_alu_def. Qed.

  Lemma remu_def: forall (a b: word wXLEN),
      remu a b = wmod a b.
  Proof. unfold remu. prove_alu_def. Qed.

  Ltac rewrite_alu_op_defs :=
    repeat (rewrite fromImm_def in *
            || rewrite zero_def in *
            || rewrite one_def in *
            || rewrite add_def in *
            || rewrite sub_def in *
            || rewrite mul_def in *
            || rewrite div_def in *
            || rewrite rem_def in *
            || rewrite signed_less_than_def in *
            || rewrite signed_eqb_def in *
            || rewrite xor_def in *
            || rewrite or_def in *
            || rewrite and_def in *
            || rewrite sll_def in *
            || rewrite srl_def in *
            || rewrite sra_def in *
            || rewrite ltu_def in *
            || rewrite divu_def in *
            (* missing: remu_def because it's only used for alignment checks and we prefer
               keeping it as remu *) ).

  Hint Unfold
    Nop
    Mov
    Not
    Neg
    Negw
    Sextw
    Seqz
    Snez
    Sltz
    Sgtz
    Beqz
    Bnez
    Blez
    Bgez
    Bltz
    Bgtz
    Bgt
    Ble
    Bgtu
    Bleu
    J
    Jr
  : unf_pseudo.


  (*
  Lemma list2imem_head: forall inst insts imemStart,
      (list2imem (inst :: insts) imemStart) imemStart = inst.
  Proof.
    intros.
    unfold list2imem.
    rewrite wminus_def.
    rewrite wminus_inv.
    rewrite wzero_div.
    rewrite wordToNat_wzero.
    reflexivity.
  Qed.
  *)

  (*
  Lemma list2imem_skip: forall imemStart insts0 insts1 offs pc0,
    imemStart ^+ $4 ^* $(length insts0) ^+ offs = pc0 ->
    (list2imem (insts0 ++ insts1) imemStart) pc0  =
    (list2imem insts1 imemStart) (imemStart ^+ offs).
  Proof.
    intros. subst. unfold list2imem.
    (*
    induction insts0.
    - simpl. admit.
    - simpl. rewrite <- IHinsts0.
      unfold list2imem. simpl.*)
    ring_simplify (imemStart ^+ $ (4) ^* $ (length insts0) ^+ offs ^- imemStart).
    ring_simplify (imemStart ^+ offs ^- imemStart).
    (*
    rewrite wminus_def.
    rewrite wplus_comm.
    rewrite? wplus_assoc.
    rewrite (wplus_comm (^~ imemStart) imemStart).
    rewrite wminus_inv.
    rewrite wplus_unit.
    rewrite wminus_def.
    rewrite (wplus_comm imemStart).
    rewrite <- wplus_assoc.
    rewrite wminus_inv.
    rewrite <- (wplus_comm (wzero wXLEN)).
    rewrite wplus_unit.
    replace ((($4 ^* $ (length insts0) ^+ offs) ^/ $4)) with
        ($ (length insts0) ^+ (offs ^/ $4)) by admit.
    *)
    
    Abort.

  Definition wnth{A}{sz}(n: word sz)(l: list A)(default: A): A. Admitted.

  Definition wlength{A}{sz}(l: list A): word sz. Admitted.
  
  (*
  Lemma wnth_app_2:
    wnth (a ^+ b) (insts0 ++ insts1) InvalidInstruction =
  *)
  Definition list2imem'(l: list Instruction)(offset: word wXLEN): InstructionMem :=
    fun addr => wnth (wdiv (addr ^- offset) $4) l InvalidInstruction.

  Lemma list2imem_skip: forall imemStart insts0 insts1 offs pc0,
    imemStart ^+ $4 ^* (wlength insts0) ^+ offs = pc0 ->
    (list2imem' (insts0 ++ insts1) imemStart) pc0  =
    (list2imem' insts1 imemStart) (imemStart ^+ offs).
  Proof.
    intros. unfold list2imem'. subst pc0.
    rewrite wminus_def.
    rewrite wplus_comm.
    rewrite? wplus_assoc.
    rewrite (wplus_comm (^~ imemStart) imemStart).
    rewrite wminus_inv.
    rewrite wplus_unit.
    rewrite wminus_def.
    rewrite (wplus_comm imemStart).
    rewrite <- wplus_assoc.
    rewrite wminus_inv.
    rewrite <- (wplus_comm (wzero wXLEN)).
    rewrite wplus_unit.
    replace ((($4 ^* (wlength insts0) ^+ offs) ^/ $4)) with
        ((wlength insts0) ^+ (offs ^/ $4)) by admit.
    (* does not hold without additional size constraint assumption! *)

    (*
    rewrite app_nth2. (* stupid overflow of offs possible! *)
     *)
  Abort.
  
  Lemma list2imem_skip: forall imemStart insts0 insts1 offs pc0,
    imemStart ^+ $4 ^* $(length insts0) ^+ $4 ^* $offs = pc0 ->
    (list2imem (insts0 ++ insts1) imemStart) pc0  =
    (list2imem insts1 imemStart) (imemStart ^+ $4 ^* $offs).
  Proof.
    intros. subst.
    unfold list2imem.
    rewrite wminus_def.
    rewrite wplus_comm.
    rewrite? wplus_assoc.
    rewrite (wplus_comm (^~ imemStart) imemStart).
    rewrite wminus_inv.
    rewrite wplus_unit. rewrite app_nth2. (* stupid overflow of offs possible! *)

(* how to simplify this?:
    
list2imem
    (instsBefore ++
     (compile_stmt s1 ++
      Beq cond Register0
        (Z.pos (Pos.of_succ_nat (length (compile_stmt s2) + S (length (compile_stmt s2) + 0))))
      :: compile_stmt s2 ++
         [[Jal Register0
             (Z.neg
                (Pos.succ
                   (Pos.of_succ_nat
                      (length (compile_stmt s1) + length (compile_stmt s2) +
                       S (S (length (compile_stmt s1) + length (compile_stmt s2) + 0))))))]]) ++
     instsAfter) imemStart
    (imemStart ^+ $ (4) ^* $ (length instsBefore) ^+ $ (4) ^* $ (length (compile_stmt s1)))
 *)
 *)

  Arguments mult: simpl never.
  Arguments run1: simpl never.

  Lemma remu40_mod40: forall a,
      #a mod 4 = 0 ->
      remu a four = $0.
  Proof.
    intros.
    rewrite remu_def.
    unfold four, two. rewrite one_def. rewrite? add_def.
    rewrite <-? natToWord_plus. simpl.
    replace 4 with (# (natToWord wXLEN 4)) in H.
    - rewrite <- wordToNat_mod in H.
      + apply wordToNat_inj.
        rewrite H. symmetry. apply roundTrip_0.
      + intro. apply natToWord_inj in H0; [discriminate|clear..];
                 unfold wXLEN, bitwidth; destruct Bw; simpl; omega.
    - apply wordToNat_natToWord_idempotent'.
      clear; unfold wXLEN, bitwidth; destruct Bw; simpl; omega.
  Qed.

  Hypothesis translate_id_if_aligned_4: forall a mode,
      (wordToNat a) mod 4 = 0 ->
      translate mode four a = Return a.

  Hypothesis translate_id_if_aligned_8: forall a mode,
      (wordToNat a) mod 8 = 0 ->
      translate mode eight a = Return a.

  (* requires destructed RiscvMachine and containsProgram *)
  Ltac fetch_inst :=
      match goal with
      | Cp: containsProgram _ [[?inst]] ?pc0 |- runsTo _ _ ?E _ =>
        match E with
        | execState run1 ?initialL =>
          let Eqpc := fresh in
          assert (pc0 = initialL.(core).(pc)) as Eqpc by solve_word_eq;
            replace E with (execState (execute inst;; step) initialL) by
              (symmetry; eapply run1_simpl; [ exact Cp | exact Eqpc ]);
            clear Eqpc
        end
      end.

  Ltac rewrite_reg_value :=
    match goal with
    | |- context [getReg _ _] => idtac
    | _ => fail 1 "wrong shape of goal"
    end;
    let G1 := fresh "G1" in
    match goal with
    | G2: get ?st2 ?x = ?v, E: extends ?st1 ?st2 |- context [@getReg ?RF ?R ?V ?TC ?st1 ?x] =>
      let gg := constr:(@getReg RF R V TC st1 x) in
      let gg' := eval unfold getReg, State_is_RegisterFile in gg in
      progress change gg with gg';
      match gg' with
      | match ?gg'' with | _ => _ end => assert (G1: gg'' = v) by (clear -G2 E; state_calc)
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
  
  Inductive AllInsts: list Instruction -> Prop :=
    mkAllInsts: forall l, AllInsts l.

  Ltac solve_valid_registers :=
    match goal with
    | |- valid_registers _ => solve [simpl; auto]
    end.

  Ltac solve_imem_old :=
    repeat match goal with
           (* by doing an explicit match, we make sure (?a ++ ?b) is not unified with
                an evar in an infinite loop *)
           | |- context [(?a ++ ?b) ++ ?c] => rewrite <- (app_assoc a b c)
           end;
    reflexivity.

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
    forall {initialMem finalMem: Memory.mem} {a0 w: word wXLEN},
      Memory.write_mem a0 w initialMem = Some finalMem ->
      forall a, Memory.read_mem a initialMem = None <-> Memory.read_mem a finalMem = None.
  Proof.
    intros. unfold Memory.write_mem in *.
    destruct_one_match_hyp; [|discriminate].
    inversions H.
    unfold Memory.read_mem in *.
    split; intros.
    - repeat destruct_one_match. subst.
      + rewrite E0 in E. rewrite E in H. discriminate.
      + assumption.
      + reflexivity.
    - repeat destruct_one_match_hyp; subst; reflexivity || discriminate || assumption.
  Qed.

  Lemma mem_accessibility_trans:
    forall {initialMem middleMem finalMem: Memory.mem} {a: word wXLEN},
      (Memory.read_mem a initialMem = None <-> Memory.read_mem a middleMem = None) ->
      (Memory.read_mem a middleMem  = None <-> Memory.read_mem a finalMem  = None) ->
      (Memory.read_mem a initialMem = None <-> Memory.read_mem a finalMem  = None).
  Proof. intros. tauto. Qed.
  
  Lemma eval_stmt_preserves_mem_accessibility:  forall {fuel: nat} {initialMem finalMem: Memory.mem}
      {s: @stmt Bw TestFlatImp.ZName} {initialRegs finalRegs: state},
      eval_stmt fuel initialRegs initialMem s = Some (finalRegs, finalMem) ->
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
  Qed.

  Lemma eval_stmt_preserves_mem_inaccessible: forall {fuel: nat} {initialMem finalMem: Memory.mem}
      {s: @stmt Bw TestFlatImp.ZName} {initialRegs finalRegs: state},
      eval_stmt fuel initialRegs initialMem s = Some (finalRegs, finalMem) ->
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
    | |- remu _ four = $0 => idtac
    | |- $0 = remu _ four => idtac
    | _ => fail 1 "wrong shape of goal"
    end;
    rewrite <-? (Z.mul_comm 4);
    rewrite? ZToWord_mult;
    rewrite? Z4four;                                    
    rewrite? remu_four_distrib_plus;
    rewrite? remu_four_undo;
    rewrite? remu_four_four;
    repeat match goal with
           | H: _ |- _ => apply remu40_mod40 in H; rewrite H
           end;
    rewrite? wplus_unit;
    reflexivity.

  Ltac solve_mem_inaccessible :=
    eapply eval_stmt_preserves_mem_inaccessible; [|eassumption];
    try eassumption;
    let Eq := fresh "Eq" in
    match goal with
    | E1: eval_stmt ?f ?r1 ?m1 ?s1 = Some (?r2, ?m2),
      E2: eval_stmt ?f ?r2 ?m2 ?s2 = Some (?r3, ?m3)
      |-   eval_stmt _ _ ?m1 _ = Some (_, ?m3)
      => assert (eval_stmt (S f) r1 m1 (SSeq s1 s2) = Some (r3, m3)) as Eq
          by (simpl; rewrite E1; exact E2); exact Eq
    end.

  Ltac spec_IH originalIH IH stmt1 :=
    pose proof originalIH as IH;
    match goal with
    | |- runsTo _ _ ?st _ => specialize IH with (initialL := st); simpl in IH
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
    | |- context [weqb ?r ?expectZero] =>
      match expectZero with
      | $0 => idtac
      end;
      match r with
      | remu ?a four => replace r with expectZero by prove_remu_four_zero
      end
    end;
    rewrite weqb_eq by reflexivity;
    simpl.

  Lemma elim_then_true_else_false: forall P Q (c: {P} + {Q}) A (v1 v2: A),
      (if if c then true else false then v1 else v2)
      = (if c then v1 else v2).
  Proof.
    intros. destruct c; reflexivity.
  Qed.

  Ltac run1step' :=
    apply runsToStep;
    simpl in *; subst *;
    fetch_inst;
    autounfold with unf_pseudo in *;
    cbn [execute ExecuteI.execute ExecuteM.execute ExecuteI64.execute ExecuteM64.execute];
    repeat (
        do_get_set_Register || 
        simpl_RiscvMachine_get_set ||
        rewrite_reg_value ||
        rewrite_getReg ||
        rewrite_setReg ||
        rewrite_alu_op_defs ||
        (rewrite weqb_ne by congruence) ||
        (rewrite weqb_eq by congruence) ||
        rewrite elim_then_true_else_false ||
        rewrite left_identity ||
        simpl_remu4_test ||
        rewrite put_put_same ||
        rewrite get_put_same).

  Ltac run1step :=
    run1step';
    rewrite execState_step;
    simpl_RiscvMachine_get_set.

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

  (* TODO it seems we need this inside proofs where we destructed Bw, how can we make
     typeclass search work there? *)
  Tactic Notation "myrewrite" uconstr(c) "by" tactic3(t) :=
    (unshelve erewrite c by t;
      [ ( apply State_is_RegisterFile || typeclasses eauto ) .. | ]).

  Tactic Notation "myrewrite" uconstr(c) :=
    (unshelve erewrite c;
      [ ( apply State_is_RegisterFile || typeclasses eauto ) .. | ]).

  Lemma execute_load: forall {A: Type} (x a: Register) (addr v: word wXLEN) (initialMH: Memory.mem)
           (f:unit -> OState RiscvMachine A) (initialL: RiscvMachine) initialRegsH,
      valid_register x ->
      valid_register a ->
      Memory.read_mem addr initialMH = Some v ->
      containsMem initialL.(machineMem) initialMH ->
      get initialRegsH a = Some addr ->
      extends initialL.(core).(registers) initialRegsH ->
      execState (Bind (execute (LwXLEN x a 0)) f) initialL =
      execState (f tt) (with_registers (setReg initialL.(core).(registers) x v) initialL).
  Proof.
    intros.
    unfold containsMem, Memory.read_mem, wXLEN_in_bytes, wXLEN, bitwidth in *.
    unfold LwXLEN, bitwidth, loadWordwXLEN in *.
    destruct Bw eqn: EBw;
      simpl in H2;
      specialize H2 with (1 := H1);
      (destruct_one_match_hyp; [|discriminate]);
      simpl in H2; inversions H2;
      cbn [execute ExecuteI.execute ExecuteM.execute ExecuteI64.execute ExecuteM64.execute];
      rewrite associativity;    
      (unshelve erewrite @Bind_getRegister;
      [ apply State_is_RegisterFile
      | idtac
      | typeclasses eauto
      | assumption ]);
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
        [ (erewrite @Bind_loadWord;   [ | typeclasses eauto ]) |
          (erewrite @Bind_loadDouble; [ | typeclasses eauto ]) ];
        (unshelve erewrite @Bind_setRegister;
        [ apply State_is_RegisterFile
        | reflexivity
        | typeclasses eauto
        | assumption ]).
  Qed.

  (*
  Lemma execute_load_from_imem: forall {A: Type} (x a: Register) (addr1 addr2 v: word wXLEN)
           (offset: Z) (f:unit -> OState RiscvMachine A) (initialL: RiscvMachine),
      valid_register x ->
      valid_register a ->
      containsProgram initialL.(machineMem) (embed_word v) addr2 ->
      getReg initialL.(core).(registers) a = addr1 ->
      addr1 ^+ ZToWord wXLEN offset = addr2 ->
      (wordToZ (addr1 ^+ ZToWord wXLEN offset) mod (Z.of_nat wXLEN_in_bytes))%Z = 0%Z ->
      execState (Bind (execute (LwXLEN x a offset)) f) initialL =
      execState (f tt) (with_registers (setReg initialL.(core).(registers) x v) initialL).
  Proof.
    intros.
    rewrite containsProgram_alt in *.
    unfold containsProgram', ldInst, Memory.read_mem, wXLEN_in_bytes in *.
    unfold LwXLEN, embed_word, wXLEN_to_word_list, bitwidth in *.
    destruct Bw eqn: EBw;
      cbn [execute ExecuteI.execute ExecuteM.execute ExecuteI64.execute ExecuteM64.execute];
      rewrite associativity;
      (myrewrite Bind_getRegister by assumption);
      rewrite associativity;
      unfold add, fromImm, MachineWidthInst, bitwidth, MachineWidth32, MachineWidth64;
      rewrite H2;
      [ rewrite translate_id_if_aligned_4 by assumption |
        rewrite translate_id_if_aligned_8 by assumption ];
        rewrite left_identity;
        rewrite associativity;
        [ (erewrite @Bind_loadWord;   [ | typeclasses eauto ]) |
          (erewrite @Bind_loadDouble; [ | typeclasses eauto ]) ];
        (unshelve erewrite @Bind_setRegister;
        [ apply State_is_RegisterFile
        | repeat f_equal
        | typeclasses eauto
        | assumption ]).
    - simpl in H1. specialize (H1 0 _ eq_refl).
      simpl in H1.
      unfold int32ToReg, encode, encode_Invalid, id in *.
      apply wordToZ_inj in H1.
      subst.
      simpl.
      rewrite wmult_neut_r.
      rewrite <- (wplus_comm $0).
      rewrite wplus_unit.
      reflexivity.
    - pose proof (H1 0 _ eq_refl) as W1.
      pose proof (H1 1 _ eq_refl) as W2.
      clear H1.
      unfold int32ToReg, encode, apply_InstructionMapper, id in *.
      unfold map_Invalid, Encoder, encode_Invalid, id in *.
      apply wordToZ_inj in W1.
      apply wordToZ_inj in W2.
      unfold wXLEN, bitwidth in *.
      subst.
      simpl.
      rewrite wmult_neut_r in W1.
      rewrite <- (wplus_comm $0) in W1.
      rewrite wplus_unit in W1.
      rewrite wmult_unit_r in W2.
      (* TODO we also need a lemma about how loadDouble is related to loadWord! *)
      (* unfold read_double. *)
      unfold getReg, State_is_RegisterFile in *.
      unfold wXLEN, bitwidth in *.
      rewrite <- W1.
      rewrite <- W2.
      clear.
      apply (Word.combine_split 32 32 v).
  Abort.
  *)
      
  Lemma execute_store: forall {A: Type} (ra rv: Register) (a v: word wXLEN)
                         (initialMH finalMH: Memory.mem)
                         (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine) initialRegsH,
      valid_register ra ->
      valid_register rv ->
      Memory.write_mem a v initialMH = Some finalMH ->
      containsMem initialL.(machineMem) initialMH ->
      get initialRegsH ra = Some a ->
      get initialRegsH rv = Some v ->
      extends initialL.(core).(registers) initialRegsH ->
      execState (Bind (execute (SwXLEN ra rv 0)) f) initialL =
      execState (f tt) (with_machineMem (storeWordwXLEN initialL.(machineMem) a v) initialL).
  Proof.
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
      myrewrite Bind_getRegister by assumption;
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
      (erewrite @Bind_getRegister; [|typeclasses eauto|assumption]);
      [ (erewrite @Bind_storeWord; [|typeclasses eauto]) |
        (erewrite @Bind_storeDouble; [|typeclasses eauto]) ];
      rewrite_reg_value;
      reflexivity.
  Qed.   
  
  Arguments Bind: simpl never.
  Arguments Return: simpl never.
  Arguments app: simpl never. (* don't simpl ([[ oneInst ]] ++ rest) into oneInst :: rest
    because otherwise solve_imem doesn't recognize "middle" any more *)

  (* otherwise simpl takes forever: *)
  Arguments split1: simpl never.
  Arguments split2: simpl never.
  Arguments ZToWord: simpl never.

  (* Note: alignment refers to addr, not to the range *)
  Definition in_range{w: nat}(addr: word w)(alignment start size: nat): Prop :=
    start <= wordToNat addr /\ wordToNat addr + alignment <= start + size /\ wordToNat addr mod alignment = 0.
  
  Definition not_in_range{w: nat}(addr: word w)(alignment start size: nat): Prop :=
    wordToNat addr + alignment <= start \/ start + size <= wordToNat addr.

  Lemma loadWord_storeDouble_ne': forall m (a1 a2: word wXLEN) (v : word 64),
      in_range a1 8 0 (Memory.memSize m) ->
      in_range a2 4 0 (Memory.memSize m) ->
      not_in_range a2 4 #a1 8 -> (* a2 (4 bytes big) is not in the 8-byte range starting at a1 *)
      Memory.loadWord (Memory.storeDouble m a1 v) a2 = Memory.loadWord m a2.
  Proof.
    intros.
    pose proof (Memory.memSize_bound m).
    apply Memory.loadWord_storeDouble_ne;
      unfold in_range, not_in_range, Memory.valid_addr in *;
      simpl in *;
      intuition (subst; try omega);
      rewrite (wordToNat_wplus' a1 $4) in H6; rewrite wordToNat_natToWord_idempotent' in *; try omega. 
  Qed.

  Lemma in_range0_valid_addr: forall (sz: nat) (a: word sz) al l,
      in_range a al 0 l ->
      Memory.valid_addr a al l.
  Proof.
    unfold in_range, Memory.valid_addr. intuition idtac.
  Qed.
  
  Lemma store_preserves_containsProgram: forall initialL_mem insts imemStart a v,
      containsProgram initialL_mem insts imemStart ->
      not_in_range a wXLEN_in_bytes #imemStart (4 * (length insts)) ->
      in_range a wXLEN_in_bytes 0 (Memory.memSize initialL_mem) ->
      (* better than using $4 ^* imemStart because that prevents overflow *)
      #imemStart mod 4 = 0 -> 
      containsProgram (storeWordwXLEN initialL_mem a v) insts imemStart.
  Proof.
    rewrite containsProgram_alt. (* <-- TODO do we still need that? *)
    unfold containsProgram2.
    intros. rename H2 into A. destruct H.
    clear -H H0 H1 H2 A.
    assert (forall (a: word wXLEN), a = a ^+ $ (4) ^- $ (4)) as helper4 by (intros; solve_word_eq).
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
      rewrite Memory.loadWord_storeDouble_ne; try assumption.
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
      + intro C. rename H0 into R.
        unfold not_in_range in *.
        destruct R as [R | R].
        * replace (#a + 8) with (#(a ^+ $4) + 4) in R.
          { rewrite <- C in R. rewrite wordToNat_wplus' in R; omega. }
          { rewrite wordToNat_wplus'.
            - rewrite wordToNat_natToWord_idempotent'; omega.
            - clear D. (* otherwise omega takes too long *)
              rewrite wordToNat_natToWord_idempotent'; omega.
          }
        * unfold Memory.valid_addr in *.
          assert (a = imemStart ^+ $(4*i) ^- $4) as E. {
            rewrite C. apply helper4.
          }
          clear C.
          subst a.
          clear -R H1 F.
          admit. (* TODO! *)
  Admitted.

  (*
  Lemma store_preserves_containsProgram: forall initialL_mem insts imemStart a v,
      containsProgram initialL_mem insts ($4 ^* imemStart) ->
      ~ #($4 ^* imemStart) <= #a < #($4 ^* imemStart) + 4 * (length insts) ->
      Memory.valid_addr a wXLEN_in_bytes (Memory.memSize initialL_mem) ->
      (forall i, i < length insts ->
            Memory.valid_addr ($4 ^* imemStart ^+ $4 ^* $i) 4 (Memory.memSize initialL_mem)) ->
      containsProgram (storeWordwXLEN initialL_mem a v) insts ($4 ^* imemStart).
  Proof.
    unfold containsProgram.
    intros.
    clear -H H0 H1 H2 H3.
    unfold storeWordwXLEN, ldInst, wXLEN_in_bytes, wXLEN, bitwidth in *;
      destruct Bw; simpl in *;
        rewrite? Memory.storeWord_preserves_memSize;
        rewrite? Memory.storeDouble_preserves_memSize;
        try assumption;
        specialize H with (1 := H3).
    - pose proof (Memory.memSize_bound initialL_mem) as B.
      assert (nth_error insts i <> None) as F by congruence.
      apply nth_error_Some in F.
      pose proof (@wordToNat_natToWord_idempotent' 32 (4 * i)) as D.
      pose proof H2 as H2'.
      specialize H2 with (1 := F).
      rewrite Memory.loadStoreWord_ne; try assumption.
      intro C. subst a. apply H0.
      destruct insts as [|inst0 insts]; simpl in F; [omega|].
      specialize (H2' (length insts)).
      unfold Memory.valid_addr in H2'. destruct H2' as [F1 F2]; [ simpl; omega | ].
      unfold Memory.valid_addr in H2. destruct H2 as [F3 F4].
      rewrite wordToNat_plus.
      * split; try omega. (* F3 (from additional hyp) is useless because overflow
        could have happened there too *)
  Abort.
  
  Lemma store_preserves_containsProgram: forall initialL_mem insts imemStart a v,
      containsProgram initialL_mem insts $(4 * imemStart) ->
      ~ 4 * imemStart <= #a < 4 * imemStart + 4 * (length insts) ->
      Memory.valid_addr a wXLEN_in_bytes (Memory.memSize initialL_mem) ->
      containsProgram (storeWordwXLEN initialL_mem a v) insts $(4 * imemStart).
  Proof.
    rewrite containsProgram_alt.
    unfold containsProgram2.
    intros. destruct H.
    clear -H H0 H1 H2.
    unfold storeWordwXLEN, ldInst, wXLEN_in_bytes, wXLEN, bitwidth in *;
      destruct Bw;
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
        * rewrite wordToNat_plus; omega.
        * rewrite wordToNat_plus by omega.
          rewrite D by omega.
          rewrite wordToNat_natToWord_idempotent'.
          { rewrite Nat.add_mod by omega.
            rewrite Nat.mul_comm. rewrite Nat.mod_mul by omega.
            rewrite Nat.mul_comm. rewrite Nat.mod_mul by omega.
            reflexivity. }
          { unfold pow2. 
           (* "$4 ^* imemStart" could overflow, H still not strong enough,
              because after (4 * imemStart), it is still converted to word and then back to
              nat *) 
  Abort.
    
  Lemma store_preserves_containsProgram: forall initialL_mem insts imemStart a v,
      containsProgram initialL_mem insts ($4 ^* imemStart) ->
      ~ #($4 ^* imemStart) <= #a < #($4 ^* imemStart) + 4 * (length insts) ->
      Memory.valid_addr a wXLEN_in_bytes (Memory.memSize initialL_mem) ->
      containsProgram (storeWordwXLEN initialL_mem a v) insts ($4 ^* imemStart).
  Proof.
    rewrite containsProgram_alt.
    unfold containsProgram2.
    intros. destruct H.
    clear -H H0 H1 H2.
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
        * rewrite wordToNat_plus; omega.
        * rewrite wordToNat_plus by omega.
          rewrite D by omega.
          rewrite wordToNat_mult.
          { rewrite wordToNat_natToWord_idempotent'.
            - rewrite Nat.add_mod by omega.
              rewrite Nat.mul_comm. rewrite Nat.mod_mul by omega.
              rewrite Nat.mul_comm. rewrite Nat.mod_mul by omega.
              reflexivity.
            - unfold pow2. omega. }
          { (* "$4 ^* imemStart" could overflow! *) admit. }
      + intro C. subst a. apply H0.
        rewrite wordToNat_plus; omega.
    -
  Admitted.
  *)

  (*
  Lemma store_preserves_containsProgram: forall initialL_mem insts imemAddr a v,
      containsProgram initialL_mem insts imemAddr ->
      ~ ((imemAddr <= a)%word /\ (a < imemAddr ^+ $4 ^* $(length insts))%word) ->
      Memory.valid_addr a wXLEN_in_bytes (Memory.memSize initialL_mem) ->
      containsProgram (storeWordwXLEN initialL_mem a v) insts imemAddr.
  Proof.
    intros.
  Admitted.

  Lemma mem_inaccessible_read:  forall a v initialMH start eend,
      Memory.read_mem a initialMH = Some v ->
      mem_inaccessible initialMH start eend ->
      ~ ((start <= a)%word /\ (a < eend)%word).
  Proof.
    intros. unfold mem_inaccessible in *.
    intros [P Q].
    specialize (H0 _ P Q).
    congruence.
  Qed.
  *)
  
  Lemma mem_inaccessible_write:  forall a v initialMH finalMH start len,
      Memory.write_mem a v initialMH = Some finalMH ->
      mem_inaccessible initialMH start len ->
      ~ #start <= #a < #start + len.
  Proof.
    intros. unfold Memory.write_mem, mem_inaccessible in *.
    destruct_one_match_hyp; [|discriminate].
    eapply H0. eassumption.
  Qed.

  Lemma read_mem_valid_addr: forall a0 initialMH initialML w,
      Memory.read_mem a0 initialMH = Some w ->
      containsMem initialML initialMH ->
      Memory.valid_addr a0 wXLEN_in_bytes (Memory.memSize initialML).
  Proof.
    intros. unfold Memory.valid_addr, containsMem in *.
    specialize H0 with (1 := H). destruct H0 as [A B].
    unfold Memory.read_mem in *.
    destruct_one_match_hyp; try discriminate.
    auto.
  Qed.

  Lemma write_mem_valid_addr: forall a0 v0 initialMH finalMH initialML,
      Memory.write_mem a0 v0 initialMH = Some finalMH ->
      containsMem initialML initialMH ->
      Memory.valid_addr a0 wXLEN_in_bytes (Memory.memSize initialML).
  Proof.
    intros. unfold Memory.write_mem in *.
    destruct_one_match_hyp; try discriminate.
    inversion H. clear H. subst finalMH.
    eapply read_mem_valid_addr; eassumption.
  Qed.
  
  Lemma compile_stmt_correct_aux:
    forall allInsts imemStart fuelH s insts initialH  initialMH finalH finalMH initialL
      instsBefore instsAfter,
    compile_stmt s = insts ->
    allInsts = instsBefore ++ insts ++ instsAfter ->  
    stmt_not_too_big s ->
    valid_registers s ->
    #imemStart mod 4 = 0 ->
    eval_stmt fuelH initialH initialMH s = Some (finalH, finalMH) ->
    extends initialL.(core).(registers) initialH ->
    containsMem initialL.(machineMem) initialMH ->
    containsProgram initialL.(machineMem) allInsts imemStart ->
    initialL.(core).(pc) = imemStart ^+ $4 ^* $(length instsBefore) ->
    initialL.(core).(nextPC) = initialL.(core).(pc) ^+ $4 ->
    mem_inaccessible initialMH imemStart (4 * length allInsts) ->
    runsToSatisfying initialL (fun finalL =>
       extends finalL.(core).(registers) finalH /\
       containsMem finalL.(machineMem) finalMH /\
       containsProgram finalL.(machineMem) allInsts imemStart /\
       finalL.(core).(pc) = initialL.(core).(pc) ^+ $ (4) ^* $ (length insts) /\
       finalL.(core).(nextPC) = finalL.(core).(pc) ^+ $4).
  Proof.
    intros allInsts imemStart. pose proof (mkAllInsts allInsts).
    induction fuelH; [intros; discriminate |].
    intros.
    unfold runsToSatisfying in *.
    invert_eval_stmt;
      try match goal with
          | o: binop |- _ => destruct o (* do this before destruct_containsProgram *)
          end;
      simpl in *; unfold compile_lit, compile_lit_rec in *;
      destruct_everything.
    - (* SLoad *)
      clear IHfuelH.
      apply runsToStep; simpl in *; subst *.
      fetch_inst.
      erewrite execute_load; [|eassumption..].
      simpl_RiscvMachine_get_set.
      simpl.
      rewrite execState_step.
      simpl_RiscvMachine_get_set.
      run1done.
    - (* SStore *)
      clear IHfuelH.
      apply runsToStep; simpl in *; subst *.
      fetch_inst.
      erewrite execute_store; [|eassumption..].
      simpl_RiscvMachine_get_set.
      rewrite execState_step.
      simpl_RiscvMachine_get_set.
      run1done.
      apply store_preserves_containsProgram.
      + solve_containsProgram.
      + eapply mem_inaccessible_write; eassumption.
      + eapply write_mem_valid_addr; eassumption.
      + assumption.
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
      match goal with
      | E: Some _ = Some _ |- _ => rewrite <- E
      end.
      f_equal.
      clear.
      change (Pos.to_nat 8) with 8.
      rewrite? wlshift_distr_plus.
      rewrite? wlshift_iter.
      simpl.
      change 56%nat with (Z.to_nat 56).
      change 48%nat with (Z.to_nat 48).
      change 40%nat with (Z.to_nat 40).
      change 32%nat with (Z.to_nat 32).
      change 24%nat with (Z.to_nat 24).
      change 16%nat with (Z.to_nat 16).
      change 8%nat with (Z.to_nat 8).
      rewrite <-? wplus_assoc.
      change 16%Z with ( 8+8)%Z at 3. rewrite wlshift_bitSlice_plus. change ( 8+8)%Z with 16%Z.
      change 24%Z with (16+8)%Z at 3. rewrite wlshift_bitSlice_plus. change (16+8)%Z with 24%Z.
      change 32%Z with (24+8)%Z at 3. rewrite wlshift_bitSlice_plus. change (24+8)%Z with 32%Z.
      change 40%Z with (32+8)%Z at 3. rewrite wlshift_bitSlice_plus. change (32+8)%Z with 40%Z.
      change 48%Z with (40+8)%Z at 3. rewrite wlshift_bitSlice_plus. change (40+8)%Z with 48%Z.
      change 56%Z with (48+8)%Z at 4. rewrite wlshift_bitSlice_plus. change (48+8)%Z with 56%Z.
      change 64%Z with (56+8)%Z at 1. rewrite wlshift_bitSlice_plus. change (56+8)%Z with 64%Z.
      rewrite wlshift_zero.
      rewrite wplus_unit.
      rewrite bitSlice_wordToZ_all; [ apply ZToWord_wordToZ | ].
      clear.
      unfold wXLEN, bitwidth. destruct Bw; cbv; omega.
      (* SOp *)
    - run1step. run1done.
    - run1step. run1done.
    - run1step. run1done.
    - run1step. run1step. run1done.
      replace (ZToWord wXLEN 1) with (natToWord wXLEN 1).
      + rewrite reduce_eq_to_sub_and_lt.
        assumption.
      + change 1%Z with (Z.of_nat 1). rewrite ZToWord_Z_of_nat. reflexivity.
    - run1step. run1done.
    - run1step. run1done.

    - (* SSet *)
      clear IHfuelH.
      run1step.
      run1done.
      rewrite wplus_unit.
      assumption.
    - (* SIf/Then *)
      (* branch if cond = 0 (will not branch) *)
      run1step.
      (* use IH for then-branch *)
      spec_IH IHfuelH IH s1.
      apply (runsToSatisfying_trans _ _ _ _ _ IH). clear IH.
      (* jump over else-branch *)
      intros.
      destruct_everything.
      run1step.
      run1done.
    - (* SIf/Else *)
      (* branch if cond = 0 (will  branch) *)
      run1step.
      (* use IH for else-branch *)
      spec_IH IHfuelH IH s2.
      IH_done IH.

    - (* SLoop/done *)
      (* We still have to run part 1 of the loop body which is before the break *)
      spec_IH IHfuelH IH s1.
      apply (runsToSatisfying_trans _ _ _ _ _ IH). clear IH.
      intros.
      destruct_everything.
      run1step.
      run1done.

    - (* SLoop/again *)
      (* 1st application of IH: part 1 of loop body *)
      spec_IH IHfuelH IH s1.
      apply (runsToSatisfying_trans _ _ _ _ _ IH). clear IH.
      intros.
      destruct_everything.
      run1step.

      (* 2nd application of IH: part 2 of loop body *)      
      spec_IH IHfuelH IH s2.
      apply (runsToSatisfying_trans _ _ _ _ _ IH). clear IH.
      intros.
      destruct_everything.
      run1step.
      
      (* 3rd application of IH: run the whole loop again *)
      spec_IH IHfuelH IH (SLoop s1 cond s2).
      IH_done IH.
      
    - (* SSeq *)
      spec_IH IHfuelH IH s1.
      apply (runsToSatisfying_trans _ _ _ _ _ IH). clear IH.
      intros.
      destruct_everything.
      spec_IH IHfuelH IH s2.
      IH_done IH.
    - (* SSkip *)
      run1done.
  Admitted.

  (*
  Lemma every_state_contains_empty_state: forall s,
    containsState s empty.
  Proof.
    unfold containsState.
    intros. rewrite empty_is_empty in H. discriminate.
  Qed.

  Definition evalL(fuel: nat)(insts: list Instruction)(initial: RiscvMachine): RiscvMachine :=
    execState (run fuel) (putProgram insts initial).

  Lemma putProgram_containsProgram: forall p initial,
    4 * (length p) < pow2 wXLEN ->
    containsProgram (putProgram p initial) p (pc (putProgram p initial)).
  Proof.
    intros. unfold containsProgram, putProgram.
    intros.
    destruct initial as [imem regs pc0 eh].
    cbv [pc instructionMem]. apply nth_error_nth.
    match goal with
    | H: nth_error _ ?i1 = _ |- nth_error _ ?i2 = _ => replace i2 with i1; [assumption|]
    end.
    rewrite wplus_unit.
    rewrite <- natToWord_mult.
    rewrite wordToNat_natToWord_idempotent'.
    - symmetry. apply mul_div_undo. auto.
    - assert (i < length p). {
        apply nth_error_Some. intro. congruence.
      }
      omega.
  Qed.

  Lemma compile_stmt_correct: forall fuelH finalH s insts initialL,
    stmt_size s * 16 < pow2 wimm ->
    compile_stmt s = insts ->
    evalH fuelH empty s = Success finalH ->
    exists fuelL,
      forall resVar res,
      get finalH resVar = Some res ->
      (evalL fuelL insts initialL).(registers) resVar = res.
  Proof.
    introv B C E.
    pose proof runsToSatisfying_exists_fuel_old as Q.
    specialize (Q (putProgram insts initialL)
      (fun finalL => forall resVar res,
       get finalH resVar = Some res ->
       finalL.(registers) resVar = res)).
    cbv beta in Q.
    apply Q; clear Q.
    eapply runsToSatisfying_imp.
    - eapply @compile_stmt_correct_aux with (s := s) (initialH := empty)
        (fuelH := fuelH) (finalH := finalH).
      + reflexivity.
      + assumption.
      + apply E.
      + subst insts. apply putProgram_containsProgram.
        change (stmt_not_too_big s) in B.
        assert (2 * pow2 wimm < pow2 wXLEN). {
          clear. destruct Bw. unfold RiscvBitWidths.wimm, RiscvBitWidths.wXLEN.
          destruct wXLEN; [omega|].
          simpl_pow2.
          pose proof (@pow2_inc wimm wXLEN).
          omega.
        }
        solve_length_compile_stmt.
      + apply every_state_contains_empty_state.
      + reflexivity.
    - intros.
      simpl in H. apply proj1 in H.
      unfold containsState in H.
      specialize (H resVar).
      destruct (Common.get finalH resVar) eqn: Q.
      + specialize (H _ eq_refl).
        simpl in Q. unfold id in Q. simpl in *. congruence.
      + discriminate.
  Qed.
  *)

End FlatToRiscv.
