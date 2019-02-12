Require Import lib.LibTacticsMin.
Require Import riscv.util.Monads. Require Import riscv.util.MonadNotations.
Require Import coqutil.Macros.unique.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Program.
Require Import riscv.Decode.
Require Import riscv.PseudoInstructions.
Require Import riscv.RiscvMachine.
Require Import riscv.Execute.
Require Import riscv.Run.
Require Import riscv.Memory.
Require Import riscv.util.PowerFunc.
Require Import riscv.util.ListLib.
Require Import coqutil.Decidable.
Require Import Coq.Program.Tactics.
Require Import Coq.Bool.Bool.
Require Import riscv.InstructionCoercions.
Require Import riscv.Primitives.
Require Import Coq.micromega.Lia.
Require Import riscv.util.div_mod_to_quot_rem.
Require Import compiler.util.Misc.
Require Import riscv.Utility.
Require Import riscv.util.ZBitOps.
Require Import compiler.util.Common.
Require Import riscv.Utility.
Require Import riscv.MkMachineWidth.
Require Import riscv.runsToNonDet.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.EmitsValid.
Require Import compiler.SeparationLogic.
Require Import bedrock2.Scalars.
Require Import compiler.Simp.
Require Import compiler.SimplWordExpr.
Require Import bedrock2.ptsto_bytes.

Local Open Scope ilist_scope.
Local Open Scope Z_scope.

Set Implicit Arguments.

Section TODO.
  Context {K V: Type}.
  Context {M: map.map K V}.
  Axiom put_put_same: forall k v1 v2 m, map.put (map.put m k v1) k v2 = map.put m k v2.
End TODO.


Local Set Refine Instance Mode.

Definition TODO{T: Type}: T. Admitted.

Module Import FlatToRiscv.
  Export FlatToRiscvDef.FlatToRiscvDef.

  Class parameters := {
    def_params :> FlatToRiscvDef.parameters;

    W :> Words;

    locals :> map.map Register word;
    locals_ok :> map.ok locals;
    mem :> map.map word byte;
    mem_ok :> map.ok mem;
    actname_eq_dec :> DecidableEq actname;

    iset := if width =? 32 then RV32IM else RV64IM;

    M: Type -> Type;
    MM :> Monad M;
    RVM :> RiscvProgram M word;
    PR :> Primitives actname M;

    trace := list (mem * Syntax.actname * list word * (mem * list word));
    ext_spec : trace -> mem -> Syntax.actname -> list word -> (mem -> list word -> Prop) -> Prop;

    (* these two instances are needed to define compile_ext_call_correct below *)

    syntax_params: Syntax.parameters := {|
      Syntax.varname := Register;
      Syntax.funname := Empty_set;
      Syntax.actname := actname;
    |};

    env :> map.map Syntax.funname (list Syntax.varname * list Syntax.varname * stmt);
    env_ok: map.ok env;

    FlatImp_params: FlatImp.parameters := {|
      FlatImp.syntax_params := syntax_params;
      FlatImp.ext_spec := ext_spec;
      FlatImp.max_ext_call_code_size := max_ext_call_code_size;
      FlatImp.max_ext_call_code_size_nonneg := FlatImpSize.max_ext_call_code_size_nonneg;
    |};

    Machine := @RiscvMachine Register W _ mem actname;

    (* An abstract predicate on the low-level state, which can be chosen by authors of
       extensions. The compiler will ensure that this guarantee holds before each external
       call. *)
    ext_guarantee: Machine -> Prop;

    (* For authors of extensions, a freely choosable ext_guarantee sounds too good to be true!
       And indeed, there are two restrictions:
       The first restriction is that ext_guarantee needs to be preservable for the compiler: *)
    ext_guarantee_preservable: forall (m1 m2: Machine),
        ext_guarantee m1 ->
        map.same_domain m1.(getMem) m2.(getMem) ->
        m1.(getLog) = m2.(getLog) ->
        ext_guarantee m2;

    (* And the second restriction is part of the correctness requirement for compilation of
       external calls: Every compiled external call has to preserve ext_guarantee *)
    compile_ext_call_correct: forall (initialL: Machine) action postH newPc insts
        (argvars resvars: list Register) initialMH R,
      insts = compile_ext_call resvars action argvars ->
      newPc = word.add initialL.(getPc) (word.mul (word.of_Z 4) (word.of_Z (Zlength insts))) ->
      Forall valid_register argvars ->
      Forall valid_register resvars ->
      (program initialL.(getPc) insts * eq initialMH * R)%sep initialL.(getMem) ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      ext_guarantee initialL ->
      exec map.empty (@SInteract (@FlatImp.syntax_params FlatImp_params) resvars action argvars)
           initialL.(getLog) initialMH initialL.(getRegs) postH ->
      runsTo (mcomp_sat (run1 iset)) initialL
             (fun finalL =>
                  (* external calls can't modify the memory for now *)
                  postH finalL.(getLog) initialMH finalL.(getRegs) /\
                  finalL.(getPc) = newPc /\
                  finalL.(getNextPc) = add newPc (ZToReg 4) /\
                  (program initialL.(getPc) insts * eq initialMH * R)%sep finalL.(getMem) /\
                  ext_guarantee finalL);

    (* bitwidth-specific: *)
    go_load: forall sz x a (addr v: word) initialL post f,
      valid_register x ->
      valid_register a ->
      map.get initialL.(getRegs) a = Some addr ->
      Memory.load sz (getMem initialL) addr = Some v ->
      mcomp_sat (f tt) (withRegs (map.put initialL.(getRegs) x v) initialL) post ->
      mcomp_sat (Bind (execute (compile_load iset sz x a 0)) f) initialL post;

    go_store: forall sz x a (addr v: word) initialL m' post f,
      valid_register x ->
      valid_register a ->
      map.get initialL.(getRegs) x = Some v ->
      map.get initialL.(getRegs) a = Some addr ->
      Memory.store sz (getMem initialL) addr v = Some m' ->
      mcomp_sat (f tt) (withMem m' initialL) post ->
      mcomp_sat (Bind (execute (compile_store iset sz a x 0)) f) initialL post;

  }.

End FlatToRiscv.

Local Unset Universe Polymorphism. (* for Add Ring *)

Section FlatToRiscv1.
  Context {p: unique! FlatToRiscv.parameters}.

  Notation var := Z (only parsing).

  Definition trace := list (LogItem actname).

  Local Notation RiscvMachineL := (RiscvMachine Register actname).

  Definition word_ring_theory := word.ring_theory (word := word).
  Add Ring word_ring : word_ring_theory.

  Ltac state_calc0 := map_solver locals_ok.

  Hint Rewrite @Zlength_nil @Zlength_cons @Zlength_app: rew_Zlength.

  (* TODO is there a principled way of writing such proofs? *)
  Lemma reduce_eq_to_sub_and_lt: forall (y z: word) {T: Type} (thenVal elseVal: T),
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

  (* Set Printing Projections.
     Uncaught anomaly when stepping through proofs :(
     https://github.com/coq/coq/issues/6257 *)

  Arguments Z.mul: simpl never.
  Arguments Z.add: simpl never.
  Arguments run1: simpl never.

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

  Lemma pow2_wXLEN_4: 4 < 2 ^ XLEN.
  Proof.
    unfold XLEN, MachineWidth_XLEN.
    pose proof (@word.width_pos _ _ word_ok).
    pose proof (Z.pow_gt_1 2 width).
    (* TODO doesn't hold, if we want this we'll have to add a stronger bound to Words,
       or somewhere else *)
  Admitted.

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

  Definition runsTo: RiscvMachineL -> (RiscvMachineL -> Prop) -> Prop :=
    runsTo (mcomp_sat (run1 iset)).

  Lemma one_step: forall initialL P,
      mcomp_sat (run1 iset) initialL P ->
      runsTo initialL P.
  Proof.
    intros.
    eapply runsToStep; [eassumption|].
    intros.
    apply runsToDone. assumption.
  Qed.

  Lemma det_step: forall initialL midL P,
      mcomp_sat (run1 iset) initialL (eq midL) ->
      runsTo midL P ->
      runsTo initialL P.
  Proof.
    intros.
    eapply runsToStep; [eassumption|].
    intros. subst.
    assumption.
  Qed.

  Ltac simpl_run1 :=
    cbv [run1 (*execState*) OStateNDOperations.put OStateNDOperations.get
         Return Bind State_Monad OStateND_Monad
         execute ExecuteI.execute ExecuteM.execute ExecuteI64.execute ExecuteM64.execute
         getRegs getPc getNextPc getMem getLog
         getPC setPC getRegister setRegister].

  Tactic Notation "log_solved" tactic(t) :=
    match goal with
    | |- ?G => let H := fresh in assert G as H by t; idtac "solved" G; exact H
    | |- ?G => idtac "did not solve" G
    end.

  Local Ltac solve_stmt_not_too_big :=
    lazymatch goal with
    | H: stmt_not_too_big _ |- stmt_not_too_big _ =>
        clear -H;
        unfold stmt_not_too_big in *;
        change (2 ^ 9)%Z with 512%Z in *;
        simpl stmt_size in H;
        repeat match goal with
               | s: stmt |- _ => unique pose proof (stmt_size_pos s)
               end;
        match goal with
        | |- ?SZ _ _ < _ => (* COQBUG https://github.com/coq/coq/issues/9268 *)
          change @stmt_size with SZ in *
        end;
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

  Ltac simpl_RiscvMachine_get_set := simpl in *. (* TODO is this enough? *)

  Ltac destruct_RiscvMachine_0 m :=
    let t := type of m in
    unify t RiscvMachine;
    let r := fresh m "_regs" in
    let p := fresh m "_pc" in
    let n := fresh m "_npc" in
    let e := fresh m "_eh" in
    let me := fresh m "_mem" in
    destruct m as [ [r p n e] me ];
    simpl_RiscvMachine_get_set.

  Ltac destruct_RiscvMachine m :=
    let t := type of m in
    unify t RiscvMachineL;
    let r := fresh m "_regs" in
    let p := fresh m "_pc" in
    let n := fresh m "_npc" in
    let me := fresh m "_mem" in
    let l := fresh m "_log" in
    destruct m as [r p n me l];
    simpl_RiscvMachine_get_set.

  Arguments Z.modulo : simpl never.

  Hint Unfold
       Program.getRegister
       Program.setRegister
       Program.loadByte
       Program.loadHalf
       Program.loadWord
       Program.loadDouble
       Program.storeByte
       Program.storeHalf
       Program.storeWord
       Program.storeDouble
       Program.getPC
       Program.setPC
       Program.step
       Program.raiseException
    : unf_Program_methods.

(*
  Ltac prove_go_lemma :=
    intros;
    unfold valid_register, computation_satisfies in *;
    autounfold with unf_Program_methods in *;
    unfold IsRiscvMachineL in *;
    unfold valid_register, Register0,
           liftLoad, liftStore, logEvent in *;
    repeat match goal with
           | |- _ => reflexivity
           | |- _ => progress (subst)
           | |- _ => solve [exfalso; lia]
           | |- _ => discriminate
           | |- _ => assumption
           | |- _ => rewrite associativity
           | |- _ => rewrite OStateNDOperations.Bind_get
           | |- _ => rewrite OStateNDOperations.Bind_put
           | |- _ => rewrite left_identity
           | |- context [if ?x then _ else _] => let E := fresh "E" in destruct x eqn: E
           | _: context [if ?x then _ else _] |- _ => let E := fresh "E" in destruct x eqn: E
           end.
*)

  Ltac sidecondition_less_safe := eassumption || reflexivity || idtac.

  (*
  Notation K := Z.
  Notation V := mword.
  *)

  (* only strictly needed if we want to export the goal into a map_solver-only environment,
     but might result in a speed up if used anyways *)
  Ltac prepare_for_map_solver :=
    repeat match goal with
             | IH: forall (s : stmt), _ |- _ => clear IH
             | H: context [FlatImp.modVars ?var ?func ?s] |- _ =>
               let n := fresh "mv" s in
               forget (FlatImp.modVars var func s) as n
         (*  | H: Memory.read_mem _ _ = _ |- _ => clear H *)
             | H: ?P |- _ =>
               let h := head_of_app P in
               match h with
               | @stmt_not_too_big => clear H
               | @valid_register => clear H
               | @valid_registers => clear H
        (*     | @divisibleBy4 => clear H  *)
               end
             | H: @eq ?T _ _ |- _ =>
               match T with
            (* | option Semantics.word => don't clear because we have maps of Semantics.word *)
           (*  | option (map Z word * Memory.mem) => clear H *)
               | option mem => clear H
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

(*
  Hint Rewrite
      (@associativity  _ (OStateND_Monad RiscvMachine))
      (@left_identity  _ (OStateND_Monad RiscvMachine))
      (@right_identity _ (OStateND_Monad RiscvMachine))
      (@Bind_getRegister _ _ _ _ _ _ _)
      (@Bind_getRegister0 _ _ _ _ _ _ _)
      (@Bind_setRegister _ _ _ _ _ _ _)
      (@Bind_setRegister0 _ _ _ _ _ _ _)
      (@Bind_getPC _ _ _ _ _ _ _)
      (@Bind_setPC _ _ _ _ _ _ _)
  using assumption : rew_get_set_Register.

  Ltac do_get_set_Register := autorewrite with rew_get_set_Register.
*)

  (* requires destructed RiscvMachine and containsProgram *)
  Ltac fetch_inst :=
    eapply go_fetch_inst; [reflexivity|simpl (*; solve_containsProgram *)|].

  Ltac rewrite_reg_value :=
    match goal with
    | |- context [get    _ _] => idtac
    | _ => fail 1 "wrong shape of goal"
    end. (*;
    let G1 := fresh "G1" in
    match goal with
    | G2: get ?st2 ?x = ?v, E: map.extends ?st1 ?st2 |- context [@getReg ?RF ?R ?V ?TC ?st1 ?x] =>
      let gg := constr:(@getReg RF R V TC st1 x) in
      let gg' := eval unfold getReg, State_is_RegisterFile in gg in
      progress change gg with gg';
      match gg' with
      | match ?gg'' with | _ => _ end => assert (G1: gg'' = v) by state_calc
      end
    | G2: get ?st2 ?x = ?v, E: map.extends ?st1 ?st2 |- context [?gg'] =>
      match gg' with
      | match ?gg'' with | _ => _ end => assert (G1: gg'' = v) by state_calc
      end
    end;
    rewrite G1;
    clear G1. *)

  Ltac rewrite_getReg := idtac. (*
    match goal with
    | |- context [@getReg ?RF ?R ?V ?TC ?st1 ?x] =>
      let gg := constr:(@getReg RF R V TC st1 x) in
      let gg' := eval unfold getReg, State_is_RegisterFile in gg in
          progress change gg with gg'
    end. *)

  Ltac rewrite_setReg := idtac. (*
    match goal with
    | |- context [@setReg ?RF ?R ?V ?TC ?st1 ?x ?v] =>
      let gg := constr:(@setReg RF R V TC st1 x v) in
      let gg' := eval unfold setReg, State_is_RegisterFile in gg in
          progress change gg with gg'
    end. *)

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

  Instance word_eq_dec: DecidableEq word. (* TODO *) Admitted.

  Lemma disjoint_putmany_preserves_store_bytes: forall n a vs (m1 m1' mq: mem),
      store_bytes n m1 a vs = Some m1' ->
      map.disjoint m1 mq ->
      store_bytes n (map.putmany m1 mq) a vs = Some (map.putmany m1' mq).
  Proof.
    intros.
    unfold store_bytes, load_bytes, unchecked_store_bytes in *. simp.
    erewrite map.getmany_of_tuple_in_disjoint_putmany by eassumption.
    f_equal.
    set (ks := (footprint a n)) in *.
    rename mq into m2.
    rewrite map.putmany_of_tuple_to_putmany.
    rewrite (map.putmany_of_tuple_to_putmany n m1 ks vs).
    apply map.disjoint_putmany_commutes.
    pose proof map.getmany_of_tuple_to_sub_domain as P.
    specialize P with (1 := E).
    apply map.sub_domain_value_indep with (vs2 := vs) in P.
    set (mp := (map.putmany_of_tuple ks vs map.empty)) in *.
    apply map.disjoint_comm.
    eapply map.sub_domain_disjoint; eassumption.
  Qed.

  Lemma store_bytes_preserves_footprint: forall n a v (m m': mem),
      Memory.store_bytes n m a v = Some m' ->
      map.same_domain m m'.
  Proof.
    intros. unfold store_bytes, load_bytes, unchecked_store_bytes in *. simp.
    eauto using map.putmany_of_tuple_preserves_domain.
  Qed.

(*
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
  *)

  Hint Rewrite word.eqb_ne word.eqb_eq using congruence : rew_reg_eqb.

  Hint Rewrite
      elim_then_true_else_false
      (@left_identity M MM)
      @map.get_put_same
      @put_put_same
  : rew_run1step.

  Ltac simpl_bools :=
    repeat match goal with
           | H : ?x = false |- _ =>
             progress rewrite H in *
           | H : ?x = true |- _ =>
             progress rewrite H in *
           | |- context [negb true] => progress unfold negb
           | |- context [negb false] => progress unfold negb
           | H : negb ?x = true |- _ =>
             let H' := fresh in
             assert (x = false) as H' by (eapply negb_true_iff; eauto);
             clear H
           | H : negb ?x = false |- _ =>
             let H' := fresh in
             assert (x = true) as H' by (eapply negb_false_iff; eauto);
             clear H
           end.

  Ltac prove_ext_guarantee :=
    eapply ext_guarantee_preservable; [eassumption | simpl | reflexivity ];
    (* eauto using the lemmas below doesn't work, why? *)
    first [ eapply map.same_domain_refl |
            eapply store_bytes_preserves_footprint; eassumption ].

  Ltac simulate'_step :=
    first (* lemmas introduced only in this file: *)
          [ eapply go_load  ; [sidecondition..|]
          | eapply go_store ; [sidecondition..|]
          | simulate_step ].

  Ltac simulate' := repeat simulate'_step.

  Ltac run1det :=
    eapply det_step;
    [ simulate';
      match goal with
      | |- ?mid = ?RHS =>
        (* simpl RHS because mid will be instantiated to it and turn up again in the next step *)
        is_evar mid; simpl; reflexivity
      | |- _ => fail 10000 "simulate' did not go through completely"
      end
    | ].

  Ltac run1done :=
    apply runsToDone;
    simpl in *;
    eexists;
    repeat split;
    simpl_word_exprs (@word_ok (@W p));
    first
      [ eassumption
      | solve_word_eq (@word_ok (@W p))
      | seplog
      | prove_ext_guarantee
      | idtac ].

(*
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
*)

  Arguments LittleEndian.combine: simpl never.

  Definition load_lit_semantics(v: Z): word :=
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

  Ltac substs :=
    repeat match goal with
           | x := _ |- _ => subst x
           | _: ?x = _ |- _ => subst x
           | _: _ = ?x |- _ => subst x
           end.

  Lemma compile_lit_correct_full: forall initialL post x v R,
      initialL.(getNextPc) = add initialL.(getPc) (ZToReg 4) ->
      let insts := compile_stmt iset (SLit x v) in
      let d := mul (ZToReg 4) (ZToReg (Zlength insts)) in
      (program initialL.(getPc) insts * R)%sep initialL.(getMem) ->
      valid_register x ->
      runsTo (withRegs   (map.put initialL.(getRegs) x (ZToReg v))
             (withPc     (add initialL.(getPc) d)
             (withNextPc (add initialL.(getNextPc) d)
                         initialL)))
             post ->
      runsTo initialL post.
  Proof.
    intros. substs.
    unfold compile_stmt, compile_lit, compile_lit_rec in *.
    simpl in *.
  (*
    destruct_everything; simpl in *.
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
    match goal with
    | R: runsTo ?m post |- runsToNonDet.runsTo _ _ ?m' post =>
      replace m' with m; [exact R|]
    end.
    f_equal; try solve_word_eq.
    f_equal. symmetry. apply compile_lit_correct.
  Qed.
  *)
  Admitted.

  Existing Instance FlatToRiscv.syntax_params.
  Existing Instance FlatToRiscv.FlatImp_params.

  Definition eval_stmt := exec map.empty.

  Lemma seplog_subst_eq{A B R: mem -> Prop} {mL mH: mem}
      (H: A mL)
      (H0: iff1 A (R * eq mH)%sep)
      (H1: B mH):
      (B * R)%sep mL.
  Proof.
    unfold iff1 in *.
    destruct (H0 mL) as [P1 P2]. specialize (P1 H).
    apply sep_comm.
    unfold sep in *.
    destruct P1 as (mR & mH' & P11 & P12 & P13). subst mH'. eauto.
  Qed.

  Lemma subst_load_bytes_for_eq {sz} {mH mL: mem} {addr: word} {bs P R}:
      let n := @Memory.bytes_per width sz in
      bedrock2.Memory.load_bytes n mH addr = Some bs ->
      (P * eq mH * R)%sep mL ->
      exists Q, (P * ptsto_bytes n addr bs * Q * R)%sep mL.
  Proof.
    intros n H H0.
    apply sep_of_load_bytes in H; cycle 1. {
      subst n. clear. destruct sz; destruct width_cases as [C | C]; rewrite C; cbv; discriminate.
    }
    destruct H as [Q A]. exists Q.
    assert (((ptsto_bytes n addr bs * Q) * (P * R))%sep mL); [|ecancel_assumption].
    eapply seplog_subst_eq; [exact H0|..|exact A]. ecancel.
  Qed.

  Ltac subst_load_bytes_for_eq :=
    match goal with
    | Load: bedrock2.Memory.load_bytes _ ?m _ = _, Sep: (_ * eq ?m * _)%sep _ |- _ =>
      let Q := fresh "Q" in
      destruct (subst_load_bytes_for_eq Load Sep) as [Q ?]
    end.

  Lemma doesSupportM: supportsM iset = true.
  Proof.
    unfold iset. destruct_one_match; reflexivity.
  Qed.

  Lemma store_bytes_frame: forall {n: nat} {m1 m1' m: mem} {a: word} {v: HList.tuple byte n} {F},
      Memory.store_bytes n m1 a v = Some m1' ->
      (eq m1 * F)%sep m ->
      exists m', (eq m1' * F)%sep m' /\ Memory.store_bytes n m a v = Some m'.
  Proof.
    intros.
    unfold sep in H0.
    destruct H0 as (mp & mq & A & B & C).
    subst mp.
    unfold map.split in A. destruct A as [A1 A2].
    eexists (map.putmany m1' mq).
    split.
    - unfold sep.
      exists m1' mq. repeat split; trivial.
      apply store_bytes_preserves_footprint in H.
      clear -H A2.
      unfold map.disjoint, map.same_domain, map.sub_domain in *. destruct H as [P Q].
      intros.
      edestruct Q; eauto.
    - subst m.
      eauto using disjoint_putmany_preserves_store_bytes.
  Qed.

(*
  Definition divisibleBy4(x: word): Prop :=
    word.modu x (word.of_Z 4) = word.of_Z 0.
*)

  Definition divisibleBy4(x: word): Prop := (word.unsigned x) mod 4 = 0.

  Lemma four_fits: 4 < 2 ^ width.
  Proof.
    destruct width_cases as [C | C]; rewrite C; reflexivity.
  Qed.

  Ltac div4_sidecondition :=
    pose proof four_fits;
    rewrite ?word.unsigned_of_Z, ?Z.mod_small;
    lia.

  Lemma unsigned_of_Z_4: word.unsigned (word.of_Z (word := word) 4) = 4.
  Proof. div4_sidecondition. Qed.

  Lemma unsigned_of_Z_0: word.unsigned (word.of_Z (word := word) 0) = 0.
  Proof. div4_sidecondition. Qed.

  Lemma divisibleBy4_add_4_r(x: word)
    (D: divisibleBy4 x):
    divisibleBy4 (word.add x (word.of_Z 4)).
  Proof.
    unfold divisibleBy4 in *.
    rewrite word.unsigned_add.
    rewrite <- Znumtheory.Zmod_div_mod.
    - rewrite Zplus_mod. rewrite D. rewrite unsigned_of_Z_4. reflexivity.
    - lia.
    - destruct width_cases as [C | C]; rewrite C; reflexivity.
    - unfold Z.divide. exists (2 ^ width / 4).
      destruct width_cases as [C | C]; rewrite C; reflexivity.
  Qed.

  Lemma compile_stmt_correct_aux:
    forall (s: @stmt (@FlatImp.syntax_params (@FlatImp_params p))) t initialMH initialRegsH postH,
    eval_stmt s t initialMH initialRegsH postH ->
    forall R initialL insts,
    @compile_stmt def_params iset s = insts ->
    stmt_not_too_big s ->
    valid_registers s ->
    divisibleBy4 initialL.(getPc) ->
    initialL.(getRegs) = initialRegsH ->
    (program initialL.(getPc) insts * eq initialMH * R)%sep initialL.(getMem) ->
    initialL.(getLog) = t ->
    initialL.(getNextPc) = add initialL.(getPc) (ZToReg 4) ->
    ext_guarantee initialL ->
    runsTo initialL (fun finalL => exists finalMH,
          postH finalL.(getLog) finalMH finalL.(getRegs) /\
          (program initialL.(getPc) insts * eq finalMH * R)%sep finalL.(getMem) /\
          finalL.(getPc) = add initialL.(getPc) (mul (ZToReg 4) (ZToReg (Zlength insts))) /\
          finalL.(getNextPc) = add finalL.(getPc) (ZToReg 4) /\
          ext_guarantee finalL).
  Proof.
    pose proof compile_stmt_emits_valid.
    induction 1; intros;
      lazymatch goal with
      | H1: valid_registers ?s, H2: stmt_not_too_big ?s |- _ =>
        pose proof (compile_stmt_emits_valid _ doesSupportM H1 H2)
      end;
      repeat match goal with
             | m: _ |- _ => destruct_RiscvMachine m
             end;
      simpl in *;
      simp.

    - (* SInteract *)
      eapply runsTo_weaken.
      + eapply compile_ext_call_correct with (postH := post) (action0 := action)
                                             (argvars0 := argvars) (resvars0 := resvars);
          simpl; reflexivity || eassumption || ecancel_assumption || idtac.
        eapply @ExInteract; try eassumption.
      + simpl. intros finalL A. destruct_RiscvMachine finalL. simpl in *.
        destruct_products. subst. eauto 7.

    - (* SCall *)
      match goal with
      | A: map.get map.empty _ = Some _ |- _ =>
        clear -A; exfalso; simpl in *;
        rewrite (map.get_empty (ok := env_ok)) in A
      end.
      discriminate.

    - (* SLoad *)
      unfold Memory.load, Memory.load_Z in *. simp. subst_load_bytes_for_eq.
      run1det. run1done.

    - (* SStore *)
      assert ((eq m * (program initialL_pc [[compile_store iset sz a v 0]] * R))%sep initialL_mem)
             as A by ecancel_assumption.
      pose proof (store_bytes_frame H2 A) as P.
      destruct P as (finalML & P1 & P2).
      run1det. run1done.

    - (* SLit *)
      remember (compile_lit x v) as insts.
      eapply compile_lit_correct_full.
      + sidecondition.
      + unfold compile_stmt. unfold getPc, getMem. subst insts. ecancel_assumption.
      + sidecondition.
      + simpl. run1done.

      (* SOp *)
    - admit.
      (*
      match goal with
      | o: Syntax.bopname.bopname |- _ => destruct o (* do this before destruct_containsProgram *)
      end.
      admit.
      simpl in *; destruct_everything;
      try solve [run1step; run1done].
      (* all except eq are implemented with one instruction *)
      run1step. run1step. run1done.
      rewrite reduce_eq_to_sub_and_lt.
      state_calc.
      *)

    - (* SSet *)
      run1det. run1done.

    - (* SIf/Then *)
      (* branch if cond = false (will not branch *)
      eapply det_step; simpl in *; subst.
      + simulate'.
        destruct cond; [destruct op | ];
          simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity.
      + (* use IH for then-branch *)
        eapply runsTo_trans.
        * eapply IHexec.
          1: reflexivity.
          1: solve_stmt_not_too_big.
          1: assumption.
          {

  Ltac solve_divisibleBy4 :=
    lazymatch goal with
    | |- divisibleBy4 _ => idtac
    | |- _ => fail "not a divisibleBy4 goal"
    end;
    repeat match goal with
           | H: ?P |- _ => let h := head_of_app P in
                           assert_fails (constr_eq h @divisibleBy4);
                           clear H
           end;
    simpl;
    auto using divisibleBy4_add_4_r.

            solve_divisibleBy4.
          }
          1: reflexivity.
          1: simpl.
          { move H7 at bottom.
            unfold program in *.
            repeat match goal with
            | H: _ ?m |- _ ?m => simpl in H (* does array_cons *) || seprewrite_in @array_append H
            end.
            seplog.
          }
          { reflexivity. }
          { reflexivity. }
          { prove_ext_guarantee. }
        * simpl. intros. simp. destruct_RiscvMachine middle. subst.
          eapply det_step.
          { simulate'.
            { simpl.
              replace ((word.eqb
            (word.modu
               (word.add
                  (word.add (word.add initialL_pc (word.of_Z 4))
                     (word.mul (word.of_Z 4) (word.of_Z (Zlength (compile_stmt iset bThen)))))
                  (word.of_Z ((Zlength (compile_stmt iset bElse) + 1) * 4)))
               (word.of_Z 4)) (word.of_Z 0))) with true by admit.
              simpl.
              simulate'.
              simpl.
              reflexivity. }
          }
          { run1done.
            - admit.
            - simpl_word_exprs word_ok. admit. }

    - (* SIf/Else *) (*
      (* branch if cond = 0 (will  branch) *)
      eapply runsToStep; simpl in *; subst *.
      + fetch_inst.
        destruct cond; [destruct op | ]; simpl in *;
          destruct_everything;
          run1step''';
          apply execState_step.
      + simpl.
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
      + fetch_inst.
        destruct cond; [destruct op | ]; simpl in *;
          destruct_everything;
          run1step''';
          apply execState_step.
      + run1done.

    - (* SLoop/again *)
      (* 1st application of IH: part 1 of loop body *)
      spec_IH IHfuelH IH s1.
      apply (runsToSatisfying_trans IH). clear IH.
      intros.
      destruct_everything.
      eapply runsToStep; simpl in *; subst *.
      + fetch_inst.
        destruct cond; [destruct op | ]; simpl in *;
          destruct_everything;
          run1step''';
          apply execState_step.
      + (* 2nd application of IH: part 2 of loop body *)
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

  Qed.
  *) Admitted.

  (*
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
  *)

End FlatToRiscv1.
