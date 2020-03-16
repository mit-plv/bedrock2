Require Export Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Export ListNotations.
Require Export coqutil.Decidable.
Require        compiler.ExprImp.
Require Export compiler.FlattenExprDef.
Require Export compiler.FlattenExpr.
Require        compiler.FlatImp.
Require Export riscv.Spec.Machine.
Require Export riscv.Platform.Run.
Require Export riscv.Platform.Minimal.
Require Export riscv.Platform.MetricLogging.
Require Export riscv.Utility.Monads.
Require Import riscv.Utility.runsToNonDet.
Require Export riscv.Platform.MetricRiscvMachine.
Require Import coqutil.Z.Lia.
Require Import compiler.NameGen.
Require Import compiler.StringNameGen.
Require Export compiler.util.Common.
Require Export coqutil.Decidable.
Require Export riscv.Utility.Encode.
Require Import riscv.Spec.Decode.
Require Export riscv.Spec.Primitives.
Require Export riscv.Spec.MetricPrimitives.
Require Import compiler.GoFlatToRiscv.
Require Import riscv.Utility.MkMachineWidth.
Require Export riscv.Proofs.DecodeEncode.
Require Export riscv.Proofs.EncodeBound.
Require Export compiler.EmitsValid.
Require Import riscv.Utility.Utility.
Require Export riscv.Platform.Memory.
Require Export riscv.Utility.InstructionCoercions.
Require Import compiler.SeparationLogic.
Require Import compiler.Simp.
Require Import compiler.FlattenExprSimulation.
Require Import compiler.RegRename.
Require Import compiler.FlatToRiscvSimulation.
Require Import compiler.Simulation.
Require Import compiler.RiscvEventLoop.
Require Coq.Init.Byte.
Require Import bedrock2.MetricLogging.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvFunctions.
Require Import compiler.DivisibleBy4.
Require Import compiler.SimplWordExpr.
Require Import compiler.ForeverSafe.
Require Export compiler.MemoryLayout.
Require Import FunctionalExtensionality.
Require Import coqutil.Tactics.autoforward.
Require Import compiler.FitsStack.
Import Utility.

Existing Instance riscv.Spec.Machine.DefaultRiscvState.

Open Scope Z_scope.

Section WithWordAndMem.
  Context {width: Z} {word: word.word width} {mem: map.map word byte}.

  (* bedrock2.ptsto_bytes.ptsto_bytes takes an n-tuple of bytes, whereas this one takes a list of bytes *)
  Definition ptsto_bytes: word -> list byte -> mem -> Prop := array ptsto (word.of_Z 1).

  Definition mem_available(start pastend: word)(m: mem): Prop :=
    exists anybytes: list byte,
      Z.of_nat (List.length anybytes) = word.unsigned (word.sub pastend start) /\
      ptsto_bytes start anybytes m.

  Definition mem_available_to_exists: forall start pastend m P,
      (mem_available start pastend * P)%sep m ->
      exists anybytes,
        Z.of_nat (List.length anybytes) = word.unsigned (word.sub pastend start) /\
        (ptsto_bytes start anybytes * P)%sep m.
  Proof.
    unfold mem_available, sep. simpl.
    intros. simp. eauto 10.
  Qed.
End WithWordAndMem.

Require Import Coq.Sorting.Permutation.

(* TODO move to coqutil *)
Module List.
  Section WithA.
    Context {A: Type} {a_eqb: A -> A -> bool} {a_eqb_spec: EqDecider a_eqb}.

    Lemma fold_right_change_order{R: Type}(f: A -> R -> R)
          (f_comm: forall a1 a2 r, f a1 (f a2 r) = f a2 (f a1 r)):
      forall l1 l2: list A,
        Permutation l1 l2 ->
        forall r0, fold_right f r0 l1 = fold_right f r0 l2.
    Proof.
      induction 1; intros.
      - reflexivity.
      - simpl. f_equal. auto.
      - simpl. apply f_comm.
      - rewrite IHPermutation1, IHPermutation2. reflexivity.
    Qed.
  End WithA.
End List.

Module map.
  Section WithMap.
    Context {key value} {map : map.map key value} {ok : map.ok map}.
    Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.

    Definition tuples(m: map): list (key * value) :=
      map.fold (fun l k v => (k, v) :: l) nil m.

    (* Folding over a map preserves relations *)
    Axiom fold_parametricity: forall {A B : Type} (R : A -> B -> Prop)
        (fa: A -> key -> value -> A) (fb: B -> key -> value -> B),
        (forall a b k v, R a b -> R (fa a k v) (fb b k v)) ->
        forall a0 b0, R a0 b0 -> forall m, R (map.fold fa a0 m) (map.fold fb b0 m).

    Lemma fold_two_spec:
      forall {R1 R2: Type} (P: map -> R1 -> R2 -> Prop)
             (f1: R1 -> key -> value -> R1) (f2: R2 -> key -> value -> R2) r01 r02,
        P map.empty r01 r02 ->
        (forall k v m r1 r2, map.get m k = None ->
                             P m r1 r2 ->
                             P (map.put m k v) (f1 r1 k v) (f2 r2 k v)) ->
        forall m, P m (map.fold f1 r01 m) (map.fold f2 r02 m).
    Proof.
      intros.
      pose proof (@fold_parametricity (R1 * R2) R1
        (fun '(r11, r21) r12 => r12 = r11)
        (fun '(r1, r2) k v => (f1 r1 k v, f2 r2 k v)) f1) as Q.
      specialize Q with (a0 := (r01, r02)) (b0 := r01) (m := m).
      simpl in Q.
      destruct (map.fold (fun '(r1, r2) (k : key) (v : value) => (f1 r1 k v, f2 r2 k v)) (r01, r02) m)
        as [r1 r2] eqn: E.
      rewrite Q. 3: reflexivity. 2: {
        intros. destruct a as [r1' r2'].  subst r1'. reflexivity.
      }
      clear Q.
      pose proof (@fold_parametricity (R1 * R2) R2
        (fun '(r11, r21) r22 => r22 = r21)
        (fun '(r1, r2) k v => (f1 r1 k v, f2 r2 k v)) f2) as Q.
      specialize Q with (a0 := (r01, r02)) (b0 := r02) (m := m).
      simpl in Q.
      rewrite E in Q.
      rewrite Q. 3: reflexivity. 2: {
        intros. destruct a as [r1' r2'].  subst r2'. reflexivity.
      }
      clear Q.
      revert r1 r2 E.
      eapply map.fold_spec; intros.
      - congruence.
      - destruct r as [ri1 ri2]. inversion E. subst r1 r2. clear E.
        eauto.
    Qed.

    Lemma tuples_NoDup: forall m, NoDup (tuples m).
    Proof.
      intros.
      eapply proj1 with (B := forall k v, List.In (k, v) (tuples m) -> map.get m k = Some v).
      unfold tuples.
      eapply map.fold_spec.
      - simpl. intuition constructor.
      - intros. destruct H0. intuition (try constructor; try assumption).
        + intro C. specialize H1 with (1 := C). congruence.
        + simpl in *. destruct H2.
          * inversion H2; rewrite map.get_put_same; congruence.
          * rewrite map.get_put_dec.
            destr (key_eqb k k0).
            -- subst k0. specialize H1 with (1 := H2). congruence.
            -- eauto.
    Qed.

    Lemma fold_to_tuples_fold : forall {R: Type} (f: R -> key -> value -> R) r0 m,
        map.fold f r0 m =
        List.fold_right (fun '(k, v) r => f r k v) r0 (tuples m).
    Proof.
      intros. unfold tuples.
      eapply fold_two_spec with
          (f1 := f)
          (f2 := (fun (l : list (key * value)) (k : key) (v : value) => (k, v) :: l)).
      - reflexivity.
      - intros. subst. simpl. reflexivity.
    Qed.

    Lemma tuples_spec: forall (m: map) (k : key) (v : value),
        In (k, v) (tuples m) <-> map.get m k = Some v.
    Proof.
      intro m. unfold tuples.
      eapply map.fold_spec; intros; split; intros; simpl in *.
      - contradiction.
      - rewrite map.get_empty in H. discriminate.
      - rewrite map.get_put_dec.
        destr (key_eqb k k0).
        + subst k0. destruct H1.
          * inversion H1; subst v0. reflexivity.
          * specialize (H0 k v0). apply proj1 in H0. specialize (H0 H1).
            congruence.
        + destruct H1.
          * congruence.
          * eapply H0. assumption.
      - rewrite map.get_put_dec in H1.
        destr (key_eqb k k0).
        + subst k0. inversion H1; subst v0. auto.
        + right. eapply H0. assumption.
    Qed.

    Lemma fold_spec_with_order : forall m, exists (l: list (key * value)),
      (forall k v, List.In (k, v) l <-> map.get m k = Some v) /\
      forall {R: Type} (f: R -> key -> value -> R) r0,
        map.fold f r0 m = List.fold_right (fun '(k, v) r => f r k v) r0 l.
    Proof.
      intros. eexists. split.
      - eapply tuples_spec.
      - intros. eapply fold_to_tuples_fold.
    Qed.

    Lemma fold_comm{R: Type}(f: R -> key -> value -> R)
          (f_comm: forall r k1 v1 k2 v2, f (f r k1 v1) k2 v2 = f (f r k2 v2) k1 v1):
      forall r0 m k v,
        map.fold f (f r0 k v) m = f (map.fold f r0 m) k v.
    Proof.
      intros.
      eapply fold_two_spec with (f1 := f) (f2 := f) (r01 := f r0 k v) (r02 := r0).
      - reflexivity.
      - intros. subst. apply f_comm.
    Qed.

    Lemma map_ind(P: map -> Prop):
      P map.empty ->
      (forall m, P m -> forall k v, map.get m k = None -> P (map.put m k v)) ->
      forall m, P m.
    Proof.
      intros Base Step.
      eapply (map.fold_spec (fun (m: map) (_: unit) => P m) (fun acc _ _ => acc) tt Base).
      intros.
      eapply Step; assumption.
    Qed.

    Lemma tuples_put: forall m k v,
        map.get m k = None ->
        forall k0 v0, List.In (k0, v0) (tuples (map.put m k v)) <-> List.In (k0, v0) ((k, v) :: tuples m).
    Proof.
      intros.
      rewrite (tuples_spec (map.put m k v)).
      simpl.
      rewrite (tuples_spec m).
      rewrite map.get_put_dec.
      destr (key_eqb k k0); intuition congruence.
    Qed.

    Lemma fold_put{R: Type}(f: R -> key -> value -> R)
          (f_comm: forall r k1 v1 k2 v2, f (f r k1 v1) k2 v2 = f (f r k2 v2) k1 v1):
      forall r0 m k v,
        map.get m k = None ->
        map.fold f r0 (map.put m k v) = f (map.fold f r0 m) k v.
    Proof.
      intros.
      do 2 rewrite fold_to_tuples_fold.
      match goal with
      | |- ?L = f (fold_right ?F r0 (tuples m)) k v =>
        change (L = fold_right F r0 ((k, v) :: tuples m))
      end.
      apply List.fold_right_change_order.
      - intros [k1 v1] [k2 v2] r. apply f_comm.
      - apply NoDup_Permutation.
        + apply tuples_NoDup.
        + constructor.
          * pose proof (tuples_spec m k v). intuition congruence.
          * apply tuples_NoDup.
        + intros [k0 v0].
          rewrite (tuples_put m k v H).
          reflexivity.
    Qed.

    Lemma fold_remove{R: Type}(f: R -> key -> value -> R)
      (f_comm: forall r k1 v1 k2 v2, f (f r k1 v1) k2 v2 = f (f r k2 v2) k1 v1):
      forall r0 m k v,
        map.get m k = Some v ->
        map.fold f r0 m = f (map.fold f r0 (map.remove m k)) k v.
    Proof.
      intros.
      replace m with (map.put (map.remove m k) k v) at 1.
      - rewrite fold_put; eauto using map.get_remove_same.
      - apply map.map_ext.
        intros.
        rewrite map.get_put_dec.
        destr (key_eqb k k0); try rewrite map.get_remove_diff; congruence.
    Qed.
  End WithMap.
End map.


Module Import Pipeline.

  Class parameters := {
    FlatToRiscvDef_params :> FlatToRiscvDef.FlatToRiscvDef.parameters;

    mem :> map.map word byte;
    Registers :> map.map Z word;
    string_keyed_map :> forall T: Type, map.map string T; (* abstract T for better reusability *)
    trace := list (mem * string * list word * (mem * list word));
    ExtSpec := trace -> mem -> string -> list word -> (mem -> list word -> Prop) -> Prop;
    ext_spec : ExtSpec;

    (* Note: this one is not needed because it's subsumed by funname_env,
       and if we do add it, type class inference will infer funname_env in one place
       and src2imp in another and then terms which should be convertible arent'
    src2imp :> map.map string Z; *)

    M: Type -> Type;
    MM :> Monad M;
    RVM :> RiscvProgram M word;
    PRParams :> PrimitivesParams M MetricRiscvMachine;
  }.

  Instance FlattenExpr_parameters{p: parameters}: FlattenExpr.parameters := {
    FlattenExpr.W := _;
    FlattenExpr.locals := _;
    FlattenExpr.mem := mem;
    FlattenExpr.ext_spec := ext_spec;
    FlattenExpr.NGstate := string;
  }.

  Instance FlatToRiscv_params{p: parameters}: FlatToRiscvCommon.parameters := {|
    FlatToRiscvCommon.ext_spec := ext_spec;
  |}.

  Class assumptions{p: parameters}: Prop := {
    word_riscv_ok :> RiscvWordProperties.word.riscv_ok word;
    string_keyed_map_ok :> forall T, map.ok (string_keyed_map T);
    Registers_ok :> map.ok Registers;
    PR :> MetricPrimitives PRParams;
    FlatToRiscv_hyps :> FlatToRiscvCommon.assumptions;
    ext_spec_ok :> Semantics.ext_spec.ok (FlattenExpr.mk_Semantics_params FlattenExpr_parameters);
  }.

End Pipeline.


Section Pipeline1.

  Context {p: parameters}.
  Context {h: assumptions}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Local Axiom TODO_sam: False.

  Instance mk_FlatImp_ext_spec_ok:
    FlatImp.ext_spec.ok  string (FlattenExpr.mk_FlatImp_params FlattenExpr_parameters).
  Proof.
    destruct h. destruct ext_spec_ok0.
    constructor.
    all: intros; eauto.
    eapply intersect; eassumption.
  Qed.

  Instance FlattenExpr_hyps: FlattenExpr.assumptions FlattenExpr_parameters.
  Proof.
    constructor.
    - apply (string_keyed_map_ok (p := p) (@word (@FlattenExpr.W (@FlattenExpr_parameters p)))).
    - exact mem_ok.
    - apply (string_keyed_map_ok (p := p) (list string * list string * Syntax.cmd.cmd)).
    - apply (string_keyed_map_ok (p := p) (list string * list string * FlatImp.stmt string)).
    - apply mk_FlatImp_ext_spec_ok.
  Qed.

  Definition available_registers: list Z :=
    Eval cbv in List.unfoldn Z.succ 29 3.

  Lemma NoDup_available_registers: NoDup available_registers.
  Proof. cbv. repeat constructor; cbv; intros; intuition congruence. Qed.

  Lemma valid_FlatImp_vars_available_registers: Forall FlatToRiscvDef.valid_FlatImp_var available_registers.
  Proof. repeat constructor; cbv; intros; discriminate. Qed.

  Local Notation source_env := (@string_keyed_map p (list string * list string * Syntax.cmd)).
  Local Notation flat_env := (@string_keyed_map p (list string * list string * FlatImp.stmt string)).
  Local Notation renamed_env := (@string_keyed_map p (list Z * list Z * FlatImp.stmt Z)).

  Definition flattenPhase(prog: source_env): option flat_env := flatten_functions (2^10) prog.
  Definition renamePhase(prog: flat_env): option renamed_env :=
    rename_functions available_registers prog.

  (* Note: we could also track code size from the source program all the way to the target
     program, and a lot of infrastructure is already there, will do once/if we want to get
     a total compiler.
     Returns the fun_pos_env so that users know where to jump to call the compiled functions. *)
  Definition riscvPhase(ml: MemoryLayout)(prog: renamed_env):
    option (list Instruction * funname_env Z) :=
    bind_opt stack_needed <- stack_usage prog;
    let num_stackwords := word.unsigned (word.sub ml.(stack_pastend) ml.(stack_start)) / bytes_per_word in
    if Z.ltb num_stackwords stack_needed then None (* not enough stack *) else
    let positions := FlatToRiscvDef.build_fun_pos_env prog in
    let '(i, _) := FlatToRiscvDef.compile_funs positions prog in
    Some (i, positions).

  Definition composePhases{A B C: Type}(phase1: A -> option B)(phase2: B -> option C)(a: A) :=
    match phase1 a with
    | Some b => phase2 b
    | None => None
    end.

  Definition compile(ml: MemoryLayout):
    source_env -> option (list Instruction * funname_env Z) :=
    (composePhases flattenPhase
    (composePhases renamePhase
                   (riscvPhase ml))).

  Section Sim.
    Context (ml: MemoryLayout)
            (mlOk: MemoryLayoutOk ml)
            (f_entry_rel_pos : Z)
            (f_entry_name : string)
            (p_call: word) (* address where the call to the entry function is stored *)
            (p_functions: word) (* address where the compiled functions are stored *)
            (Rdata Rexec : FlatToRiscvCommon.mem -> Prop)
            (prog: renamed_env)
            (e1 : FlattenExpr.ExprImp_env)
            (e2 : FlattenExpr.FlatImp_env)
            (funname : string)
            (Hf: flatten_functions (2 ^ 10) e1 = Some e2).
    Let c2 := (@FlatImp.SSeq String.string FlatImp.SSkip (FlatImp.SCall [] funname [])).
    Let c3 := (@FlatImp.SSeq Z FlatImp.SSkip (FlatImp.SCall [] f_entry_name [])).
    Context (av' : list Z) (r' : string_keyed_map Z)
            (ER: envs_related available_registers e2 prog)
            (Ren: rename map.empty c2 available_registers = Some (r', c3, av'))
            (H_p_call: word.unsigned p_call mod 4 = 0)
            (H_p_functions: word.unsigned p_functions mod 4 = 0)
            (G: map.get (FlatToRiscvDef.build_fun_pos_env prog) f_entry_name = Some f_entry_rel_pos)
            (F: fits_stack (word.unsigned (word.sub (stack_pastend ml) (stack_start ml)) / bytes_per_word) prog
                           (FlatImp.SSeq FlatImp.SSkip (FlatImp.SCall [] f_entry_name [])))
            (GEI: good_e_impl prog (FlatToRiscvDef.build_fun_pos_env prog)).

    Definition flattenSim: simulation _ _ _ :=
      FlattenExprSimulation.flattenExprSim (2^10) e1 e2 funname Hf.
    Definition regAllocSim: simulation _ _ _ :=
      renameSim available_registers (@ext_spec p) NoDup_available_registers
                e2 prog c2 c3 av' r' ER Ren.
    Definition flatToRiscvSim: simulation _ _ _ :=
      FlatToRiscvSimulation.flatToRiscvSim
        f_entry_rel_pos f_entry_name p_call Rdata Rexec
        p_functions ml.(stack_start) ml.(stack_pastend)
        prog H_p_call H_p_functions G F GEI.

    Definition sim: simulation _ _ _ :=
      (compose_sim flattenSim (compose_sim regAllocSim flatToRiscvSim)).
  End Sim.

  Lemma rename_fun_valid: forall argnames retnames body impl',
      rename_fun available_registers (argnames, retnames, body) = Some impl' ->
      NoDup argnames ->
      NoDup retnames ->
      FlatImp.stmt_size body < 2 ^ 10 ->
      FlatToRiscvDef.valid_FlatImp_fun impl'.
  Proof.
    unfold rename_fun, FlatToRiscvDef.valid_FlatImp_fun.
    intros.
    simp.
    eapply rename_binds_props in E; cycle 1.
    { eapply map.empty_injective. }
    { eapply map.not_in_range_empty. }
    { apply NoDup_available_registers. }
    simp.
    eapply rename_binds_props in E0; cycle 1.
    { assumption. }
    { assumption. }
    { pose proof NoDup_available_registers as P.
      replace available_registers with (used ++ l) in P by assumption.
      apply invert_NoDup_app in P. tauto. }
    simp.
    pose proof E1 as E1'.
    eapply rename_props in E1; cycle 1.
    { assumption. }
    { assumption. }
    { pose proof NoDup_available_registers as P.
      replace available_registers with (used ++ used0 ++ l1) in P by assumption.
      apply invert_NoDup_app in P. simp. apply invert_NoDup_app in Prl. simp. assumption. }
    simp.
    ssplit.
    - eapply Forall_impl. 2: {
        eapply map.getmany_of_list_in_map. eassumption.
      }
      simpl.
      intros. simp.
      match goal with
      | X: _ |- _ => specialize X with (1 := H); rename X into A
      end.
      destruct A as [A | A].
      + pose proof valid_FlatImp_vars_available_registers as V.
        eapply (proj1 (Forall_forall _ _) V).
        replace available_registers with (used ++ used0 ++ used1 ++ l3) by assumption.
        rewrite ?in_app_iff. auto.
      + rewrite map.get_empty in A. discriminate A.
    - eapply Forall_impl. 2: {
        eapply map.getmany_of_list_in_map. eassumption.
      }
      simpl.
      intros. simp.
      match goal with
      | X: _ |- _ => specialize X with (1 := H); rename X into A
      end.
      destruct A as [A | A].
      + pose proof valid_FlatImp_vars_available_registers as V.
        eapply (proj1 (Forall_forall _ _) V).
        replace available_registers with (used ++ used0 ++ used1 ++ l3) by assumption.
        rewrite ?in_app_iff. auto.
      + match goal with
        | X: _ |- _ => specialize X with (1 := A); rename X into B
        end.
        destruct B as [B | B].
        * pose proof valid_FlatImp_vars_available_registers as V.
          eapply (proj1 (Forall_forall _ _) V).
          replace available_registers with (used ++ used0 ++ used1 ++ l3) by assumption.
          rewrite ?in_app_iff. auto.
        * rewrite map.get_empty in B. discriminate B.
    - eapply FlatImp.ForallVars_stmt_impl; [|eassumption].
      simpl. intros. simp.
      match goal with
      | X: _ |- _ => specialize X with (1 := H); rename X into A
      end.
      destruct A as [A | A].
      + pose proof valid_FlatImp_vars_available_registers as V.
        eapply (proj1 (Forall_forall _ _) V).
        replace available_registers with (used ++ used0 ++ used1 ++ l3) by assumption.
        rewrite ?in_app_iff. auto.
      + match goal with
        | X: _ |- _ => specialize X with (1 := A); rename X into B
        end.
        destruct B as [B | B].
        * pose proof valid_FlatImp_vars_available_registers as V.
          eapply (proj1 (Forall_forall _ _) V).
          replace available_registers with (used ++ used0 ++ used1 ++ l3) by assumption.
          rewrite ?in_app_iff. auto.
        * match goal with
          | X: _ |- _ => specialize X with (1 := B); rename X into C
          end.
          destruct C as [C | C].
          -- pose proof valid_FlatImp_vars_available_registers as V.
             eapply (proj1 (Forall_forall _ _) V).
             replace available_registers with (used ++ used0 ++ used1 ++ l3) by assumption.
             rewrite ?in_app_iff. auto.
          -- rewrite map.get_empty in C. discriminate C.
    - eapply map.getmany_of_list_injective_NoDup. 3: eassumption. all: eassumption.
    - eapply map.getmany_of_list_injective_NoDup. 3: eassumption. all: eassumption.
    - unfold FlatToRiscvDef.stmt_not_too_big.
      pose proof (rename_preserves_stmt_size _ _ _ _ _ _ E1') as M.
      rewrite <- M.
      assumption.
  Qed.

  Lemma get_build_fun_pos_env: forall e f,
      map.get e f <> None ->
      exists pos, map.get (FlatToRiscvDef.build_fun_pos_env e) f = Some pos.
  Proof.
    intros pos0 e.
    unfold FlatToRiscvDef.build_fun_pos_env, FlatToRiscvDef.compile_funs.
    eapply map.fold_spec.
    - intros. rewrite map.get_empty in H. congruence.
    - intros. destruct r as [ insts env]. simpl.
      rewrite map.get_put_dec in H1.
      rewrite map.get_put_dec.
      destruct_one_match; eauto.
  Qed.

  Local Axiom TODO_andres: False.

  (* TODO not sure if this is the best definition, if needed, etc *)
  Definition byte_list_to_word_list(bytes: list byte): list word. case TODO_andres. Defined.

  Lemma byte_list_to_word_list_array: forall p bytes,
      iff1 (array ptsto (word.of_Z 1) p bytes)
           (array ptsto_word (word.of_Z bytes_per_word) p (byte_list_to_word_list bytes)).
  Proof.
    case TODO_andres.
  Qed.

  Lemma byte_list_to_word_list_length: forall bytes,
      Z.of_nat (Datatypes.length (byte_list_to_word_list bytes)) =
      Z.of_nat (Datatypes.length bytes) / bytes_per_word.
  Proof.
    case TODO_andres.
  Qed.

  Lemma mem_available_ptsto_word: forall stack_trash ml (mlOk: MemoryLayoutOk ml),
      iff1 (array ptsto_word (word.of_Z bytes_per_word) (stack_start ml) stack_trash)
           (mem_available (stack_start ml) (stack_pastend ml)).
  Proof.
    intros. case TODO_andres.
  Qed.

  Lemma get_compile_funs_pos: forall e,
      let '(insts, posmap) := FlatToRiscvDef.compile_funs map.empty e in
      forall f impl, map.get e f = Some impl -> exists pos2, map.get posmap f = Some pos2 /\ pos2 mod 4 = 0.
  Proof.
    intros e.
    unfold FlatToRiscvDef.compile_funs.
    eapply map.fold_spec.
    - intros. rewrite map.get_empty in H. congruence.
    - intros. destruct r as [ insts env]. simpl.
      intros.
      rewrite map.get_put_dec in H1.
      rewrite map.get_put_dec.
      destruct_one_match; eauto.
      eexists. split; [reflexivity|].
      solve_divisibleBy4.
  Qed.

  Lemma mod_2width_mod_bytes_per_word: forall x,
      (x mod 2 ^ width) mod bytes_per_word = x mod bytes_per_word.
  Proof.
    intros.
    rewrite <- Znumtheory.Zmod_div_mod.
    - reflexivity.
    - unfold bytes_per_word. destruct width_cases as [E | E]; rewrite E; reflexivity.
    - destruct width_cases as [E | E]; rewrite E; reflexivity.
    - unfold Z.divide.
      exists (2 ^ width / bytes_per_word).
      unfold bytes_per_word.
      destruct width_cases as [E | E]; rewrite E; simpl.
      1: change (Z.of_nat (Pos.to_nat 4)) with (2 ^ 2).
      2: change (Z.of_nat (Pos.to_nat 8)) with (2 ^ 3).
      all: rewrite <- Z.pow_sub_r by blia;
           rewrite <- Z.pow_add_r by blia;
           reflexivity.
  Qed.

  Lemma program_mod_4_0: forall a instrs R m,
      instrs <> [] ->
      (program a instrs * R)%sep m ->
      word.unsigned a mod 4 = 0.
  Proof.
    intros.
    destruct instrs as [|instr instrs]. 1: congruence.
    simpl in *.
    unfold sep, ptsto_instr, sep, emp in *.
    simp.
    assumption.
  Qed.

  Lemma compile_funs_nonnil: forall e positions positions' f impl instrs,
      map.get e f = Some impl ->
      FlatToRiscvDef.compile_funs positions e = (instrs, positions') ->
      instrs <> [].
  Proof.
    intros e positions.
    unfold FlatToRiscvDef.compile_funs.
    eapply map.fold_spec; intros.
    - rewrite map.get_empty in H.
      discriminate.
    - rewrite map.get_put_dec in H1.
      destr (k =? f)%string.
      + subst.
        unfold FlatToRiscvDef.add_compiled_function in H2. simp.
        unfold FlatToRiscvDef.compile_function.
        destruct impl as [ [args res] body ].
        intro C. destruct l; discriminate.
      + specialize H0 with (1 := H1).
        destruct r as [ instrs'' positions'' ].
        specialize H0 with (1 := eq_refl).
        intro C. subst instrs.
        unfold FlatToRiscvDef.add_compiled_function in H2. simp.
        unfold FlatToRiscvDef.compile_function in *.
        destruct v as [ [args res] body ].
        destruct instrs''; discriminate.
  Qed.

  Ltac ignore_positions :=
    repeat match goal with
           | |- _ => reflexivity
           | |- _ => rewrite !List.app_length
           | |- _ => solve [eauto]
           | |- _ => progress simpl
           | |- S _ = S _ => f_equal
           | |- (_ + _)%nat = (_ + _)%nat => f_equal
           end.

  Lemma compile_stmt_length_ignores_positions: forall posmap1 posmap2 c pos1 pos2,
      List.length (FlatToRiscvDef.compile_stmt posmap1 pos1 c) =
      List.length (FlatToRiscvDef.compile_stmt posmap2 pos2 c).
  Proof.
    induction c; intros; ignore_positions.
  Qed.

  Lemma compile_function_length_ignores_positions: forall posmap1 posmap2 pos1 pos2 impl,
      List.length (FlatToRiscvDef.compile_function posmap1 pos1 impl) =
      List.length (FlatToRiscvDef.compile_function posmap2 pos2 impl).
  Proof.
    intros. destruct impl as [ [args rets] body ]. ignore_positions.
    apply compile_stmt_length_ignores_positions.
  Qed.

  Lemma build_fun_pos_env_ignores_posmap_aux: forall posmap1 posmap2 e i1 m1 i2 m2,
      map.fold (FlatToRiscvDef.add_compiled_function posmap1) ([], map.empty) e = (i1, m1) ->
      map.fold (FlatToRiscvDef.add_compiled_function posmap2) ([], map.empty) e = (i2, m2) ->
      m1 = m2 /\ List.length i1 = List.length i2.
  Proof.
    intros until e.
    eapply map.fold_parametricity with (fa := (FlatToRiscvDef.add_compiled_function posmap1))
                                       (fb := (FlatToRiscvDef.add_compiled_function posmap2));
      intros.
    - destruct a as [insts1 map1]. destruct b as [insts2 map2].
      unfold FlatToRiscvDef.add_compiled_function in *.
      inversion H0. inversion H1. subst. clear H0 H1.
      specialize H with (1 := eq_refl) (2 := eq_refl). destruct H.
      rewrite ?H0. subst.
      split. 1: reflexivity.
      ignore_positions.
      apply compile_function_length_ignores_positions.
    - inversion H. inversion H0. subst. auto.
  Qed.

  Lemma build_fun_pos_env_ignores_posmap: forall posmap1 posmap2 e,
      snd (map.fold (FlatToRiscvDef.add_compiled_function posmap1) ([], map.empty) e) =
      snd (map.fold (FlatToRiscvDef.add_compiled_function posmap2) ([], map.empty) e).
  Proof.
    intros.
    destr (map.fold (FlatToRiscvDef.add_compiled_function posmap1) ([], map.empty) e).
    destr (map.fold (FlatToRiscvDef.add_compiled_function posmap2) ([], map.empty) e).
    simpl.
    edestruct build_fun_pos_env_ignores_posmap_aux.
    - exact E.
    - exact E0.
    - assumption.
  Qed.

  (* This lemma should relate two map.folds which fold two different f over the same env e:
     1) FlatToRiscvDef.compile_funs, which folds FlatToRiscvDef.add_compiled_function.
        Note that this one is called twice: First in build_fun_pos_env, and then in
        compile_funs, and we rely on the order being the same both times.
     2) functions, which folds sep
     Note that 1) is not commutative (the iteration order determines in which order code
     is layed out in memory), while 2) should be commutative because the "function"
     separation logic predicate it seps onto the separation logic formula is the same
     if we pass it the same function position map. *)
  Lemma functions_to_program: forall ml functions_start e instrs pos_map,
      riscvPhase ml e = Some (instrs, pos_map) ->
      iff1 (program functions_start instrs)
           (FlatToRiscvFunctions.functions functions_start (FlatToRiscvDef.build_fun_pos_env e) e).
  Proof.
    (* PARAMRECORDS *)
    assert (map.ok FlatImp.env). { unfold FlatImp.env. simpl. typeclasses eauto. }
    assert (map.ok mem) as Ok by exact mem_ok.

    unfold riscvPhase.
    intros.
    simp.
    unfold FlatToRiscvDef.compile_funs, functions in *.
    remember (FlatToRiscvDef.build_fun_pos_env e) as positions.
    (* choose your IH carefully! *)
    lazymatch goal with
    | |- ?G => enough ((forall f, map.get r f <> None <-> map.get e f <> None) /\
                       ((forall f pos, map.get r f = Some pos -> map.get positions f = Some pos) -> G))
    end.
    1: {
      destruct H0. apply H1; clear H1.
      intros. rewrite <- H1. f_equal.
      subst.
      apply (f_equal snd) in E1. simpl in E1. rewrite <- E1.
      transitivity (snd (map.fold (FlatToRiscvDef.add_compiled_function map.empty) ([], map.empty) e)).
      - unfold FlatToRiscvDef.build_fun_pos_env, snd. reflexivity.
      - apply build_fun_pos_env_ignores_posmap.
    }
    revert E1.
    revert instrs r. clear E E0 z.
    eapply (map.fold_spec (R:=(list Instruction * _))) with (m:=e); repeat (cbn || simp || intros).
    { rewrite map.fold_empty. intuition try reflexivity.
      - eapply H0. eapply map.get_empty.
      - eapply H0. eapply map.get_empty.
    }
    rewrite map.fold_put; trivial.
    2: { intros.
      eapply functional_extensionality_dep; intros x.
      eapply PropExtensionality.propositional_extensionality; revert x.
      match goal with |- forall x, ?P x <-> ?Q x => change (iff1 P Q) end.
      cancel. }
    case r as (instrs'&r').
    specialize H1 with (1 := eq_refl).
    unfold FlatToRiscvDef.add_compiled_function in E1.
    injection E1; clear E1; intros. subst.
    unfold program in *.
    wseplog_pre.
    destruct H1.
    split. {
      intros. rewrite ?map.get_put_dec.
      destr (k =? f)%string. 2: eauto. intuition discriminate.
    }
    intros.
    rewrite H2. 2: {
      intros.
      eapply H3.
      rewrite map.get_put_dec.
      destr (k =? f)%string. 2: assumption.
      subst. exfalso.
      specialize (H1 f). unfold not in H1. rewrite H0 in H1. rewrite H4 in H1.
      intuition congruence.
    }
    cancel.
    unfold function.
    specialize (H3 k).
    rewrite map.get_put_same in H3.
    specialize H3 with (1 := eq_refl).
    simpl in *. rewrite H3.
    cancel.
    unfold program.
    cancel_seps_at_indices 0%nat 0%nat. 2: reflexivity.
    f_equal.
    f_equal.
    solve_word_eq word_ok.
  Qed.

  Open Scope ilist_scope.

  Definition machine_ok(p_functions: word)(f_entry_rel_pos: Z)(stack_start stack_pastend: word)
             (finstrs: list Instruction)
             (p_call pc: word)(mH: mem)(Rdata Rexec: mem -> Prop)(mach: MetricRiscvMachine): Prop :=
      let CallInst := Jal RegisterNames.ra
                          (f_entry_rel_pos + word.unsigned p_functions - word.unsigned p_call) : Instruction in
      (program p_functions finstrs *
       program p_call [CallInst] *
       mem_available stack_start stack_pastend *
       Rdata * Rexec * eq mH
      )%sep mach.(getMem) /\
      subset (footpr (program p_functions finstrs *
                      program p_call [CallInst] *
                      Rexec)%sep)
             (of_list (getXAddrs mach)) /\
      word.unsigned (mach.(getPc)) mod 4 = 0 /\
      mach.(getPc) = pc /\
      mach.(getNextPc) = word.add mach.(getPc) (word.of_Z 4) /\
      regs_initialized mach.(getRegs) /\
      map.get mach.(getRegs) RegisterNames.sp = Some stack_pastend /\
      (* configured by PrimitivesParams, can contain invariants needed for external calls *)
      valid_machine mach.

  (* This lemma translates "sim", which depends on the large definition "related", into something
     more understandable and usable. *)
  Lemma compiler_correct: forall
      (ml: MemoryLayout)
      (mlOk: MemoryLayoutOk ml)
      (f_entry_name : string) (fbody: Syntax.cmd.cmd) (f_entry_rel_pos: Z)
      (p_call p_functions: word)
      (Rdata Rexec : mem -> Prop)
      (functions: source_env)
      (instrs: list Instruction)
      (pos_map: funname_env Z)
      (mH: mem) (mc: MetricLog)
      (postH: Semantics.trace -> Semantics.mem -> Prop)
      (initial: MetricRiscvMachine),
      ExprImp.valid_funs functions ->
      compile ml functions = Some (instrs, pos_map) ->
      map.get functions f_entry_name = Some (nil, nil, fbody) ->
      map.get pos_map f_entry_name = Some f_entry_rel_pos ->
      Semantics.exec functions fbody initial.(getLog) mH map.empty mc (fun t' m' l' mc' => postH t' m') ->
      machine_ok p_functions f_entry_rel_pos ml.(stack_start) ml.(stack_pastend) instrs
                 p_call p_call mH Rdata Rexec initial ->
      runsTo initial (fun final => exists mH',
          postH final.(getLog) mH' /\
          machine_ok p_functions f_entry_rel_pos ml.(stack_start) ml.(stack_pastend) instrs
                     p_call (word.add p_call (word.of_Z 4)) mH' Rdata Rexec final).
  Proof.
    intros.
    match goal with
    | H: map.get pos_map _ = Some _ |- _ => rename H into GetPos
    end.
    unfold compile, composePhases, renamePhase, flattenPhase in *. simp.
    eapply runsTo_weaken.
    - pose proof sim as P. unfold simulation, ExprImp.SimState, ExprImp.SimExec in P.
      specialize (P ml f_entry_rel_pos f_entry_name p_call p_functions Rdata Rexec).
      specialize P with (e1 := functions) (s1 := (initial.(getLog), mH, map.empty, mc)).
      specialize P with (post1 := fun '(t', m', l', mc') => postH t' m').
      simpl in P.
      eapply P; clear P; cycle -1. {
        econstructor.
        + eassumption.
        + reflexivity.
        + unfold map.of_list_zip, map.putmany_of_list_zip. reflexivity.
        + eassumption.
        + intros. exists nil. split; [reflexivity|].
          exists map.empty. split; [reflexivity|].
          eassumption.
      }
      { eassumption. }
      { unfold envs_related.
        intros f [ [argnames resnames] body1 ] G.
        unfold rename_functions in *.
        eapply map.map_all_values_fw.
        5: exact G. 4: eassumption.
        - eapply String.eqb_spec.
        - typeclasses eauto.
        - typeclasses eauto.
      }
      { reflexivity. }
      { unfold machine_ok in *. simp. solve_divisibleBy4. }
      { unfold riscvPhase, machine_ok in *. simp.
        eapply program_mod_4_0. 2: ecancel_assumption.
        destruct (map.map_all_values_fw _ _ _ _ E _ _ H1) as [ [ [args' rets'] fbody' ] [ F G ] ].
        unfold flatten_function in F. simp.
        epose proof (map.map_all_values_fw _ _ _ _ E0 _ _ G) as [ [ [args' rets'] fbody' ] [ F G' ] ].
        unfold rename_fun in F. simp.
        eapply compile_funs_nonnil; eassumption.
      }
      { unfold riscvPhase in *. simp. exact GetPos. }
      { simpl. unfold riscvPhase in *. simpl in *. simp.
        move E1 at bottom.
        eapply fits_stack_seq. 1: eapply fits_stack_skip. {
          eapply Z.div_pos.
          - eapply proj1. eapply word.unsigned_range.
          - clear. unfold bytes_per_word, Memory.bytes_per.
            destruct width_cases as [E | E]; rewrite E; reflexivity.
        }
        destruct (map.map_all_values_fw _ _ _ _ E _ _ H1) as [ [ [args' rets'] fbody' ] [ F G ] ].
        unfold flatten_function in F. simp.
        epose proof (map.map_all_values_fw _ _ _ _ E0 _ _ G) as [ [ [args' rets'] fbody' ] [ F G' ] ].
        unfold rename_fun in F. simp.
        apply_in_hyps rename_binds_preserves_length.
        destruct rets'; [|discriminate].
        destruct args'; [|discriminate].
        repeat match goal with
               | H: _ |- _ => autoforward with typeclass_instances in H
               end.
        econstructor. 1: eassumption.
        eapply fits_stack_monotone. 2: {
          apply Z.sub_le_mono_r.
          eassumption.
        }
        eapply stack_usage_correct; eassumption. }
      { unfold good_e_impl.
        intros.
        simpl in *.
        match goal with
        | H: rename_functions _ _ = _ |- _ => rename H into RenameEq
        end.
        unfold rename_functions in RenameEq.
        match goal with
        | H: _ |- _ => unshelve epose proof (map.map_all_values_bw _ _ _ _ RenameEq _ _ H)
        end.
        simp. destruct v1 as [ [argnames' retnames'] body' ].
        match goal with
        | H: flatten_functions _ _ = _ |- _ => rename H into FlattenEq
        end.
        unfold flatten_functions in FlattenEq.
        match goal with
        | H: _ |- _ => unshelve epose proof (map.map_all_values_bw _ _ _ _ FlattenEq _ _ H) as P
        end.
        unfold flatten_function in P.
        simp.
        match goal with
        | H: ExprImp.valid_funs _ |- _ => rename H into V
        end.
        unfold ExprImp.valid_funs in V.
        specialize V with (1 := Pr).
        unfold ExprImp.valid_fun in V.
        destruct V.
        ssplit.
        - eapply rename_fun_valid; try eassumption.
          unfold ExprImp2FlatImp in *.
          simp.
          repeat match goal with
                 | H: @eq bool _ _ |- _ => autoforward with typeclass_instances in H
                 end.
          assumption.
        - unfold FlatToRiscvDef.build_fun_pos_env, FlatToRiscvDef.build_fun_pos_env.
          pose proof (get_compile_funs_pos r0) as P.
          destruct (FlatToRiscvDef.compile_funs map.empty r0) as [ insts posmap ] eqn: F.
          eapply P.
          eassumption.
      }
      unfold related, compose_relation.
      unfold FlatToRiscvSimulation.related, FlattenExprSimulation.related, RegRename.related.
      refine (ex_intro _ (_, _, _, _) _).
      ssplit; try reflexivity.
      refine (ex_intro _ (_, _, _, _) _).
      ssplit; try reflexivity.
      { intros. ssplit; reflexivity. }
      { unfold machine_ok in *. simp. assumption. }
      { unfold machine_ok in *. simp.
        (* PARAMRECORDS *) simpl.
        solve_word_eq word_ok. }
      unfold goodMachine. simpl. ssplit.
      { simpl. unfold map.extends. intros k v Emp. rewrite map.get_empty in Emp. discriminate. }
      { simpl. unfold map.extends. intros k v Emp. rewrite map.get_empty in Emp. discriminate. }
      { simpl. unfold machine_ok in *. simp. assumption. }
      { (* TODO remove duplicate regs_initialized *) unfold machine_ok in *. simp. assumption. }
      { unfold machine_ok in *. simp. assumption. }
      { unfold machine_ok in *. simp. simpl.
        eapply rearrange_footpr_subset. 1: eassumption.
        (* COQBUG https://github.com/coq/coq/issues/11649 *)
        pose proof (mem_ok: @map.ok (@word (@W (@FlatToRiscvDef_params p))) Init.Byte.byte (@mem p)).
        wwcancel.
        eapply functions_to_program.
        eassumption. }
      { simpl.
        (* COQBUG https://github.com/coq/coq/issues/11649 *)
        pose proof (mem_ok: @map.ok (@word (@W (@FlatToRiscvDef_params p))) Init.Byte.byte (@mem p)).
        unfold machine_ok in *. simp.
        edestruct mem_available_to_exists as [ stack_trash [? ?] ]. 1: simpl; ecancel_assumption.
        exists (byte_list_to_word_list stack_trash).
        split. 2: {
          unfold word_array.
          rewrite <- (iff1ToEq (byte_list_to_word_list_array _ _)).
          match goal with
          | E: Z.of_nat _ = word.unsigned (word.sub _ _) |- _ => simpl in E|-*; rewrite <- E
          end.
          lazymatch goal with
          | H: riscvPhase _ _ = _ |- _ => specialize functions_to_program with (1 := H) as P
          end.
          symmetry in P.
          simpl in P|-*. unfold program in P.
          seprewrite P. clear P.
          assert (word.ok FlatImp.word) by exact word_ok.
          rewrite <- Z_div_exact_2; cycle 1. {
            unfold bytes_per_word. clear -h.
            destruct width_cases as [E | E]; rewrite E; reflexivity.
          }
          {
            match goal with
            | H: ?x = ?y |- _ => rewrite H
            end.
            destruct mlOk.
            rewrite word.unsigned_sub. unfold word.wrap.
            rewrite mod_2width_mod_bytes_per_word.
            rewrite Zminus_mod.
            rewrite stack_start_aligned.
            rewrite stack_pastend_aligned.
            rewrite Z.sub_diag.
            apply Zmod_0_l.
          }
          wcancel_assumption.
          rewrite word.of_Z_unsigned.
          cancel_seps_at_indices O O. {
            (* PARAMRECORDS *) simpl.
            sepclause_eq word_ok.
          }
          cbn [seps]. reflexivity.
        }
        match goal with
        | E: Z.of_nat _ = word.unsigned (word.sub _ _) |- _ => simpl in E|-*; rewrite <- E
        end.
        apply byte_list_to_word_list_length. }
      { reflexivity. }
      { unfold machine_ok in *. simp. assumption. }
    - intros. unfold compile_inv, related, compose_relation in *.
      match goal with
      | H: context[machine_ok] |- _ =>
        unfold machine_ok in H;
        repeat match type of H with
               | _ /\ _ => let A := fresh "HOK0" in destruct H as [A H];
                           lazymatch type of A with
                           | verify _ _ => idtac
                           | _ = p_call => idtac
                         (*| _ => clear A*)
                           end
               end
      end.
      subst.
      repeat match goal with
             | H: context[Semantics.exec] |- _ => clear H
             end.
      unfold FlatToRiscvSimulation.related, FlattenExprSimulation.related, RegRename.related, goodMachine in *.
      simp.
      eexists. split. 1: eassumption.
      unfold machine_ok. ssplit; try assumption.
      + use_sep_assumption.
        cbn [dframe xframe ghostConsts program_base ghostConsts e_pos e_impl p_insts insts].
        progress simpl (@FlatToRiscvCommon.mem (@FlatToRiscv_params p)).
        wwcancel.
        cancel_seps_at_indices 0%nat 3%nat. {
          reflexivity.
        }
        cancel_seps_at_indices 0%nat 2%nat. {
          cbn [num_stackwords ghostConsts p_sp].
          replace (word.sub (stack_pastend ml) (word.of_Z (bytes_per_word *
                      (word.unsigned (word.sub (stack_pastend ml) (stack_start ml)) / bytes_per_word))))
            with (stack_start ml). 2: {
            rewrite <- Z_div_exact_2; cycle 1. {
              unfold bytes_per_word. clear -h. simpl.
              destruct width_cases as [E | E]; rewrite E; reflexivity.
            }
            {
              destruct mlOk.
              rewrite word.unsigned_sub. unfold word.wrap.
              rewrite mod_2width_mod_bytes_per_word.
              rewrite Zminus_mod.
              rewrite stack_start_aligned.
              rewrite stack_pastend_aligned.
              rewrite Z.sub_diag.
              apply Zmod_0_l.
            }
            rewrite word.of_Z_unsigned.
            solve_word_eq word_ok.
          }
          apply iff1ToEq.
          apply mem_available_ptsto_word.
          assumption.
        }
        unfold ptsto_instr.
        simpl.
        unfold ptsto_bytes, ptsto_instr, truncated_scalar, littleendian, ptsto_bytes.ptsto_bytes.
        simpl.
        assert (map.ok mem). { exact mem_ok. } (* PARAMRECORDS *)
        wwcancel.
        epose proof (functions_to_program ml _ r0 instrs) as P.
        cbn [seps].
        rewrite <- P; clear P.
        * wwcancel. reflexivity.
        * eassumption.
      + unfold machine_ok in *. simp. simpl.
        eapply rearrange_footpr_subset. 1: eassumption.
        (* COQBUG https://github.com/coq/coq/issues/11649 *)
        pose proof (mem_ok: @map.ok (@word (@W (@FlatToRiscvDef_params p))) Init.Byte.byte (@mem p)).
        (* TODO remove duplication *)
        lazymatch goal with
        | H: riscvPhase _ _ = _ |- _ => specialize functions_to_program with (1 := H) as P
        end.
        symmetry in P.
        rewrite P. clear P.
        cbn [dframe xframe ghostConsts program_base ghostConsts e_pos e_impl p_insts insts program].
        simpl.
        unfold ptsto_bytes, ptsto_instr, truncated_scalar, littleendian, ptsto_bytes.ptsto_bytes.
        simpl.
        wwcancel.
      + destr_RiscvMachine final. subst. solve_divisibleBy4.
    Unshelve.
    all: try exact (bedrock2.MetricLogging.mkMetricLog 0 0 0 0).
    all: try (simpl; typeclasses eauto).
    all: try exact EmptyString.
    all: try exact nil.
    all: try exact map.empty.
    all: try exact mem_ok.
  Qed.

  Definition instrencode(p: list Instruction): list byte :=
    List.flat_map (fun inst => HList.tuple.to_list (LittleEndian.split 4 (encode inst))) p.

End Pipeline1.
