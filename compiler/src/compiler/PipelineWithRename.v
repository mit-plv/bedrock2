Require Export Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Export ListNotations.
Require Export coqutil.Decidable.
Require        compiler.ExprImp.
Require Export compiler.FlattenExprDef.
Require Export compiler.FlattenExpr.
Require        compiler.FlatImp.
Require Export riscv.Spec.Decode.
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
Require Export riscv.Spec.Primitives.
Require Export riscv.Spec.MetricPrimitives.
Require Import compiler.GoFlatToRiscv.
Require Import riscv.Utility.MkMachineWidth.
Require Export riscv.Proofs.DecodeEncode.
Require Export riscv.Proofs.EncodeBound.
Require Export compiler.EmitsValid.
Require coqutil.Map.SortedList.
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

Module List.
  Lemma nth_error_option_all{T: Type}: forall {l1: list (option T)} {l2: list T} (i: nat),
    List.option_all l1 = Some l2 ->
    (i < List.length l1)%nat ->
    exists v, nth_error l2 i = Some v.
  Proof.
    induction l1; intros.
    - simpl in *. exfalso. inversion H0.
    - simpl in *. simp.
      destruct i as [|j].
      + simpl. eauto.
      + simpl. assert (j < List.length l1)%nat as D by blia. eauto.
  Qed.

  Lemma In_option_all{T: Type}: forall {l1: list (option T)} {l2: list T} {v1o: option T},
    List.option_all l1 = Some l2 ->
    List.In v1o l1 ->
    exists v1, v1o = Some v1 /\ List.In v1 l2.
  Proof.
    induction l1; intros.
    - simpl in *. contradiction.
    - simpl in *. simp. destruct H0.
      + subst. simpl. eauto.
      + simpl. firstorder idtac.
  Qed.

  (* same as nodup from standard library but using BoolSpec instead of sumbool *)
  Definition dedup{A: Type}(aeqb: A -> A -> bool){aeqb_spec: EqDecider aeqb}: list A -> list A :=
    fix rec l :=
      match l with
      | [] => []
      | x :: xs => if List.find (aeqb x) xs then rec xs else x :: rec xs
      end.

  Lemma dedup_preserves_In{A: Type}(aeqb: A -> A -> bool){aeqb_spec: EqDecider aeqb}(l: list A) a:
    In a l <-> In a (dedup aeqb l).
  Proof.
    induction l.
    - simpl. firstorder idtac.
    - simpl. split; intro H.
      + destruct H.
        * subst. destruct_one_match.
          { apply find_some in E. destruct E as [E1 E2].
            destr (aeqb a a0). 2: discriminate. subst a0. firstorder idtac. }
          { simpl. auto. }
        * destruct_one_match.
          { apply find_some in E. destruct E as [E1 E2].
            destr (aeqb a0 a1). 2: discriminate. subst a0. firstorder idtac. }
          { simpl. firstorder idtac. }
      + destruct_one_match_hyp.
        * apply find_some in E. destruct E as [E1 E2].
          destr (aeqb a0 a1). 2: discriminate. subst a0. firstorder idtac.
        * simpl in H. destruct H.
          { subst. auto. }
          { firstorder idtac. }
  Qed.

  Lemma NoDup_dedup{A: Type}(aeqb: A -> A -> bool){aeqb_spec: EqDecider aeqb}: forall (l: list A),
      NoDup (dedup aeqb l).
  Proof.
    induction l.
    - simpl. constructor.
    - simpl. destruct_one_match.
      + assumption.
      + constructor. 2: assumption.
        intro C.
        apply dedup_preserves_In in C.
        pose proof (find_none _ _ E _ C).
        destr (aeqb a a); congruence.
  Qed.

End List.


(* TODO express flatten_functions in terms of this, or add map_values, or get_dom to the
   map interface *)
Section MapKeys.
  Context {K V1 V2: Type} {M1: map.map K V1} {M2: map.map K V2}.

  Definition map_values(f: V1 -> V2)(m1: M1): list K -> M2 :=
    fix rec keys :=
      match keys with
      | nil => map.empty
      | k :: ks =>
        match map.get m1 k with
        | Some v1 => map.put (rec ks) k (f v1)
        | None => map.empty
        end
      end.

  Context (keqb: K -> K -> bool) {keqb_spec: EqDecider keqb}
          {OK1: map.ok M1} {OK2: map.ok M2}.

  Lemma get_map_values: forall (f: V1 -> V2) (keys: list K) (m1: M1) (k: K) (v1: V1),
      (forall x, In x keys -> map.get m1 x <> None) ->
      In k keys ->
      map.get m1 k = Some v1 ->
      map.get (map_values f m1 keys) k = Some (f v1).
  Proof.
    induction keys; intros.
    - simpl in *. contradiction.
    - simpl in *.
      destruct H0.
      + subst.
        destr (map.get m1 k).
        * rewrite map.get_put_same. congruence.
        * exfalso. eapply H. 2: exact E. auto.
      + destr (map.get m1 a).
        * rewrite map.get_put_dec.
          destr (keqb a k).
          { subst. congruence. }
          { eauto. }
        * exfalso. unfold not in H. eauto.
  Qed.

End MapKeys.


Module Import Pipeline.
  Definition varname := string.

  Class parameters := {
    FlatToRiscvDef_params :> FlatToRiscvDef.FlatToRiscvDef.parameters;

    mem :> map.map word byte;
    locals :> map.map varname word;
    Registers :> map.map Register word;
    funname_env :> forall T: Type, map.map string T; (* abstract T for better reusability *)
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
    FlattenExpr.varname := varname;
    FlattenExpr.varname_eqb := String.eqb;
    FlattenExpr.W := _;
    FlattenExpr.locals := locals;
    FlattenExpr.mem := mem;
    FlattenExpr.ext_spec := ext_spec;
    FlattenExpr.NGstate := string;
  }.

  Instance FlatToRiscv_params{p: parameters}: FlatToRiscvCommon.parameters := {|
    FlatToRiscvCommon.ext_spec := ext_spec;
  |}.

  Class assumptions{p: parameters}: Prop := {
    word_riscv_ok :> RiscvWordProperties.word.riscv_ok word;
    mem_ok :> map.ok mem;
    locals_ok :> map.ok locals;
    funname_env_ok :> forall T, map.ok (funname_env T);
    (* src2imp_ok :> map.ok src2imp; *)
    Registers_ok :> map.ok Registers;
    PR :> MetricPrimitives PRParams;
    FlatToRiscv_hyps :> FlatToRiscvCommon.assumptions;
    ext_spec_ok :> Semantics.ext_spec.ok (FlattenExpr.mk_Semantics_params FlattenExpr_parameters);
  }.

End Pipeline.


Section Pipeline1.

  Context {p: parameters}.
  Context {h: assumptions}.

  Definition funname := string.

  Axiom TODO_sam: False.

  Instance FlattenExpr_hyps: FlattenExpr.assumptions FlattenExpr_parameters := {
    FlattenExpr.locals_ok := locals_ok;
    FlattenExpr.mem_ok := mem_ok;
    FlattenExpr.funname_env_ok := funname_env_ok;
    FlattenExpr.ext_spec_ok := ext_spec_ok;
  }.

  Definition available_registers: list Register :=
    Eval cbv in List.unfoldn Z.succ 29 3.

  Lemma NoDup_available_registers: NoDup available_registers.
  Proof. cbv. repeat constructor; cbv; intros; intuition congruence. Qed.

  Lemma valid_FlatImp_vars_available_registers: Forall FlatToRiscvDef.valid_FlatImp_var available_registers.
  Proof. repeat constructor; cbv; intros; discriminate. Qed.

  Local Notation source_env :=
    (@funname_env p (list string * list string * (@Syntax.cmd (FlattenExpr.mk_Syntax_params _)))).
  Local Notation flat_env :=
    (@funname_env p (list string * list string * (@FlatImp.stmt (FlattenExpr.mk_Syntax_params _)))).
  Local Notation renamed_env :=
    (@funname_env p (list Z * list Z * @FlatImp.stmt (@impparams Z string string))).

  Definition flattenPhase(prog: source_env): option flat_env := flatten_functions (2^10) prog.
  Definition renamePhase(prog: flat_env): option renamed_env :=
    rename_functions String.eqb Z.eqb String.eqb String.eqb
                     available_registers ext_spec prog.

  (* Note: we could also track code size from the source program all the way to the target
     program, and a lot of infrastructure is already there, will do once/if we want to get
     a total compiler.
     Returns the fun_pos_env so that users know where to jump to call the compiled functions. *)
  Definition riscvPhase(ml: MemoryLayout Semantics.width)(prog: renamed_env):
    option (list Instruction * funname_env Z) :=
    bind_opt stack_needed <- stack_usage prog;
    let num_stackwords := word.unsigned (word.sub ml.(stack_pastend) ml.(stack_start)) / bytes_per_word in
    if Z.ltb num_stackwords stack_needed then None (* not enough stack *) else
    (* TODO compile_funs should be map.fold so that it doesn't need the funnames arg *)
    let funnames := map.fold (fun acc fname fimpl => cons fname acc) nil prog in
    let positions := FlatToRiscvDef.function_positions prog in
    let i := FlatToRiscvDef.compile_funs positions prog 0 funnames in
    let maxSize := word.unsigned ml.(code_pastend) - word.unsigned ml.(code_start) in
    if 4 * Z.of_nat (List.length i) <=? maxSize then Some (i, positions) else None.

  Definition composePhases{A B C: Type}(phase1: A -> option B)(phase2: B -> option C)(a: A) :=
    match phase1 a with
    | Some b => phase2 b
    | None => None
    end.

  Definition compile(ml: MemoryLayout Semantics.width):
    source_env -> option (list Instruction * funname_env Z) :=
    (composePhases flattenPhase
    (composePhases renamePhase
                   (riscvPhase ml))).

  Local Notation cmd := (@Syntax.cmd (FlattenExprDef.FlattenExpr.mk_Syntax_params _)).
  Local Notation env := (@Semantics.env (FlattenExpr.mk_Semantics_params _)).
  Local Notation localsH := (@Semantics.locals (FlattenExpr.mk_Semantics_params _)).

  Context (ml: MemoryLayout Semantics.width)
          (mlOk: MemoryLayoutOk ml).

  Context (f_entry_rel_pos : Z)
          (f_entry_name : string)
          (p_call: word) (* address where the call to the entry function is stored *)
          (Rdata Rexec : FlatToRiscvCommon.mem -> Prop).

  Definition related :=
    (compose_relation (FlattenExprSimulation.related (2^10))
    (compose_relation (RegRename.related eqb Z.eqb eqb eqb available_registers ext_spec)
                      (FlatToRiscvSimulation.related f_entry_rel_pos f_entry_name p_call Rdata Rexec
                                                     ml.(code_start) ml.(stack_start) ml.(stack_pastend)))).

  Definition flattenSim := FlattenExprSimulation.flattenExprSim (2^10).
  Definition regAllocSim := renameSim String.eqb Z.eqb String.eqb String.eqb
                                      available_registers (@ext_spec p) NoDup_available_registers.
  Definition flatToRiscvSim := FlatToRiscvSimulation.flatToRiscvSim
                                 f_entry_rel_pos f_entry_name p_call Rdata Rexec
                                 ml.(code_start) ml.(stack_start) ml.(stack_pastend).

  Lemma sim: simulation ExprImp.SimExec runsTo related.
  Proof. exact (compose_sim flattenSim (compose_sim regAllocSim flatToRiscvSim)). Qed.

End Pipeline1.
