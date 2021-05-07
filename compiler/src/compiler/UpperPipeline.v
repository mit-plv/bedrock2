Require Export Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Export ListNotations.
Require Import coqutil.Decidable.
Require Import coqutil.Z.Lia.
Require Import coqutil.Tactics.Simp.
Require Import bedrock2.MetricLogging.
Require Import compiler.ExprImp.
Require Import compiler.FlattenExprDef.
Require Import compiler.FlattenExpr.
Require Import compiler.FlatImp.
Require Import compiler.NameGen.
Require Import compiler.StringNameGen.
Require Import compiler.util.Common.
Require Import compiler.SeparationLogic.
Require Import compiler.Spilling.
Require Import compiler.RegRename.

Section WithWordAndMem.
  Context {width: Z} {word: Interface.word width} {mem : map.map word byte}.

  (* TODO put into common file *)
  Definition trace: Type := list (mem * string * list word * (mem * list word)).
  Definition ExtSpec: Type := trace -> mem -> string -> list word -> (mem -> list word -> Prop) -> Prop.

  Record Lang: Type := {
    Var: Type;
    Cmd: Type;
    Locals : map.map Var word;
    Env : map.map string (list Var * list Var * Cmd);
    Exec: Env -> Cmd -> trace -> mem -> Locals -> MetricLog ->
          (trace -> mem -> Locals -> MetricLog -> Prop) -> Prop
  }.

  Definition relation(L1 L2: Lang): Type := bool ->
    L1.(Env) -> L1.(Cmd) -> trace -> mem -> L1.(Locals) -> MetricLog ->
    L2.(Env) -> L2.(Cmd) -> trace -> mem -> L2.(Locals) -> MetricLog -> Prop.

  Definition simulation{L1 L2: Lang}(R: relation L1 L2) :=
    forall (e1: L1.(Env)) (e2: L2.(Env)) (c1: L1.(Cmd)) (c2: L2.(Cmd))
           (P1: trace -> mem -> L1.(Locals) -> MetricLog -> Prop)
           (P2: trace -> mem -> L2.(Locals) -> MetricLog -> Prop),
      (forall t1 m1 l1 mc1 t2 m2 l2 mc2, R true e1 c1 t1 m1 l1 mc1 e2 c2 t2 m2 l2 mc2 ->
                                         P1 t1 m1 l1 mc1 -> P2 t2 m2 l2 mc2) ->
      (forall t1 m1 l1 mc1 t2 m2 l2 mc2, R false e1 c1 t1 m1 l1 mc1 e2 c2 t2 m2 l2 mc2 ->
                                         L1.(Exec) e1 c1 t1 m1 l1 mc1 P1 ->
                                         L2.(Exec) e2 c2 t2 m2 l2 mc2 P2).

  Definition compose_related{L1 L2 L3: Lang}(R12: relation L1 L2)(R23: relation L2 L3): relation L1 L3 :=
    fun done e1 c1 t1 m1 l1 mc1 e3 c3 t3 m3 l3 mc3 =>
      exists e2 c2 t2 m2 l2 mc2, R12 done e1 c1 t1 m1 l1 mc1 e2 c2 t2 m2 l2 mc2 /\
                                 R23 done e2 c2 t2 m2 l2 mc2 e3 c3 t3 m3 l3 mc3.

  Lemma compose_simulation{L1 L2 L3: Lang}{R12: relation L1 L2}{R23: relation L2 L3}
        (S12: simulation R12)(S23: simulation R23): simulation (compose_related R12 R23).
  Proof.
    unfold simulation, compose_related in *.
    intros e1 e3 c1 c3 P1 P3 W t1 m1 l1 mc1 t3 m3 l3 mc3 R13 Ex1.
    simp.
    eapply S23. 2: eassumption. 2: {
      eapply S12 with (P2 := (fun t2' m2' l2' mc2' => exists t1' m1' l1' mc1',
                                  R12 true e1 c1 t1' m1' l1' mc1' e2 c2 t2' m2' l2' mc2' /\
                                  P1 t1' m1' l1' mc1')).
      3: eassumption. 2: eassumption. clear. eauto 10.
    }
    cbv beta. clear -W. intros. simp. eauto 10.
  Qed.

  Section WithMoreParams.
    Context {Zlocals: map.map Z word}
            {string_keyed_map: forall T: Type, map.map string T} (* abstract T for better reusability *)
            (ext_spec: ExtSpec)
            (width_cases : width = 32 \/ width = 64)
            {word_ok : word.ok word}
            {mem_ok: map.ok mem}
            {string_keyed_map_ok: forall T, map.ok (string_keyed_map T)}
            {Zlocals_ok: map.ok Zlocals}.

    Instance W: Words := {| Utility.width_cases := width_cases |}.

    Instance FlattenExpr_parameters: FlattenExpr.parameters := {
      FlattenExpr.W := _;
      FlattenExpr.locals := _;
      FlattenExpr.mem := mem;
      FlattenExpr.ext_spec := ext_spec;
      FlattenExpr.NGstate := N;
    }.

    Context {ext_spec_ok : Semantics.ext_spec.ok (FlattenExpr.mk_Semantics_params FlattenExpr_parameters)}.

    Definition SrcLang := {|
      Var := string;
      Cmd := Syntax.cmd;
      Env := string_keyed_map (list string * list string * Syntax.cmd);
      Exec := Semantics.exec
    |}.

    Definition FlatLangStr := {|
      Var := string;
      Cmd := FlatImp.stmt string;
      Env := string_keyed_map (list string * list string * FlatImp.stmt string);
      Exec := FlatImp.exec
    |}.

    Instance FlatImp_params: FlatImp.parameters Z := {|
      FlatImp.varname_eqb := Z.eqb;
      FlatImp.ext_spec := ext_spec;
    |}.

    Definition FlatLangZ := {|
      Var := Z;
      Cmd := FlatImp.stmt Z;
      Locals := Zlocals;
      Env := string_keyed_map (list Z * list Z * FlatImp.stmt Z);
      Exec := FlatImp.exec
    |}.

    Instance mk_FlatImp_string_ext_spec_ok:
      FlatImp.ext_spec.ok string (FlattenExpr.mk_FlatImp_params FlattenExpr_parameters).
    Proof.
      destruct ext_spec_ok.
      constructor.
      all: intros; eauto.
      eapply intersect; eassumption.
    Qed.

    Instance mk_FlatImp_Z_ext_spec_ok:
      FlatImp.ext_spec.ok Z FlatImp_params.
    Proof.
      destruct ext_spec_ok.
      constructor.
      all: intros; eauto.
      eapply intersect; eassumption.
    Qed.

    Definition flattenPhase(prog: SrcLang.(Env)): option FlatLangStr.(Env) :=
      flatten_functions prog.
    Definition renamePhase(prog: FlatLangStr.(Env)): option FlatLangZ.(Env) :=
      rename_functions prog.
    Definition spillingPhase(prog: FlatLangZ.(Env)): option FlatLangZ.(Env) :=
      Some (spill_functions prog).

    Definition composePhases{A B C: Type}(phase1: A -> option B)(phase2: B -> option C)(a: A) :=
      match phase1 a with
      | Some b => phase2 b
      | None => None
      end.

    Definition composedCompileEnv: SrcLang.(Env) -> option FlatLangZ.(Env) :=
      (composePhases flattenPhase
      (composePhases renamePhase
                     spillingPhase)).

    Definition flattening_related: relation SrcLang FlatLangStr :=
      fun done e1 c1 t1 m1 l1 mc1 e2 c2 t2 m2 l2 mc2 =>
        ExprImp2FlatImp c1 = c2 /\
        flatten_functions e1 = Some e2 /\
        t1 = t2 /\
        m1 = m2 /\
        (done = false -> l1 = map.empty /\ l2 = map.empty /\ mc1 = mc2).

    Lemma flattening_sim: simulation flattening_related.
    Proof.
      unfold simulation, flattening_related, ExprImp2FlatImp. intros.
      simp. specialize (H0p2 eq_refl). simp.
      eapply FlatImp.exec.weaken.
      - eapply @flattenStmt_correct_aux with (eH := e1).
        + econstructor; try typeclasses eauto.
        + eassumption.
        + eassumption.
        + reflexivity.
        + match goal with
          | |- ?p = _ => rewrite (surjective_pairing p)
          end.
          reflexivity.
        + intros x k A. rewrite map.get_empty in A. discriminate.
        + unfold map.undef_on, map.agree_on. intros. reflexivity.
        + eapply freshNameGenState_disjoint.
      - simpl. intros. simp. eapply H. 2: eassumption. simpl. intuition (discriminate || eauto).
    Qed.

    Definition renaming_related: relation FlatLangStr FlatLangZ :=
      fun done e1 c1 t1 m1 l1 mc1 e2 c2 t2 m2 l2 mc2 =>
      RegRename.envs_related e1 e2 /\
      (exists r' av', RegRename.rename map.empty c1 lowest_available_impvar = Some (r', c2, av')) /\
      t1 = t2 /\
      m1 = m2 /\
      (done = false -> l1 = map.empty /\ l2 = map.empty /\ mc1 = mc2).

    Lemma renaming_sim: simulation renaming_related.
    Proof.
      unfold simulation, renaming_related. intros.
      simp. specialize (H0p3 eq_refl). simp.
      pose proof H0p1 as A.
      apply rename_props in A;
        [|eapply map.empty_injective|eapply dom_bound_empty].
      simp.
      eapply FlatImp.exec.weaken.
      - eapply rename_correct with (ext_spec0 := ext_spec).
        1: eassumption.
        1: eassumption.
        3: {
          eapply Ap2. eapply TestLemmas.extends_refl.
        }
        1: eassumption.
        1: eassumption.
        unfold states_compat. intros *. intro B.
        erewrite map.get_empty in B. discriminate.
      - simpl. intros. simp.
        eapply H. 2: eassumption. simpl. clear H. intuition (discriminate || eauto).
    Qed.

    Axiom TODO: False.

    Definition spilling_related: relation FlatLangZ FlatLangZ :=
      fun done e1 c1 t1 m1 l1 mc1 e2 c2 t2 m2 l2 mc2 =>
      c2 = spill_stmt c1 /\
      exists maxvar (fpval: word),
        Spilling.envs_related e1 e2 /\
        Spilling.valid_vars_src maxvar c1 /\
        Spilling.related ext_spec maxvar (emp True) fpval t1 m1 l1 t2 m2 l2.

    Lemma spilling_sim: simulation spilling_related.
    Proof.
      unfold simulation, spilling_related.
      intros. simp.
      eapply FlatImp.exec.weaken.
      - eapply spilling_correct with (ext_spec0 := ext_spec); eassumption.
      - cbv beta. intros. simp. eapply H. 2: eassumption. simpl.
        eauto 10.
    Qed.

    Definition upper_related: relation SrcLang FlatLangZ :=
      (compose_related flattening_related
      (compose_related renaming_related
                       spilling_related)).

    Lemma sim: simulation upper_related.
    Proof.
      exact (compose_simulation flattening_sim
            (compose_simulation renaming_sim
                                spilling_sim)).
    Qed.

    (* Note: spilling uses stackalloc to store spilled vars in the memory, so there are some points
       in execution where the low-level memory differs from the high-level memory, but before and
       after calling the top-level function the memories are equal, so we can simplify the correctness
       theorem to this case *)

    Lemma upper_compiler_correct: forall
        (f_entry_name : string) (fbodyH: Syntax.cmd.cmd)
        (functionsH: SrcLang.(Env)) (functionsL: FlatLangZ.(Env))
        t (m: mem) (mc: MetricLog)
        (post: Semantics.trace -> Semantics.mem -> Prop),
        ExprImp.valid_funs functionsH ->
        composedCompileEnv functionsH = Some functionsL ->
        map.get functionsH f_entry_name = Some (nil, nil, fbodyH) ->
        Semantics.exec functionsH fbodyH t m map.empty mc (fun t' m' l' mc' => post t' m') ->
        exists fbodyL, map.get functionsL f_entry_name = Some (nil, nil, fbodyL) /\
                       FlatImp.exec functionsL fbodyL t m map.empty mc (fun t' m' l' mc' => post t' m').
    Proof.
      intros.
      unfold composedCompileEnv, composePhases in *. simp.
      rename r into functionsF, r0 into functionsR.

      pose proof E as GF.
      unfold flattenPhase, flatten_functions in GF.
      eapply map.map_all_values_fw in GF. 5: eassumption. 2-4: typeclasses eauto.
      simp. unfold flatten_function in GFp0.
      (* simp would also unfold freshNameGenState *)
      apply Option.eq_of_eq_Some in GFp0. destruct v2 as ((? & ?) & ?).
      eapply pair_equal_spec in GFp0. destruct GFp0 as (GFp0 & ?).
      eapply pair_equal_spec in GFp0. destruct GFp0 as (GFp0 & ?).
      subst.

      pose proof E0 as GR.
      unfold renamePhase, rename_functions in GR.
      eapply map.map_all_values_fw in GR. 5: eassumption. 2-4: typeclasses eauto.
      simp. unfold rename_fun, rename_binds in GRp0. simp.

      pose proof H0 as GL.
      unfold spillingPhase in GL. apply Option.eq_of_eq_Some in GL.
      unfold spill_functions in GL.
      eapply map.map_values_fw in GL. 5: eassumption. 2-4: typeclasses eauto.
      simp. unfold spill_fun in GLp1.

      eexists. split. 1: exact GLp1.

      unfold spill_fbody.
      eapply FlatImp.exec.stackalloc. {
        rewrite Z.mul_comm.
        apply Z_mod_mult.
      }
      intros *. intros Ab Sp.

      pose proof sim as Sim. unfold simulation, upper_related, Exec, SrcLang, FlatLangZ in Sim.
      cbn in Sim. eapply Sim; clear Sim. 3: eassumption.

      2: { (* upper_related holds initially: *)
        unfold compose_related, flattening_related, renaming_related, spilling_related. cbn.
        do 6 eexists. ssplit. all: eauto 3.
        do 6 eexists. ssplit. all: eauto 3.
        { unfold envs_related. intros.
          eapply map.map_all_values_fw. 5: eassumption. 4: eassumption. all: typeclasses eauto. }
        do 2 eexists. ssplit.
        { unfold Spilling.envs_related. intros *. intro G.
          pose proof H0 as GL'.
          unfold spillingPhase in GL'. apply Option.eq_of_eq_Some in GL'.
          unfold spill_functions in GL'.
          eapply map.map_values_fw in GL'. 5: exact G. 2-4: typeclasses eauto.
          simp. ssplit.
          - assumption.
          - (* need that argvars/resvars in (argvars, resvars, body1) are < 32,
               which should almost always be the case because reg rename assigns the lowest
               vars to these and only then continues with the function body *)

    Abort.

    (* Note: Spilling.related has an "exists stackwords", because after spilling, all commands are
       always wrapped inside a stackalloc block, but if we make the command just an argument-less
       function call, we can set stackwords to the empty list and simplify "upper_related" *)


  End WithMoreParams.
End WithWordAndMem.
