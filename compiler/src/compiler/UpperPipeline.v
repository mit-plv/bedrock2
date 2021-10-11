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
Require Import compiler.RegAlloc.

Section WithWordAndMem.
  Context {width: Z} {BW: Bitwidth width} {word: Interface.word width} {mem : map.map word byte}.

  Definition CallSpec(FunEnv: Type): Type :=
    FunEnv -> string -> trace -> mem -> list word -> MetricLog ->
    (trace -> mem -> list word -> Prop) -> Prop.

  Definition phase_correct{Func1 Func2: Type}
             {env1: map.map string Func1}{env2: map.map string Func2}
             (Call1: CallSpec env1)(Call2: CallSpec env2)
             (compile: env1 -> option env2): Prop :=
    forall functions1 functions2 fname,
      compile functions1 = Some functions2 ->
      forall argvals t m mc post,
        Call1 functions1 fname t m argvals mc post ->
        Call2 functions2 fname t m argvals mc post.

  Definition compose_phases{A B C: Type}(phase1: A -> option B)(phase2: B -> option C)(a: A) :=
    match phase1 a with
    | Some b => phase2 b
    | None => None
    end.

  Lemma compose_phases_correct{Func1 Func2 Func3: Type}
        {env1: map.map string Func1}{env2: map.map string Func2}{env3: map.map string Func3}
        (Call1: CallSpec env1)(Call2: CallSpec env2)(Call3: CallSpec env3)
        (compile12: env1 -> option env2)
        (compile23: env2 -> option env3):
    phase_correct Call1 Call2 compile12 ->
    phase_correct Call2 Call3 compile23 ->
    phase_correct Call1 Call3 (compose_phases compile12 compile23).
  Proof.
    unfold phase_correct, compose_phases. intros C12 C23. intros. simp.
    specialize C12 with (1 := E) (2 := H0).
    specialize C23 with (1 := H) (2 := C12).
    exact C23.
  Qed.

  Section WithMoreParams.
    Context {Zlocals: map.map Z word}
            {string_keyed_map: forall T: Type, map.map string T} (* abstract T for better reusability *)
            {ext_spec: ExtSpec}
            {word_ok : word.ok word}
            {mem_ok: map.ok mem}
            {string_keyed_map_ok: forall T, map.ok (string_keyed_map T)}
            {Zlocals_ok: map.ok Zlocals}.

    Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

    Definition SrcLang: CallSpec (string_keyed_map (list string * list string * Syntax.cmd)) :=
      fun e f t m argvals mc post =>
        exists argnames retnames fbody,
          map.get e f = Some (argnames, retnames, fbody) /\
          forall l, map.of_list_zip argnames argvals = Some l ->
                    Semantics.exec e fbody t m l mc (fun t' m' l' mc' =>
                      exists retvals, map.getmany_of_list l' retnames = Some retvals /\
                                      post t' m' retvals).

    Definition FlatLang(Var: Type){locals: map.map Var word}:
      CallSpec (string_keyed_map (list Var * list Var * FlatImp.stmt Var)) :=
      fun e f t m argvals mc post =>
        exists argnames retnames fbody,
          map.get e f = Some (argnames, retnames, fbody) /\
          forall l, map.of_list_zip argnames argvals = Some l ->
                    FlatImp.exec e fbody t m l mc (fun t' m' l' mc' =>
                      exists retvals, map.getmany_of_list l' retnames = Some retvals /\
                                      post t' m' retvals).

    Lemma flattening_correct: phase_correct SrcLang (FlatLang string) flatten_functions.
    Proof.
      unfold phase_correct, SrcLang, FlatLang. intros. simp.

      pose proof H as GF.
      unfold flatten_functions in GF.
      eapply map.map_all_values_fw in GF. 5: eassumption. 2-4: typeclasses eauto.
      unfold flatten_function in GF. simp.

      eexists _, _, _. split. 1: eassumption.
      intros.
      eapply FlatImp.exec.weaken.
      - eapply flattenStmt_correct_aux with (mcH := mc).
        + eassumption.
        + eauto.
        + reflexivity.
        + match goal with
          | |- ?p = _ => rewrite (surjective_pairing p)
          end.
          reflexivity.
        + intros x k A. assumption.
        + unfold map.undef_on, map.agree_on. cbn. intros k A.
          rewrite map.get_empty. destr (map.get l k). 2: reflexivity. exfalso.
          unfold map.of_list_zip in H0.
          edestruct (map.putmany_of_list_zip_find_index _ _ _ _ _ _ H0 E) as [G | G]. 2: {
            rewrite map.get_empty in G. discriminate.
          }
          destruct G as (i & G1 & G2).
          eapply nth_error_In in G1.
          eapply start_state_spec. 2: exact A.
          eapply ListSet.In_list_union_l. eapply ListSet.In_list_union_l. assumption.
        + eapply @freshNameGenState_disjoint_fbody.
      - simpl. intros. simp. eauto using map.getmany_of_list_extends.
    Qed.

    Lemma regalloc_correct: phase_correct (FlatLang string) (FlatLang Z) regalloc_functions.
    Proof.
      unfold phase_correct, FlatLang. intros. simp.

      pose proof H as GR.
      unfold regalloc_functions in GR.
      simp. rename E into GR.
      eapply map.map_all_values_fw in GR. 5: eassumption. 2-4: typeclasses eauto.
      simp. clear GRp0.
      pose proof E0 as C.
      unfold check_funcs in E0.
      eapply map.get_forallb in E0. 2: eassumption.
      unfold lookup_and_check_func, check_func in E0. simp.

      eexists _, _, _. split. 1: reflexivity. intros.
      unfold map.of_list_zip in *.
      apply_in_hyps assert_ins_same_length.
      apply_in_hyps assignments_same_length.
      apply_in_hyps @map.putmany_of_list_zip_sameLength.
      assert (List.length argnames = List.length argvals) as P by congruence.
      eapply map.sameLength_putmany_of_list in P. destruct P as [st2 P].
      eapply FlatImp.exec.weaken.
      - eapply checker_correct; eauto.
        eapply states_compat_precond.
        edestruct putmany_of_list_zip_states_compat as (lL' & P' & Cp); try eassumption.
        1: eapply states_compat_empty.
        rewrite H0 in P'. inversion P'. exact Cp.
      - simpl. intros. simp. eexists. split. 2: eassumption.
        destruct u. eauto using states_compat_getmany.
    Qed.

    Lemma spilling_correct: phase_correct (FlatLang Z) (FlatLang Z) spill_functions.
    Proof.
      unfold phase_correct, FlatLang. intros. simp.
      pose proof H as GL.
      unfold spill_functions in GL.
      eapply map.map_all_values_fw in GL. 5: eassumption. 2-4: typeclasses eauto.
      destruct GL as (((argnames2 & retnames2) & fbody2) & Sp & G2).
      exists argnames2, retnames2, fbody2.
      split. 1: exact G2.
      eapply spill_fun_correct; eassumption.
    Qed.

    Definition upper_compiler :=
      compose_phases flatten_functions (compose_phases regalloc_functions spill_functions).

    Lemma upper_compiler_correct: phase_correct SrcLang (FlatLang Z) upper_compiler.
    Proof.
      unfold upper_compiler.
      eapply compose_phases_correct. 1: exact flattening_correct.
      eapply compose_phases_correct. 1: exact regalloc_correct.
      exact spilling_correct.
    Qed.

  End WithMoreParams.
End WithWordAndMem.
