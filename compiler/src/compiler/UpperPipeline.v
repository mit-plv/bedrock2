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
      unfold spill_fun in GL. simp.
      eapply Bool.andb_true_iff in E. destruct E as (E & LR). eapply Nat.leb_le in LR.
      eapply Bool.andb_true_iff in E. destruct E as (E & LA). eapply Nat.leb_le in LA.
      eapply Bool.andb_true_iff in E. destruct E as (E & Fs).
      eapply Bool.andb_true_iff in E. destruct E as (Fargs & Frets).
      unfold is_valid_src_var in *.
      eapply forallb_vars_stmt_correct in Fs. 2: {
        intros x. split; intros F.
        - rewrite ?Bool.andb_true_iff, ?Bool.orb_true_iff, ?Z.ltb_lt in F. exact F.
        - rewrite ?Bool.andb_true_iff, ?Bool.orb_true_iff, ?Z.ltb_lt. exact F.
      }
      eexists _, _, _. split. 1: eassumption. intros.
      unfold map.of_list_zip in *.

      rewrite ?List.firstn_length in *.
      pose proof H0 as L. eapply map.putmany_of_list_zip_sameLength in L.
      replace (Datatypes.length argnames) with
          (Datatypes.length (List.firstn (Datatypes.length argnames)
                   (Registers.reg_class.all Registers.reg_class.arg))) in L. 2: {
        rewrite List.firstn_length.
        change (Datatypes.length (Registers.reg_class.all Registers.reg_class.arg)) with 8%nat.
        blia.
      }
      eapply map.sameLength_putmany_of_list in L. destruct L as (lL & PM').
      (* Note: redoing half (the callee part, but not the caller part) of call case of
         spilling proof... *)

      (*
      eapply FlatImp.exec.stackalloc. {
        rewrite Z.mul_comm.
        apply Z_mod_mult.
      }
      intros *. intros Ab Sp.

      assert (BW48: bytes_per_word = 4 \/ bytes_per_word = 8). {
        unfold bytes_per_word.
        destruct width_cases as [C | C]; rewrite C.
        + change (Memory.bytes_per_word 32) with 4. auto.
        + change (Memory.bytes_per_word 64) with 8. auto.
      }

      eapply FlatImp.exec.weaken.
      - eapply spilling_correct. 2: eassumption.
        { unfold Spilling.envs_related. intros *. intro G.
          pose proof H as GL'.
          unfold spill_functions in GL'.
          eapply map.map_all_values_fw in GL'. 5: exact G. 2-4: typeclasses eauto.
          unfold spill_fun in GL'. simp.
          eapply Bool.andb_true_iff in E. destruct E as (B1 & B3).
          eapply Bool.andb_true_iff in B1. destruct B1 as (B1 & B2).
          eapply List.forallb_to_Forall in B1. 2: {
            intros x F. rewrite Bool.andb_true_iff in F. rewrite ?Z.ltb_lt in F. exact F.
          }
          eapply List.forallb_to_Forall in B2. 2: {
            intros x F. rewrite Bool.andb_true_iff in F. rewrite ?Z.ltb_lt in F. exact F.
          }
          eapply forallb_vars_stmt_correct in B3. 2: {
            intros x. split; intros F.
            - rewrite ?Z.ltb_lt in F. exact F.
            - apply Z.ltb_lt. assumption.
          }
          2: {
            intros x. split; intros F.
            - rewrite Bool.andb_true_iff in F. rewrite ?Z.ltb_lt in F. exact F.
            - apply  Bool.andb_true_iff. rewrite ?Z.ltb_lt. assumption.
          }
          ssplit; try assumption.
          unfold valid_vars_src.
          eapply max_var_sound. exact B3.
        }
        { unfold valid_vars_src.
          eapply max_var_sound. exact Fs. }
        { unfold Spilling.related.
          edestruct hl_mem_to_ll_mem with (mL := mCombined) (mTraded := mStack) (R := emp (map := mem) True)
            as (returned_bytes & L & Q).
          1, 2: eassumption.
          { rewrite sep_emp_r. clear. auto. }
          edestruct (byte_list_to_word_list_array returned_bytes) as (returned_words & LL & QQ). {
            rewrite L. rewrite Z2Nat.id.
            - rewrite Z.mul_comm. apply Z_mod_mult.
            - blia.
          }
          seprewrite_in QQ Q. unfold word_array.
          eexists map.empty, l1, returned_words.
          ssplit.
          - reflexivity.
          - ecancel_assumption.
          - intros *. intro G.
            epose proof (proj1 (@forallb_forall _ _ _) Fargs _) as A. cbv beta in A.
            rewrite Bool.andb_true_iff in A. rewrite !Z.ltb_lt in A. eapply A.
            eauto using map.putmany_of_list_zip_to_In.
          - intros *. rewrite map.get_empty. discriminate.
          - unfold sep, map.split. exists l1, map.empty.
            rewrite ?map.putmany_empty_r. eauto using map.disjoint_empty_r.
          - unfold sep, map.split, ptsto. eexists l1, _. ssplit.
            4: reflexivity.
            + rewrite <- map.put_putmany_commute. rewrite map.putmany_empty_r. reflexivity.
            + apply map.disjoint_comm. unfold map.disjoint. intros *. intros G1 G2.
              rewrite map.get_put_dec in G1. rewrite map.get_empty in G1. destr (fp =? k). 2: discriminate.
              apply Option.eq_of_eq_Some in G1. subst k a.
              eapply map.putmany_of_list_zip_to_In in H1. 2: exact G2.
              epose proof (proj1 (@forallb_forall _ _ _) Fargs _ H1) as A. cbv beta in A.
              rewrite Bool.andb_true_iff in A. rewrite !Z.ltb_lt in A. clear -A. blia.
            + exists l1, map.empty. unfold tmps. setoid_rewrite map.get_empty.
              rewrite map.putmany_empty_r.
              intuition (eauto using map.disjoint_empty_r || discriminate).
          - intros ? ? ? C. rewrite map.get_empty in C. discriminate C.
          - eapply Nat2Z.inj. rewrite LL. rewrite L. rewrite Z2Nat.id by blia.
            rewrite Z.mul_comm. rewrite Z_div_mult by blia. reflexivity.
        }
      - cbv beta. intros. simp.
        unfold Spilling.related in *. simp.
        match goal with
        | H: (_ * _)%sep m' |- _ => rename H into HM
        end.
        unfold word_array in HM.
        seprewrite_in @cast_word_array_to_bytes HM.
        edestruct ll_mem_to_hl_mem with (mL := m') as (mStack' & HM' & D & Ab'). {
          ecancel_assumption.
        }
        eexists _, _. ssplit.
        + match goal with
          | |- ?G => let T := type of Ab' in replace G with T; [exact Ab'|clear Ab']
          end.
          f_equal.
          rewrite List.length_flat_map with (n := Z.to_nat bytes_per_word).
          * simpl_addrs. rewrite !Z2Nat.id by blia. blia.
          * clear. intros. rewrite HList.tuple.length_to_list. reflexivity.
        + rewrite sep_emp_r in HM'. apply proj1 in HM'. subst m'. unfold map.split.
          split. 1: reflexivity. exact D.
        + eexists. split. 2: eassumption.
          unfold sep in H3p0p4.
          destruct H3p0p4 as (regsAndTmp & lfp & ? & A & Pt).
          destruct A as (lRegs' & tmps' & ? & ? & ?).
          subst lRegs'.
          eapply map.getmany_of_list_zip_grow. 1: eassumption.
          eapply map.getmany_of_list_zip_grow. 1: eassumption.
          unfold sep in H3p0p3. destruct H3p0p3 as (lRegs' & lStack' & Spl & ? & ?). subst lRegs' lStack'.
          eapply map.getmany_of_list_zip_shrink. 1: exact Spl. 1: assumption.
          intros *. intro HI. destr (map.get lStack k). 2: assumption. exfalso.
          pose proof (H3p0p2 _ _ E) as B.
          epose proof (proj1 (@forallb_forall _ _ _) Frets _ HI) as A. cbv beta in A.
          rewrite Bool.andb_true_iff in A. rewrite !Z.ltb_lt in A. clear -A B. blia.
    Qed. *)
    Admitted.

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
