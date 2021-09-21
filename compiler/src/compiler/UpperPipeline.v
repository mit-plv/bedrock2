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

  Record Lang: Type := {
    Var: Type;
    Cmd: Type;
    Locals : map.map Var word;
    Env : map.map string (list Var * list Var * Cmd);
    Exec: Env -> Cmd -> trace -> mem -> Locals -> MetricLog ->
          (trace -> mem -> Locals -> MetricLog -> Prop) -> Prop
  }.

  Definition phase_correct{L1 L2: Lang}(compile: L1.(Env) -> option L2.(Env)): Prop :=
    forall functions1 functions2 f_entry_name argnames1 retnames1 fbody1,
      compile functions1 = Some functions2 ->
      map.get functions1 f_entry_name = Some (argnames1, retnames1, fbody1) ->
      exists argnames2 retnames2 fbody2,
        map.get functions2 f_entry_name = Some (argnames2, retnames2, fbody2) /\
        forall argvals t m l1 mc post,
          map.of_list_zip argnames1 argvals = Some l1 ->
          L1.(Exec) functions1 fbody1 t m l1 mc (fun t' m' l1' mc' =>
            exists retvals, map.getmany_of_list l1' retnames1 = Some retvals /\ post t' m' retvals) ->
          exists l2, map.of_list_zip argnames2 argvals = Some l2 /\
            L2.(Exec) functions2 fbody2 t m l2 mc (fun t' m' l2' mc' =>
              exists retvals, map.getmany_of_list l2' retnames2 = Some retvals /\ post t' m' retvals).

  Definition compose_phases{A B C: Type}(phase1: A -> option B)(phase2: B -> option C)(a: A) :=
    match phase1 a with
    | Some b => phase2 b
    | None => None
    end.

  Lemma compose_phases_correct{L1 L2 L3: Lang}
        (compile12: L1.(Env) -> option L2.(Env))
        (compile23: L2.(Env) -> option L3.(Env)):
    phase_correct compile12 -> phase_correct compile23 -> phase_correct (compose_phases compile12 compile23).
  Proof.
    unfold phase_correct, compose_phases. intros C12 C23. intros *. intros ? G1. simp.
    specialize C12 with (1 := E) (2 := G1). simp.
    specialize C23 with (1 := H) (2 := C12p0). simp.
    eexists _, _, _. split. 1: eassumption.
    intros *. intros OL1 Ex1.
    specialize C12p1 with (1 := OL1) (2 := Ex1). simp.
    specialize C23p1 with (1 := C12p1p0) (2 := C12p1p1).
    exact C23p1.
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

    Definition FlatLangZ := {|
      Var := Z;
      Cmd := FlatImp.stmt Z;
      Locals := Zlocals;
      Env := string_keyed_map (list Z * list Z * FlatImp.stmt Z);
      Exec := FlatImp.exec
    |}.

    Lemma flattening_correct: @phase_correct SrcLang FlatLangStr flatten_functions.
    Proof.
      unfold phase_correct. intros.

      pose proof H0 as GF.
      unfold flatten_functions in GF.
      eapply map.map_all_values_fw in GF. 5: eassumption. 2-4: typeclasses eauto.
      unfold flatten_function in GF. simp.

      eexists _, _, _. split. 1: eassumption.
      intros. eexists. split. 1: eassumption.
      eapply FlatImp.exec.weaken.
      - eapply flattenStmt_correct_aux.
        + eassumption.
        + eassumption.
        + reflexivity.
        + match goal with
          | |- ?p = _ => rewrite (surjective_pairing p)
          end.
          reflexivity.
        + intros x k A. assumption.
        + unfold map.undef_on, map.agree_on. cbn. intros k A.
          rewrite map.get_empty. destr (map.get l1 k). 2: assumption. exfalso.
          unfold map.of_list_zip in H1.
          edestruct (map.putmany_of_list_zip_find_index _ _ _ _ _ _ H1 E) as [G | G]. 2: {
            rewrite map.get_empty in G. discriminate.
          }
          destruct G as (i & G1 & G2).
          eapply nth_error_In in G1.
          eapply start_state_spec. 2: exact A.
          eapply ListSet.In_list_union_l. eapply ListSet.In_list_union_l. assumption.
        + eapply @freshNameGenState_disjoint_fbody.
      - simpl. intros. simp. eauto using map.getmany_of_list_extends.
    Qed.

    Lemma regalloc_correct: @phase_correct FlatLangStr FlatLangZ regalloc_functions.
    Proof.
      unfold phase_correct. intros.

      pose proof H as GR.
      unfold regalloc_functions in GR.
      simp. rename E into GR.
      eapply map.map_all_values_fw in GR. 5: eassumption. 2-4: typeclasses eauto.
      simp. clear GRp0.
      pose proof E0 as C.
      unfold check_funcs in E0.
      eapply map.get_forallb in E0. 2: eassumption.
      unfold lookup_and_check_func, check_func in E0. simp.

      eexists _, _, _. split. 1: eassumption. intros.
      unfold map.of_list_zip in *.
      apply_in_hyps @map.putmany_of_list_zip_sameLength.
      apply_in_hyps assert_ins_same_length.
      apply_in_hyps assignments_same_length.
      cbn [Var FlatLangStr] in *. (* PARAMRECORDS *)
      assert (List.length l = List.length argvals) as P by congruence.
      eapply map.sameLength_putmany_of_list in P. destruct P as [st2 P].
      eexists. split. 1: exact P.
      eapply FlatImp.exec.weaken.
      - eapply checker_correct; try eassumption.
        eapply states_compat_precond.
        edestruct putmany_of_list_zip_states_compat as (lL' & P' & Cp); try eassumption.
        1: eapply states_compat_empty.
        rewrite P in P'. inversion P'. exact Cp.
      - simpl. intros. simp. eexists. split. 2: eassumption.
        destruct u. eauto using states_compat_getmany.
    Qed.

    Lemma spilling_correct: @phase_correct FlatLangZ FlatLangZ spill_functions.
    Proof.
      unfold phase_correct. intros.

      pose proof H as GL.
      unfold spill_functions in GL.
      eapply map.map_all_values_fw in GL. 5: eassumption. 2-4: typeclasses eauto.
      unfold spill_fun in GL. simp. eapply Bool.andb_true_iff in E.
      destruct E as (E & Fs).
      eapply Bool.andb_true_iff in E.
      destruct E as (Fargs & Frets).
      eapply forallb_vars_stmt_correct in Fs. 2: {
        intros x. split; intros F.
        - rewrite ?Z.ltb_lt in F. exact F.
        - apply Z.ltb_lt. assumption.
      }
      2: {
        intros x. split; intros F.
        - rewrite Bool.andb_true_iff in F. rewrite ?Z.ltb_lt in F. exact F.
        - apply  Bool.andb_true_iff. rewrite ?Z.ltb_lt. assumption.
      }

      eexists _, _, _. split. 1: eassumption. intros.
      unfold map.of_list_zip in *.
      eexists. split. 1: exact H1.
      unfold spill_fbody.
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
    Qed.

    Definition upper_compiler :=
      compose_phases flatten_functions (compose_phases regalloc_functions spill_functions).

    Lemma upper_compiler_correct: @phase_correct SrcLang FlatLangZ upper_compiler.
    Proof.
      unfold upper_compiler.
      eapply (@compose_phases_correct SrcLang FlatLangStr FlatLangZ). 1: exact flattening_correct.
      eapply (@compose_phases_correct FlatLangStr FlatLangZ FlatLangZ). 1: exact regalloc_correct.
      exact spilling_correct.
    Qed.

  End WithMoreParams.
End WithWordAndMem.
