Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Primitives.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.util.Common.
Require Import compiler.Simp.
Require Import compiler.SeparationLogic.
Require Import compiler.SimplWordExpr.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.DivisibleBy4.
Require Import compiler.EmitsValid.
Require Import compiler.MetricsToRiscv.
Require Import compiler.FlatImp.
Require Import compiler.RunInstruction.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscvCommon.
Import compiler.FlatToRiscvCommon.FlatToRiscv.
Require Import compiler.load_save_regs_correct.


Section Proofs.
  Context {p: FlatToRiscv.parameters}.
  Context {h: FlatToRiscv.assumptions}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Local Notation RiscvMachineL := MetricRiscvMachine.

  (*
     high addresses!             ...
                      p_sp   --> mod_var_0 of previous function call arg0
                                 argn
                                 ...
                                 arg0
                                 retn
                                 ...
                                 ret0
                                 ra
                                 mod_var_n
                                 ...
                      new_sp --> mod_var_0
     low addresses               ...
  *)
  Definition stackframe(p_sp: word)(argvals retvals: list word)
             (ra_val: word)(modvarvals: list word): mem -> Prop :=
    word_array
      (word.add p_sp
         (word.of_Z
           (- (bytes_per_word *
             Z.of_nat (List.length argvals + List.length retvals + 1 + List.length modvarvals)))))
      (modvarvals ++ [ra_val] ++ retvals ++ argvals).

  (* measured in words, needs to be multiplied by 4 or 8 *)
  Definition framelength: list Register * list Register * stmt -> Z :=
    fun '(argvars, resvars, body) =>
      let mod_vars := modVars_as_list body in
      Z.of_nat (List.length argvars + List.length resvars + 1 + List.length mod_vars).

  Lemma framesize_nonneg: forall argvars resvars body,
      0 <= framelength (argvars, resvars, body).
  Proof.
    intros. unfold framelength.
    unfold bytes_per_word, Memory.bytes_per. blia.
  Qed.

  (* Note:
     - This predicate cannot be proved for recursive functions
     - Measured in words, needs to be multiplied by 4 or 8 *)
  Inductive fits_stack: Z -> env -> stmt -> Prop :=
  | fits_stack_load: forall n e sz x y,
      0 <= n ->
      fits_stack n e (SLoad sz x y)
  | fits_stack_store: forall n e sz x y,
      0 <= n ->
      fits_stack n e (SStore sz x y)
  | fits_stack_lit: forall n e x v,
      0 <= n ->
      fits_stack n e (SLit x v)
  | fits_stack_op: forall n e op x y z,
      0 <= n ->
      fits_stack n e (SOp x op y z)
  | fits_stack_set: forall n e x y,
      0 <= n ->
      fits_stack n e (SSet x y)
  | fits_stack_if: forall n e c s1 s2,
      fits_stack n e s1 ->
      fits_stack n e s2 ->
      fits_stack n e (SIf c s1 s2)
  | fits_stack_loop: forall n e c s1 s2,
      fits_stack n e s1 ->
      fits_stack n e s2 ->
      fits_stack n e (SLoop s1 c s2)
  | fits_stack_seq: forall n e s1 s2,
      fits_stack n e s1 ->
      fits_stack n e s2 ->
      fits_stack n e (SSeq s1 s2)
  | fits_stack_skip: forall n e,
      0 <= n ->
      fits_stack n e SSkip
  | fits_stack_call: forall n e binds fname args argnames retnames body,
      map.get e fname = Some (argnames, retnames, body) ->
      fits_stack (n - framelength (argnames, retnames, body)) e body ->
      fits_stack n e (SCall binds fname args)
  | fits_stack_interact: forall n e binds act args,
      0 <= n ->
      fits_stack n e (SInteract binds act args).

  Lemma fits_stack_nonneg: forall n e s,
      fits_stack n e s ->
      0 <= n.
  Proof.
    induction 1; try blia. pose proof (@framesize_nonneg argnames retnames body). blia.
  Qed.

  (* high stack addresses     | stackframe of main             \
                              ...                               \
    g|                        ---                                }- stuffed into R
    r|                        | stackframe of current func      /
    o|              p_sp -->  ---                              /
    w|                        |
    s|                        | currently unused stack
     |                        | (old_stackvals)
     V                        |
            p_stacklimit -->  ---

     low stack addresses *)

  Instance fun_pos_env: map.map Syntax.funname Z := _.

  (* Note: This definition would not be usable in the same way if we wanted to support
     recursive functions, because separation logic would prevent us from mentioning
     the snippet of code being run twice (once in [program initialL.(getPc) insts] and
     a second time inside [functions]).
     To avoid this double mentioning, we will remove the function being called from the
     list of functions before entering the body of the function. *)
  Definition functions(base: word)(rel_positions: fun_pos_env)(impls: env):
    list Syntax.funname -> mem -> Prop :=
    fix rec funnames :=
      match funnames with
      | nil => emp True
      | fname :: rest =>
        (match map.get rel_positions fname, map.get impls fname with
         | Some pos, Some impl =>
           program (word.add base (word.of_Z pos))
                   (compile_function rel_positions pos impl)
         | _, _ => emp True
         end * (rec rest))%sep
      end.

  Instance funname_eq_dec: DecidableEq Syntax.funname := string_dec.

  Lemma functions_expose: forall base rel_positions impls funnames f pos impl,
      map.get rel_positions f = Some pos ->
      map.get impls f = Some impl ->
      iff1 (functions base rel_positions impls funnames)
           (functions base rel_positions impls (List.remove funname_eq_dec f funnames) *
            program (word.add base (word.of_Z pos)) (compile_function rel_positions pos impl))%sep.
  Proof.
  Admitted.

  Lemma union_Forall: forall {T: Type} {teq: DecidableEq T} (P: T -> Prop) (l1 l2: list T),
      Forall P l1 ->
      Forall P l2 ->
      Forall P (ListLib.list_union l1 l2).
  Proof.
    induction l1; intros; simpl; [assumption|].
    simp. destruct_one_match; eauto.
  Qed.

  Lemma modVars_as_list_valid_registers: forall (s: @stmt (mk_Syntax_params _)),
      valid_registers s ->
      Forall valid_register (modVars_as_list s).
  Proof.
    induction s; intros; simpl in *; simp; eauto 10 using @union_Forall.
  Qed.

  Lemma getmany_of_list_exists{K V: Type}{M: map.map K V}:
    forall (m: M) (P: K -> Prop) (ks: list K),
      Forall P ks ->
      (forall k, P k -> exists v, map.get m k = Some v) ->
      exists vs, map.getmany_of_list m ks = Some vs.
  Proof.
    induction ks; intros.
    - exists nil. reflexivity.
    - inversion H. subst. clear H.
      edestruct IHks as [vs IH]; [assumption..|].
      edestruct H0 as [v ?]; [eassumption|].
      exists (v :: vs). cbn. rewrite H. unfold map.getmany_of_list in IH.
      rewrite IH. reflexivity.
  Qed.

  Ltac simpl_addrs :=
    repeat (
        rewrite !List.app_length ||
        simpl ||
        rewrite !Nat2Z.inj_add ||
        rewrite !Zlength_correct ||
        rewrite !Nat2Z.inj_succ ||
        rewrite <-! Z.add_1_r ||
        autorewrite with rew_word_morphism);
    unfold Register, MachineInt in *;
    (* note: it's the user's responsability to ensure that left-to-right rewriting with all
     nat and Z equations terminates, otherwise we'll loop infinitely here *)
    repeat match goal with
           | E: @eq ?T _ _ |- _ =>
             lazymatch T with
             | Z => idtac
             | nat => idtac
             end;
             progress rewrite E
           end.

  Ltac wseplog_pre OK :=
    use_sep_assumption;
    autounfold with unf_to_array;
    unfold program, word_array;
    repeat match goal with
           | |- context [ array ?PT ?SZ ?start (?xs ++ ?ys) ] =>
             rewrite (array_append_DEPRECATED PT SZ xs ys start)
           end;
    simpl_addrs.

  Set Printing Depth 100000.

  Hint Unfold program word_array: unf_to_array.

  Lemma compile_stmt_length_position_indep: forall e_pos1 e_pos2 s pos1 pos2,
      List.length (compile_stmt_new e_pos1 pos1 s) =
      List.length (compile_stmt_new e_pos2 pos2 s).
  Proof.
    induction s; intros; simpl; try reflexivity;
      repeat (simpl; rewrite ?List.app_length); erewrite ?IHs1; erewrite ?IHs2; try reflexivity.
  Qed.

  Lemma f_equal2: forall {A B: Type} {f1 f2: A -> B} {a1 a2: A},
      f1 = f2 -> a1 = a2 -> f1 a1 = f2 a2.
  Proof. intros. congruence. Qed.

  (* deliberately leaves word and Z goals open if it fails to solve them, so that the
     user can inspect them and solve them manually or tweak things to make them solvable
     automatically *)
  Ltac sepclause_part_eq OK :=
    lazymatch type of OK with
    | word.ok ?WORD =>
      lazymatch goal with
      | |- @eq ?T ?x ?y =>
        tryif first [is_evar x | is_evar y | constr_eq x y] then (
          reflexivity
        ) else (
          tryif (unify T (@word.rep _ WORD)) then (
            try solve [autorewrite with rew_word_morphism; solve_word_eq OK]
          ) else (
            tryif (unify T Z) then (
              try solve [bomega]
            ) else (
              lazymatch x with
              | ?x1 ?x2 => lazymatch y with
                           | ?y1 ?y2 => refine (f_equal2 _ _); sepclause_part_eq OK
                           | _ => fail "" x "is an application while" y "is not"
                           end
              | _ => lazymatch y with
                     | ?y1 ?y2 => fail "" x "is not an application while" y "is"
                     | _ => tryif constr_eq x y then idtac else fail "" x "does not match" y
                     end
              end
            )
          )
        )
      end
    | _ => fail 1000 "OK does not have the right type"
    end.

  Ltac sepclause_eq := sepclause_part_eq (@word_ok (@W (@def_params p))).

  Ltac pick_nat n :=
    multimatch n with
    | S ?m => constr:(m)
    | S ?m => pick_nat m
    end.

  Require Import coqutil.Tactics.rdelta.

  Ltac wcancel_step :=
    let RHS := lazymatch goal with |- Lift1Prop.iff1 _ (seps ?RHS) => RHS end in
    let jy := index_and_element_of RHS in
    let j := lazymatch jy with (?i, _) => i end in
    let y := lazymatch jy with (_, ?y) => y end in
    assert_fails (idtac; let y := rdelta_var y in is_evar y);
    let LHS := lazymatch goal with |- Lift1Prop.iff1 (seps ?LHS) _ => LHS end in
    let l := eval cbv [List.length] in (List.length LHS) in
    let i := pick_nat l in
    cancel_seps_at_indices i j; [sepclause_eq|].

  Ltac wcancel :=
    cancel;
    repeat (wcancel_step; let n := numgoals in guard n <= 1);
    try solve [ecancel_done'].

  (* TODO make sure it's compatible with users of it *)
  Axiom compile_ext_call_correct_new: forall (initialL: RiscvMachineL)
        action postH newPc insts (argvars resvars: list Register) initialMH R initialRegsH
        initialMetricsH argvals mGive outcome p_sp,
      insts = compile_ext_call resvars action argvars ->
      newPc = word.add initialL.(getPc) (word.mul (word.of_Z 4) (word.of_Z (Zlength insts))) ->
      map.extends initialL.(getRegs) initialRegsH ->
      Forall valid_register argvars ->
      Forall valid_register resvars ->
      (program initialL.(getPc) insts * eq initialMH * R)%sep initialL.(getMem) ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      map.get initialL.(getRegs) RegisterNames.sp = Some p_sp ->
      ext_guarantee initialL ->
      (* from FlatImp.exec/case interact, but for the case where no memory is exchanged *)
      map.getmany_of_list initialL.(getRegs) argvars = Some argvals ->
      ext_spec initialL.(getLog) mGive action argvals outcome ->
      (forall (resvals : list word),
          outcome map.empty resvals ->
          mGive = map.empty ->
          exists (finalRegsH: locals) finalMetricsH,
            map.putmany_of_list resvars resvals initialRegsH = Some finalRegsH /\
            postH ((map.empty, action, argvals, (map.empty, resvals)) :: initialL.(getLog))
                  initialMH finalRegsH finalMetricsH) ->
      runsTo initialL
             (fun finalL =>
                exists (finalRegsH: locals) finalMetricsH,
                  map.extends finalL.(getRegs) finalRegsH /\
                  map.get finalL.(getRegs) RegisterNames.sp = Some p_sp /\
                  (* external calls can't modify the memory for now *)
                  postH finalL.(getLog) initialMH finalRegsH finalMetricsH /\
                  finalL.(getPc) = newPc /\
                  finalL.(getNextPc) = add newPc (ZToReg 4) /\
                  (program initialL.(getPc) insts * eq initialMH * R)%sep finalL.(getMem) /\
                  (finalL.(getMetrics) - initialL.(getMetrics) <=
                   lowerMetrics (finalMetricsH - initialMetricsH))%metricsL /\
                  ext_guarantee finalL).

  Lemma compile_stmt_correct_new:
    forall (program_base p_stacklimit: word),
    forall e_impl_full (s: stmt) t initialMH initialRegsH initialMetricsH postH,
    exec e_impl_full s t (initialMH: mem) initialRegsH initialMetricsH postH ->
    (* note: [e_impl_reduced] and [funnames] will shrink one function at a time each time
       we enter a new function body, to make sure functions cannot call themselves, while
       [e_impl_full] and [e_pos] remain the same throughout because that's mandated by
       [FlatImp.exec] and [compile_stmt], respectively *)
    forall e_pos e_impl_reduced funnames,
    map.extends e_impl_full e_impl_reduced ->
    (forall f (argnames retnames: list Syntax.varname) (body: stmt),
        map.get e_impl_reduced f = Some (argnames, retnames, body) ->
        Forall valid_register argnames /\
        Forall valid_register retnames /\
        valid_registers body /\
        List.In f funnames /\
        exists pos, map.get e_pos f = Some pos /\ pos mod 4 = 0) ->
    forall (R: mem -> Prop) (initialL: RiscvMachineL) insts p_sp (old_stackvals: list word) pos,
    @compile_stmt_new def_params _ e_pos pos s = insts ->
    stmt_not_too_big s ->
    valid_registers s ->
    initialL.(getPc) = word.add program_base (word.of_Z pos) ->
    pos mod 4 = 0 ->
    divisibleBy4 program_base ->
    map.extends initialL.(getRegs) initialRegsH ->
    map.get initialL.(getRegs) RegisterNames.sp = Some p_sp ->
    (forall r, 0 < r < 32 -> exists v, map.get initialL.(getRegs) r = Some v) ->
    fits_stack (Z.of_nat (List.length old_stackvals)) e_impl_reduced s ->
    p_sp = word.add p_stacklimit
                    (word.of_Z (bytes_per_word * Z.of_nat (List.length old_stackvals))) ->
    (R * eq initialMH *
     word_array p_stacklimit old_stackvals *
     program initialL.(getPc) insts *
     functions program_base e_pos e_impl_full funnames)%sep initialL.(getMem) ->
    initialL.(getLog) = t ->
    initialL.(getNextPc) = add initialL.(getPc) (ZToReg 4) ->
    ext_guarantee initialL ->
    runsTo initialL (fun finalL => exists finalRegsH finalMH finalMetricsH
                                          (final_stackvals: list word),
          postH finalL.(getLog) finalMH finalRegsH finalMetricsH /\
          map.extends finalL.(getRegs) finalRegsH /\
          map.get finalL.(getRegs) RegisterNames.sp = Some p_sp /\
          List.length final_stackvals = List.length old_stackvals /\
          (R * eq finalMH *
           word_array p_stacklimit final_stackvals *
           program initialL.(getPc) insts *
           functions program_base e_pos e_impl_full funnames)%sep finalL.(getMem) /\
          finalL.(getPc) = add initialL.(getPc) (mul (ZToReg 4) (ZToReg (Zlength insts))) /\
          finalL.(getNextPc) = add finalL.(getPc) (ZToReg 4) /\
          ext_guarantee finalL).
(* TODO these constrains will have to be added:
    Forall valid_FlatImp_var useargs ->
    Forall valid_FlatImp_var useresults ->
    Forall valid_FlatImp_var defargs ->
    Forall valid_FlatImp_var defresults ->

    (* note: use-site argument/result names are allowed to have duplicates, but definition-site
       argument/result names aren't *)
    NoDup defargs ->
    NoDup defresults ->
 *)
  Proof.
    pose proof compile_stmt_emits_valid.
    induction 1; intros;
      lazymatch goal with
      | H1: valid_registers ?s, H2: stmt_not_too_big ?s |- _ =>
        pose proof (@compile_stmt_new_emits_valid _ _ s e_pos pos iset_is_supported H1 H2)
      end.
      all: repeat match goal with
                  | m: _ |- _ => destruct_RiscvMachine m
                  end.
      all: subst.
      all: simp.

    - (* SInteract *)
      eapply runsTo_weaken.
      + eapply compile_ext_call_correct_new with
            (postH := fun t' m' l' mc' => post t' m (* <- not m' because unchanged *) l' mc')
            (action := action) (argvars := argvars) (resvars := resvars);
          simpl; reflexivity || eassumption || ecancel_assumption || idtac.
        * eapply map.getmany_of_list_extends; eassumption.
        * intros resvals HO ?. subst mGive.
          match goal with
          | H: forall _, _ |- _ =>
            specialize H with (1 := HO);
            move H at bottom;
            destruct H as (finalRegsH & ? & finalMH & ? & ?)
          end.
          edestruct (map.putmany_of_list_extends_exists (ok := locals_ok))
            as (finalRegsL & ? & ?); [eassumption..|].
          do 2 match goal with
          | H: map.split _ _ map.empty |- _ => apply map.split_empty_r in H
          end.
          replace mKeep with m in * by congruence. clear mKeep.
          replace finalMH with m in * by congruence. clear finalMH.
          repeat eexists;
          repeat split; try eassumption.
      + simpl. intros finalL A. destruct_RiscvMachine finalL. simpl in *.
        destruct_products. subst.
        do 4 eexists. repeat split; try eassumption. ecancel_assumption.

    - (* SCall *)
      (* We have one "map.get e fname" from exec, one from fits_stack, make them match *)
      lazymatch goal with
      | H1: map.get e_impl_full fname = ?RHS1,
        H2: map.get e_impl_reduced fname = ?RHS2,
        H3: map.extends e_impl_full e_impl_reduced |- _ =>
        let F := fresh in assert (RHS1 = RHS2) as F
            by (clear -H1 H2 H3;
                unfold map.extends in H3;
                specialize H3 with (1 := H2); clear H2;
                etransitivity; [symmetry|]; eassumption);
        inversion F; subst; clear F
      end.
      unfold fun_pos_env in *.
      match goal with
      | H: map.get e_impl_reduced fname = Some _, G: _ |- _ =>
          specialize G with (1 := H);
          destruct G as [? [? [? [? [funpos [GetPos ?] ] ] ] ] ]
      end.
      rewrite GetPos in *.

      set (FL := framelength (argnames, retnames, body)) in *.
      (* We have enough stack space for this call: *)
      assert (FL <= Z.of_nat (List.length old_stackvals)) as enough_stack_space. {
        match goal with
        | H: fits_stack _ _ _ |- _ => apply fits_stack_nonneg in H; clear -H
        end.
        blia.
      }

      assert (exists remaining_stack old_modvarvals old_ra old_retvals old_argvals,
                 old_stackvals = remaining_stack ++ old_modvarvals ++ [old_ra] ++
                                                 old_retvals ++ old_argvals /\
                 List.length old_modvarvals = List.length (modVars_as_list body) /\
                 List.length old_retvals = List.length retnames /\
                 List.length old_argvals = List.length argnames) as TheSplit. {
        subst FL. unfold framelength in *.
        clear -enough_stack_space.

        refine (ex_intro _ (List.firstn _ old_stackvals) _).
        refine (ex_intro _ (List.firstn _ (List.skipn _ old_stackvals)) _).
        refine (ex_intro _ (List.nth _ old_stackvals (word.of_Z 0)) _).
        refine (ex_intro _ (List.firstn _ (List.skipn _ old_stackvals)) _).
        refine (ex_intro _ (List.firstn _ (List.skipn _ old_stackvals)) _).

        repeat split.
        1: eapply ListLib.firstn_skipn_reassemble; [reflexivity|].
        1: eapply ListLib.firstn_skipn_reassemble; [reflexivity|].
        1: rewrite List.skipn_skipn.
        1: eapply ListLib.firstn_skipn_reassemble.
        1: eapply ListLib.firstn_skipn_nth.
        2: rewrite List.skipn_skipn.
        2: eapply ListLib.firstn_skipn_reassemble; [reflexivity|].
        2: rewrite List.skipn_skipn.
        2: rewrite List.firstn_all.
        2: reflexivity.
        2: rewrite List.length_firstn_inbounds.
        2: reflexivity.
        3: rewrite List.length_firstn_inbounds.
        3: reflexivity.
        4: rewrite List.length_firstn_inbounds.
        4: rewrite List.length_skipn.
        4: lazymatch goal with
           | |- ?LHS = ?RHS =>
             match LHS with
             | context C [ ?x ] =>
               is_evar x;
               let LHS' := context C [ 0%nat ] in
               assert (LHS' - RHS = x)%nat
             end
           end.
        4: reflexivity.

        all: rewrite ?List.length_skipn.
        all: try blia.
      }
      destruct TheSplit as (remaining_stack & old_modvarvals & old_ra & old_retvals & old_argvals
                                & ? & ? &  ? & ?).
      subst old_stackvals.

      (* note: left-to-right rewriting with all [length _ = length _] equations has to
         be terminating *)
      match goal with
      | H: _ |- _ => let N := fresh in pose proof H as N;
                     apply map.putmany_of_list_sameLength in N;
                     symmetry in N
      end.
      match goal with
      | H: _ |- _ => let N := fresh in pose proof H as N;
                     apply map.getmany_of_list_length in N
      end.

      (* put arguments on stack *)
      eapply runsTo_trans. {
        eapply save_regs_correct with (vars := args) (offset := - bytes_per_word * Z.of_nat (List.length args)); simpl;
          try solve [sidecondition].
        - admit.
        - solve_divisibleBy4.
        - eapply map.getmany_of_list_extends; eassumption.
        - instantiate (1 := old_argvals). unfold Register, MachineInt in *. blia.
        - wseplog_pre word_ok.

        wcancel.
      }

    cbn [getRegs getPc getNextPc getMem getLog getMachine getMetrics].
    repeat match goal with
           | H: (_ * _)%sep _ |- _ => clear H
           end.
    intros. simp.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    assert (valid_register RegisterNames.ra) by (cbv; auto).
    assert (valid_register RegisterNames.sp) by (cbv; auto).

    (* jump to function *)
    eapply runsToStep. {
      eapply run_Jal; simpl; try solve [sidecondition | solve_divisibleBy4].
      rewrite !@length_save_regs in *.
      wseplog_pre word_ok.
      wcancel.
    }

    cbn [getRegs getPc getNextPc getMem getLog getMachine getMetrics].
    repeat match goal with
           | H: (_ * _)%sep _ |- _ => clear H
           end.
    intros. simp.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    pose proof functions_expose as P.
    match goal with
    | H: map.get e_impl_full _ = Some _ |- _ => specialize P with (2 := H)
    end.
    specialize P with (1 := GetPos).
    specialize (P program_base funnames).
    match goal with
    | H: (_ * _)%sep _ |- _ => seprewrite_in P H; clear P
    end.

    pose proof (@compile_function_emits_valid _ _ e_pos funpos argnames retnames body) as V.
    especialize V.
    { exact iset_is_supported. }
    { admit. (* valid argnames *) }
    { admit. (* valid retnames *) }
    { admit. (* valid_registers for function being called *) }
    { admit. (* stmt_not_too_big for function being called *) }

    simpl in *.

    (* decrease sp *)
    eapply runsToStep. {
      eapply run_Addi; try solve [sidecondition | simpl; solve_divisibleBy4 ].
      - simpl.
        rewrite map.get_put_diff by (clear; cbv; congruence).
        eassumption.
      - simpl.
        wseplog_pre word_ok.
        wcancel.
    }

    cbn [getRegs getPc getNextPc getMem getLog getMachine getMetrics].
    repeat match goal with
           | H: (_ * _)%sep _ |- _ => clear H
           end.
    intros. simp.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    (* save ra on stack *)
    eapply runsToStep. {
      eapply run_store_word; try solve [sidecondition | simpl; solve_divisibleBy4]. {
        simpl.
        rewrite map.get_put_diff by (clear; cbv; congruence).
        rewrite map.get_put_same. reflexivity.
      }
      simpl.
      wseplog_pre word_ok.
      wcancel.
    }

    cbn [getRegs getPc getNextPc getMem getLog getMachine getMetrics].
    repeat match goal with
           | H: (_ * _)%sep _ |- _ => clear H
           end.
    intros. simp.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    (* save vars modified by callee onto stack *)
    match goal with
    | |- context [ {| getRegs := ?l |} ] =>
      pose proof (@getmany_of_list_exists _ _ _ l valid_register (modVars_as_list body)) as P
    end.
    edestruct P as [newvalues P2]; clear P.
    { apply modVars_as_list_valid_registers. assumption. }
    {
      intros.
      rewrite !map.get_put_dec.
      destruct_one_dec_eq; [eexists; reflexivity|].
      destruct_one_dec_eq; [eexists; reflexivity|].
      eauto.
    }
    eapply runsTo_trans. {
      eapply save_regs_correct; simpl; cycle 2.
      1: solve_divisibleBy4.
      2: rewrite map.get_put_same; reflexivity.
      1: exact P2.
      4: eapply modVars_as_list_valid_registers; eassumption.
      1: eassumption.
      2: reflexivity.
      1: { (* PARAMRECORDS *)

        change Syntax.varname with Register in *.

        repeat match goal with
        | H: _ = List.length ?M |- _ =>
          lazymatch M with
          | @modVars_as_list ?params ?eqd ?s =>
            so fun hyporgoal => match hyporgoal with
                                | context [?M'] =>
                                  lazymatch M' with
                                  | @modVars_as_list ?params' ?eqd' ?s =>
                                    assert_fails (constr_eq M M');
                                    change M' with M in *;
                                    idtac M' "--->" M
                                  end
                                end
          end
        end.

        wseplog_pre word_ok.
        wcancel.
      }
      1: admit. (* offet 0 not too big *)
    }

    simpl.
    cbn [getRegs getPc getNextPc getMem getLog getMachine getMetrics].
    repeat match goal with
           | H: (_ * _)%sep _ |- _ => clear H
           end.
    intros. simp.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    (* load argvars from stack *)
    eapply runsTo_trans. {
      eapply load_regs_correct with
          (vars := argnames) (values := argvs)
          (p_sp := (word.add p_stacklimit
                         (word.of_Z (bytes_per_word * Z.of_nat (List.length remaining_stack)))));
        simpl; cycle -2; try assumption.
      - rewrite !@length_save_regs in *.
        wseplog_pre word_ok.
        wcancel.
      - reflexivity.
      - replace valid_FlatImp_var with valid_register by admit.
        assumption.
      - admit. (* NoDup *)
      - admit. (* offset stuff *)
      - solve_divisibleBy4.
      - rewrite map.get_put_same. f_equal.
          repeat (
              rewrite !List.app_length ||
              simpl ||
              rewrite !Nat2Z.inj_add ||
              rewrite !Zlength_correct ||
              rewrite !Nat2Z.inj_succ ||
              rewrite <-! Z.add_1_r).
          replace (List.length old_retvals) with (List.length retnames) by blia.
          replace (List.length old_argvals) with (List.length argnames) by blia.
          replace (List.length (modVars_as_list body)) with (List.length old_modvarvals) by blia.
          unfold Register, MachineInt.
          autorewrite with rew_word_morphism.
          solve_word_eq word_ok.
    }

    simpl.
    cbn [getRegs getPc getNextPc getMem getLog getMachine getMetrics].
    repeat match goal with
           | H: (_ * _)%sep _ |- _ => clear H
           end.
    intros. simp.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    (* execute function body *)
    eapply runsTo_trans. {
      eapply IHexec with (funnames := (remove funname_eq_dec fname funnames));
        simpl; try assumption.
      - eassumption.
      - (* Note: we'd have to shrink e_impl in FlatImp.exec if we want to shrink it in
           the induction too *)
        admit.
      - reflexivity.
      - admit. (* stmt_not_too_big *)
      - match goal with
        | |- ?x = word.add ?y (word.of_Z ?E) =>
          is_evar E; instantiate (1 := word.unsigned (word.sub x y))
        end.
        rewrite word.of_Z_unsigned.
        solve_word_eq word_ok.
      - (* TODO put this into solve_divisibleBy4 *)
        rewrite word.unsigned_sub. unfold word.wrap.
        divisibleBy4_pre.
        auto 25 with mod4_0_hints.
      - (* map_solver with middle_regs and middle_regs0 *) admit.
      - (* map_solver with middle_regs and middle_regs0 *) admit.
      - (* map_solver with middle_regs and middle_regs0 *) admit.
      - instantiate (1 := remaining_stack).
        match goal with
        | H: fits_stack ?n1 _ _ |- fits_stack ?n2 _ _ =>
          replace n2 with n1; [exact H|]
        end.
        subst FL.
        rewrite !List.app_length. simpl.
        replace (List.length (modVars_as_list body)) with (List.length old_modvarvals) by blia.
        rewrite !List.app_length.
        blia.
      - reflexivity.
      - unfold fun_pos_env in *.
        rewrite !@length_load_regs in *.
        wseplog_pre word_ok.
        wcancel.
        wcancel_step. 1: admit.
        ecancel_done'.
      - admit. (* log equality?? *)
      - reflexivity.
      - eapply ext_guarantee_preservable.
        + eassumption.
        + cbn.
          (* TODO will need stronger prove_ext_guarantee, derive same_domain from sep *)
          admit.
        + cbn.  (* log equality?? *)
          admit.
    }

    simpl.
    cbn [getRegs getPc getNextPc getMem getLog getMachine getMetrics].
    repeat match goal with
           | H: (_ * _)%sep _ |- _ => clear H
           end.
    intros. simp.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    match goal with
    | H: outcome _ _ _ _ |- _ => rename H into HO
    end.
    match goal with
    | H: forall _, _ |- _ =>
      specialize H with (1 := HO);
      move H at bottom;
      destruct H as (retvs & finalRegsH & ? & ? & ?)
    end.

    (* save results onto stack *)
    eapply runsTo_trans. {
      eapply save_regs_correct with (vars := retnames); simpl; cycle 2.
      - solve_divisibleBy4.
      - eapply map.getmany_of_list_extends; try eassumption.
      - eassumption.
      - instantiate (1 := old_retvals). unfold Register, MachineInt in *. blia.
      - wseplog_pre word_ok.
        wcancel.
        wcancel_step. {
          match goal with
          | |- ?LHS = ?RHS =>
            match LHS with
            | context [List.length (compile_stmt_new ?epos1 ?pos1 ?s)] =>
              match RHS with
              | context [List.length (compile_stmt_new ?epos2 ?pos2 s)] =>
                replace (List.length (compile_stmt_new epos1 pos1 s))
                  with (List.length (compile_stmt_new epos2 pos2 s))
                    by apply compile_stmt_length_position_indep
              end
            end
          end.
          solve_word_eq word_ok.
        }
        wcancel_step.
        ecancel_done'.
      - reflexivity.
      - assumption.
      - admit. (* offset bounds *)
    }

    Notation "! n" := (word.of_Z n) (at level 0, n at level 0, format "! n") : word_scope.
    Notation "# n" := (Z.of_nat n) (at level 0, n at level 0, format "# n") : word_scope.
    Infix "+" := word.add : word_scope.
    Infix "-" := word.sub : word_scope.
    Infix "*" := word.mul : word_scope.
    Notation "- x" := (word.opp x) : word_scope.

    Delimit Scope word_scope with word.

    Open Scope word_scope.

    simpl.
    cbn [getRegs getPc getNextPc getMem getLog getMachine getMetrics].
    repeat match goal with
           | H: (_ * _)%sep _ |- _ => clear H
           end.
    intros. simp.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    (* load back the modified vars *)
    eapply runsTo_trans. {
      eapply load_regs_correct with
          (vars := (modVars_as_list body)) (values := newvalues)
          (p_sp := (word.add p_stacklimit
                             (word.of_Z (bytes_per_word * Z.of_nat (List.length remaining_stack)))));
        simpl; cycle -2; try assumption.
      - wseplog_pre word_ok.
        wcancel.
        wcancel_step.
        {
          match goal with
          | |- ?LHS = ?RHS =>
            match LHS with
            | context [List.length (compile_stmt_new ?epos1 ?pos1 ?s)] =>
              match RHS with
              | context [List.length (compile_stmt_new ?epos2 ?pos2 s)] =>
                replace (List.length (compile_stmt_new epos1 pos1 s))
                  with (List.length (compile_stmt_new epos2 pos2 s))
                    by apply compile_stmt_length_position_indep
              end
            end
          end.
          solve_word_eq word_ok.
        }
        wcancel_step.
        ecancel_done'.
      - reflexivity.
      - replace valid_FlatImp_var with valid_register by admit.
        apply modVars_as_list_valid_registers.
        assumption.
      - admit. (* NoDup *)
      - admit. (* offset stuff *)
      - solve_divisibleBy4.
      - repeat match goal with
               | H: map.getmany_of_list _ _ = Some _ |- _ =>
                 unique eapply @map.getmany_of_list_length in copy of H
               end.
        blia.
    }

    simpl.
    cbn [getRegs getPc getNextPc getMem getLog getMachine getMetrics].
    repeat match goal with
           | H: (_ * _)%sep _ |- _ => clear H
           end.
    intros. simp.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    (* load back the return address *)
    eapply runsToStep. {
      eapply run_load_word; try solve [sidecondition].
      - simpl. solve_divisibleBy4.
      - simpl.
        instantiate (1 := (p_stacklimit + !(bytes_per_word * #(List.length remaining_stack)))).
        repeat match goal with
               | H: ?T |- _ => lazymatch T with
                               | assumptions => fail
                               | map.only_differ middle_regs1 _ middle_regs2 => fail
                               | map.get middle_regs1 RegisterNames.sp = Some _ => fail
                               | _ => clear H
                               end
               end.
        match goal with
        | D: map.only_differ middle_regs1 _ middle_regs2 |- _ =>
          specialize (D RegisterNames.sp); destruct D as [A | A]
        end.
        + exfalso. (* contradiction: sp cannot be in modVars of body *) admit.
        + etransitivity; [symmetry|]; eassumption.
      - simpl.
        wseplog_pre word_ok.
        wcancel.
        wcancel_step.
        {
          match goal with
          | |- ?LHS = ?RHS =>
            match LHS with
            | context [List.length (compile_stmt_new ?epos1 ?pos1 ?s)] =>
              match RHS with
              | context [List.length (compile_stmt_new ?epos2 ?pos2 s)] =>
                replace (List.length (compile_stmt_new epos1 pos1 s))
                  with (List.length (compile_stmt_new epos2 pos2 s))
                    by apply compile_stmt_length_position_indep
              end
            end
          end.
          solve_word_eq word_ok.
        }
        ecancel_done'.
    }

    simpl.
    cbn [getRegs getPc getNextPc getMem getLog].
    repeat match goal with
           | H: (_ * _)%sep _ |- _ => clear H
           end.
    intros. simp.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    (* increase sp *)
    eapply runsToStep. {
      eapply (run_Addi _ _ _
             (* otherwise it will pick the decreasing (with a - in front) *)
              (bytes_per_word *
                  #(List.length argnames + List.length retnames + 1 + List.length (modVars_as_list body)))%Z);
        try solve [sidecondition | simpl; solve_divisibleBy4 ].
      - simpl.
        rewrite map.get_put_diff by (clear; cbv; congruence).
        repeat match goal with
               | H: ?T |- _ => lazymatch T with
                               | assumptions => fail
                               | map.only_differ middle_regs1 _ middle_regs2 => fail
                               | map.get middle_regs1 RegisterNames.sp = Some _ => fail
                               | _ => clear H
                               end
               end.
        match goal with
        | D: map.only_differ middle_regs1 _ middle_regs2 |- _ =>
          specialize (D RegisterNames.sp); destruct D as [A | A]
        end.
        + exfalso. (* contradiction: sp cannot be in modVars of body *) admit.
        + etransitivity; [symmetry|]; eassumption.
      - simpl.
        wseplog_pre word_ok.
        wcancel.
        wcancel_step. {
          match goal with
          | |- ?LHS = ?RHS =>
            match LHS with
            | context [List.length (compile_stmt_new ?epos1 ?pos1 ?s)] =>
              match RHS with
              | context [List.length (compile_stmt_new ?epos2 ?pos2 s)] =>
                replace (List.length (compile_stmt_new epos1 pos1 s))
                  with (List.length (compile_stmt_new epos2 pos2 s))
                    by apply compile_stmt_length_position_indep
              end
            end
          end.
          solve_word_eq word_ok.
        }
        ecancel_done'.
    }

    simpl.
    cbn [getRegs getPc getNextPc getMem getLog].
    repeat match goal with
           | H: (_ * _)%sep _ |- _ => clear H
           end.
    intros. simp.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    (* jump back to caller *)
    eapply runsToStep. {
      eapply run_Jalr0; simpl;
        try solve [sidecondition | solve_divisibleBy4].
      - admit. (*   word.unsigned ?dest mod 4 = 0  *)
      - rewrite map.get_put_diff by (clear; cbv; congruence).
        rewrite map.get_put_same. reflexivity.
      - wseplog_pre word_ok.
        wcancel.
        wcancel_step. {
          match goal with
          | |- ?LHS = ?RHS =>
            match LHS with
            | context [List.length (compile_stmt_new ?epos1 ?pos1 ?s)] =>
              match RHS with
              | context [List.length (compile_stmt_new ?epos2 ?pos2 s)] =>
                replace (List.length (compile_stmt_new epos1 pos1 s))
                  with (List.length (compile_stmt_new epos2 pos2 s))
                    by apply compile_stmt_length_position_indep
              end
            end
          end.
          solve_word_eq word_ok.
        }
        ecancel_done'.
    }

    simpl.
    cbn [getRegs getPc getNextPc getMem getLog getMachine].
    repeat match goal with
           | H: (_ * _)%sep _ |- _ => clear H
           end.
    intros. simp.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    (* load result values from stack *)
    eapply runsTo_trans. {
      eapply load_regs_correct with
          (vars := binds) (values := retvs)
          (offset := (- bytes_per_word * Z.of_nat (length args + length binds))%Z)
          (p_sp := p_stacklimit + !bytes_per_word * !#(Datatypes.length remaining_stack) +
                   !bytes_per_word * !FL);
        simpl; cycle -2; try assumption.
      - wseplog_pre word_ok.
        wcancel.
        wcancel_step. {
          subst FL.
          (* PARAMRECORDS *)
          change (@Syntax.varname (mk_Syntax_params (@def_params p))) with Z in *.
          replace (Datatypes.length binds) with (Datatypes.length retnames); cycle 1. {
            repeat match goal with
            | H: _ |- _ => let N := fresh in pose proof H as N;
                                               apply map.putmany_of_list_sameLength in N;
                                               symmetry in N;
                                               ensure_new N
            end.
            repeat match goal with
            | H: _ |- _ => let N := fresh in pose proof H as N;
                                               apply map.getmany_of_list_length in N;
                                               ensure_new N
            end.
            simpl_addrs.
            reflexivity.
          }
          simpl_addrs.
          solve_word_eq word_ok.
        }
        ecancel_done'.
      - reflexivity.
      - replace valid_FlatImp_var with valid_register by admit.
        assumption.
      - admit. (* NoDup *)
      - admit. (* offset stuff *)
      - solve_divisibleBy4.
      - subst FL.
        simpl_addrs.
        rewrite map.get_put_same. reflexivity.
      - repeat match goal with
               | H: _ |- _ => let N := fresh in pose proof H as N;
                                                  apply map.putmany_of_list_sameLength in N;
                                                  symmetry in N;
                                                  ensure_new N
               end.
        repeat match goal with
               | H: _ |- _ => let N := fresh in pose proof H as N;
                                                  apply map.getmany_of_list_length in N;
                                                  ensure_new N
               end.
        simpl_addrs.
        reflexivity.
    }

    simpl.
    cbn [getRegs getPc getNextPc getMem getLog getMachine].
    repeat match goal with
           | H: (_ * _)%sep _ |- _ => clear H
           end.
    intros. simp.
    repeat match goal with
           | m: _ |- _ => destruct_RiscvMachine m
           end.
    subst.

    (* computed postcondition satisfies required postcondition: *)
    apply runsToDone.
    cbn [getRegs getPc getNextPc getMem getLog getMachine].
    do 3 eexists.
    epose (?[new_ra]: word) as new_ra. cbv delta [id] in new_ra.
    evar (new_retvals: list word).
    evar (new_argvals: list word).
    evar (new_remaining_stack: list word).
    exists (new_remaining_stack ++ newvalues ++ [new_ra] ++ new_retvals ++ new_argvals).
    repeat split.
    + replace middle_log3 with middle_log1 by admit. (* TODO investigate! *)
      eassumption.
    + (* TODO chain of extends *)
      admit.
    + match goal with
      | H: map.only_differ ?m1 _ ?m2 |- map.get ?m2 _ = Some _ =>
        replace m2 with m1 by admit (* TODO almost *)
      end.
      rewrite map.get_put_same. f_equal.
      simpl_addrs.
      solve_word_eq word_ok.
    + admit. (* TODO lengths of old/new stack contents *)
    + assert (Datatypes.length (modVars_as_list body) = Datatypes.length newvalues). {
        eapply map.getmany_of_list_length. eassumption.
      }

      (* PARAMRECORDS *)
      change Syntax.varname with Register in *.
      repeat match goal with
             | H: _ = List.length ?M |- _ =>
               lazymatch M with
               | @modVars_as_list ?params ?eqd ?s =>
                 so fun hyporgoal => match hyporgoal with
                                     | context [?M'] =>
                                       lazymatch M' with
                                       | @modVars_as_list ?params' ?eqd' ?s =>
                                         assert_fails (constr_eq M M');
                                           change M' with M in *;
                                           idtac M' "--->" M
                                       end
                                     end
               end
             end.

      wseplog_pre word_ok.
      rewrite !@length_save_regs in *.
      wcancel.
      wcancel_step. {
        replace (Datatypes.length remaining_stack) with (Datatypes.length x2) by congruence.
        subst new_remaining_stack.
        solve_word_eq word_ok.
      }
      wcancel_step. {
        subst new_remaining_stack.
        simpl_addrs. reflexivity.
      }
      {
        subst new_ra. reflexivity.
      }
      wcancel_step. {
        simpl_addrs. reflexivity.
      }
      wcancel_step. {
        simpl_addrs. solve_word_eq word_ok.
      }
      subst new_remaining_stack.
      wcancel_step.
      instantiate (new_argvals := argvs). subst new_argvals.
      instantiate (new_retvals := retvs). subst new_retvals.
      wcancel_step. {
        subst FL.
        replace (Datatypes.length retnames) with (Datatypes.length binds); cycle 1. {
          repeat match goal with
                 | H: _ |- _ => let N := fresh in pose proof H as N;
                                                    apply map.putmany_of_list_sameLength in N;
                                                    ensure_new N
                 end.
          repeat match goal with
                 | H: _ |- _ => let N := fresh in pose proof H as N;
                                                    apply map.getmany_of_list_length in N;
                                                    ensure_new N
                 end.
          simpl_addrs.
          reflexivity.
        }
        simpl_addrs.
        solve_word_eq word_ok.
      }
      replace (Datatypes.length retvs) with (Datatypes.length retnames); cycle 1. {
        eapply map.getmany_of_list_length. eassumption.
      }
      wcancel_step. {
        simpl_addrs.
        solve_word_eq word_ok.
      }
      pose proof functions_expose as P.
      match goal with
      | H: map.get e_impl_full _ = Some _ |- _ => specialize P with (2 := H)
      end.
      specialize P with (1 := GetPos).
      specialize (P program_base funnames).
      setoid_rewrite P. clear P. cbn [seps].
      wcancel.
      cancel_seps_at_indices 10%nat 0%nat. {
        reflexivity.
      }
      unfold program, compile_function.
      cbn [seps].
      repeat match goal with
             | |- context [ array ?PT ?SZ ?start (?xs ++ ?ys) ] =>
               rewrite (array_append_DEPRECATED PT SZ xs ys start)
             end.
      simpl_addrs.
      rewrite! length_save_regs.
      rewrite! length_load_regs.
      wcancel.
      wcancel_step. {
        simpl_addrs.
        solve_word_eq word_ok.
      }
      repeat (wcancel_step; [
        match goal with
        | |- ?LHS = ?RHS =>
          match LHS with
          | context [List.length (compile_stmt_new ?epos1 ?pos1 ?s)] =>
            match RHS with
            | context [List.length (compile_stmt_new ?epos2 ?pos2 s)] =>
              replace (List.length (compile_stmt_new epos1 pos1 s))
                with (List.length (compile_stmt_new epos2 pos2 s))
                by apply compile_stmt_length_position_indep
            end
          end
        end;
        unfold fun_pos_env; (* <- PARAMRECORDS-related *)
        simpl_addrs;
        solve_word_eq word_ok
              | ]).
      cbn [seps].
      match goal with
      | |- iff1 ?LHS ?RHS => replace LHS with RHS; [ecancel_done'|]
      end.
      f_equal.
      {
        simpl_addrs.
        solve_word_eq word_ok.
      }
      {
        assert (forall e_pos pos s, compile_stmt_new e_pos pos s =
                                    compile_stmt_new e_pos (word.wrap (ok := word_ok) pos) s) as
            compile_stmt_new_wrap_pos. {
          admit.
        }
        rewrite compile_stmt_new_wrap_pos. rewrite <- word.unsigned_of_Z.
        f_equal.
        autorewrite with rew_word_morphism.
        f_equal.
        ring.
      }
    + simpl_addrs.
      rewrite !length_load_regs.
      rewrite !length_save_regs.
      simpl_addrs.
      solve_word_eq word_ok.
    + match goal with
      | H: ext_guarantee {| getMetrics := initialL_metrics |} |- _ => clear H
      end.
      match goal with
      | H: ext_guarantee _ |- _ => move H at bottom
      end.
      eapply ext_guarantee_preservable.
      * eassumption.
      * simpl. (* TODO memory same domain *) admit.
      * simpl. (* TODO log equality?? *) admit.

    - (* SLoad *)


  Abort.

End Proofs.
