Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Primitives.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.util.Common.
Require Import compiler.util.ListLib.
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
Import Utility MetricLogging.

Axiom TODO_sam: False.

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
      let mod_vars := modVars_as_list Z.eqb body in
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
      fits_stack (n - framelength (argnames, retnames, body)) (map.remove e fname) body ->
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

  Lemma functions_expose: forall base rel_positions impls funnames f pos impl,
      map.get rel_positions f = Some pos ->
      map.get impls f = Some impl ->
      iff1 (functions base rel_positions impls funnames)
           (functions base rel_positions impls (ListLib.removeb String.eqb f funnames) *
            program (word.add base (word.of_Z pos)) (compile_function rel_positions pos impl))%sep.
  Proof. case TODO_sam. Qed.

  Lemma union_Forall: forall {T: Type} (teqb: T -> T -> bool) (P: T -> Prop) (l1 l2: list T),
      Forall P l1 ->
      Forall P l2 ->
      Forall P (ListLib.list_union teqb l1 l2).
  Proof.
    induction l1; intros; simpl; [assumption|].
    simp. destruct_one_match; eauto.
  Qed.

  Lemma modVars_as_list_valid_registers: forall (s: @stmt (mk_Syntax_params _)),
      valid_registers s ->
      Forall valid_register (modVars_as_list Z.eqb s).
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
             rewrite (array_append' PT SZ xs ys start)
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
            try solve [simpl_addrs; autorewrite with rew_word_morphism; solve_word_eq OK]
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
  Lemma compile_ext_call_correct_new: forall (initialL: RiscvMachineL)
        action postH newPc insts (argvars resvars: list Register) initialMH R initialRegsH
        initialMetricsH argvals mGive outcome p_sp,
      insts = compile_ext_call resvars action argvars ->
      newPc = word.add initialL.(getPc) (word.of_Z (4 * (Z.of_nat (List.length insts)))) ->
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
  Proof. case TODO_sam. Qed.

  (* Ghost state used to describe low-level state introduced by the compiler.
     Called "ghost constants" because after executing a piece of code emitted by
     the compiler, these values should still be the same.
     Note, though, that when focusing on a sub-statement (i.e. when invoking the IH)
     the ghost constants will change: instructions are shoveled from insts into the frame,
     the amount of available stack shrinks, the stack pointer decreases, and if we're
     in a function call, the function being called is remove from funnames so that
     it can't be recursively called again. *)
  Record GhostConsts := {
    p_sp: word;
    num_stackwords: Z;
    p_insts: word;
    insts: list Instruction;
    program_base: word;
    e_pos: fun_pos_env;
    e_impl: env;
    funnames: list Syntax.funname;
    frame: mem -> Prop;
  }.

  Definition goodMachine
      (* high-level state ... *)
      (t: list LogItem)(m: mem)(l: locals)
      (* ... plus ghost constants ... *)
      (g: GhostConsts)
      (* ... equals low-level state *)
      (lo: MetricRiscvMachine): Prop :=
    (* registers: *)
    map.extends lo.(getRegs) l /\
    map.get lo.(getRegs) RegisterNames.sp = Some g.(p_sp) /\
    (* pc: *)
    lo.(getNextPc) = word.add lo.(getPc) (word.of_Z 4) /\
    (* memory: *)
    (exists stack_trash,
        Z.of_nat (List.length stack_trash) = g.(num_stackwords) /\
        (g.(frame) * eq m *
         word_array (word.sub g.(p_sp) (word.of_Z (bytes_per_word * g.(num_stackwords))))
                    stack_trash *
         program g.(p_insts) g.(insts) *
         functions g.(program_base) g.(e_pos) g.(e_impl) g.(funnames))%sep lo.(getMem)) /\
    (* trace: *)
    lo.(getLog) = t /\
    (* misc: *)
    ext_guarantee lo.

  (* note: [e_impl_reduced] and [g.(funnames)] will shrink one function at a time each time
     we enter a new function body, to make sure functions cannot call themselves, while
     [e_impl] and [e_pos] remain the same throughout because that's mandated by
     [FlatImp.exec] and [compile_stmt], respectively *)
  Definition exists_good_reduced_e_impl(g: GhostConsts)(s: stmt): Prop :=
    exists e_impl_reduced,
      map.extends g.(e_impl) e_impl_reduced /\
      fits_stack g.(num_stackwords) e_impl_reduced s /\
      (forall f (argnames retnames: list Syntax.varname) (body: stmt),
          map.get e_impl_reduced f = Some (argnames, retnames, body) ->
          Forall valid_register argnames /\
          Forall valid_register retnames /\
          valid_registers body /\
          stmt_not_too_big body /\
          List.In f g.(funnames) /\
          exists pos, map.get g.(e_pos) f = Some pos /\ pos mod 4 = 0).

  Notation "! n" := (word.of_Z n) (at level 0, n at level 0, format "! n") : word_scope.
  Notation "# n" := (Z.of_nat n) (at level 0, n at level 0, format "# n") : word_scope.
  Infix "+" := word.add : word_scope.
  Infix "-" := word.sub : word_scope.
  Infix "*" := word.mul : word_scope.
  Notation "- x" := (word.opp x) : word_scope.

  Delimit Scope word_scope with word.

  Open Scope word_scope.

  Axiom TODO_sam_offset_in_range: forall (offset: Z) (vars: list Register),
      - 2 ^ 11 <= offset < 2 ^ 11 - bytes_per_word * #(List.length vars).

  (* doesn't hold, only the other direction holds *)
  Axiom TODO_sam_valid_register_to_valid_FlatImp_var: forall x,
      valid_register x ->
      valid_FlatImp_var x.

  Axiom TODO_sam_no_dups: forall vars: list Register, NoDup vars.

  Definition regs_initialized(regs: locals): Prop :=
    forall r : Z, 0 < r < 32 -> exists v : word, map.get regs r = Some v.

  Lemma getmany_of_list_exists_elem: forall (m: locals) ks k vs,
      In k ks ->
      map.getmany_of_list m ks = Some vs ->
      exists v, map.get m k = Some v.
  Proof.
    induction ks; intros.
    - cbv in H. contradiction.
    - destruct H as [A | A].
      + subst a. unfold map.getmany_of_list in H0. simpl in H0. simp. eauto.
      + unfold map.getmany_of_list in H0. simpl in H0. simp. eauto.
  Qed.

  Lemma preserve_regs_initialized_after_load_regs: forall regs1 regs2 vars vals,
    regs_initialized regs1 ->
    map.only_differ regs1 (PropSet.of_list vars) regs2 ->
    map.getmany_of_list regs2 vars = Some vals ->
    regs_initialized regs2.
  Proof.
    intros. intros r B.
    specialize (H r B).
    specialize (H0 r). destruct H0 as [A | A].
    - unfold PropSet.elem_of, PropSet.of_list in A.
      eapply getmany_of_list_exists_elem; eassumption.
    - rewrite <- A. exact H.
  Qed.

  Lemma preserve_regs_initialized_after_put: forall regs var val,
    regs_initialized regs ->
    regs_initialized (map.put regs var val).
  Proof.
    unfold regs_initialized. intros. specialize (H _ H0).
    rewrite map.get_put_dec. destruct_one_match; subst; eauto.
  Qed.

  Lemma compile_stmt_correct_new:
    forall e_impl_full (s: stmt) initialTrace initialMH initialRegsH initialMetricsH postH,
    exec e_impl_full s initialTrace (initialMH: mem) initialRegsH initialMetricsH postH ->
    forall (g: GhostConsts) (initialL: RiscvMachineL) (pos: Z),
    g.(e_impl) = e_impl_full ->
    exists_good_reduced_e_impl g s ->
    @compile_stmt_new def_params _ g.(e_pos) pos s = g.(insts) ->
    stmt_not_too_big s ->
    valid_registers s ->
    pos mod 4 = 0 ->
    regs_initialized initialL.(getRegs) ->
    initialL.(getPc) = word.add g.(program_base) (word.of_Z pos) ->
    g.(p_insts)      = word.add g.(program_base) (word.of_Z pos) ->
    goodMachine initialTrace initialMH initialRegsH g initialL ->
    runsTo initialL (fun finalL => exists finalTrace finalMH finalRegsH finalMetricsH,
         postH finalTrace finalMH finalRegsH finalMetricsH /\
         finalL.(getPc) = word.add initialL.(getPc)
                                   (word.of_Z (4 * Z.of_nat (List.length g.(insts)))) /\
         goodMachine finalTrace finalMH finalRegsH g finalL).
  Proof.
    induction 1; intros; unfold goodMachine in *;
      destruct g as [p_sp num_stackwords p_insts insts program_base
                     e_pos e_impl funnames frame].
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
        do 4 eexists. repeat split; try eassumption. eexists. split; [reflexivity|].
        ecancel_assumption.

    - (* SCall *)
      (* We have one "map.get e fname" from exec, one from fits_stack, make them match *)
      lazymatch goal with
      | H: exists_good_reduced_e_impl _ _ |- _ => destruct H as (e_impl_reduced & ? & ? & ?)
      end.
      simpl in *.
      simp.
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
          pose proof G as e_impl_reduced_props;
          specialize G with (1 := H);
          destruct G as [? [? [? [? [? [funpos [GetPos ?] ] ] ] ] ] ]
      end.
      rewrite GetPos in *.

      rename stack_trash into old_stackvals.

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
                 List.length old_modvarvals = List.length (modVars_as_list Z.eqb body) /\
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
        eapply save_regs_correct with (vars := args)
                (offset := (- bytes_per_word * Z.of_nat (List.length args))%Z); simpl;
          try solve [sidecondition].
        - apply TODO_sam_offset_in_range.
        - eapply map.getmany_of_list_extends; eassumption.
        - instantiate (1 := old_argvals). unfold Register, MachineInt in *. blia.
        - wseplog_pre word_ok. wcancel.
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
      eapply run_Jal; simpl; try solve [sidecondition]; cycle 2.
      - rewrite !@length_save_regs in *.
        wseplog_pre word_ok.
        wcancel.
      - solve_divisibleBy4.
      - assumption.
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

    simpl in *.

    (* decrease sp *)
    eapply runsToStep. {
      eapply run_Addi with (rd := RegisterNames.sp) (rs := RegisterNames.sp);
        try solve [sidecondition | simpl; solve_divisibleBy4 ].
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
      eapply run_store_word with (rs1 := RegisterNames.sp) (rs2 := RegisterNames.ra);
        try solve [sidecondition | simpl; solve_divisibleBy4]. {
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
      pose proof (@getmany_of_list_exists _ _ _ l valid_register (modVars_as_list Z.eqb body)) as P
    end.
    edestruct P as [newvalues P2]; clear P.
    { apply modVars_as_list_valid_registers. assumption. }
    {
      intros.
      rewrite !map.get_put_dec.
      destruct_one_match; [eexists; reflexivity|].
      destruct_one_match; [eexists; reflexivity|].
      eauto.
    }
    eapply runsTo_trans. {
      eapply save_regs_correct; simpl; cycle 2.
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
          | @modVars_as_list ?EQ ?params ?eqd ?s =>
            so fun hyporgoal => match hyporgoal with
                                | context [?M'] =>
                                  lazymatch M' with
                                  | @modVars_as_list ?EQ ?params' ?eqd' ?s =>
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
      1: apply TODO_sam_offset_in_range.
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
          (vars := argnames) (values := argvs);
        simpl; cycle 3.
      - rewrite map.get_put_same. reflexivity.
      - assumption.
      - rewrite !@length_save_regs in *.
        wseplog_pre word_ok.
        wcancel.
      - reflexivity.
      - eapply Forall_impl.
        + apply TODO_sam_valid_register_to_valid_FlatImp_var.
        + assumption.
      - apply TODO_sam_no_dups.
      - apply TODO_sam_offset_in_range.
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
      eapply IHexec with (g := {|
        p_sp := word.sub p_sp !(bytes_per_word * FL);
        e_pos := e_pos;
        program_base := program_base;
        funnames := (ListLib.removeb String.eqb fname funnames) |});
        simpl; try assumption.
      1: reflexivity.
      1: {
        unfold exists_good_reduced_e_impl. simpl. eexists.
        split; [|split].
        2: eassumption.
        - generalize (funname_env_ok (list Register * list Register * stmt)).
          match goal with
          | H: map.extends e_impl_full _ |- _ => clear -H
          end.
          intro OK.
          Require Import coqutil.Datatypes.String.
          map_solver OK.
        - move e_impl_reduced_props at bottom.
          intros *. intro G.
          assert (map.get e_impl_reduced f = Some (argnames0, retnames0, body0)) as G'. {
            generalize (funname_env_ok (list Register * list Register * stmt)). clear -G.
            intro OK.
            map_solver OK.
          }
          specialize e_impl_reduced_props with (1 := G'). simp.
          repeat split; eauto.
          destr (String.eqb f fname).
          + subst f.
            generalize (funname_env_ok (list Register * list Register * stmt)). clear -G.
            intro OK. exfalso. map_solver OK.
          + eapply remove_In_ne; try typeclasses eauto; assumption.
      }
      1: reflexivity.
      4: reflexivity.
      4: repeat split.
      6: {
        eexists. split; cycle 1.
        - subst FL. unfold fun_pos_env in *.
          rewrite !@length_load_regs in *.
          wseplog_pre word_ok.
          wcancel.
          cbn [seps].
          match goal with
          | |- iff1 ?LHS ?RHS =>
            match LHS with
            | context [array ptsto_instr ?SZ ?ADDR (compile_stmt_new ?EPOS ?POS body)] =>
              match RHS with
              | context [array ptsto_instr ?SZ' ?ADDR' (compile_stmt_new ?EPOS' ?POS' body)] =>
                replace (array ptsto_instr SZ ADDR (compile_stmt_new EPOS POS body)) with
                        (array ptsto_instr SZ' ADDR' (compile_stmt_new EPOS' POS' body));
                  [ecancel|]
              end
            end
          end.
          f_equal. solve_word_eq word_ok.
        - subst FL. simpl_addrs. blia.
      }
      1: solve_divisibleBy4.
      {
        eapply preserve_regs_initialized_after_load_regs; cycle 1; try eassumption.
        eapply preserve_regs_initialized_after_put.
        eapply preserve_regs_initialized_after_put.
        assumption.
      }
      { simpl_addrs. solve_word_eq word_ok. }
      { move H1 at bottom. move H13 at bottom.
        Set Nested Proofs Allowed.

  Lemma putmany_of_list_find_index: forall keys vals (m1 m2: locals) k v,
      map.putmany_of_list keys vals m1 = Some m2 ->
      map.get m2 k = Some v ->
      (exists n, nth_error keys n = Some k /\ nth_error vals n = Some v) \/
      (map.get m1 k = Some v).
  Proof.
    induction keys; intros.
    - simpl in H. simp. eauto.
    - simpl in H. simp. specialize IHkeys with (1 := H) (2 := H0).
      destruct IHkeys as [IH | IH].
      + destruct IH as (n & IH).
        left. exists (S n). simpl. exact IH.
      + rewrite map.get_put_dec in IH. destruct_one_match_hyp.
        * subst. left. exists O. simpl. auto.
        * right. assumption.
  Qed.

  Lemma getmany_of_list_get: forall keys n (m: locals) vals k v,
      map.getmany_of_list m keys = Some vals ->
      nth_error keys n = Some k ->
      nth_error vals n = Some v ->
      map.get m k = Some v.
  Proof.
    induction keys; intros.
    - apply nth_error_nil_Some in H0. contradiction.
    - unfold map.getmany_of_list in *. simpl in *. simp.
      destruct n.
      + simpl in *. simp. assumption.
      + simpl in *. eauto.
  Qed.

  Lemma extends_putmany_of_list_empty: forall argnames argvals (lL lH: locals),
      map.putmany_of_list argnames argvals map.empty = Some lH ->
      map.getmany_of_list lL argnames = Some argvals ->
      map.extends lL lH.
  Proof.
    unfold map.extends. intros.
    pose proof putmany_of_list_find_index as P.
    specialize P with (1 := H) (2 := H1). destruct P as [P | P]; cycle 1. {
      rewrite map.get_empty in P. discriminate.
    }
    destruct P as (n & P1 & P2).
    eapply getmany_of_list_get; eassumption.
  Qed.

  eapply extends_putmany_of_list_empty; eassumption.
      }
      {
        assert (forall x, In x argnames -> valid_FlatImp_var x) as F. {
          eapply Forall_forall.
          eapply Forall_impl.
          + apply TODO_sam_valid_register_to_valid_FlatImp_var.
          + assumption.
        }
        revert F.
        subst FL.
        repeat match goal with
               | H: ?T |- _ => lazymatch T with
                               | map.only_differ _ _ middle_regs0 => revert H
                               | assumptions => fail
                               | _ => clear H
                               end
               end.
        intros HO F.
        unfold map.only_differ in HO.
        unfold PropSet.elem_of, PropSet.of_list in HO.
        specialize (HO RegisterNames.sp).
        destruct HO as [HO | HO].
        - specialize (F _ HO). unfold valid_FlatImp_var, RegisterNames.sp in F. exfalso. blia.
        - rewrite <- HO.
          rewrite map.get_put_same.
          f_equal. simpl_addrs. solve_word_eq word_ok.
      }
      {
        case TODO_sam. (* TODO log unchanged --> strengthen all used lemmas *)
      }
      {
        eapply ext_guarantee_preservable.
        + eassumption.
        + cbn.
          (* TODO will need stronger prove_ext_guarantee, derive same_domain from sep *)
          case TODO_sam.
        + cbn.  (* log equality? *)
          case TODO_sam.
      }
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
      destruct H as (retvs & finalRegsH' & ? & ? & ?)
    end.

    (* save results onto stack *)
    eapply runsTo_trans. {
      eapply save_regs_correct with (vars := retnames); simpl; cycle 2.
      - eapply map.getmany_of_list_extends; try eassumption.
      - eassumption.
      - instantiate (1 := old_retvals). unfold Register, MachineInt in *. blia.
      - subst FL.
        wseplog_pre word_ok.
        wcancel.
      - reflexivity.
      - assumption.
      - apply TODO_sam_offset_in_range.
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

    (* load back the modified vars *)
    eapply runsTo_trans. {
      eapply load_regs_correct with
          (vars := (modVars_as_list _ body)) (values := newvalues);
        simpl; cycle 3.
      - eassumption.
      - repeat match goal with
               | H: map.getmany_of_list _ _ = Some _ |- _ =>
                 unique eapply @map.getmany_of_list_length in copy of H
               end.
        instantiate (1 := Z.eqb).
        blia.
      - subst FL.
        wseplog_pre word_ok.
        wcancel.
      - reflexivity.
      - replace valid_FlatImp_var with valid_register by case TODO_sam.
        apply modVars_as_list_valid_registers.
        assumption.
      - apply TODO_sam_no_dups.
      - apply TODO_sam_offset_in_range.
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
      eapply run_load_word; cycle 2; try solve [sidecondition].
      - simpl.
        assert (forall x, In x (modVars_as_list Z.eqb body) -> valid_FlatImp_var x) as F. {
          eapply Forall_forall.
          eapply Forall_impl.
          + apply TODO_sam_valid_register_to_valid_FlatImp_var.
          + eapply modVars_as_list_valid_registers. assumption.
        }
        revert F.
        subst FL.

        repeat match goal with
               | H: ?T |- _ => lazymatch T with
                               | assumptions => fail
                               | map.only_differ middle_regs1 _ middle_regs2 => revert H
                               | map.get middle_regs1 RegisterNames.sp = Some _ => revert H
                               | _ => clear H
                               end
               end.
        intros G HO F.
        match goal with
        | D: map.only_differ middle_regs1 _ middle_regs2 |- _ =>
          specialize (D RegisterNames.sp); destruct D as [A | A]
        end.
        + exfalso. unfold PropSet.elem_of, PropSet.of_list in A.
          specialize (F _ A). unfold valid_FlatImp_var, RegisterNames.sp in F.
          blia.
        + etransitivity; [symmetry|]; eassumption.
      - simpl.
        subst FL.
        wseplog_pre word_ok.
        wcancel.
      - assumption.
      - assumption.
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
      eapply (run_Addi RegisterNames.sp RegisterNames.sp _
             (* otherwise it will pick the decreasing (with a - in front) *)
              (bytes_per_word *
                  #(List.length argnames + List.length retnames + 1 + List.length (modVars_as_list _ body)))%Z);
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
        + exfalso. (* contradiction: sp cannot be in modVars of body *) case TODO_sam.
        + etransitivity; [symmetry|]; eassumption.
      - simpl.
        instantiate (2 := BinInt.Z.eqb).
        wseplog_pre word_ok.
        wcancel.
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
      eapply run_Jalr0 with (rs1 := RegisterNames.ra); simpl;
        try solve [sidecondition | solve_divisibleBy4].
      - case TODO_sam. (*   ?oimm12 mod 4 = 0 *)
      - case TODO_sam. (*   word.unsigned ?dest mod 4 = 0  *)
      - rewrite map.get_put_diff by (clear; cbv; congruence).
        rewrite map.get_put_same. reflexivity.
      - wseplog_pre word_ok.
        wcancel.
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
          (offset := (- bytes_per_word * Z.of_nat (List.length args + List.length binds))%Z)
          (p_sp0 := p_sp);
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
      - replace valid_FlatImp_var with valid_register by case TODO_sam.
        assumption.
      - apply TODO_sam_no_dups.
      - apply TODO_sam_offset_in_range.
      - subst FL.
        simpl_addrs.
        rewrite map.get_put_same. f_equal. solve_word_eq word_ok.
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
    do 4 eexists.
    repeat split.
    + replace middle_log3 with middle_log1 by case TODO_sam. (* TODO investigate! *)
      eassumption.
    + simpl_addrs. rewrite length_load_regs. rewrite length_save_regs. simpl_addrs.
      solve_word_eq word_ok.
    + (* TODO chain of extends *)
      case TODO_sam.
    + match goal with
      | H: map.only_differ ?m1 _ ?m2 |- map.get ?m2 _ = Some _ =>
        replace m2 with m1 by case TODO_sam (* TODO almost *)
      end.
      rewrite map.get_put_same. f_equal. subst FL.
      simpl_addrs.
      solve_word_eq word_ok.
    + epose (?[new_ra]: word) as new_ra. cbv delta [id] in new_ra.
      match goal with
      | H:   #(Datatypes.length ?new_remaining_stack) = _ |- _ =>
        exists (new_remaining_stack ++ newvalues ++ [new_ra] ++ retvs ++ argvs)
      end.
      assert (Datatypes.length (modVars_as_list Z.eqb body) = Datatypes.length newvalues). {
        eapply map.getmany_of_list_length. eassumption.
      }
      assert (Datatypes.length retnames = Datatypes.length retvs). {
        eapply map.getmany_of_list_length. eassumption.
      }

      (* PARAMRECORDS *)
      change Syntax.varname with Register in *.
      repeat match goal with
             | H: _ = List.length ?M |- _ =>
               lazymatch M with
               | @modVars_as_list ?EQ ?params ?eqd ?s =>
                 so fun hyporgoal => match hyporgoal with
                                     | context [?M'] =>
                                       lazymatch M' with
                                       | @modVars_as_list ?EQ ?params' ?eqd' ?s =>
                                         assert_fails (constr_eq M M');
                                           change M' with M in *;
                                           idtac M' "--->" M
                                       end
                                     end
               end
             end.

      split. {
        simpl_addrs. subst FL. simpl_addrs. ring.
      }
      subst FL.
      wseplog_pre word_ok.
      rewrite !@length_save_regs in *.
      wcancel.
      wcancel_step. {
        subst new_ra. reflexivity.
      }
      wcancel_step. {
        subst new_ra.
        simpl_addrs.
        replace (Datatypes.length retvs) with (Datatypes.length binds).
        - solve_word_eq word_ok.
        - eapply map.getmany_of_list_length. eassumption.
      }
      pose proof functions_expose as P.
      match goal with
      | H: map.get e_impl_full _ = Some _ |- _ => specialize P with (2 := H)
      end.
      specialize P with (1 := GetPos).
      specialize (P program_base funnames).
      setoid_rewrite P. clear P. cbn [seps].
      wcancel.
      unfold program, compile_function.
      cbn [seps].
      repeat match goal with
             | |- context [ array ?PT ?SZ ?start (?xs ++ ?ys) ] =>
               rewrite (array_append' PT SZ xs ys start)
             end.
      simpl_addrs.
      rewrite! length_save_regs.
      rewrite! length_load_regs.
      wcancel.
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
    + match goal with
      | H: ext_guarantee {| getMetrics := initialL_metrics |} |- _ => clear H
      end.
      match goal with
      | H: ext_guarantee _ |- _ => move H at bottom
      end.
      eapply ext_guarantee_preservable.
      * eassumption.
      * simpl. (* TODO memory same domain *) case TODO_sam.
      * simpl. (* TODO log equality?? *) case TODO_sam.

    - (* SLoad *)
      case TODO_sam.
      (*
      unfold Memory.load, Memory.load_Z in *. simp. subst_load_bytes_for_eq.
      run1det. run1done.
      *)

    - (* SStore *)
      case TODO_sam.
      (*
      simpl_MetricRiscvMachine_get_set.
      assert ((eq m * (program initialL_pc [[compile_store sz a v 0]] * R))%sep initialL_mem)
             as A by ecancel_assumption.
      pose proof (store_bytes_frame H2 A) as P.
      destruct P as (finalML & P1 & P2).
      run1det. run1done.
      *)

    - (* SLit *)
      case TODO_sam.
      (*
      eapply compile_lit_correct_full.
      + sidecondition.
      + unfold compile_stmt. simpl. ecancel_assumption.
      + sidecondition.
      + simpl. run1done;
        remember (updateMetricsForLiteral v initialL_metrics) as finalMetrics;
        symmetry in HeqfinalMetrics;
        pose proof update_metrics_for_literal_bounded as Hlit;
        specialize Hlit with (1 := HeqfinalMetrics);
        solve_MetricLog.
       *)

    - (* SOp *)
      case TODO_sam.
      (*
      match goal with
      | o: Syntax.bopname.bopname |- _ => destruct o
      end;
        simpl in *; run1det; try solve [run1done].
      + simpl_MetricRiscvMachine_get_set.
        run1det. run1done;
      [match goal with
      | H: ?post _ _ _ |- ?post _ _ _ => eqexact H
      end | solve_MetricLog..].
      rewrite reduce_eq_to_sub_and_lt.
      symmetry. apply map.put_put_same.
      *)

    - (* SSet *)
      case TODO_sam.
      (*
      run1det. run1done.
      *)

    - (* SIf/Then *)
      case TODO_sam.
      (*
      (* execute branch instruction, which will not jump *)
      eapply runsTo_det_step; simpl in *; subst.
      + simulate'. simpl_MetricRiscvMachine_get_set.
        destruct cond; [destruct op | ];
          simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity.
      + eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
        * (* use IH for then-branch *)
          eapply IHexec; IH_sidecondition.
        * (* jump over else-branch *)
          simpl. intros. destruct_RiscvMachine middle. simp. subst.
          run1det. run1done.
       *)

    - (* SIf/Else *)
      case TODO_sam.
      (*
      (* execute branch instruction, which will jump over then-branch *)
      eapply runsTo_det_step; simpl in *; subst.
      + simulate'.
        destruct cond; [destruct op | ];
          simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity.
      + eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
        * (* use IH for else-branch *)
          eapply IHexec; IH_sidecondition.
        * (* at end of else-branch, i.e. also at end of if-then-else, just prove that
             computed post satisfies required post *)
          simpl. intros. destruct_RiscvMachine middle. simp. subst. run1done.
          *)

    - (* SLoop/again *)
      case TODO_sam.
      (*
      on hyp[(stmt_not_too_big body1); runsTo] do (fun H => rename H into IH1).
      on hyp[(stmt_not_too_big body2); runsTo] do (fun H => rename H into IH2).
      on hyp[(stmt_not_too_big (SLoop body1 cond body2)); runsTo] do (fun H => rename H into IH12).
      eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
      + (* 1st application of IH: part 1 of loop body *)
        eapply IH1; IH_sidecondition.
      + simpl in *. simpl. intros. destruct_RiscvMachine middle. simp. subst.
        destruct (@eval_bcond (@Semantics_params p) middle_regs cond) as [condB|] eqn: E.
        2: exfalso;
           match goal with
           | H: context [_ <> None] |- _ => solve [eapply H; eauto]
           end.
        destruct condB.
        * (* true: iterate again *)
          eapply runsTo_det_step; simpl in *; subst.
          { simulate'.
            destruct cond; [destruct op | ];
              simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity. }
          { eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
            - (* 2nd application of IH: part 2 of loop body *)
              eapply IH2; IH_sidecondition; simpl_MetricRiscvMachine_get_set; eassumption.
            - simpl in *. simpl. intros. destruct_RiscvMachine middle. simp. subst.
              (* jump back to beginning of loop: *)
              run1det.
              eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
              + (* 3rd application of IH: run the whole loop again *)
                eapply IH12; IH_sidecondition; simpl_MetricRiscvMachine_get_set; eassumption.
              + (* at end of loop, just prove that computed post satisfies required post *)
                simpl. intros. destruct_RiscvMachine middle. simp. subst.
                run1done. }
        * (* false: done, jump over body2 *)
          eapply runsTo_det_step; simpl in *; subst.
          { simulate'.
            destruct cond; [destruct op | ];
              simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity. }
          { simpl in *. run1done. }
          *)

    - (* SSeq *)
      case TODO_sam.
      (*
      rename IHexec into IH1, H2 into IH2.
      eapply runsTo_trans.
      + eapply IH1; IH_sidecondition.
      + simpl. intros. destruct_RiscvMachine middle. simp. subst.
        eapply runsTo_trans.
        * eapply IH2; IH_sidecondition; simpl_MetricRiscvMachine_get_set; eassumption.
        * simpl. intros. destruct_RiscvMachine middle. simp. subst. run1done.
        *)

    - (* SSkip *)
      case TODO_sam.
      (*
      run1done.
      *)

    Grab Existential Variables. repeat constructor.
  Qed. (* <-- takes a while *)

End Proofs.
