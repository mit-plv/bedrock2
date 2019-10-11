Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.rewr.
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
Require Import compiler.FlatToRiscvLiterals.
Import compiler.FlatToRiscvCommon.FlatToRiscv.
Require Import compiler.load_save_regs_correct.
Require Import compiler.eqexact.
Require Import compiler.RiscvWordProperties.
Require Import compiler.on_hyp_containing.
Require Import coqutil.Word.DebugWordEq.
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

  Notation fun_pos_env := (@funname_env p Z).

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
         | _, _ => emp False
         end * (rec rest))%sep
      end.

  Lemma removeb_not_In{A : Type}{aeqb : A -> A -> bool}{aeqb_dec: EqDecider aeqb}:
    forall (l : list A) (a: A), ~ In a l -> removeb aeqb a l = l.
  Proof.
    induction l; intros; simpl; try reflexivity.
    destr (aeqb a0 a); simpl in *; subst.
    + exfalso. auto.
    + f_equal. eauto.
  Qed.

  Lemma In_removeb_In{A : Type}{aeqb : A -> A -> bool}{aeqb_dec: EqDecider aeqb}:
    forall (a1 a2: A) (l: list A), In a1 (removeb aeqb a2 l) -> In a1 l.
  Proof.
    induction l; intros; simpl in *; try contradiction.
    destr (aeqb a2 a); simpl in *; intuition idtac.
  Qed.

  Lemma In_removeb_diff{A : Type}{aeqb : A -> A -> bool}{aeqb_dec: EqDecider aeqb}:
    forall (a1 a2: A) (l: list A), a1 <> a2 -> In a1 l -> In a1 (removeb aeqb a2 l).
  Proof.
    induction l; intros; simpl in *; try contradiction.
    destr (aeqb a2 a); simpl in *; subst; intuition congruence.
  Qed.

  Lemma NoDup_removeb{A : Type}{aeqb : A -> A -> bool}{aeqb_dec: EqDecider aeqb}:
    forall (a: A) (l: list A),
      NoDup l ->
      NoDup (removeb aeqb a l).
  Proof.
    induction l; intros; simpl in *; try assumption.
    destr (aeqb a a0); simpl in *; simp; auto.
    constructor; auto. intro C. apply H2. eapply In_removeb_In. eassumption.
  Qed.

  Ltac cancel_emps_at_indices i j :=
    lazymatch goal with
    | |- Lift1Prop.iff1 (seps ?LHS) (seps ?RHS) =>
      simple refine (cancel_emps_at_indices i j LHS RHS _ _ eq_refl eq_refl _ _);
      cbn [firstn skipn app hd tl]
    end.

  Lemma functions_expose: forall base rel_positions impls funnames f pos impl,
      map.get rel_positions f = Some pos ->
      map.get impls f = Some impl ->
      List.In f funnames ->
      List.NoDup funnames ->
      iff1 (functions base rel_positions impls funnames)
           (functions base rel_positions impls (ListLib.removeb String.eqb f funnames) *
            program (word.add base (word.of_Z pos)) (compile_function rel_positions pos impl))%sep.
  Proof.
    intros base rel_positions impls.
    induction funnames; intros.
    - contradiction.
    - simpl in *. simp. destr (f =? a)%string.
      + subst a. simpl. rewrite_match. simp.
        rewrite removeb_not_In by assumption.
        ecancel.
      + assert (In f funnames) by intuition congruence.
        unfold negb. simpl.
        destruct (map.get rel_positions a) as [pos'|];
          destruct (map.get impls a) as [impl'|].
        1: { cancel. eapply IHfunnames; assumption. }
        all: clear; unfold iff1, sep, emp; intros; split; intros; simp; contradiction.
  Qed.

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
    simpl_Z_nat;
    unfold Register, MachineInt in *;
    (* note: it's the user's responsability to ensure that left-to-right rewriting with all
     nat and Z equations terminates, otherwise we'll loop infinitely here *)
    repeat match goal with
           | E: @eq ?T ?LHS _ |- _ =>
             lazymatch T with
             | Z => idtac
             | nat => idtac
             end;
             progress prewrite LHS E
           end.

  Ltac wseplog_pre OK :=
    use_sep_assumption;
    autounfold with unf_to_array;
    unfold program, word_array;
    (* Note that "rewr" only works with equalities, not with iff1, so we use
       iff1ToEq to turn iff1 into eq (requires functional and propositionl extensionality).
       Alternatively, we could use standard rewrite (which might instantiate too many evars),
       or we could make a "seprewrite" which works on "seps [...] [...]" by replacing the
       i-th clause on any side with the rhs of the provided iff1, or we could make a
       seprewrite which first puts the clause to be replaced as the left-most, and then
       eapplies a "Proper_sep_iff1: Proper (iff1 ==> iff1 ==> iff1) sep", but that would
       change the order of the clauses. *)
    rewr (fun t => match t with
           | context [ array ?PT ?SZ ?start (?xs ++ ?ys) ] =>
             constr:(iff1ToEq (array_append' PT SZ xs ys start))
           | context [ array ?PT ?SZ ?start (?x :: ?xs) ] =>
             constr:(iff1ToEq (array_cons PT SZ x xs start))
           end) in |-*;
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

  Ltac tag P ::=
    let __ := lazymatch type of P with
              | @map.rep _ _ _ -> Prop => idtac
              | _ => fail 10000 P "is not a sep clause"
              end in
    lazymatch P with
    | array ptsto_instr _ _ (compile_stmt_new _ _ ?Code) => Code
    | ptsto_instr _ ?Instr => Instr
    | array ptsto_word _ _ ?Words => Words
    | functions _ _ _ ?FunNames => FunNames
    | _ => fail "no recognizable tag"
    end.

  Ltac addr P ::=
    let __ := lazymatch type of P with
              | @map.rep _ _ _ -> Prop => idtac
              | _ => fail 10000 P "is not a sep clause"
              end in
    lazymatch P with
    | array _ _ ?A _ => A
    | ptsto_instr ?A _ => A
    | ptsto_word ?A _ => A
    | _ => fail "no recognizable address"
    end.

  Ltac wcancel_instantiated := wcancel (@word_ok (@W (@def_params p))).
  (* shadows original wcancel: *)
  Ltac wcancel := wcancel_instantiated.

  Ltac safe_sidecond :=
    match goal with
    (* proving these equalties with eq_refl will make other goals harder to prove,
       so we prefer to leave these open, so that they will become instantiated,
       and we can do interesting work here
    | |- ?L = _ => is_evar L; reflexivity
    | |- _ = ?R => is_evar R; reflexivity
      However, for some equalities, it's ok to prove them with eq_refl:
    *)
    | |- @eq ?T _ _ => first [ unify T (list Instruction) | unify T (@env (@Semantics_params p)) ];
                       reflexivity
    | H: fits_stack _ _ ?Code |- fits_stack _ _ ?Code => exact H
    | H: map.get ?R RegisterNames.sp = Some _ |- map.get ?R RegisterNames.sp = Some _ => exact H
    | |- ?G => assert_fails (has_evar G);
               solve [ prove_ext_guarantee
                     | simpl_addrs; solve_word_eq (@word_ok (@W (@def_params p)))
                     | solve_stmt_not_too_big
                     | reflexivity
                     | assumption
                     | solve_divisibleBy4 ]
    | |- _ => solve [wseplog_pre word_ok; wcancel ] (* TODO probably not safe as-is *)
    | |- ?G => is_lia G; assert_fails (has_evar G);
               (* not sure why this line is needed, lia should be able to deal with (x := _) hyps,
                  maybe it changes some implicit args or universes? *)
               repeat match goal with x := _ |- _ => subst x end;
               blia
    end.

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
     in a function call, the function being called is removed from funnames so that
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

  Ltac simpl_g_get :=
    cbn [p_sp num_stackwords p_insts insts program_base e_pos e_impl funnames frame] in *.

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

  (* note: [e_impl_reduced] and [funnames] will shrink one function at a time each time
     we enter a new function body, to make sure functions cannot call themselves, while
     [e_impl] and [e_pos] remain the same throughout because that's mandated by
     [FlatImp.exec] and [compile_stmt], respectively *)
  Definition good_reduced_e_impl(e_impl_reduced e_impl: env)
    (num_stackwords: Z)(funnames: list Syntax.funname)(e_pos: fun_pos_env): Prop :=
      map.extends e_impl e_impl_reduced /\
      (forall f (argnames retnames: list Syntax.varname) (body: stmt),
          map.get e_impl_reduced f = Some (argnames, retnames, body) ->
          Forall valid_register argnames /\
          Forall valid_register retnames /\
          valid_registers body /\
          stmt_not_too_big body /\
          List.In f funnames /\
          exists pos, map.get e_pos f = Some pos /\ pos mod 4 = 0).

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

  Ltac run1done :=
    apply runsToDone;
    simpl_MetricRiscvMachine_get_set;
    simpl in *;
    repeat match goal with
    | |- exists (_: _), _ => eexists
    end;
    repeat split;
    simpl_word_exprs (@word_ok (@W (@def_params p)));
    match goal with
    | |- _ => solve [eauto]
    | |- _ => solve_word_eq (@word_ok (@W (@def_params p)))
    | |- exists _, _ = _ /\ (_ * _)%sep _ =>
      eexists; split; cycle 1; [ wseplog_pre (@word_ok (@W (@def_params p))); wcancel | blia ]
    | |- _ => prove_ext_guarantee
    | |- _ => solve [map_solver (@locals_ok p h)]
    | |- _ => idtac
    end.

  Ltac after_IH :=
    simpl_MetricRiscvMachine_get_set;
    simpl_g_get;
    rewrite ?@length_save_regs, ?@length_load_regs in *;
    unfold Register, MachineInt in *;
    simpl_word_exprs (@word_ok (@W (@def_params p)));
    repeat match goal with
           | |- _ /\ _ => split
           | |- exists _, _ => eexists
           end.

  Ltac sidecondition_hook ::=
    try solve [ map_solver (@locals_ok p h)
              | wseplog_pre (@word_ok (@W (@def_params p))); wcancel ].

  Lemma split_from_right{A: Type}: forall (l: list A) (len: nat),
      (len <= length l)%nat ->
      exists lL lR, l = lL ++ lR /\ length lL = (length l - len)%nat /\ length lR = len.
  Proof.
    intros.
    exists (List.firstn (List.length l - len)%nat l).
    exists (List.skipn (List.length l - len)%nat l).
    ssplit.
    - eapply ListLib.firstn_skipn_reassemble; reflexivity.
    - rewrite List.length_firstn_inbounds; blia.
    - rewrite List.length_skipn; blia.
  Qed.

  Ltac split_from_right nameOrig nameL nameR len :=
    let nL := fresh in let nR := fresh in
    destruct (split_from_right nameOrig len) as [ nL [ nR [ ? [ ? ? ] ] ] ];
    [ blia | ];
    subst nameOrig;
    rename nL into nameL, nR into nameR.

  Lemma map_extends_remove: forall (m1 m2: funname_env (list Z * list Z * stmt)) k,
      map.extends m1 m2 ->
      map.extends m1 (map.remove m2 k).
  Proof.
    generalize (funname_env_ok (list Z * list Z * stmt)).
    simpl in *.
    unfold Register, MachineInt in *.
    intro OK.
    map_solver OK.
  Qed.

  Lemma map_get_Some_remove: forall (m: funname_env (list Z * list Z * stmt)) k1 k2 v,
      map.get (map.remove m k1) k2 = Some v ->
      map.get m k2 = Some v.
  Proof.
    generalize (funname_env_ok (list Z * list Z * stmt)).
    intro OK. intros. map_solver OK.
  Qed.

  Lemma compile_stmt_correct_new:
    forall e_impl_full (s: stmt) initialTrace initialMH initialRegsH initialMetricsH postH,
    exec e_impl_full s initialTrace (initialMH: mem) initialRegsH initialMetricsH postH ->
    forall (g: GhostConsts) (initialL: RiscvMachineL) (pos: Z) (e_impl_reduced: env),
    g.(e_impl) = e_impl_full ->
    good_reduced_e_impl e_impl_reduced g.(e_impl) g.(num_stackwords) g.(funnames) g.(e_pos) ->
    fits_stack g.(num_stackwords) e_impl_reduced s ->
    @compile_stmt_new def_params _ g.(e_pos) pos s = g.(insts) ->
    stmt_not_too_big s ->
    valid_registers s ->
    pos mod 4 = 0 ->
    (word.unsigned g.(program_base)) mod 4 = 0 ->
    regs_initialized initialL.(getRegs) ->
    initialL.(getPc) = word.add g.(program_base) (word.of_Z pos) ->
    g.(p_insts)      = word.add g.(program_base) (word.of_Z pos) ->
    NoDup g.(funnames) ->
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
      | H: good_reduced_e_impl _ _ _  _ _ |- _ => destruct H as (? & ?)
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
        unfold framelength in *. subst FL. simpl in *.
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
        rename old_stackvals into ToSplit.
        split_from_right ToSplit ToSplit old_argvals (List.length argnames).
        split_from_right ToSplit ToSplit old_retvals (List.length retnames).
        split_from_right ToSplit ToSplit old_ras 1%nat.
        split_from_right ToSplit ToSplit old_modvarvals
                         (Datatypes.length (modVars_as_list Z.eqb body)).
        destruct old_ras as [|old_ra rest]; try discriminate.
        destruct rest; try discriminate.
        repeat econstructor;
          [ do 3 rewrite <- List.app_assoc; reflexivity | blia.. ].
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
        eapply save_regs_correct with (vars := args) (p_sp0 := p_sp)
                (offset := (- bytes_per_word * Z.of_nat (List.length args))%Z); simpl; cycle -2.
        - wseplog_pre word_ok. wcancel.
        - sidecondition.
        - sidecondition.
        - apply TODO_sam_offset_in_range.
        - eapply map.getmany_of_list_extends; eassumption.
        - sidecondition.
        - unfold Register, MachineInt in *. blia.
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
    auto_specialize.
    match goal with
    | H: (_ * _)%sep _ |- _ => seprewrite_in P H; clear P
    end.

    simpl in *.

    (* decrease sp *)
    eapply runsToStep. {
      eapply run_Addi with (rd := RegisterNames.sp) (rs := RegisterNames.sp);
        try solve [sidecondition | simpl; solve_divisibleBy4 ].
        simpl.
        rewrite map.get_put_diff by (clear; cbv; congruence).
        eassumption.
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
        try solve [sidecondition | simpl; solve_divisibleBy4].
        simpl.
        rewrite map.get_put_diff by (clear; cbv; congruence).
        rewrite map.get_put_same. reflexivity.
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
      1: { wseplog_pre word_ok. wcancel. }
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
      unfold good_reduced_e_impl in *. simp.
      eapply IHexec with (g := {|
        p_sp := word.sub p_sp !(bytes_per_word * FL);
        e_pos := e_pos;
        program_base := program_base;
        funnames := (ListLib.removeb String.eqb fname funnames) |});
      after_IH;
      subst FL. (* <-- TODO needed? *)
      all: try safe_sidecond.
      all: try safe_sidecond.
      { eapply map_extends_remove; eassumption. }
      {   move e_impl_reduced_props at bottom.
          intros *. intro G.
          assert (map.get e_impl_reduced f = Some (argnames0, retnames0, body0)) as G'. {
            eapply map_get_Some_remove; eassumption.
          }
          specialize e_impl_reduced_props with (1 := G'). simp.
          repeat split; eauto.
          destr (String.eqb f fname).
          + subst f.
            simpl in *. unfold Register, MachineInt in *.
            generalize (funname_env_ok (list Z * list Z * stmt)). clear -G.
            intro OK. exfalso. map_solver OK.
          + eapply remove_In_ne; try typeclasses eauto; assumption.
      }
      {
        eapply preserve_regs_initialized_after_load_regs; cycle 1; try eassumption.
        eapply preserve_regs_initialized_after_put.
        eapply preserve_regs_initialized_after_put.
        assumption.
      }
      { eapply NoDup_removeb; eassumption. }
      { eapply map.extends_putmany_of_list_empty; eassumption. }
      {
        assert (forall x, In x argnames -> valid_FlatImp_var x) as F. {
          eapply Forall_forall.
          eapply Forall_impl.
          + apply TODO_sam_valid_register_to_valid_FlatImp_var.
          + assumption.
        }
        revert F.
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
      eapply run_load_word; cycle 2.
      - simpl. solve [sidecondition].
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
      - reflexivity.
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
        subst FL.
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
        cbn [seps].
        wcancel.
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
    + rename l into lH, finalRegsH into lFH', finalRegsH' into lH', st0 into lFH,
             middle_regs into lL.

      (*

         Summary of what happened in FlatImp:

         Acion (in order):
         ------------------------------
         put (argnames, argvals) from outer locals into new empty map
         execute function body
         take (retnames, retvals) out of map and put into outer locals



         Summary of what happened in riscv:              Original low-level locals: lL

         Action (in order):               Correctness lemma:      New low-level locals:
         -------------------------------  ---------------------   ---------------------
         put arguments on stack           save_regs_correct
         jump to function                 run_Jal
         decrease sp                      run_Addi
         save ra on stack                 run_store_word
         save vars modified by callee     save_regs_correct
         load argvars from stack          load_regs_correct       middle_regs0
         execute function body            IHexec                  middle_regs1
         save results onto stack          save_regs_correct
         load back the modified vars      load_regs_correct       middle_regs2
         load back the return address     run_load_word
         increase sp                      run_Addi
         jump back to caller              run_Jalr0
         load result values from stack    load_regs_correct       middle_regs3
       *)

      (* TODO this should be in the IH *)
      assert (map.only_differ middle_regs0 (PropSet.of_list (modVars_as_list Z.eqb body))
                              middle_regs1) by admit.

      (* TODO do we have to save argvars (names chosen by callee) on the stack, ie
         treat them the same as of modVars of function body?? *)

      (* TODO how to explain map.getmany_of_list and map.putmany_of_list to map_solver? *)

      (*
      try match goal with
      | x: ?T |- _ => unify T (@map.rep _ _ (@locals p)); idtac x; fail
      end.
      *)

      case TODO_sam.
    + subst FL.
      assert (Forall valid_FlatImp_var binds) as A. {
        eapply Forall_impl; [|eassumption].
        apply TODO_sam_valid_register_to_valid_FlatImp_var.
      }
      match goal with
      | H: map.only_differ (map.put (map.put _ _ _) _ ?v) _ ?m2 |- map.get ?m2 _ = Some ?v' =>
        rename H into D; clear -D h A;
        replace v with v' in D by solve_word_eq word_ok
      end.
      assert (~ PropSet.elem_of RegisterNames.sp (PropSet.of_list binds)). {
        clear -A. cbv -[List.In].
        intro C.
        eapply Forall_forall in A. 2: exact C.
        cbv in A. intuition congruence.
      }
      (* TODO map_solver should work directly here *)
      preprocess_impl locals_ok true.
      change Z with Register in *.
      map_solver locals_ok.
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
      assert (Datatypes.length retvs = Datatypes.length binds). {
        symmetry. eapply map.getmany_of_list_length. eassumption.
      }
      (* PARAMRECORDS *)
      change Syntax.varname with Register in *.
      subst FL new_ra. simpl_addrs.
      split. { ring. (* faster than lia *) }
      wseplog_pre word_ok.
      rewrite !@length_save_regs in *.
      pose proof functions_expose as P.
      match goal with
      | H: map.get e_impl_full _ = Some _ |- _ => specialize P with (2 := H)
      end.
      specialize P with (1 := GetPos).
      specialize (P program_base funnames).
      auto_specialize.
      apply iff1ToEq in P.
      rewrite P. clear P.
      unfold program, compile_function.
      rewr (fun t => match t with
           | context [ array ?PT ?SZ ?start (?xs ++ ?ys) ] =>
             constr:(iff1ToEq (array_append' PT SZ xs ys start))
           | context [ array ?PT ?SZ ?start (?x :: ?xs) ] =>
             constr:(iff1ToEq (array_cons PT SZ x xs start))
           end) in |-*.
      (* PARAMRECORDS *)
      change (@Syntax.varname (mk_Syntax_params (@def_params p))) with Z in *.
      repeat match goal with
             | |- context [@array ?Wi ?Wo ?V ?M ?T ?E ?SZ ?A nil] =>
               change (@array Wi Wo V M T E SZ A nil) with (emp True)
             end.
      rewrite! length_save_regs. rewrite! length_load_regs. (* <- needs to be before simpl_addrs *)
      simpl_addrs.
      wcancel.
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
      progress unfold Memory.load, Memory.load_Z in *. simp.
      subst_load_bytes_for_eq.
      assert (x <> RegisterNames.sp). {
        apply_in_hyps TODO_sam_valid_register_to_valid_FlatImp_var.
        unfold valid_FlatImp_var, RegisterNames.sp in *.
        blia.
      }
      run1det. clear H0. (* <-- TODO this should not be needed *) run1done.

    - (* SStore *)
      simpl_MetricRiscvMachine_get_set.
      unfold Memory.store, Memory.store_Z in *.
      change Memory.store_bytes with Platform.Memory.store_bytes in *.
      match goal with
      | H: Platform.Memory.store_bytes _ _ _ _ = _ |- _ =>
        unshelve epose proof (@store_bytes_frame _ _ _ _ _ _ _ _ _ H _) as P; cycle 2
      end.
      1: ecancel_assumption.
      destruct P as (finalML & P1 & P2).
      run1det. run1done.

    - (* SLit *)
      eapply compile_lit_correct_full.
      + sidecondition.
      + unfold compile_stmt. simpl. ecancel_assumption.
      + sidecondition.
      + simpl.
        assert (x <> RegisterNames.sp). {
          apply_in_hyps TODO_sam_valid_register_to_valid_FlatImp_var.
          unfold valid_FlatImp_var, RegisterNames.sp in *.
          blia.
        }
        run1done.

    - (* SOp *)
      assert (x <> RegisterNames.sp). {
        apply_in_hyps TODO_sam_valid_register_to_valid_FlatImp_var.
        unfold valid_FlatImp_var, RegisterNames.sp in *.
        blia.
      }
      match goal with
      | o: Syntax.bopname.bopname |- _ => destruct o
      end;
      simpl in *; run1det;
      rewrite ?word.sru_ignores_hibits,
              ?word.slu_ignores_hibits,
              ?word.srs_ignores_hibits,
              ?word.mulhuu_simpl,
              ?word.divu0_simpl,
              ?word.modu0_simpl;
      try solve [run1done].
      (* bopname.eq requires two instructions *)
      run1det. run1done.
      rewrite reduce_eq_to_sub_and_lt.
      rewrite map.put_put_same.
      map_solver locals_ok.

    - (* SSet *)
      assert (x <> RegisterNames.sp). {
        apply_in_hyps TODO_sam_valid_register_to_valid_FlatImp_var.
        unfold valid_FlatImp_var, RegisterNames.sp in *.
        blia.
      }
      run1det. run1done.

    - (* SIf/Then *)
      (* execute branch instruction, which will not jump *)
      eapply runsTo_det_step; simpl in *; subst.
      + simulate'. simpl_MetricRiscvMachine_get_set.
        destruct cond; [destruct op | ];
          simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity.
      + eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
        * (* use IH for then-branch *)
          eapply IHexec with (g := {| p_sp := _; |}) (pos := (pos + 4)%Z);
            after_IH;
            try safe_sidecond.
          all: try safe_sidecond.
          all: try safe_sidecond.
        * (* jump over else-branch *)
          simpl. intros. destruct_RiscvMachine middle. simp. subst.
          run1det. run1done.

    - (* SIf/Else *)
      (* execute branch instruction, which will jump over then-branch *)
      eapply runsTo_det_step; simpl in *; subst.
      + simulate'.
        destruct cond; [destruct op | ];
          simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity.
      + eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
        * (* use IH for else-branch *)
          eapply IHexec with (g := {| p_sp := _; |});
            after_IH;
            try safe_sidecond.
            all: try safe_sidecond.
        * (* at end of else-branch, i.e. also at end of if-then-else, just prove that
             computed post satisfies required post *)
          simpl. intros. destruct_RiscvMachine middle. simp. subst. run1done.

    - (* SLoop *)
      on hyp[(stmt_not_too_big body1); runsTo] do (fun H => rename H into IH1).
      on hyp[(stmt_not_too_big body2); runsTo] do (fun H => rename H into IH2).
      on hyp[(stmt_not_too_big (SLoop body1 cond body2)); runsTo] do (fun H => rename H into IH12).
      eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
      + (* 1st application of IH: part 1 of loop body *)
          eapply IH1 with (g := {| p_sp := _; |});
            after_IH;
            try safe_sidecond.
          all: try safe_sidecond.
      + simpl in *. simpl. intros. destruct_RiscvMachine middle.
        match goal with
        | H: exists _ _ _ _, _ |- _ => destruct H as [ tH' [ mH' [ lH' [ mcH' H ] ] ] ]
        end.
        simp. subst.
        destruct (@eval_bcond (@Semantics_params p) lH' cond) as [condB|] eqn: E.
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
              eapply IH2 with (g := {| p_sp := _; |});
                after_IH;
                try safe_sidecond.
              all: try safe_sidecond.
              1: eassumption.
              all: try safe_sidecond.
              all: try safe_sidecond.
              match goal with
              | H: regs_initialized _ |- _ => move H at bottom
              end.
              case TODO_sam. (* TODO add regs_initialized to goodMachine *)
            - simpl in *. simpl. intros. destruct_RiscvMachine middle. simp. subst.
              (* jump back to beginning of loop: *)
              run1det.
              eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
              + (* 3rd application of IH: run the whole loop again *)
                eapply IH12 with (g := {| p_sp := _; |});
                  after_IH.
                all: try safe_sidecond.
                1: eassumption.
                9: {
                  wseplog_pre word_ok.
                  wcancel. simpl. (* TODO add array-nil to rewrite steps *)
                  wcancel.
                }
                all: try safe_sidecond.
                1: constructor; congruence.
                case TODO_sam. (* TODO add regs_initialized to goodMachine *)
              + (* at end of loop, just prove that computed post satisfies required post *)
                simpl. intros. destruct_RiscvMachine middle. simp. subst.
                run1done. }
        * (* false: done, jump over body2 *)
          eapply runsTo_det_step; simpl in *; subst.
          { simulate'.
            destruct cond; [destruct op | ];
              simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity. }
          { simpl in *. run1done. cbn. wcancel. }

    - (* SSeq *)
      on hyp[(stmt_not_too_big s1); runsTo] do (fun H => rename H into IH1).
      on hyp[(stmt_not_too_big s2); runsTo] do (fun H => rename H into IH2).
      eapply runsTo_trans.
      + eapply IH1 with (g := {| p_sp := _; |});
          after_IH;
          try safe_sidecond.
        all: try safe_sidecond.
      + simpl. intros. destruct_RiscvMachine middle. simp. subst.
        eapply runsTo_trans.
        * eapply IH2 with (g := {| p_sp := _; |});
            after_IH;
            try safe_sidecond.
          1: eassumption.
          all: try safe_sidecond.
          all: try safe_sidecond.
          case TODO_sam. (* TODO add regs_initialized to goodMachine *)
        * simpl. intros. destruct_RiscvMachine middle. simp. subst. run1done.

    - (* SSkip *)
      run1done.

    Grab Existential Variables.
    all: try (unfold env; simpl; eapply funname_env_ok).
    all: repeat (exact Z0 || assumption || constructor).
  Qed. (* <-- takes a while *)

End Proofs.
