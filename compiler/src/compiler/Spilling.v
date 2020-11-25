Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Map.SeparationLogic.
Require Import compiler.FlatImp.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.simpl_rewrite.
Require Import coqutil.Datatypes.PropSet.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.Utility.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.Simp.
Require Import compiler.Simulation.
Require Import compiler.SeparationLogic.
Require Import compiler.SpillingMapGoals.
Require Import bedrock2.MetricLogging.

Open Scope Z_scope.

Ltac specialize_rec H :=
  lazymatch type of H with
  | ?P -> ?Q => let F := fresh in assert P as F; [clear H|specialize (H F); clear F; specialize_rec H]
  | forall (x: ?T), _ => let n := fresh x in evar (n: T); specialize (H n); subst n; specialize_rec H
  | _ => idtac
  end.

Tactic Notation "spec" constr(t) "as" ident(H) := pose proof t as H; specialize_rec H.

Lemma sumbool_of_BoolSpec: forall {P Q: Prop} {b: bool},
    BoolSpec P Q b -> {P} + {Q}.
Proof.
  intros. destruct b.
  - left. inversion H. assumption.
  - right. inversion H. assumption.
Defined.

Lemma sumbool_of_EqDecider{T: Type}{d: T -> T -> bool}:
  EqDecider d ->
  forall x y: T, {x = y} + {x <> y}.
Proof. intros. eapply sumbool_of_BoolSpec. apply H. Qed.

Module map.
  Section MAP.
    Context {key value} {map : map.map key value}.
    Context {ok : map.ok map} {key_eqb: key -> key -> bool} {key_eq_dec : EqDecider key_eqb}.

    (* to get stronger guarantees such as indexing into vs, we'd need NoDup *)
    Lemma putmany_of_list_zip_get: forall (ks: list key) (vs: list value) m0 m k,
        map.putmany_of_list_zip ks vs m0 = Some m ->
        In k ks ->
        map.get m k <> None.
    Proof.
      induction ks as [|k ks]; intros.
      - simpl in H0. destruct H0.
      - simpl in H0. destruct H0.
        + subst k0. cbn in H. simp. intro C.
          eapply map.putmany_of_list_zip_to_putmany in H.
          destruct H as (M & A & B). subst m.
          rewrite map.get_putmany_dec in C. rewrite map.get_put_same in C.
          destruct_one_match_hyp; discriminate.
        + cbn in H. simp. eapply IHks; eauto.
    Qed.

    Lemma split_remove_put: forall m m1 m2 k v,
        map.split m m1 m2 ->
        map.get m k = Some v ->
        map.split m (map.remove m1 k) (map.put m2 k v).
    Proof.
      intros.
      destruct (map.get_split k _ _ _ H) as [(A & B) | (A & B)].
      - eapply map.split_put_l2r.
        + apply map.get_remove_same.
        + replace (map.put (map.remove m1 k) k v) with m1. 1: assumption.
          apply map.map_ext.
          intro x.
          rewrite map.get_put_dec.
          destruct_one_match.
          * subst x. congruence.
          * rewrite map.get_remove_diff by congruence. reflexivity.
      - replace (map.remove m1 k) with m1. 2: {
          eapply map.map_ext. intro x. rewrite map.get_remove_dec.
          destruct_one_match.
          - subst x. assumption.
          - reflexivity.
        }
        replace (map.put m2 k v) with m2. 2: {
          apply map.map_ext. intro x. rewrite map.get_put_dec.
          destruct_one_match.
          - subst x. congruence.
          - reflexivity.
        }
        assumption.
    Qed.

    Lemma getmany_of_list_to_split: forall m (ks: list key) (vs: list value),
        map.getmany_of_list m ks = Some vs ->
        exists mrest mks, map.of_list_zip ks vs = Some mks /\ map.split m mrest mks.
    Proof.
      induction ks as [|k ks]; intros; destruct vs as [|v vs].
      - do 2 eexists. split. 1: reflexivity. unfold map.split. rewrite map.putmany_empty_r.
        split. 1: reflexivity. apply map.disjoint_empty_r.
      - discriminate.
      - cbn in H. simp. destruct_one_match_hyp; discriminate.
      - cbn in H. simp. specialize (IHks _ E0). simp. cbn.
        unfold map.of_list_zip in *.
        exists (map.remove mrest k), (map.put mks k v). split.
        + destr (map.putmany_of_list_zip ks vs (map.put map.empty k v)). 2: {
            pose proof map.putmany_of_list_zip_sameLength _ _ _ _ IHksp0 as C.
            eapply map.sameLength_putmany_of_list in C. destruct C as [a C].
            rewrite E1 in C. discriminate.
          }
          f_equal.
          eapply map.map_ext.
          intro x.
          eapply map.putmany_of_list_zip_to_putmany in E1.
          destruct E1 as (mks' & F & G).
          subst r.
          rewrite IHksp0 in F. apply Option.eq_of_eq_Some in F. subst mks'.
          rewrite map.get_putmany_dec.
          rewrite !map.get_put_dec.
          rewrite map.get_empty.
          destr (key_eqb k x). 2: destruct_one_match; reflexivity.
          subst x.
          destruct_one_match. 2: reflexivity.
          unfold map.split in IHksp1. simp.
          rewrite map.get_putmany_dec in E.
          rewrite E1 in E.
          assumption.
        + eapply split_remove_put; assumption.
    Qed.
  End MAP.
End map.

Section MoreSepLog.
  Context {key value} {map : map.map key value}.
  Context {ok : map.ok map} {key_eqb: key -> key -> bool} {key_eq_dec : EqDecider key_eqb}.

  Lemma subst_split: forall (m m1 m2 M: map) (R: map -> Prop),
      map.split m m1 m2 ->
      (eq m * R)%sep M ->
      (eq m1 * eq m2 * R)%sep M.
  Proof.
    (* FIRSTORDER? *)
    intros.
    unfold map.split in H. simp.
    use_sep_assumption.
    cancel.
    cbn [seps].
    intro m. unfold sep, map.split. split; intros.
    - subst. eauto 10.
    - simp. reflexivity.
  Qed.
End MoreSepLog.

Section Spilling.

  Notation stmt := (stmt Z).

  Definition zero := 0.
  Definition ra := 1.
  Definition sp := 2.
  Definition tmp1 := 3.
  Definition tmp2 := 4.
  Definition fp := 5. (* returned by stackalloc, always a constant away from sp: a wasted register *)
  Definition regvar0 := 6.

  (* TODO: storing value returned by stackalloc into a register is always a wasted register,
     because it's constant away from the stackpointer

     integrate spilling into FlatToRiscv?

     Or make StackImp language with same syntax as FlatImp but with a stack in the memory and
     which shares the register file among function calls? *)

  (* Definition needs_spilling: Z -> bool := Z.leb 32. *)

  Context {W: Utility.Words} {mem: map.map word byte} {mem_ok: map.ok mem}.

  Definition stack_loc(r: Z): option Z :=
    if Z.leb 32 r then Some ((r - 32) * bytes_per_word) else None.

  Definition arg_reg1(r: Z): Z := if Z.leb 32 r then tmp1 else r.
  Definition arg_reg2(r: Z): Z := if Z.leb 32 r then tmp2 else r.
  Definition res_reg(r: Z): Z := if Z.leb 32 r then tmp1 else r.

  Definition load_arg_reg1(r: Z): stmt :=
    match stack_loc r with
    | Some o => SLoad Syntax.access_size.word tmp1 fp o
    | None => SSkip
    end.

  Definition load_arg_reg2(r: Z): stmt :=
    match stack_loc r with
    | Some o => SLoad Syntax.access_size.word tmp2 fp o
    | None => SSkip
    end.

  Definition save_res_reg(r: Z): stmt :=
    match stack_loc r with
    | Some o => SStore Syntax.access_size.word fp tmp1 o
    | None => SSkip
    end.

  Notation "s1 ;; s2" := (SSeq s1 s2) (right associativity, at level 100).

  Definition prepare_bcond(c: bcond Z): stmt :=
    match c with
    | CondBinary _ x y => load_arg_reg1 x;; load_arg_reg2 y
    | CondNez x => load_arg_reg1 x
    end.

  Definition spill_bcond(c: bcond Z): bcond Z :=
    match c with
    | CondBinary op x y => CondBinary op (arg_reg1 x) (arg_reg2 y)
    | CondNez x => CondNez (arg_reg1 x)
    end.

  Fixpoint spill_stmt(s: stmt): stmt :=
    match s with
    | SLoad sz x y o =>
      load_arg_reg1 y;;
      SLoad sz (res_reg x) (arg_reg1 y) o;;
      save_res_reg x
    | SStore sz x y o =>
      load_arg_reg1 x;; load_arg_reg2 y;;
      SStore sz (arg_reg1 x) (arg_reg2 y) o
    | SInlinetable sz x t i =>
      load_arg_reg1 i;;
      SInlinetable sz (res_reg x) t (arg_reg1 i);;
      save_res_reg x
    | SStackalloc x n body =>
      SStackalloc (res_reg x) n (save_res_reg x;; spill_stmt body)
    | SLit x n =>
      SLit (res_reg x) n;;
      save_res_reg x
    | SOp x op y z =>
      load_arg_reg1 y;; load_arg_reg2 z;;
      SOp (res_reg x) op (arg_reg1 y) (arg_reg2 z);;
      save_res_reg x
    | SSet x y => (* TODO could be optimized if exactly one is on the stack *)
      load_arg_reg1 y;;
      SSet (res_reg x) (arg_reg1 y);;
      save_res_reg x
    | SIf c thn els =>
      prepare_bcond c;;
      SIf (spill_bcond c) (spill_stmt thn) (spill_stmt els)
    | SLoop s1 c s2 =>
      SLoop (spill_stmt s1;; prepare_bcond c) (spill_bcond c) (spill_stmt s2)
    | SSeq s1 s2 => SSeq (spill_stmt s1) (spill_stmt s2)
    | SSkip => SSkip
    (* Note: these two are only correct if argvars and resvars all are registers! *)
    | SCall argvars f resvars => SCall argvars f resvars
    | SInteract argvars f resvars => SInteract argvars f resvars
    end.

  Definition valid_vars_bcond(c: bcond Z): Prop :=
    match c with
    | CondBinary _ x y => fp < x /\ fp < y
    | CondNez x => fp < x
    end.

  (*
  Fixpoint calls_use_registers(s: stmt): bool :=
    match s with
    | SLoad _ _ _ _ | SStore _ _ _ _ | SLit _ _ | SOp _ _ _ _ | SSet _ _ | SSkip => true
    | SStackalloc x n body => calls_use_registers body
    | SIf _ s1 s2 | SLoop s1 _ s2 | SSeq s1 s2 => calls_use_registers s1 && calls_use_registers s2
    | SCall argvars _ resvars | SInteract argvars _ resvars =>
      List.forallb (Z.gtb 32) argvars && List.forallb (Z.gtb 32) resvars
    end.
   *)

  Definition max_var_bcond(c: bcond Z): Z :=
    match c with
    | CondBinary _ x y => Z.max x y
    | CondNez x => x
    end.

  Fixpoint max_var(s: stmt): Z :=
    match s with
    | SLoad _ x y _ | SStore _ x y _ | SInlinetable _ x _ y | SSet x y => Z.max x y
    | SStackalloc x n body => Z.max x (max_var body)
    | SLit x _ => x
    | SOp x _ y z => Z.max x (Z.max y z)
    | SIf c s1 s2 | SLoop s1 c s2 => Z.max (max_var_bcond c) (Z.max (max_var s1) (max_var s2))
    | SSeq s1 s2 => Z.max (max_var s1) (max_var s2)
    | SSkip => 0
    (* Variables involved in function calls are not spilled, so we can ignore them *)
    | SCall argvars f resvars | SInteract argvars f resvars => 0
    end.

  Definition spill_fbody(s: stmt): stmt :=
    SStackalloc fp (bytes_per_word * (max_var s - 32)) (spill_stmt s).

  Context {locals: map.map Z word}.
  Context {localsOk: map.ok locals}.
  Context {env: map.map String.string (list Z * list Z * stmt)}.
  Context (ext_spec:  list (mem * String.string * list word * (mem * list word)) ->
                      mem -> String.string -> list word -> (mem -> list word -> Prop) -> Prop).

  Instance semanticsParams: FlatImp.parameters Z. refine ({|
    FlatImp.varname_eqb := Z.eqb;
    FlatImp.locals := locals;
    FlatImp.ext_spec := ext_spec;
  |}).
  Defined.

  Definition valid_vars_src(maxvar: Z): stmt -> Prop :=
    Forall_vars_stmt (fun x => fp < x <= maxvar) (fun x => fp < x < 32).

  Definition valid_vars_tgt: stmt -> Prop :=
    Forall_vars_stmt (fun x => sp < x <= 32) (fun x => sp < x < 32).

  Lemma spill_stmt_valid_vars: forall s m,
      max_var s <= m ->
      valid_vars_src m s ->
      valid_vars_tgt (spill_stmt s).
  Proof.
    (* Wihtout the clear, firstorder becomes very slow COQBUG https://github.com/coq/coq/issues/11352.
       Not using firstorder though because there's something higher order here: *)
    clear mem mem_ok locals localsOk env ext_spec.
    assert (forall vars, Forall (fun x : Z => 5 < x < 32) vars -> Forall (fun x : Z => 2 < x < 32) vars). {
      intros. eapply Forall_impl. 2: eassumption. simpl. blia.
    }
    unfold valid_vars_src, valid_vars_tgt.
    induction s; simpl; intros;
      repeat match goal with
             | c: bcond Z |- _ => destr c
             | |- context[Z.leb ?x ?y] => destr (Z.leb x y)
             | |- _ => progress simpl
             | |- _ => progress unfold tmp1, tmp2, sp, fp, res_reg, arg_reg1, arg_reg2, res_reg,
                         spill_bcond, max_var_bcond, ForallVars_bcond, prepare_bcond,
                         load_arg_reg1, load_arg_reg2, save_res_reg, stack_loc in *
             end;
      try blia;
      simp;
      repeat match goal with
      | IH: _, H: Forall_vars_stmt _ _ _ |- _ =>
        specialize IH with (2 := H);
        match type of IH with
        | ?P -> _ => let A := fresh in assert P as A by blia; specialize (IH A); clear A
        end
      end;
      eauto;
      intuition try blia.
  Qed.

  Definition related(maxvar: Z)(frame: mem -> Prop)(done: bool)
             (t1: trace)(m1: mem)(l1: locals)(mc1: MetricLog)
             (t2: trace)(m2: mem)(l2: locals)(mc2: MetricLog): Prop :=
      exists fpval tmp1val tmp2val lStack lRegs stackwords,
        t1 = t2 /\
        (eq m1 * word_array fpval stackwords * frame)%sep m2 /\
        (forall x v, map.get lRegs x = Some v -> fp < x < 32) /\
        (forall x v, map.get lStack x = Some v -> 32 <= x <= maxvar) /\
        (eq lRegs * eq lStack)%sep l1 /\
        (eq lRegs * ptsto tmp1 tmp1val * ptsto tmp2 tmp2val * ptsto fp fpval)%sep l2 /\
        forall r, 32 <= r <= maxvar -> forall v, map.get lStack r = Some v ->
           nth_error stackwords (Z.to_nat (r - 32)) = Some v.

  Definition envs_related(e1 e2: env): Prop :=
    forall f argvars resvars body1,
      map.get e1 f = Some (argvars, resvars, body1) ->
      map.get e2 f = Some (argvars, resvars, spill_fbody body1).

  Lemma seq_cps: forall e s1 s2 t m l mc post,
      exec e s1 t m l mc (fun t' m' l' mc' => exec e s2 t' m' l' mc' post) ->
      exec e (SSeq s1 s2) t m l mc post.
  Proof.
    intros. eapply exec.seq. 1: eassumption. simpl. clear. auto.
  Qed.

  Lemma sep_def: forall {m: mem} {P Q: mem -> Prop},
      (P * Q)%sep m ->
      exists m1 m2, map.split m m1 m2 /\ P m1 /\ Q m2.
  Proof. unfold sep. intros *. apply id. Qed.

  Lemma spilling_correct (e e1 e2 : env) (Ev : envs_related e1 e2)
        (s1 : stmt)
  (t1 : trace)
  (m1 : mem)
  (l1 : locals)
  (mc1 : MetricLog)
  (post : trace -> mem -> locals -> MetricLog -> Prop):
  exec e1 s1 t1 m1 l1 mc1 post ->
  forall (frame : mem -> Prop) (maxvar : Z),
  valid_vars_src maxvar s1 ->
  forall (t2 : trace) (m2 : mem) (l2 : locals) (mc2 : MetricLog),
  related maxvar frame false t1 m1 l1 mc1 t2 m2 l2 mc2 ->
  exec e2 (spill_stmt s1) t2 m2 l2 mc2
    (fun (t2' : trace) (m2' : mem) (l2' : locals) (mc2' : MetricLog) =>
       exists t1' m1' l1' mc1',
         related maxvar frame false t1' m1' l1' mc1' t2' m2' l2' mc2' /\
         post t1' m1' l1' mc1').
  Proof.
    unfold related. induction 1; intros; simp; subst.
    - (* exec.interact *)
      spec (subst_split (ok := mem_ok) m) as A.
      1: eassumption. 1: ecancel_assumption.
      edestruct (@sep_def m2 (eq mGive)) as (mGive' & mKeepL & B & ? & C).
      1: simpl. (* PARAMRECORDS *) 1: ecancel_assumption.
      subst mGive'.
      simpl in H3. destruct H3 as [FR FA].
      eapply map.getmany_of_list_to_split in H0.
      destruct H0 as (l1rest & largs & F1 & S1).
      (*unfold sep in H4p3. destruct H4p3 as (lRegs' & lStack' & S2 & ? & ?). subst lRegs' lStack'.*)
      rename H4p3 into S2.
      move S1 before S2. move FA after S2. move F1 before S1.

      (* largs is contained in lRegs by FA, H4p0, H4p1
         need interaction between map.dom and sep

      eapply @exec.interact with (mGive := mGive).
      + eapply map.split_comm. exact B.
      +

      + erewrite map__getmany_of_list_shrink. 2: eassumption. 2: {
          eapply Forall_impl. 2: eassumption.
          clear -localsOk. unfold fp, tmp1, tmp2. intros.
          rewrite ?map.get_put_dec.
          rewrite ?(proj2 (Z.eqb_neq _ _ )) by blia.
          apply map.get_empty.
        }
        erewrite <- map__getmany_of_list_shrink; [eassumption..|].
        eapply Forall_impl. 2: eassumption.
        simpl.
        intros. unfold map__dom_in in *.
        destr (map.get lStack a). 2: reflexivity.
        match goal with
        | H: forall _, _ |- _ => specialize H with (1 := E)
        end.
        blia.
      + eassumption.
      + intros.
        match goal with
        | H: context[outcome], A: context[outcome] |- _ =>
          specialize H with (1 := A); move H at bottom
        end.
        simp.
        pose proof H2l as P.
        eapply map__putmany_of_list_zip_split in P. 2: eassumption. 2: {
          eapply Forall_impl. 2: eassumption.
          simpl.
          intros. unfold map__dom_in in *.
          destr (map.get lStack a). 2: reflexivity.
          match goal with
          | H: forall _, _ |- _ => specialize H with (1 := E)
          end.
          blia.
        }
        simp.
        eapply map__putmany_of_list_zip_grow with (l := l2) in Pr. 2: eassumption. 2: {
          eapply Forall_impl. 2: eassumption.
          clear -localsOk. unfold fp, tmp1, tmp2. intros.
          rewrite ?map.get_put_dec.
          rewrite ?(proj2 (Z.eqb_neq _ _ )) by blia.
          apply map.get_empty.
        }
        destruct Pr as (l2' & ? & ?).
        eexists. split. 1: eassumption.
        intros.
        repeat match goal with
               | |- exists (_: FlatImp.SimState _), _ => refine (ex_intro _ (_, _, _, _) _)
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               end.
        9: eapply H2r.
        1: reflexivity.
        8: eapply split_interact_shrink; eassumption.
        1: eapply split_interact_assoc; eassumption.
        1: eassumption.
        5: eassumption.
        4: eassumption.
        3: eassumption.
        2: eassumption.
        assert (map__dom_in (map.put (map.put (map.put map.empty fp fpval) tmp2 tmp2val) tmp1 tmp1val)
                            (fun x => x = fp \/ x = tmp2 \/ x = tmp1)) as A. {
          unfold map__dom_in. clear -localsOk. intros. rewrite ?map.get_put_dec in H.
          repeat destruct_one_match_hyp; subst; auto.
          rewrite map.get_empty in H. discriminate.
        }
        pose proof map__split_dom_in _ _ _ _ _ Rrrrrrrl Rrrrl A as B. simpl in B.
        pose proof map__putmany_of_list_zip_dom_in as C.
        specialize C with (1 := H4) (2 := B). simpl in C.
        apply map__split_dom_spec in H2. simp.
        assert (subset (of_list resvars) (fun x : Z => fp < x < 32)) as Vl' by admit.
        assert (subset (of_list argvars) (fun x : Z => fp < x < 32)) as Vr' by admit.
        change (map__dom_in l2' (union (fun x : Z => (fp < x < 32 \/ x = fp \/ x = tmp2 \/ x = tmp1)) (of_list resvars))) in C.
        assert (subset (map__dom l2') (union (fun x : Z => (fp < x < 32 \/ x = fp \/ x = tmp2 \/ x = tmp1)) (of_list resvars))) as C' by admit.
        clear - H2l0 H2r0 Vl' C'.
        unfold fp, tmp1, tmp2 in *.
        replace (map__dom (map.put (map.put (map.put map.empty 5 fpval) 4 tmp2val) 3 tmp1val)) with
            (fun x => x = 5 \/ x = 4 \/ x = 3) in * by admit.
        assert (subset (map__dom l1') (fun x : Z => fp < x < 32)). {
          set_solver_generic Z; try blia.
        }
        admit. (* ok, but TODO use map__dom instead of map__dom_in *)

      + eapply mem_eq_trans. 1: eassumption.
        eapply mem_eq_trans.
        * eapply mem_eq_rewrite. 1: exact H.
          match goal with
          | |- ?L1 \+/ ?L2 \+/ ?L3 == ?R1 \+/ ?R2 =>
            change (map.dus [L3; L2; L1] == map.dus [R2; R1])
          end.
          cancel_at_indices 2%nat 1%nat. 1: reflexivity.
          cbv [map.dus].
          eapply mem_eq_refl.
          eapply mem_eq_trans. 1: exact H5p0.
          match goal with
          | |- ?L1 \+/ ?L2 \+/ ?L3 == ?R1 \+/ ?R2 =>
            change (map.dus [L3; L2; L1] == map.dus [R2; R1])
          end.
*)
  Abort.

End Spilling.
