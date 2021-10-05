Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Map.SeparationLogic.
Require Import compiler.FlatImp.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Datatypes.PropSet.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.Utility.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.Simp.
Require Import compiler.Registers.
Require Import compiler.SeparationLogic.
Require Import compiler.SpillingMapGoals.
Require Import bedrock2.MetricLogging.
Require Import compiler.FlatImpConstraints.
Require Import coqutil.Tactics.autoforward.
Existing Class autoforward.

Open Scope Z_scope.


Module map.
  Section WithMap. Local Set Default Proof Using "All".
    Context {key value} {map : map.map key value} {ok : map.ok map}.
    Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.
    Local Hint Mode map.map - - : typeclass_instances.

    Lemma put_put_diff: forall m k1 k2 v1 v2,
        k1 <> k2 ->
        map.put (map.put m k1 v1) k2 v2 = map.put (map.put m k2 v2) k1 v1.
    Proof.
      intros. apply map.map_ext. intros.
      rewrite ?map.get_put_dec. destr (key_eqb k1 k); destr (key_eqb k2 k); congruence.
    Qed.

    Lemma getmany_of_list_cons: forall m k v ks vs,
        map.get m k = Some v ->
        map.getmany_of_list m ks = Some vs ->
        map.getmany_of_list m (k :: ks) = Some (v :: vs).
    Proof.
      intros. unfold map.getmany_of_list in *. cbn. rewrite H. rewrite H0. reflexivity.
    Qed.

    Lemma invert_getmany_of_list_cons: forall m k v ks vs,
        map.getmany_of_list m (k :: ks) = Some (v :: vs) ->
        map.get m k = Some v /\ map.getmany_of_list m ks = Some vs.
    Proof.
      intros. unfold map.getmany_of_list in *. cbn in *.
      destr (map.get m k). 2: discriminate.
      destr (List.option_all (List.map (map.get m) ks)). 2: discriminate.
      inversion H. subst. auto.
    Qed.

    Lemma getmany_of_list_put_diff: forall ks vs k v m,
        ~ In k ks ->
        map.getmany_of_list m ks = Some vs ->
        map.getmany_of_list (map.put m k v) ks = Some vs.
    Proof.
      induction ks; simpl; intros; destruct vs as [|v0 vs].
      - reflexivity.
      - discriminate.
      - cbn in H0.
        destr (map.get m a); try discriminate.
        destr (List.option_all (List.map (map.get m) ks)); try discriminate.
      - eapply invert_getmany_of_list_cons in H0. destruct H0.
        assert (a <> k) as NE. {
          intro C. apply H. auto.
        }
        assert (~ In k ks) as NI. {
          intro C. apply H. auto.
        }
        clear H.
        eapply getmany_of_list_cons.
        + rewrite map.get_put_diff by assumption. assumption.
        + eauto.
    Qed.

    Lemma of_list_zip_cons_keys: forall k ks vals m,
        map.of_list_zip (k :: ks) vals = Some m ->
        ~ In k ks ->
        exists v vs ksvs, vals = v :: vs /\ m = map.put ksvs k v /\
                          map.of_list_zip ks vs = Some ksvs.
    Proof.
      intros. destruct vals as [|v vs]. 1: discriminate.
      cbn in H.
      eapply map.putmany_of_list_zip_to_putmany in H.
      destruct H as (r & E & ?). subst. do 3 eexists.
      split; [reflexivity|].
      split; [|exact E].
      apply map.map_ext. intros.
      rewrite map.get_putmany_dec, ?map.get_put_dec.
      destr (key_eqb k k0).
      - subst. erewrite map.not_in_of_list_zip_to_get_None by eassumption. reflexivity.
      - rewrite map.get_empty. destr (map.get r k0); reflexivity.
    Qed.

    Lemma putmany_of_list_zip_cons_put: forall ks k v vs m0 m,
        ~ In k ks ->
        map.putmany_of_list_zip ks vs m0 = Some m ->
        map.putmany_of_list_zip (k :: ks) (v :: vs) m0 = Some (map.put m k v).
    Proof.
      induction ks; simpl; intros; destruct vs as [|v0 vs]; try discriminate.
      - congruence.
      - assert (a <> k) by intuition congruence.
        assert (~ In k ks) by intuition congruence.
        rewrite put_put_diff by congruence.
        eapply IHks; eassumption.
    Qed.

    Lemma of_list_zip_cons_put: forall k ks v vs m,
        ~ In k ks ->
        map.of_list_zip ks vs = Some m ->
        map.of_list_zip (k :: ks) (v :: vs) = Some (map.put m k v).
    Proof. intros. eapply putmany_of_list_zip_cons_put; eassumption. Qed.

    Global Instance of_list_zip_nil_keys: forall vs m,
        autoforward (map.of_list_zip nil vs = Some m)
                    (vs = nil /\ m = map.empty).
    Proof. intros vs m H. cbn in H. destruct vs. 2: discriminate. split; congruence. Qed.

    Global Instance of_list_zip_nil_values: forall ks m,
        autoforward (map.of_list_zip nil ks = Some m)
                    (ks = nil /\ m = map.empty).
    Proof. intros ks m H. cbn in H. destruct ks. 2: discriminate. split; congruence. Qed.

  End WithMap.
End map.

Section SepLog.
  Context {key value} {map : map.map key value} {ok : map.ok map}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.
  Local Hint Mode map.map - - : typeclass_instances.

  Lemma sep_eq_empty_l: forall R, (eq map.empty * R)%sep = R.
  Proof.
    intros. eapply iff1ToEq.
    unfold iff1, sep, map.split. split; intros.
    - destruct H as (? & ? & (? & ?) & ? & ?). subst. rewrite map.putmany_empty_l. assumption.
    - eauto 10 using map.putmany_empty_l, map.disjoint_empty_l.
  Qed.

  Lemma sep_eq_empty_r: forall R, (R * eq map.empty)%sep = R.
  Proof.
    intros. eapply iff1ToEq.
    unfold iff1, sep, map.split. split; intros.
    - destruct H as (? & ? & (? & ?) & ? & ?). subst. rewrite map.putmany_empty_r. assumption.
    - eauto 10 using map.putmany_empty_r, map.disjoint_empty_r.
  Qed.

  Lemma get_in_sep: forall lSmaller l k v R,
      map.get lSmaller k = Some v ->
      (eq lSmaller * R)%sep l ->
      map.get l k = Some v.
  Proof.
    intros. eapply sep_comm in H0.
    unfold sep, map.split in H0. simp.
    eapply map.get_putmany_right.
    assumption.
  Qed.

  Lemma eq_put_to_sep: forall m k v,
      map.get m k = None ->
      eq (map.put m k v) = sep (eq m) (ptsto k v).
    intros. eapply iff1ToEq.
    unfold iff1, ptsto, sep, map.split. split; intros.
    - subst. exists m, (map.put map.empty k v). ssplit; try reflexivity.
      + apply map.map_ext. intros.
        rewrite map.get_put_dec, map.get_putmany_dec, map.get_put_dec, map.get_empty.
        destr (key_eqb k k0); reflexivity.
      + unfold map.disjoint. intros. rewrite map.get_put_dec in H1.
        rewrite map.get_empty in H1. destr (key_eqb k k0); congruence.
    - destruct H0 as (? & ? & (? & ?) & ? & ?).  subst.
      apply map.map_ext. intros.
      rewrite map.get_put_dec, map.get_putmany_dec, map.get_put_dec, map.get_empty.
      destr (key_eqb k k0); reflexivity.
  Qed.

  Lemma ptsto_no_aliasing: forall l (Q: map -> Prop) R k v1 v2,
      Q l ->
      iff1 Q (ptsto k v1 * ptsto k v2 * R)%sep ->
      False.
  Proof.
    intros. seprewrite_in H0 H. apply sep_emp_r in H. apply proj1 in H.
    unfold sep, map.split, ptsto, map.disjoint in H.
    decompose [Logic.and ex] H. clear H. subst.
    specialize (H7 k). rewrite ?map.get_put_same in H7. eauto.
  Qed.

End SepLog.

Module List.
  Section WithA.
    Context {A: Type}.

    Lemma unfoldn_0: forall (f: A -> A) (start: A),
        List.unfoldn f 0 start = [].
    Proof. intros. reflexivity. Qed.

    Global Instance invert_Forall_cons: forall (a: A) (l: list A) (P: A -> Prop),
        autoforward (List.Forall P (a :: l))
                    (P a /\ List.Forall P l).
    Proof. intros a l P H. inversion H. subst. auto. Qed.

    Global Instance invert_NoDup_cons: forall (a: A) (l: list A),
        autoforward (NoDup (a :: l))
                    (~ In a l /\ NoDup l).
    Proof. intros a l H. inversion H. subst. auto. Qed.
  End WithA.
End List.

(* BEGIN MOVE fwd *)

Hint Rewrite
     @List.length_nil
     @List.unfoldn_0
  : fwd_rewrites.

(* One step of destructing "H: A0 /\ A1 /\ ... An" into "Hp0: A0, Hp1: A1, .. Hpn: An" *)
Ltac destr_and H :=
  (* Note: We reuse the name H, so we will only succeed if H was cleared
     (which might not be the case if H is a section variable), and enforcing that H is cleared
     is needed to avoid infinite looping *)
  let Hl := fresh H "p0" in destruct H as [Hl H];
  lazymatch type of H with
  | _ /\ _ => idtac (* not done yet *)
  | _ => let Hr := fresh H "p0" in rename H into Hr (* done, name last clause uniformly *)
  end.

(* fail on notations that we don't want to destruct *)
Ltac is_destructible_and T :=
  lazymatch T with
  | (Logic.and (N.le _ _) (N.le _ _)) => fail
  | (Logic.and (Z.le _ _) (Z.le _ _)) => fail
  | (Logic.and (Peano.le _ _) (Peano.le _ _)) => fail
  | (Logic.and (Pos.le _ _) (Pos.le _ _)) => fail
  | (Logic.and (N.le _ _) (N.lt _ _)) => fail
  | (Logic.and (Z.le _ _) (Z.lt _ _)) => fail
  | (Logic.and (Peano.le _ _) (Peano.lt _ _)) => fail
  | (Logic.and (Pos.le _ _) (Pos.lt _ _)) => fail
  | (Logic.and (N.lt _ _) (N.le _ _)) => fail
  | (Logic.and (Z.lt _ _) (Z.le _ _)) => fail
  | (Logic.and (Peano.lt _ _) (Peano.le _ _)) => fail
  | (Logic.and (Pos.lt _ _) (Pos.le _ _)) => fail
  | (Logic.and (N.lt _ _) (N.lt _ _)) => fail
  | (Logic.and (Z.lt _ _) (Z.lt _ _)) => fail
  | (Logic.and (Peano.lt _ _) (Peano.lt _ _)) => fail
  | (Logic.and (Pos.lt _ _) (Pos.lt _ _)) => fail
  | (Logic.and _ _) => idtac
  end.

Ltac autoforward_in_with_tc H :=
  let tmp := fresh H in
  rename H into tmp;
  let A := type of tmp in
  pose proof ((ltac:(typeclasses eauto with typeclass_instances) : autoforward A _) tmp) as H;
  move H after tmp;
  clear tmp.

Ltac x_neq_x H :=
  match type of H with
  | ?x <> ?x => exfalso; apply (H eq_refl)
  end.

Ltac fwd_step :=
  match goal with
  | H: ?T |- _ => is_destructible_and T; destr_and H
  | H: exists y, _ |- _ => let yf := fresh y in destruct H as [yf H]
  | H: ?x = ?x |- _ => clear H
  | H: ?LHS = ?RHS |- _ =>
    let h1 := head_of_app LHS in is_constructor h1;
    let h2 := head_of_app RHS in is_constructor h2;
    (* if not eq, H is a contradiction, but we don't want to change the number
       of open goals in this tactic *)
    constr_eq h1 h2;
    inversion H; clear H
  | H: context[match ?x with _ => _ end] |- _ => destr x; try (discriminate H || x_neq_x H); []
  | H: _ |- _ => autoforward_in_with_tc H
  | |- _ => progress subst
  | |- _ => progress autorewrite with fwd_rewrites in *
  end.

Ltac fwd := repeat fwd_step.

(* END MOVE fwd *)

Section Spilling.

  Notation stmt := (stmt Z).

  Definition zero := 0.
  Definition ra := 1.
  Definition sp := 2.
  Definition gp := 3. (* we don't use the global pointer *)
  Definition tp := 4. (* we don't use the thread pointer *)
  Definition fp := 5. (* returned by stackalloc, always a constant away from sp: a wasted register *)
  Definition a0 := 10. (* first argument register *)
  Definition a7 := 17. (* last argument register *)

  (* `i=1 \/ i=2`, we use the argument registers as temporaries for spilling *)
  Definition spill_tmp(i: Z) := 9 + i.

  (* TODO: storing value returned by stackalloc into a register is always a wasted register,
     because it's constant away from the stackpointer *)

  Context {width} {BW: Bitwidth width} {word: word.word width} {word_ok: word.ok word}.
  Context {mem: map.map word byte} {mem_ok: map.ok mem}.

  Definition stack_loc(r: Z): option Z :=
    if Z.leb 32 r then Some ((r - 32) * bytes_per_word) else None.

  (* argument/result registers for individual instructions (as opposed to for function calls) *)
  Definition iarg_reg(i r: Z): Z := if Z.leb 32 r then spill_tmp i else r.
  Definition ires_reg(r: Z): Z := if Z.leb 32 r then spill_tmp 1 else r.

  (* argument/result registers for function calls, `0 <= i < 8` *)
  Definition carg_reg(i: Z): Z := a0 + i.

  (* i needs to be 1 or 2, r any register > fp *)
  Definition load_iarg_reg(i r: Z): stmt :=
    match stack_loc r with
    | Some o => SLoad Syntax.access_size.word (9 + i) fp o
    | None => SSkip
    end.

  Definition save_ires_reg(r: Z): stmt :=
    match stack_loc r with
    | Some o => SStore Syntax.access_size.word fp (spill_tmp 1) o
    | None => SSkip
    end.

  Notation "s1 ;; s2" := (SSeq s1 s2) (right associativity, at level 100).

  (* dst must be <32, src might be >= 32 *)
  Definition write_register(dst src: Z): stmt :=
    match stack_loc src with
    | Some o => SLoad Syntax.access_size.word dst fp o
    | None => SSet dst src
    end.

  Fixpoint write_register_range(range_start: Z)(srcs: list Z): stmt :=
    match srcs with
    | nil => SSkip
    | x :: xs => write_register_range (range_start+1) xs;; write_register range_start x
    end.

  (* dst might be >=32, src must be < 32 *)
  Definition read_register(dst src: Z): stmt :=
    match stack_loc dst with
    | Some o => SStore Syntax.access_size.word fp src o
    | None => SSet dst src
    end.

  Fixpoint read_register_range(dests: list Z)(range_start: Z): stmt :=
    match dests with
    | nil => SSkip
    | x :: xs => read_register x range_start;; read_register_range xs (range_start+1)
    end.

  Definition prepare_bcond(c: bcond Z): stmt :=
    match c with
    | CondBinary _ x y => load_iarg_reg 1 x;; load_iarg_reg 2 y
    | CondNez x => load_iarg_reg 1 x
    end.

  Definition spill_bcond(c: bcond Z): bcond Z :=
    match c with
    | CondBinary op x y => CondBinary op (iarg_reg 1 x) (iarg_reg 2 y)
    | CondNez x => CondNez (iarg_reg 1 x)
    end.

  Fixpoint spill_stmt(s: stmt): stmt :=
    match s with
    | SLoad sz x y o =>
      load_iarg_reg 1 y;;
      SLoad sz (ires_reg x) (iarg_reg 1 y) o;;
      save_ires_reg x
    | SStore sz x y o =>
      load_iarg_reg 1 x;; load_iarg_reg 2 y;;
      SStore sz (iarg_reg 1 x) (iarg_reg 2 y) o
    | SInlinetable sz x t i =>
      load_iarg_reg 2 i;;
      SInlinetable sz (ires_reg x) t (iarg_reg 2 i);;
      save_ires_reg x
    | SStackalloc x n body =>
      SStackalloc (ires_reg x) n (save_ires_reg x;; spill_stmt body)
    | SLit x n =>
      SLit (ires_reg x) n;;
      save_ires_reg x
    | SOp x op y z =>
      load_iarg_reg 1 y;; load_iarg_reg 2 z;;
      SOp (ires_reg x) op (iarg_reg 1 y) (iarg_reg 2 z);;
      save_ires_reg x
    | SSet x y => (* TODO could be optimized if exactly one is on the stack *)
      load_iarg_reg 1 y;;
      SSet (ires_reg x) (iarg_reg 1 y);;
      save_ires_reg x
    | SIf c thn els =>
      prepare_bcond c;;
      SIf (spill_bcond c) (spill_stmt thn) (spill_stmt els)
    | SLoop s1 c s2 =>
      SLoop (spill_stmt s1;; prepare_bcond c) (spill_bcond c) (spill_stmt s2)
    | SSeq s1 s2 => SSeq (spill_stmt s1) (spill_stmt s2)
    | SSkip => SSkip
    | SCall resvars f argvars =>
      write_register_range a0 argvars;;
      SCall (List.firstn (length resvars) (reg_class.all reg_class.arg))
            f
            (List.firstn (length argvars) (reg_class.all reg_class.arg));;
      read_register_range resvars a0
    | SInteract resvars f argvars =>
      write_register_range a0 argvars;;
      SInteract (List.firstn (length resvars) (reg_class.all reg_class.arg))
                f
                (List.firstn (length argvars) (reg_class.all reg_class.arg));;
      read_register_range resvars a0
    end.

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
    | SCall resvars f argvars | SInteract resvars f argvars =>
      Z.max (List.fold_left Z.max argvars 0) (List.fold_left Z.max resvars 0)
    end.

  Lemma le_fold_left_max: forall l a init,
      a <= init ->
      a <= fold_left Z.max l init.
  Proof.
    induction l; simpl; intros.
    - assumption.
    - eapply IHl. apply Z.max_le_iff. left. assumption.
  Qed.

  Lemma le_fold_left_max_increase_init: forall l init1 init2,
      init1 <= init2 ->
      fold_left Z.max l init1 <= fold_left Z.max l init2.
  Proof.
    induction l; simpl; intros.
    - assumption.
    - eapply IHl. blia.
  Qed.

  Lemma Forall_le_max: forall (l: list Z), Forall (fun x : Z => x <= fold_left Z.max l 0) l.
  Proof.
    induction l; simpl.
    - constructor.
    - constructor.
      + apply le_fold_left_max. apply Z.le_max_r.
      + eapply Forall_impl. 2: exact IHl. cbv beta. intros.
        etransitivity. 1: exact H.
        eapply le_fold_left_max_increase_init.
        apply Z.le_max_l.
  Qed.

  Hint Extern 1 => blia : max_var_sound.
  Hint Extern 1 => cbv beta : max_var_sound.
  Hint Extern 1 => eapply Forall_vars_stmt_impl; cycle -1 : max_var_sound.
  Hint Resolve Forall_and : max_var_sound.
  Hint Extern 1 => eapply Forall_impl; [|eapply Forall_le_max]; cbv beta : max_var_sound.
  Hint Extern 1 => match goal with
                   | IH: forall _, _ -> Forall_vars_stmt _ _ _ |- Forall_vars_stmt _ _ _ =>
                     eapply IH
                   end : max_var_sound.

  Lemma max_var_sound: forall s,
      Forall_vars_stmt (fun x => fp < x) s ->
      Forall_vars_stmt (fun x => fp < x <= max_var s) s.
  Proof.
    induction s; simpl; intros; unfold ForallVars_bcond in *; simpl;
      repeat match goal with
             | H: _ /\ _ |- _ => destruct H
             | c: bcond _ |- _ => destruct c; simpl
             | |- _ /\ _ => split
             end;
      eauto with max_var_sound.
    Unshelve.
    all: try exact (fun _ => True).
  Qed.

  Definition spill_fbody(s: stmt): stmt :=
    let maxvar := max_var s in
    SStackalloc fp (bytes_per_word * Z.of_nat (Z.to_nat (maxvar - 31))) (spill_stmt s).
  (* `Z.of_nat (Z.to_nat _)` is to to make sure it's not negative.
     We might stackalloc 0 bytes, but that still writes fp, which is required to be
     set by `related`, and we don't want to complicate `related` to accommodate for a
     potentially uninitialized `fp` after a function call happens in a fresh locals env *)

  Open Scope bool_scope.

  Definition is_valid_src_var(x: Z): bool := Z.ltb fp x && (Z.ltb x a0 || Z.ltb a7 x).

  Definition spill_fun: list Z * list Z * stmt -> option (list Z * list Z * stmt) :=
    fun '(argnames, resnames, body) =>
      if List.forallb is_valid_src_var argnames &&
         List.forallb is_valid_src_var resnames &&
         forallb_vars_stmt is_valid_src_var body &&
         Nat.leb (List.length argnames) 8 &&
         Nat.leb (List.length resnames) 8
      then
        let argnames' := List.firstn (List.length argnames) (reg_class.all reg_class.arg) in
        let resnames' := List.firstn (List.length resnames) (reg_class.all reg_class.arg) in
        Some (argnames', resnames',
              read_register_range argnames a0;;
              spill_fbody body;;
              write_register_range a0 resnames)
      else None.

  Lemma firstn_min_absorb_length_r{A: Type}: forall (l: list A) n,
      List.firstn (Nat.min n (length l)) l = List.firstn n l.
  Proof.
    intros. destruct (Nat.min_spec n (length l)) as [[? E] | [? E]]; rewrite E.
    - reflexivity.
    - rewrite List.firstn_all. rewrite List.firstn_all2 by assumption. reflexivity.
  Qed.

  Lemma spill_stmt_uses_standard_arg_regs: forall s, uses_standard_arg_regs (spill_stmt s).
  Proof.
    induction s; simpl; unfold prepare_bcond, load_iarg_reg, save_ires_reg;
      repeat destruct_one_match; simpl; eauto.
    all: rewrite ?List.firstn_length, ?firstn_min_absorb_length_r.
  Abort.

  Context {locals: map.map Z word}.
  Context {localsOk: map.ok locals}.
  Context {env: map.map String.string (list Z * list Z * stmt)} {env_ok: map.ok env}.
  Context {ext_spec: Semantics.ExtSpec}.

  Definition spill_functions: env -> option env :=
    map.map_all_values spill_fun.

  Definition valid_vars_src(maxvar: Z): stmt -> Prop :=
    Forall_vars_stmt (fun x => fp < x <= maxvar /\ (x < a0 \/ a7 < x)).

  Definition valid_vars_tgt: stmt -> Prop :=
    Forall_vars_stmt (fun x => 3 <= x < 32).

  Local Arguments Z.of_nat: simpl never.

  Lemma read_register_range_valid_vars: forall maxvar args start,
      3 <= start ->
      start + Z.of_nat (List.length args) <= 32 ->
      Forall (fun x => fp < x <= maxvar /\ (x < a0 \/ a7 < x)) args ->
      valid_vars_tgt (read_register_range args start).
  Proof.
    induction args; simpl; intros.
    - exact I.
    - fwd. split.
      + unfold read_register, stack_loc, fp, a0, a7 in *. destr (32 <=? a); simpl; blia.
      + eapply IHargs; try blia. assumption.
  Qed.

  Lemma write_register_range_valid_vars: forall maxvar args start,
      3 <= start ->
      start + Z.of_nat (List.length args) <= 32 ->
      Forall (fun x => fp < x <= maxvar /\ (x < a0 \/ a7 < x)) args ->
      valid_vars_tgt (write_register_range start args).
  Proof.
    induction args; simpl; intros.
    - exact I.
    - fwd. split.
      + eapply IHargs; try blia. assumption.
      + unfold write_register, stack_loc, fp, a0, a7 in *. destr (32 <=? a); simpl; blia.
  Qed.

  Lemma spill_stmt_valid_vars: forall s m,
      max_var s <= m ->
      valid_vars_src m s ->
      valid_vars_tgt (spill_stmt s).
  Proof.
    unfold valid_vars_src, valid_vars_tgt.
    induction s; simpl; intros;
      repeat match goal with
             | c: bcond Z |- _ => destr c
             | |- context[Z.leb ?x ?y] => destr (Z.leb x y)
             | |- _ => progress simpl
             | |- _ => progress unfold spill_tmp, sp, fp, ires_reg, iarg_reg, iarg_reg, ires_reg,
                         spill_bcond, max_var_bcond, ForallVars_bcond, prepare_bcond,
                         load_iarg_reg, load_iarg_reg, save_ires_reg, stack_loc in *
             end;
      try blia;
      fwd;
      repeat match goal with
      | IH: _, H: Forall_vars_stmt _ _ |- _ =>
        specialize IH with (2 := H);
        match type of IH with
        | ?P -> _ => let A := fresh in assert P as A by blia; specialize (IH A); clear A
        end
      end;
      eauto;
      intuition try blia;
      try eapply write_register_range_valid_vars;
      try eapply read_register_range_valid_vars;
      unfold a0, a7 in *;
      eauto;
      rewrite ?List.firstn_length;
      try eapply List.Forall_firstn;
      try (eapply List.Forall_impl; [|eapply arg_range_Forall]; cbv beta);
      try blia.
  Qed.

  (* potentially uninitialized argument registers (used also as spilling temporaries) *)
  Definition arg_regs(l: locals): Prop :=
    forall k v, map.get l k = Some v -> 10 <= k < 18.

  Definition related(maxvar: Z)(frame: mem -> Prop)(fpval: word)
             (t1: Semantics.trace)(m1: mem)(l1: locals)
             (t2: Semantics.trace)(m2: mem)(l2: locals): Prop :=
      exists lStack lRegs stackwords,
        t1 = t2 /\
        (eq m1 * word_array fpval stackwords * frame)%sep m2 /\
        (forall x v, map.get lRegs x = Some v -> fp < x < 32 /\ (x < a0 \/ a7 < x)) /\
        (forall x v, map.get lStack x = Some v -> 32 <= x <= maxvar) /\
        (eq lRegs * eq lStack)%sep l1 /\
        (eq lRegs * arg_regs * ptsto fp fpval)%sep l2 /\
        (forall r, 32 <= r <= maxvar -> forall v, map.get lStack r = Some v ->
           nth_error stackwords (Z.to_nat (r - 32)) = Some v) /\
        length stackwords = Z.to_nat (maxvar - 31).

  Implicit Types post : Semantics.trace -> mem -> locals -> MetricLog -> Prop.

  Lemma put_arg_reg: forall l r v fpval lRegs,
      (eq lRegs * arg_regs * ptsto fp fpval)%sep l ->
      a0 <= r <= a7 ->
      (forall x v, map.get lRegs x = Some v -> fp < x < 32 /\ (x < a0 \/ a7 < x)) ->
      (eq lRegs * arg_regs * ptsto fp fpval)%sep (map.put l r v).
  Proof.
    intros.
    assert (((eq lRegs * ptsto fp fpval) * arg_regs)%sep l) as A by ecancel_assumption. clear H.
    enough (((eq lRegs * ptsto fp fpval) * arg_regs)%sep (map.put l r v)). 1: ecancel_assumption.
    unfold sep at 1. unfold sep at 1 in A. fwd.
    unfold arg_regs in *.
    unfold map.split.
    unfold map.split in Ap0. fwd.
    exists mp, (map.put mq r v). ssplit.
    - apply map.put_putmany_commute.
    - unfold sep, map.split in Ap1. fwd. unfold map.disjoint in *.
      intros. rewrite map.get_put_dec in H2. rewrite map.get_putmany_dec in H.
      unfold ptsto in *. subst.
      setoid_rewrite map.get_put_dec in Ap1p0p1. setoid_rewrite map.get_empty in Ap1p0p1.
      setoid_rewrite <- map.put_putmany_commute in Ap0p1.
      setoid_rewrite map.putmany_empty_r in Ap0p1.
      setoid_rewrite map.get_put_dec in Ap0p1.
      rewrite map.get_put_dec in H. rewrite map.get_empty in H. unfold fp, spill_tmp, a0, a7 in *.
      specialize (Ap0p1 k).
      destruct_one_match_hyp; fwd; subst; destruct_one_match_hyp; fwd; subst.
      + blia.
      + specialize H1 with (1 := H). blia.
      + eauto.
      + eauto.
    - assumption.
    - intros. rewrite map.get_put_dec in H. unfold spill_tmp, a0, a7 in *.
      destruct_one_match_hyp.
      + blia.
      + eauto.
  Qed.

  Lemma put_tmp: forall l i v fpval lRegs,
      (eq lRegs * arg_regs * ptsto fp fpval)%sep l ->
      i = 1 \/ i = 2 ->
      (forall x v, map.get lRegs x = Some v -> fp < x < 32 /\ (x < a0 \/ a7 < x)) ->
      (eq lRegs * arg_regs * ptsto fp fpval)%sep (map.put l (spill_tmp i) v).
  Proof.
    intros. assert (a0 <= spill_tmp i <= a7) by (unfold spill_tmp, a0, a7; blia).
    unfold spill_tmp. eapply put_arg_reg; eassumption.
  Qed.

  Axiom TODO: False.

  Lemma load_iarg_reg_correct(i: Z): forall r e2 t1 t2 m1 m2 l1 l2 mc2 fpval post frame maxvar v,
      i = 1 \/ i = 2 ->
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      fp < r <= maxvar /\ (r < a0 \/ a7 < r) ->
      map.get l1 r = Some v ->
      (forall mc2,
          related maxvar frame fpval t1 m1 l1 t2 m2 (map.put l2 (iarg_reg i r) v) ->
          post t2 m2 (map.put l2 (iarg_reg i r) v) mc2) ->
      exec e2 (load_iarg_reg i r) t2 m2 l2 mc2 post.
  Proof.
    intros.
    unfold load_iarg_reg, stack_loc, iarg_reg, related in *. fwd.
    destr (32 <=? r).
    - eapply exec.load.
      + eapply get_sep. ecancel_assumption.
      + eapply load_from_word_array. 1: ecancel_assumption. 2: blia.
        eapply H0p6. 1: blia.
        unfold sep in H0p4. fwd.
        eapply map.get_split_r. 1,3: eassumption.
        destr (map.get mp r); [exfalso|reflexivity].
        specialize H0p2 with (1 := E0). blia.
      + eapply H3.
        repeat match goal with
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               | |- _ => eassumption || reflexivity
               end.
        eapply put_tmp; eassumption.
    - eapply exec.skip.
      replace l2 with (map.put l2 r v) in H0p5|-*. 2: {
        apply map.put_idemp.
        edestruct (eq_sep_to_split l2) as (l2Rest & S22 & SP22). 1: ecancel_assumption.
        eapply map.get_split_grow_r. 1: eassumption.
        unfold sep in H0p4. destruct H0p4 as (lRegs' & lStack' & S2 & ? & ?). subst lRegs' lStack'.
        eapply map.get_split_l. 1: exact S2. 2: assumption.
        destr (map.get lStack r); [exfalso|reflexivity].
        specialize H0p3 with (1 := E0). blia.
      }
      eapply H3.
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             | |- _ => eassumption || reflexivity
             end.
  Qed.

  Lemma load_iarg_reg_correct'(i: Z): forall r e2 t1 t2 m1 m2 l1 l2 mc1 mc2 post frame maxvar v fpval,
      i = 1 \/ i = 2 ->
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      fp < r <= maxvar /\ (r < a0 \/ a7 < r) ->
      map.get l1 r = Some v ->
      post t1 m1 l1 mc1 ->
      exec e2 (load_iarg_reg i r) t2 m2 l2 mc2
           (fun t2' m2' l2' mc2' => exists t1' m1' l1' mc1',
                related maxvar frame fpval t1' m1' l1' t2' m2' l2' /\ post t1' m1' l1' mc1').
  Proof.
    intros.
    unfold load_iarg_reg, stack_loc, iarg_reg, related in *. fwd.
    destr (32 <=? r).
    - eapply exec.load.
      + eapply get_sep. ecancel_assumption.
      + eapply load_from_word_array. 1: ecancel_assumption. 2: blia.
        eapply H0p6. 1: blia.
        unfold sep in H0p4. fwd.
        eapply map.get_split_r. 1,3: eassumption.
        destr (map.get mp r); [exfalso|reflexivity].
        specialize H0p2 with (1 := E0). blia.
      + repeat match goal with
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               | |- _ => eassumption || reflexivity
               end.
        eapply put_tmp; eassumption.
    - eapply exec.skip.
      replace l2 with (map.put l2 r v) in H0p5|-*. 2: {
        apply map.put_idemp.
        edestruct (eq_sep_to_split l2) as (l2Rest & S22 & SP22). 1: ecancel_assumption.
        eapply map.get_split_grow_r. 1: eassumption.
        unfold sep in H0p4. destruct H0p4 as (lRegs' & lStack' & S2 & ? & ?). subst lRegs' lStack'.
        eapply map.get_split_l. 1: exact S2. 2: assumption.
        destr (map.get lStack r); [exfalso|reflexivity].
        specialize H0p3 with (1 := E0). blia.
      }
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             | |- _ => eassumption || reflexivity
             end.
  Qed.

  (* Note: if we wanted to use this lemma in subgoals created by exec.loop,
     new postcondition must not mention the original t2, m2, l2, mc2, (even though
     it would be handy to just say t2'=t2, m2=m2', l2' = map.put l2 (iarg_reg i r) v), because
     when the new postcondition is used as a "mid1" in exec.loop, and body1 is a seq
     in which this lemma was used, t2, m2, l2, mc2 are introduced after the evar "?mid1"
     is created (i.e. after exec.loop is applied), so they are not in the scope of "?mid1". *)
  Lemma load_iarg_reg_correct''(i: Z): forall r e2 t1 t2 m1 m2 l1 l2 mc2 frame maxvar v fpval,
      i = 1 \/ i = 2 ->
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      fp < r <= maxvar /\ (r < a0 \/ a7 < r) ->
      map.get l1 r = Some v ->
      exec e2 (load_iarg_reg i r) t2 m2 l2 mc2 (fun t2' m2' l2' mc2' =>
        t2' = t2 /\ m2' = m2 /\ l2' = map.put l2 (iarg_reg i r) v /\
        related maxvar frame fpval t1 m1 l1 t2' m2' l2').
  Proof.
    intros.
    unfold load_iarg_reg, stack_loc, iarg_reg, related in *. fwd.
    destr (32 <=? r).
    - eapply exec.load.
      + eapply get_sep. ecancel_assumption.
      + eapply load_from_word_array. 1: ecancel_assumption. 2: blia.
        eapply H0p6. 1: blia.
        unfold sep in H0p4. fwd.
        eapply map.get_split_r. 1,3: eassumption.
        destr (map.get mp r); [exfalso|reflexivity].
        specialize H0p2 with (1 := E0). blia.
      + repeat match goal with
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               | |- _ => eassumption || reflexivity
               end.
        eapply put_tmp; eassumption.
    - eapply exec.skip.
      assert (l2 = map.put l2 r v) as F. {
        symmetry. apply map.put_idemp.
        edestruct (eq_sep_to_split l2) as (l2Rest & S22 & SP22). 1: ecancel_assumption.
        eapply map.get_split_grow_r. 1: eassumption.
        unfold sep in H0p4. destruct H0p4 as (lRegs' & lStack' & S2 & ? & ?). subst lRegs' lStack'.
        eapply map.get_split_l. 1: exact S2. 2: assumption.
        destr (map.get lStack r); [exfalso|reflexivity].
        specialize H0p3 with (1 := E0). blia.
      }
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             | |- _ => eassumption || reflexivity
             end.
  Qed.

  (* SOp does not create an up-to-date `related` before we invoke this one, because after SOp,
     `related` does not hold: the result is already in l1 and lStack, but not yet in stackwords.
     So we request the `related` that held *before* SOp, i.e. the one where the result is not
     yet in l1 and l2. *)
  Lemma save_ires_reg_correct: forall e t1 t2 m1 m2 l1 l2 mc1 mc2 x v maxvar frame post fpval,
      post t1 m1 (map.put l1 x v) mc1 ->
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      fp < x <= maxvar /\ (x < a0 \/ a7 < x) ->
      exec e (save_ires_reg x) t2 m2 (map.put l2 (ires_reg x) v) mc2
           (fun t2' m2' l2' mc2' => exists t1' m1' l1' mc1',
                related maxvar frame fpval t1' m1' l1' t2' m2' l2' /\ post t1' m1' l1' mc1').
  Proof.
    intros.
    unfold save_ires_reg, stack_loc, ires_reg, related in *. fwd.
    destr (32 <=? x).
    - edestruct store_to_word_array as (m' & stackwords' & St & S' & Ni & Nj & L).
      1: ecancel_assumption.
      2: {
        eapply exec.store.
        - rewrite map.get_put_diff by (cbv; congruence).
          eapply get_sep. ecancel_assumption.
        - rewrite map.get_put_same. reflexivity.
        - exact St.
        - repeat match goal with
                 | |- exists _, _ => eexists
                 | |- _ /\ _ => split
                 end.
          1: reflexivity.
          8: eassumption.
          1: ecancel_assumption.
          3: {
            unfold sep, map.split in H0p3|-*.
            destruct H0p4 as (lRegs' & lStack' & (? & D) & ? & ?). subst lRegs' lStack' l1.
            exists lRegs, (map.put lStack x v).
            repeat split.
            - apply map.put_putmany_commute.
            - unfold map.disjoint. intros.
              specialize H0p2 with (1 := H0).
              rewrite map.get_put_dec in H1. destr (x =? k).
              + subst x. blia.
              + specialize H0p3 with (1 := H1). blia.
          }
          1: eassumption.
          1: {
            intros. rewrite map.get_put_dec in H0. destr (x =? x0).
            - subst x0. blia.
            - eauto.
          }
          2: {
            intros.
            intros. rewrite map.get_put_dec in H1. destr (x =? r).
            - apply Option.eq_of_eq_Some in H1. subst. assumption.
            - eapply Nj. 1: blia. eauto.
          }
          1: { unfold spill_tmp. eapply put_tmp; eauto. }
          blia.
      }
      blia.
    - eapply exec.skip.
      (* even though we did nothing, we have to reconstruct the `related` from the `related` that
         held *before* the SOp *)
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             end.
      1: reflexivity.
      8: eassumption.
      1: ecancel_assumption.
      3: {
        apply sep_comm. apply sep_comm in H0p4.
        unfold sep, map.split in H0p3|-*.
        destruct H0p4 as (lRegs' & lStack' & (? & D) & ? & ?). subst lRegs' lStack' l1.
        exists lStack, (map.put lRegs x v).
        repeat split.
        - apply map.put_putmany_commute.
        - unfold map.disjoint. intros.
          specialize H0p3 with (1 := H0).
          rewrite map.get_put_dec in H1. destr (x =? k).
          + subst x. blia.
          + specialize H0p2 with (1 := H1). blia.
      }
      1: {
        intros. rewrite map.get_put_dec in H0. destr (x =? x0).
        - subst x0. blia.
        - eauto.
      }
      2: {
        spec (sep_eq_put lRegs l2) as A. 1,3: ecancel_assumption.
        unfold arg_regs, sep, map.split, spill_tmp, fp, a0, a7 in *.
        intros. fwd.
        unfold ptsto, map.disjoint in *. subst.
        rewrite ?map.get_putmany_dec, ?map.get_put_dec, ?map.get_empty in H1.
        repeat destruct_one_match_hyp; subst; fwd; try congruence; try blia.
        specialize H0p8 with (1 := H1). blia.
      }
      all: try eassumption.
  Qed.

  (* SOp does not create an up-to-date `related` before we invoke this one, because after SOp,
     `related` does not hold: the result is already in l1 and lStack, but not yet in stackwords.
     So we request the `related` that held *before* SOp, i.e. the one where the result is not
     yet in l1 and l2. *)
  Lemma save_ires_reg_correct'': forall e t1 t2 m1 m2 l1 l2 mc2 x v maxvar frame post fpval,
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      fp < x <= maxvar /\ (x < a0 \/ a7 < x) ->
      (forall t2' m2' l2' mc2',
          related maxvar frame fpval t1 m1 (map.put l1 x v) t2' m2' l2' ->
          post t2' m2' l2' mc2') ->
      exec e (save_ires_reg x) t2 m2 (map.put l2 (ires_reg x) v) mc2 post.
  Proof.
    intros.
    unfold save_ires_reg, stack_loc, ires_reg, related in *. fwd.
    destr (32 <=? x).
    - edestruct store_to_word_array as (m' & stackwords' & St & S' & Ni & Nj & L).
      1: ecancel_assumption.
      2: {
        eapply exec.store.
        - rewrite map.get_put_diff by (cbv; congruence).
          eapply get_sep. ecancel_assumption.
        - rewrite map.get_put_same. reflexivity.
        - exact St.
        - eapply H1.
          repeat match goal with
                 | |- exists _, _ => eexists
                 | |- _ /\ _ => split
                 end.
          1: reflexivity.
          1: ecancel_assumption.
          3: {
            unfold sep, map.split in Hp3|-*.
            destruct Hp4 as (lRegs' & lStack' & (? & D) & ? & ?). subst lRegs' lStack' l1.
            exists lRegs, (map.put lStack x v).
            repeat split.
            - apply map.put_putmany_commute.
            - unfold map.disjoint. intros.
              specialize Hp2 with (1 := H).
              rewrite map.get_put_dec in H0. destr (x =? k).
              + subst x. blia.
              + eauto with zarith.
          }
          1: eassumption.
          1: {
            intros. rewrite map.get_put_dec in H. destr (x =? x0).
            - subst x0. blia.
            - eauto.
          }
          2: {
            intros.
            intros. rewrite map.get_put_dec in H0. destr (x =? r).
            - apply Option.eq_of_eq_Some in H0. subst. assumption.
            - eapply Nj. 1: blia. eauto.
          }
          1: { unfold spill_tmp. eapply put_tmp; eauto. }
          blia.
      }
      blia.
    - eapply exec.skip.
      eapply H1.
      (* even though we did nothing, we have to reconstruct the `related` from the `related` that
         held *before* the SOp *)
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             end.
      1: reflexivity.
      1: ecancel_assumption.
      3: {
        apply sep_comm. apply sep_comm in Hp4.
        unfold sep, map.split in Hp4|-*.
        destruct Hp4 as (lRegs' & lStack' & (? & D) & ? & ?). subst lRegs' lStack' l1.
        exists lStack, (map.put lRegs x v).
        repeat split.
        - apply map.put_putmany_commute.
        - unfold map.disjoint. intros.
          specialize Hp3 with (1 := H).
          rewrite map.get_put_dec in H0. destr (x =? k).
          + subst x. blia.
          + eauto with zarith.
      }
      1: {
        intros. rewrite map.get_put_dec in H. destr (x =? x0).
        - subst x0. blia.
        - eauto.
      }
      2: {
        spec (sep_eq_put lRegs l2) as A. 1,3: ecancel_assumption.
        unfold arg_regs, sep, map.split, spill_tmp, fp, a0, a7 in *.
        intros. fwd.
        unfold ptsto, map.disjoint in *. subst.
        rewrite ?map.get_putmany_dec, ?map.get_put_dec, ?map.get_empty in H0.
        repeat destruct_one_match_hyp; subst; fwd; try congruence; try blia.
        specialize Hp8 with (1 := H0). blia.
      }
      all: try eassumption.
  Qed.

  Lemma get_iarg_reg_1: forall l l2 y y' (z : Z) (z' : word),
      fp < y /\ (y < a0 \/ a7 < y) ->
      fp < z /\ (z < a0 \/ a7 < z) ->
      map.get l y = Some y' ->
      map.get l z = Some z' ->
      map.get (map.put (map.put l2 (iarg_reg 1 y) y') (iarg_reg 2 z) z') (iarg_reg 1 y) = Some y'.
  Proof.
    intros.
    destr (y =? z).
    - subst z. replace z' with y' in * by congruence.
      unfold iarg_reg, spill_tmp. destruct_one_match.
      + rewrite map.get_put_diff by blia. rewrite map.get_put_same. reflexivity.
      + rewrite map.get_put_same. reflexivity.
    - rewrite map.get_put_diff.
      + rewrite map.get_put_same. reflexivity.
      + unfold iarg_reg, spill_tmp, a0, a7, fp in *. repeat destruct_one_match; blia.
  Qed.

  (* variant of `related` where a list of HL variables (some from lRegs, some from lStack)
     is not in the usual LL regs or on the stack, but is in the arg regs *)
  Definition related'(maxvar: Z)(in_arg_regs: list Z)(first_arg_reg: Z)
             (frame: mem -> Prop)(fpval: word)
             (t1: Semantics.trace)(m1: mem)(l1: locals)
             (t2: Semantics.trace)(m2: mem)(l2: locals): Prop :=
    exists lStack lRegs hlArgRegs llArgRegs stackwords argvals,
      t1 = t2 /\
      (eq m1 * word_array fpval stackwords * frame)%sep m2 /\
      (forall x v, map.get lRegs x = Some v -> fp < x < 32 /\ (x < a0 \/ a7 < x)) /\
      (forall x v, map.get lStack x = Some v -> 32 <= x <= maxvar) /\
      map.of_list_zip in_arg_regs argvals = Some hlArgRegs /\
      map.of_list_zip (List.unfoldn (Z.add 1) (length in_arg_regs) first_arg_reg)
                      argvals = Some llArgRegs /\
      (eq lRegs * eq hlArgRegs * eq lStack)%sep l1 /\
      (eq lRegs * eq llArgRegs * arg_regs * ptsto fp fpval)%sep l2 /\
      (forall r, 32 <= r <= maxvar -> forall v, map.get lStack r = Some v ->
                 nth_error stackwords (Z.to_nat (r - 32)) = Some v) /\
      length stackwords = Z.to_nat (maxvar - 31).

  (* Need to repeat in each section because autorewrite does not run typeclass search to
     find key_eqb_spec *)
  Hint Rewrite
       (sep_eq_empty_l (key_eqb := Z.eqb))
       (sep_eq_empty_r (key_eqb := Z.eqb))
    : fwd_rewrites.

  Lemma not_In_Z_seq: forall L start d,
      start < d ->
      ~ In start (List.unfoldn (Z.add 1) L d).
  Proof.
    unfold not.
    induction L; cbn -[Z.add]; intros. 1: assumption.
    destruct H0.
    - subst. blia.
    - eapply IHL. 2: exact H0. blia.
  Qed.

  Lemma related'_nil_to_related: forall maxvar first_arg_reg frame fpval t1 t2 m1 m2 l1 l2,
      related' maxvar [] first_arg_reg frame fpval t1 m1 l1 t2 m2 l2 ->
      related maxvar frame fpval t1 m1 l1 t2 m2 l2.
  Proof.
    unfold related', related. intros. fwd.
    do 3 eexists. ssplit; try reflexivity; try eassumption.
  Qed.

  Lemma related_to_related'_nil: forall maxvar first_arg_reg frame fpval t1 t2 m1 m2 l1 l2,
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      related' maxvar [] first_arg_reg frame fpval t1 m1 l1 t2 m2 l2.
  Proof.
    unfold related', related. intros. fwd.
    eexists _, _, _, _, _, nil. ssplit; try reflexivity; try eassumption; fwd; try eassumption.
  Qed.

  Lemma read_register_range_correct:
    forall args start e t1 t2 m1 m2 l1 l2 mc2 maxvar frame post fpval,
      related' maxvar args start frame fpval t1 m1 l1 t2 m2 l2 ->
      (List.length args <= 8)%nat ->
      NoDup args ->
      a0 <= start ->
      start + Z.of_nat (List.length args) <= a7 + 1 ->
      Forall (fun x => fp < x <= maxvar /\ (x < a0 \/ a7 < x)) args ->
      (forall m2' l2' mc2',
          related maxvar frame fpval t1 m1 l1 t2 m2' l2' ->
          post t2 m2' l2' mc2') ->
      exec e (read_register_range args start) t2 m2 l2 mc2 post.
  Proof.
    induction args; intros.
    - simpl. eapply exec.skip. eauto using related'_nil_to_related.
    - simpl. unfold read_register, stack_loc.
      unfold related' in H. fwd.
      eapply map.of_list_zip_cons_keys in Hp4. 2: eassumption. fwd.
      cbn -[map.of_list_zip Z.add] in Hp5. eapply map.of_list_zip_cons_keys in Hp5. 2: {
        eapply not_In_Z_seq. blia.
      }
      fwd.
      cbn [List.unfoldn List.length] in *.
      rewrite (Z.add_comm 1 start) in *.
      rewrite eq_put_to_sep in Hp6. 2: {
        (* eauto using map.not_in_of_list_zip_to_get_None, Z.eqb_spec. WHY doesn't that work? *)
        eapply map.not_in_of_list_zip_to_get_None.
        1: eassumption. eassumption.
      }
      rewrite eq_put_to_sep in Hp7. 2: {
        eapply map.not_in_of_list_zip_to_get_None.
        1: eassumption. eapply not_In_Z_seq. blia.
      }
      destr (32 <=? a).
      + eapply exec.seq_cps.
        edestruct store_to_word_array with (i := a - 32).
        1: ecancel_assumption. 1: blia.
        fwd.
        eapply exec.store.
        { eapply get_sep. ecancel_assumption. }
        { eapply get_sep. ecancel_assumption. }
        { eassumption. }
        eapply IHargs with (l1 := l1); try eassumption; try blia.
        unfold related'. eexists (map.put lStack a v0), lRegs, _, _, _, _.
        ssplit.
        * reflexivity.
        * ecancel_assumption.
        * eassumption.
        * intros. rewrite map.get_put_dec in H. destr (a =? x0); fwd. 1: blia. eauto.
        * eassumption.
        * eassumption.
        * rewrite eq_put_to_sep. 2: {
            destr (map.get lStack a). 2: reflexivity. exfalso.
            match goal with
            | H: (_ * _)%sep l1 |- _ => rename H into HS; move HS at bottom
            end.
            replace lStack with (map.put (map.remove lStack a) a r) in HS. 2: {
              rewrite map.put_remove_same.
              apply map.put_idemp. assumption.
            }
            rewrite eq_put_to_sep in HS by apply map.get_remove_same.
            eapply (ptsto_no_aliasing l1). 1: exact HS.
            ecancel.
          }
          ecancel_assumption.
        * (* use ecancel_assumption_impl *)
          case TODO.
        * intros. rewrite map.get_put_dec in H1. destr (a =? r); fwd; eauto with zarith.
        * blia.
      + eapply exec.seq_cps.
        eapply exec.set.
        { eapply get_sep. ecancel_assumption. }
        eapply IHargs; try eassumption; try blia.
        unfold related'. eexists lStack, (map.put lRegs a v0), _, _, _, _.
        ssplit.
        * reflexivity.
        * ecancel_assumption.
        * intros. rewrite map.get_put_dec in H. destr (a =? x); fwd. 1: blia. eauto.
        * eassumption.
        * eassumption.
        * eassumption.
        * rewrite eq_put_to_sep. 2: {
            destr (map.get lRegs a). 2: reflexivity. exfalso.
            match goal with
            | H: (_ * _)%sep l1 |- _ => rename H into HS; move HS at bottom
            end.
            replace lRegs with (map.put (map.remove lRegs a) a r) in HS. 2: {
              rewrite map.put_remove_same.
              apply map.put_idemp. assumption.
            }
            rewrite eq_put_to_sep in HS by apply map.get_remove_same.
            eapply (ptsto_no_aliasing l1). 1: exact HS.
            ecancel.
          }
          ecancel_assumption.
        * (* in Hp7, hide `ptsto start v0` into `arg_regs`, then eq/map.put *)
          case TODO.
        * eauto.
        * blia.
  Qed.

  Lemma write_register_range_correct:
    forall args argvs start e t1 t2 m1 m2 l1 l2 mc2 maxvar frame post fpval,
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      (List.length args <= 8)%nat ->
      NoDup args ->
      a0 <= start ->
      start + Z.of_nat (List.length args) <= a7 + 1 ->
      Forall (fun x => fp < x <= maxvar /\ (x < a0 \/ a7 < x)) args ->
      map.getmany_of_list l1 args = Some argvs ->
      (forall m2' l2' mc2',
          related' maxvar args start frame fpval t1 m1 l1 t2 m2' l2' ->
          post t2 m2' l2' mc2') ->
      exec e (write_register_range start args) t2 m2 l2 mc2 post.
  Proof.
    induction args; intros.
    - simpl. eapply exec.skip. eauto using related_to_related'_nil.
    - simpl. unfold write_register, stack_loc.
      destruct argvs as [|v vs]. {
        unfold map.getmany_of_list in H5. cbn in H5. fwd.
        destr (List.option_all (map (map.get l1) args)); discriminate.
      }
      eapply map.invert_getmany_of_list_cons in H5. destruct H5 as [G GM].
      cbn [List.length] in *.
      fwd.
      eapply exec.seq_cps.
      eapply IHargs; try eassumption; try blia.
      unfold related'. intros. fwd.
      destr (32 <=? a).
      + eapply exec.load.
        * eapply get_sep. ecancel_assumption.
        * eapply load_from_word_array. 1: ecancel_assumption. 2: blia.
          eapply H1p10. 1: blia.
          unfold sep in H1p8. fwd.
          eapply map.get_split_r. 1,3: eassumption.
          destr (map.get mp a); [exfalso|reflexivity].
          eapply map.get_split_l in E0. 2: eassumption.
          -- specialize H1p4 with (1 := E0). blia.
          -- eapply map.not_in_of_list_zip_to_get_None; eassumption.
        * match goal with
          | H: _ |- _ => eapply H
          end.
          unfold related'.
          eexists _, _, (map.put hlArgRegs a v), (map.put llArgRegs start v), _, (v :: argvals).
          repeat match goal with
                 | |- exists _, _ => eexists
                 | |- _ /\ _ => split
                 | |- _ => eassumption || reflexivity
                 end.
          -- eapply map.of_list_zip_cons_put; eassumption.
          -- cbn -[map.of_list_zip Z.add]. eapply map.of_list_zip_cons_put.
             ++ eapply not_In_Z_seq. blia.
             ++ rewrite Z.add_comm. eassumption.
          -- (* might need to also say that some lArgRegs are on in stackwords? *)
             case TODO.
          -- case TODO.
      + eapply exec.set.
        * edestruct (eq_sep_to_split l2') as (l2Rest & S22 & SP22). 1: ecancel_assumption.
          eapply map.get_split_grow_r. 1: eassumption.
          apply sep_assoc in H1p8.
          unfold sep in H1p8 at 1. destruct H1p8 as (lRegs' & lStack' & S2 & ? & ?).
          subst lRegs'.
          eapply map.get_split_l. 1: exact S2. 2: exact G.
          case TODO.
        * match goal with
          | H: _ |- _ => eapply H
          end.
          unfold related'.
          case TODO.
  Qed.

  Lemma grow_related_mem: forall maxvar frame t1 mSmall1 l1 t2 mSmall2 l2 mStack mCombined2 fpval,
      related maxvar frame fpval t1 mSmall1 l1 t2 mSmall2 l2 ->
      map.split mCombined2 mSmall2 mStack ->
      exists mCombined1, map.split mCombined1 mSmall1 mStack /\
                         related maxvar frame fpval t1 mCombined1 l1 t2 mCombined2 l2.
  Proof.
    unfold related, map.split. intros. fwd.
    eexists. ssplit. 1: reflexivity.
    { unfold sep, map.split in Hp1. fwd.
      eapply map.disjoint_putmany_l in H0p1. apply proj1 in H0p1.
      eapply map.disjoint_putmany_l in H0p1. apply proj1 in H0p1.
      assumption. }
    do 3 eexists. ssplit; try eassumption || reflexivity.
    replace (eq (map.putmany mSmall1 mStack) * word_array fpval stackwords * frame)%sep
      with (eq (map.putmany mSmall1 mStack) * (word_array fpval stackwords * frame))%sep. 2: {
      symmetry. eapply iff1ToEq. apply sep_assoc.
    }
    replace (eq mSmall1 * word_array fpval stackwords * frame)%sep with
        (eq mSmall1 * (word_array fpval stackwords * frame))%sep in Hp1. 2: {
     symmetry. eapply iff1ToEq. apply sep_assoc.
    }
    forget (word_array fpval stackwords * frame)%sep as R.
    unfold sep, map.split in Hp1|-*. fwd.
    assert (map.disjoint mStack mq) as D. {
      apply map.disjoint_putmany_l in H0p1. apply proj2 in H0p1. apply map.disjoint_comm. exact H0p1.
    }
    do 2 eexists. ssplit. 4: eassumption.
    3: reflexivity.
    - rewrite <- (map.putmany_assoc mp mStack). rewrite (map.putmany_comm mStack mq) by exact D.
      rewrite map.putmany_assoc. reflexivity.
    - apply map.disjoint_putmany_l. auto.
  Qed.

  Lemma shrink_related_mem: forall maxvar frame t1 m1 l1 t2 m2 l2 mRemove m1Small fpval,
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      map.split m1 m1Small mRemove ->
      exists m2Small, map.split m2 m2Small mRemove /\
                      related maxvar frame fpval t1 m1Small l1 t2 m2Small l2.
  Proof.
    unfold related, map.split. intros. fwd.
    replace (eq (map.putmany m1Small mRemove) * word_array fpval stackwords * frame)%sep
      with (eq (map.putmany m1Small mRemove) * (word_array fpval stackwords * frame))%sep in Hp1. 2: {
      symmetry. eapply iff1ToEq. apply sep_assoc.
    }
    set (R := (word_array fpval stackwords * frame)%sep) in *.
    unfold sep, map.split in Hp1. fwd.
    apply map.disjoint_putmany_l in Hp1p0p1. destruct Hp1p0p1 as (D' & D).
    eexists. ssplit.
    { rewrite <- map.putmany_assoc. rewrite (map.putmany_comm mRemove mq) by exact D.
      rewrite map.putmany_assoc. reflexivity. }
    { apply map.disjoint_putmany_l. split. 1: assumption. apply map.disjoint_comm. assumption. }
    do 3 eexists. ssplit; try eassumption || reflexivity.
    replace (eq m1Small * word_array fpval stackwords * frame)%sep
      with (eq m1Small * (word_array fpval stackwords * frame))%sep. 2: {
      symmetry. eapply iff1ToEq. apply sep_assoc.
    }
    subst R.
    unfold sep, map.split.
    do 2 eexists. ssplit. 4: eassumption.
    1,3: reflexivity. assumption.
  Qed.

  Lemma spilling_correct (e1 e2 : env) (Ev : spill_functions e1 = Some e2)
        (s1 : stmt)
        (t1 : Semantics.trace)
        (m1 : mem)
        (l1 : locals)
        (mc1 : MetricLog)
        (post : Semantics.trace -> mem -> locals -> MetricLog -> Prop):
    exec e1 s1 t1 m1 l1 mc1 post ->
    forall (frame : mem -> Prop) (maxvar : Z),
      valid_vars_src maxvar s1 ->
      forall (t2 : Semantics.trace) (m2 : mem) (l2 : locals) (mc2 : MetricLog) (fpval : word),
        related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
        exec e2 (spill_stmt s1) t2 m2 l2 mc2
             (fun (t2' : Semantics.trace) (m2' : mem) (l2' : locals) (mc2' : MetricLog) =>
                exists t1' m1' l1' mc1',
                  related maxvar frame fpval t1' m1' l1' t2' m2' l2' /\
                  post t1' m1' l1' mc1').
  Proof.
    induction 1; intros; cbn [spill_stmt valid_vars_src Forall_vars_stmt] in *; fwd.
    - (* exec.interact *)
      case TODO. (*
      unfold related in *. fwd.
      spec (subst_split (ok := mem_ok) m) as A.
      1: eassumption. 1: ecancel_assumption.
      edestruct (@sep_def _ _ _ m2 (eq mGive)) as (mGive' & mKeepL & B & ? & C).
      1: ecancel_assumption.
      subst mGive'.
      rename H3p0 into FR, H3p1 into FA.
      unfold sep in H4p3. destruct H4p3 as (lRegs' & lStack' & S2 & ? & ?). subst lRegs' lStack'.
      spec (map.getmany_of_list_zip_shrink l) as R. 1,2: eassumption. {
        intros k HI. destr (map.get lStack k); [exfalso|reflexivity].
        specialize H4p2 with (1 := E).
        eapply Forall_forall in FA. 2: exact HI. clear -H4p2 FA. blia.
      }
      edestruct (eq_sep_to_split l2) as (l2Rest & S22 & SP22). 1: ecancel_assumption.
      eapply @exec.interact with (mGive := mGive).
      + eapply map.split_comm. exact B.
      + eapply map.getmany_of_list_zip_grow. 2: exact R. 1: exact S22.
      + eassumption.
      + intros.
        match goal with
        | H: context[outcome], A: context[outcome] |- _ =>
          specialize H with (1 := A); move H at bottom
        end.
        fwd.
        rename l into l1, l' into l1'.
        pose proof H2p0 as P.
        eapply map.putmany_of_list_zip_split in P. 2: eassumption. 2: {
          eapply Forall_impl. 2: eassumption.
          simpl.
          intros.
          destr (map.get lStack a). 2: reflexivity.
          match goal with
          | H: forall _, _ |- _ => specialize H with (1 := E)
          end.
          blia.
        }
        destruct P as (lRegs' & Spl1' & P).
        pose proof P as P0.
        eapply map.putmany_of_list_zip_grow with (l := l2) in P. 2: eassumption. 2: {
          eapply Forall_impl. 2: eassumption.
          clear -localsOk SP22. unfold fp, arg_regs, tmp1, tmp2 in *. intros.
          unfold sep, ptsto, map.split in *. fwd.
          rewrite ?map.get_putmany_dec, ?map.get_put_dec, ?map.get_empty.
          repeat destruct_one_match; try congruence; repeat destruct_one_match_hyp; try congruence; try blia.
          destr (map.get mp a). 2: reflexivity.
          specialize SP22p1 with (1 := E1). blia.
        }
        destruct P as (l2' & ? & ?).
        eexists. split. 1: eassumption.
        intros.
        repeat match goal with
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               end.
        1: reflexivity.
        8: eapply H2p1.
        6: eassumption.
        6: eassumption.
        4: solve [unfold sep; eauto].
        4: {
          enough ((eq lRegs' * (arg_regs * ptsto fp fpval))%sep l2') as En. 1: ecancel_assumption.
          unfold sep at 1. eauto. }
        { eenough ((eq _ * (word_array fpval stackwords * frame))%sep m') as En.
          1: ecancel_assumption.
          move C before H5.
          eapply grow_eq_sep. 1: exact C. eassumption. }
        { intros x v G.
          edestruct map.putmany_of_list_zip_find_index. 1: exact P0. 1: exact G.
          - fwd. apply nth_error_In in H6p0. eapply Forall_forall in FR. 1: exact FR. assumption.
          - eauto. }
        { assumption. }
        { unfold map.split. split; [reflexivity|].
          move C at bottom. move H5 at bottom.
          unfold sep at 1 in C. destruct C as (mKeepL' & mRest & SC & ? & _). subst mKeepL'.
          unfold map.split in H5. fwd.
          eapply map.shrink_disjoint_l; eassumption. }
          *)

    - (* exec.call *)
      rename H4p0 into FR, H4p1 into FA.
      unfold spill_functions in Ev.
      eapply map.map_all_values_fw in Ev; try typeclasses eauto. 2: eassumption.
      unfold spill_fun in Ev. fwd.
      eapply exec.seq_cps.
      apply_in_hyps @map.getmany_of_list_length.
      apply_in_hyps @map.putmany_of_list_zip_sameLength.
      eapply write_register_range_correct; try eassumption || (unfold a0, a7 in *; blia).
      1: case TODO.
      match goal with
      | H: related _ _ _ _ _ _ _ _ _ |- _ => clear H
      end.
      intros.
      assert (bytes_per_word = 4 \/ bytes_per_word = 8) as B48. {
        unfold bytes_per_word. destruct width_cases as [E' | E']; rewrite E'; cbv; auto.
      }
      eapply exec.seq_cps.
      assert (length (List.firstn (length params) (reg_class.all reg_class.arg)) = length argvs) as L. {
        rewrite List.firstn_length. change (length (reg_class.all reg_class.arg)) with 8%nat. blia.
      }
      eapply map.sameLength_putmany_of_list in L.
      destruct L as (st' & P).
      (* TODO read_register_range
      eapply exec.call_cps; try eassumption. {
        rewrite arg_regs_alt; assumption.
      }

      unfold spill_fbody.
      eapply exec.stackalloc. {
        rewrite Z.mul_comm.
        apply Z_mod_mult.
      }
      intros *. intros A Sp.
      destruct (anybytes_to_array_1 (mem_ok := mem_ok) _ _ _ A) as (bytes & Pt & L).
      edestruct (byte_list_to_word_list_array bytes) as (words & L' & F). {
        rewrite L.
        unfold Memory.ftprint.
        rewrite Z2Nat.id by blia.
        destr (0 <=? (max_var fbody - 31)).
        - rewrite Z2Nat.id by assumption. rewrite Z.mul_comm. apply Z_mod_mult.
        - replace (Z.of_nat (Z.to_nat (max_var fbody - 31))) with 0 by blia.
          rewrite Z.mul_0_r.
          apply Zmod_0_l.
      }
      eapply F in Pt.
      unfold related in *. fwd.
      unfold sep in H4p5. destruct H4p5 as (lRegs' & lStack' & S2 & ? & ?). subst lRegs' lStack'.

      eapply exec.weaken. {
        eapply IHexec with (fpval := a). 1: eassumption.
        (* after running stackalloc on a state whose locals only contain the function args,
           `related` required to call the IH holds: *)
        (* TODO need to split params into those on stack and those in registers *)
        eexists map.empty, st0, words. ssplit.
        { reflexivity. }
        { eapply join_sep. 1: exact Sp. 1: exact H4p0. 1: exact Pt.
          unfold word_array at 2. ecancel. }
        { intros x v G.
          eapply map.putmany_of_list_zip_find_index in H1. 2: exact G.
          rewrite map.get_empty in H1. destruct H1. 2: discriminate. fwd.
          apply nth_error_In in H1p0.

          Search params.

          eapply Forall_forall in Evp1. ; eassumption. }
        { intros x v G. rewrite map.get_empty in G. discriminate. }
        { unfold sep. exists st0, map.empty. ssplit; eauto. apply map.split_empty_r. reflexivity. }
        { unfold arg_regs, sep.
          repeat eexists.
          - rewrite <- map.put_putmany_commute. do 2 rewrite map.putmany_empty_r. reflexivity.
          - rewrite map.putmany_empty_r. unfold map.disjoint. intros *. intros G1 G2.
            rewrite map.get_put_dec in G2. destruct_one_match_hyp.
            2: { rewrite map.get_empty in G2. discriminate. }
            subst k. fwd.
            eapply map.putmany_of_list_zip_find_index in H1. 2: exact G1.
            rewrite map.get_empty in H1. destruct H1. 2: discriminate. fwd.
            apply nth_error_In in H1p0.
            eapply Forall_forall in Evp1. 2: eassumption. blia.
          - eapply map.disjoint_empty_r.
          - intros k v G. rewrite map.get_empty in G. discriminate. }
        { intros. rewrite map.get_empty in H5. discriminate. }
        { apply (f_equal Z.to_nat) in L'. rewrite Nat2Z.id in L'. rewrite L'. rewrite L.
          clear -B48. (* <- LIA performance *)
          Z.div_mod_to_equations. blia. }
      }
      cbv beta. intros. fwd.
      clear dependent m2'. clear mc2'. rename P into P0.
      (* according to the IH, executing the spilled function body results in a state that
         is related to a high-level state that satisfies the `outcome` postcondition,
         and now we have to use this information to prove that if we remove the additional
         stack provided by exec.stackalloc and store the result vars back into the caller's
         var map, states are still related and postcondition holds *)
      rename t' into t2', m' into m2', st0 into st2, l' into st2', mc' into mc2', l into l1, l1' into st1'.
      match goal with
      | H: context[outcome], A: context[outcome] |- _ =>
        specialize H with (1 := A); move H at bottom; rename H into Q
      end.
      fwd. rename l' into l1'.
      pose proof Qp1 as P.
      eapply map.putmany_of_list_zip_split in P. 2: eassumption. 2: {
        eapply Forall_impl. 2: eassumption.
        simpl.
        intros.
        destruct (map.get lStack a0) eqn: EG. 2: reflexivity.
        match goal with
        | H: forall _, _ |- _ => specialize H with (1 := EG)
        end.
        blia.
      }
      destruct P as (lRegs' & Spl1' & P).
      pose proof P as P0.
      eapply map.putmany_of_list_zip_grow with (l := l2) in P. 2: eassumption. 2: {
        eapply Forall_impl. 2: eassumption.
        clear -localsOk SP22. unfold fp, arg_regs, tmp1, tmp2 in *. intros.
        unfold sep, ptsto, map.split in *. fwd.
        rewrite ?map.get_putmany_dec, ?map.get_put_dec, ?map.get_empty.
        repeat destruct_one_match; try congruence; repeat destruct_one_match_hyp; try congruence; try blia.
        destr (map.get mp a). 2: reflexivity.
        specialize SP22p1 with (1 := E1). blia.
      }
      destruct P as (l2' & ? & ?).
      clear IHexec. unfold related in *. fwd.
      unfold sep in H4p0p3. destruct H4p0p3 as (lRegs0' & lStack0' & S2' & ? & ?). subst lRegs0' lStack0'.
      spec (map.getmany_of_list_zip_shrink st1') as GM. 1,2: eassumption. {
        intros k HI. destr (map.get lStack0 k); [exfalso|reflexivity].
        specialize H4p0p2 with (1 := E).
        move Evp2 at bottom.
        eapply Forall_forall in Evp2. 2: exact HI. clear -H4p0p2 Evp2. blia.
      }
      edestruct (eq_sep_to_split st2') as (st2Rest' & S22' & SP22').
      1: ecancel_assumption.
      assert (((eq m1' * word_array fpval stackwords * frame) * word_array a stackwords0)%sep m2') as M
          by (simpl; ecancel_assumption).
      unfold sep at 1 in M. destruct M as (m2Small' & mStack' & Sp' & M1 & M2).
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             end.
      13: eassumption.
      4: eassumption.
      3: { eapply map.getmany_of_list_zip_grow. 2: exact GM. 1: exact S22'. }
      4: exact M1.
      2: exact Sp'.
      1: {
        eapply cast_word_array_to_bytes in M2.
        eapply array_1_to_anybytes in M2.
        match goal with
        | H: Memory.anybytes a ?LEN1 mStack' |-
          Memory.anybytes a ?LEN2 mStack' => replace LEN2 with LEN1; [exact H|]
        end.
        erewrite List.flat_map_const_length. 2: {
          intros w. rewrite HList.tuple.length_to_list. reflexivity.
        }
        simpl. blia. }
      1: reflexivity.
      3: {
        unfold sep. eauto.
      }
      3: {
        eapply join_sep. 1: eassumption. 2: exact SP22. 2: ecancel. reflexivity.
      }
      { intros x v G.
        destr (map.get lRegs x). 1: solve[eauto].
        eapply map.putmany_of_list_zip_to_putmany in P0. destruct P0 as (retmap & P0 & ?). subst lRegs'.
        rewrite map.get_putmany_dec in G. rewrite E in G. fwd.
        eapply Forall_forall in FR. 1: exact FR.
        eapply map.putmany_of_list_zip_to_In; eassumption. }
      all: assumption.
      *)
      case TODO.

    - (* exec.load *)
      eapply exec.seq_cps.
      eapply load_iarg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H3. intros.
      eapply exec.seq_cps.
      pose proof H2 as A. unfold related in A. fwd.
      unfold Memory.load, Memory.load_Z, Memory.load_bytes in *. fwd.
      eapply exec.load. {
        rewrite map.get_put_same. reflexivity. }
      { edestruct (@sep_def _ _ _ m2 (eq m)) as (m' & m2Rest & Sp & ? & ?).
        1: ecancel_assumption. unfold map.split in Sp. fwd.
        unfold Memory.load, Memory.load_Z, Memory.load_bytes.
        erewrite map.getmany_of_tuple_in_disjoint_putmany; eauto. }
      eapply save_ires_reg_correct.
      + eassumption.
      + eassumption.
      + blia.
    - (* exec.store *)
      eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H4. intros.
      eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H3. intros.
      pose proof H3 as A. unfold related in A. fwd.
      unfold Memory.store, Memory.store_Z, Memory.store_bytes in *. fwd.
      edestruct (@sep_def _ _ _ m2 (eq m)) as (m' & m2Rest & Sp & ? & ?).
      1: ecancel_assumption. unfold map.split in Sp. fwd.
      eapply exec.store.
      1: eapply get_iarg_reg_1; eauto with zarith.
      1: apply map.get_put_same.
      { unfold Memory.store, Memory.store_Z, Memory.store_bytes.
        unfold Memory.load_bytes in *.
        erewrite map.getmany_of_tuple_in_disjoint_putmany; eauto. }
      do 4 eexists. split. 2: eassumption.
      unfold related.
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             end.
      all: try eassumption || reflexivity.
      spec store_bytes_sep_hi2lo as A. 1: eassumption.
      all: ecancel_assumption.
    - (* exec.inlinetable *)
      eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H4. intros.
      eapply exec.seq_cps.
      eapply exec.inlinetable.
      { unfold ires_reg, iarg_reg, spill_tmp, fp, a0, a7 in *. destr (32 <=? x); destr (32 <=? i); try blia. }
      { rewrite map.get_put_same. reflexivity. }
      { eassumption. }
      eapply save_ires_reg_correct.
      + eassumption.
      + eassumption.
      + blia.
    - (* exec.stackalloc *)
      rename H1 into IH.
      eapply exec.stackalloc. 1: assumption.
      intros.
      eapply exec.seq_cps.
      edestruct grow_related_mem as (mCombined1 & ? & ?). 1,2: eassumption.
      eapply save_ires_reg_correct''. 1: eassumption. 1: blia.
      intros.
      eapply exec.weaken. {
        eapply IH; eassumption. }
      cbv beta. intros. fwd.
      edestruct shrink_related_mem as (mSmall2 & ? & ?). 1,2: eassumption.
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             end.
      1,4,3,2: eassumption.
    - (* exec.lit *)
      eapply exec.seq_cps. eapply exec.lit.
      eapply save_ires_reg_correct.
      + eassumption.
      + eassumption.
      + blia.
    - (* exec.op *)
      eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H3. intros.
      eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H2. intros.
      eapply exec.seq_cps.
      eapply exec.op.
      1: eapply get_iarg_reg_1; eauto with zarith.
      1: apply map.get_put_same.
      eapply save_ires_reg_correct.
      + eassumption.
      + eassumption.
      + blia.
    - (* exec.set *)
      eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
      clear mc2 H2. intros.
      eapply exec.seq_cps.
      eapply exec.set. 1: apply map.get_put_same.
      eapply save_ires_reg_correct.
      + eassumption.
      + eassumption.
      + blia.
    - (* exec.if_true *)
      unfold prepare_bcond. destr cond; cbn [ForallVars_bcond eval_bcond spill_bcond] in *; fwd.
      + eapply exec.seq_assoc.
        eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
        clear mc2 H2. intros.
        eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
        clear mc2. intros.
        eapply exec.if_true. {
          cbn. erewrite get_iarg_reg_1 by eauto with zarith. rewrite map.get_put_same. congruence.
        }
        eapply IHexec; eassumption.
      + eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
        clear mc2 H2. intros.
        eapply exec.if_true. {
          cbn. rewrite map.get_put_same. congruence.
        }
        eapply IHexec; eassumption.
    - (* exec.if_false *)
      unfold prepare_bcond. destr cond; cbn [ForallVars_bcond eval_bcond spill_bcond] in *; fwd.
      + eapply exec.seq_assoc.
        eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
        clear mc2 H2. intros.
        eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
        clear mc2. intros.
        eapply exec.if_false. {
          cbn. erewrite get_iarg_reg_1 by eauto with zarith. rewrite map.get_put_same. congruence.
        }
        eapply IHexec; eassumption.
      + eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
        clear mc2 H2. intros.
        eapply exec.if_false. {
          cbn. rewrite map.get_put_same. congruence.
        }
        eapply IHexec; eassumption.
    - (* exec.loop *)
      rename IHexec into IH1, H3 into IH2, H5 into IH12.
      eapply exec.loop_cps.
      eapply exec.seq.
      1: eapply IH1; eassumption.
      cbv beta. intros. fwd.
      unfold prepare_bcond. destr cond; cbn [ForallVars_bcond] in *; fwd.
      + specialize H0 with (1 := H3p1). cbn in H0. fwd.
        eapply exec.seq. {
          eapply load_iarg_reg_correct''; (blia || eassumption || idtac).
        }
        cbv beta. intros. fwd.
        eapply exec.weaken. {
          eapply load_iarg_reg_correct''; (blia || eassumption || idtac).
        }
        cbv beta. intros. fwd. cbn [eval_bcond spill_bcond].
        erewrite get_iarg_reg_1 by eauto with zarith.
        rewrite map.get_put_same. eexists. split; [reflexivity|].
        split; intros.
        * do 4 eexists. split.
          -- exact H3p6.
          -- eapply H1. 1: eassumption. cbn. rewrite E, E0. congruence.
        * eapply exec.weaken. 1: eapply IH2.
          -- eassumption.
          -- cbn. rewrite E, E0. congruence.
          -- eassumption.
          -- eassumption.
          -- cbv beta. intros. fwd. eauto 10. (* IH12 *)
      + specialize H0 with (1 := H3p1). cbn in H0. fwd.
        eapply exec.weaken. {
          eapply load_iarg_reg_correct''; (blia || eassumption || idtac).
        }
        cbv beta. intros. fwd. cbn [eval_bcond spill_bcond].
        rewrite map.get_put_same. eexists. split; [reflexivity|].
        split; intros.
        * do 4 eexists. split.
          -- exact H3p5.
          -- eapply H1. 1: eassumption. cbn. rewrite E. congruence.
        * eapply exec.weaken. 1: eapply IH2.
          -- eassumption.
          -- cbn. rewrite E. congruence.
          -- eassumption.
          -- eassumption.
          -- cbv beta. intros. fwd. eauto 10. (* IH12 *)
    - (* exec.seq *)
      cbn in *. fwd.
      rename H1 into IH2, IHexec into IH1.
      eapply exec.seq.
      + eapply IH1. 1: eassumption. eauto 15.
      + cbn. intros. fwd. eapply IH2. 1,2: eassumption. eauto 15.
    - (* exec.skip *)
      eapply exec.skip. eauto 20.
    Unshelve.
    all: try exact word.eqb.
    all: try unshelve eapply word.eqb_spec.
    all: simpl.
    all: try typeclasses eauto.
    all: try exact (fun (_: mem) => True).
    all: try exact map.empty.
  Qed.

End Spilling.
