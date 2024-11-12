Require Import compiler.util.Common.
Require Import bedrock2.LeakageSemantics.
Require Import bedrock2.Map.SeparationLogic.
Require Import compiler.FlatImp.
Require Import Coq.Init.Wf Wellfounded.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import riscv.Utility.Utility.
Require Import coqutil.Map.MapEauto.
Require Import coqutil.Tactics.Simp.
Require Import compiler.CustomFix.
Require Import compiler.Registers.
Require Import compiler.SeparationLogic.
Require Import compiler.SpillingMapGoals.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.MetricCosts.
Require Import compiler.FlatImpConstraints.
Require Import coqutil.Tactics.autoforward.
Require Import coqutil.Tactics.fwd.

Open Scope Z_scope.

Section Spilling.

  Notation stmt := (stmt Z).
  Notation execpre pick_sp := (exec (pick_sp := pick_sp) PreSpill isRegZ).
  Notation execpost pick_sp := (exec (pick_sp := pick_sp) PostSpill isRegZ).

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

  Definition leak_load_iarg_reg(fpval: word) (r: Z): leakage :=
    match stack_loc r with
    | Some o => [leak_word (word.add fpval (word.of_Z o))]
    | None => nil
    end.

  Definition save_ires_reg(r: Z): stmt :=
    match stack_loc r with
    | Some o => SStore Syntax.access_size.word fp (spill_tmp 1) o
    | None => SSkip
    end.

  Definition leak_save_ires_reg(fpval: word) (r: Z) : leakage :=
    match stack_loc r with
    | Some o => [leak_word (word.add fpval (word.of_Z o))]
    | None => nil
    end.

  Notation "s1 ;; s2" := (SSeq s1 s2) (right associativity, at level 60).

  (* reg must be <32, var might be >= 32 *)
  Definition set_reg_to_var(reg var: Z): stmt :=
    match stack_loc var with
    | Some o => SLoad Syntax.access_size.word reg fp o
    | None => SSet reg var
    end.

  Definition leak_set_reg_to_var(fpval: word) (var: Z) : leakage :=
    match stack_loc var with
    | Some o => [leak_word (word.add fpval (word.of_Z o))]
    | None => nil
    end.

  Fixpoint set_reg_range_to_vars(range_start: Z)(srcs: list Z): stmt :=
    match srcs with
    | nil => SSkip
    | x :: xs => set_reg_range_to_vars (range_start+1) xs;; set_reg_to_var range_start x
    end.
  
  Fixpoint leak_set_reg_range_to_vars(fpval: word)(srcs: list Z) : leakage :=
    match srcs with
    | nil => nil
    | x :: xs => leak_set_reg_range_to_vars fpval xs ++ leak_set_reg_to_var fpval x
    end.

  (* var might be >=32, reg must be < 32 *)
  Definition set_var_to_reg(var reg: Z): stmt :=
    match stack_loc var with
    | Some o => SStore Syntax.access_size.word fp reg o
    | None => SSet var reg
    end.

  Definition leak_set_var_to_reg(fpval: word) (var: Z) : leakage :=
    match stack_loc var with
    | Some o => [leak_word (word.add fpval (word.of_Z o))]
    | None => nil
    end.

  Fixpoint set_vars_to_reg_range(dests: list Z)(range_start: Z): stmt :=
    match dests with
    | nil => SSkip
    | x :: xs => set_var_to_reg x range_start;; set_vars_to_reg_range xs (range_start+1)
    end.

  Fixpoint set_vars_to_reg_range_tailrec(do_first: stmt)(dests: list Z)(range_start: Z): stmt :=
    match dests with
    | nil => do_first
    | x :: xs => set_vars_to_reg_range_tailrec
                   (do_first;; set_var_to_reg x range_start) xs (range_start+1)
    end.

  Fixpoint leak_set_vars_to_reg_range(fpval: word) (dests: list Z) : leakage :=
    match dests with
    | nil => nil
    | x :: xs => leak_set_var_to_reg fpval x ++ leak_set_vars_to_reg_range fpval xs
    end.

  Definition prepare_bcond(c: bcond Z): stmt :=
    match c with
    | CondBinary _ x y => load_iarg_reg 1 x;; load_iarg_reg 2 y
    | CondNez x => load_iarg_reg 1 x
    end.

  Definition leak_prepare_bcond(fpval: word) (c: bcond Z) : leakage :=
    match c with
    | CondBinary _ x y => leak_load_iarg_reg fpval x ++ (leak_load_iarg_reg fpval y)
    | CondNez x => leak_load_iarg_reg fpval x
    end.

  Definition spill_bcond(c: bcond Z): bcond Z :=
    match c with
    | CondBinary op x y => CondBinary op (iarg_reg 1 x) (iarg_reg 2 y)
    | CondNez x => CondNez (iarg_reg 1 x)
    end.

  Definition leak_spill_bcond : leakage := nil.

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
    | SOp x op y oz =>
      load_iarg_reg 1 y;;
      match oz with
      | Var z => load_iarg_reg 2 z;; SOp (ires_reg x) op (iarg_reg 1 y) (Var (iarg_reg 2 z))
      | Const _ =>  SOp (ires_reg x) op (iarg_reg 1 y) oz
      end;; save_ires_reg x
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
      set_reg_range_to_vars a0 argvars;;
      SCall (List.firstn (length resvars) (reg_class.all reg_class.arg))
            f
            (List.firstn (length argvars) (reg_class.all reg_class.arg));;
      set_vars_to_reg_range resvars a0
    | SInteract resvars f argvars =>
      set_reg_range_to_vars a0 argvars;;
      SInteract (List.firstn (length resvars) (reg_class.all reg_class.arg))
                f
                (List.firstn (length argvars) (reg_class.all reg_class.arg));;
      set_vars_to_reg_range resvars a0
    end.

  Definition tuple : Type := stmt * leakage * leakage * word * (leakage -> leakage -> leakage * word).

  Definition project_tuple (tup : tuple) : nat * stmt :=
    let '(s, k, sk_so_far, fpval, f) := tup in (length k, s).
  Definition lt_tuple (x y : tuple) :=
    lt_tuple' (project_tuple x) (project_tuple y).    

  Lemma lt_tuple_wf : well_founded lt_tuple.
  Proof.
    cbv [lt_tuple]. apply wf_inverse_image. apply lt_tuple'_wf.
  Defined.

  Definition stmt_leakage_body
    {env: map.map String.string (list Z * list Z * stmt)}
    (e: env)
    (pick_sp : leakage -> word)
    (tup : stmt * leakage * leakage * word * (leakage (*skip*) -> leakage (*sk_so_far*) -> leakage * word))
    (stmt_leakage : forall othertup, lt_tuple othertup tup -> leakage * word)
    : leakage * word.
    refine (
        match tup as x return tup = x -> _ with
        | (s, k, sk_so_far, fpval, f) =>
            fun _ =>
              match s as x return s = x -> _ with
              | SLoad sz x y o =>
                  fun _ =>
                    match k with
                    | leak_word addr :: k' =>
                        f [leak_word addr] (sk_so_far ++ leak_load_iarg_reg fpval y ++ [leak_word addr] ++ leak_save_ires_reg fpval x)
                    | _ => (nil, word.of_Z 0)
                    end
              | SStore sz x y o =>
                  fun _ =>
                    match k with
                    | leak_word addr :: k' =>
                        f [leak_word addr] (sk_so_far ++ leak_load_iarg_reg fpval x ++ leak_load_iarg_reg fpval y ++ [leak_word addr])
                    | _ => (nil, word.of_Z 0)
                    end
              | SInlinetable _ x _ i =>
                  fun _ =>
                    match k with
                    | leak_word i' :: k' =>
                        f [leak_word i'] (sk_so_far ++ leak_load_iarg_reg fpval i ++ [leak_word i'] ++ leak_save_ires_reg fpval x)
                    | _ => (nil, word.of_Z 0)
                    end
              | SStackalloc x z body =>
                  fun _ =>
                    match k as x return k = x -> _ with
                    | _ :: k' =>
                        fun _ =>
                          stmt_leakage (body, k', sk_so_far ++ leak_unit :: leak_save_ires_reg fpval x, fpval, fun skip => f (leak_unit :: skip)) _
                    | nil =>
                        fun _ =>
                          (nil, pick_sp (rev sk_so_far))
                    end eq_refl
              | SLit x _ =>
                  fun _ =>
                    f [] (sk_so_far ++ leak_save_ires_reg fpval x)
              | SOp x op y oz =>
                  fun _ =>
                    let newt_a' :=
                      match op with
                      | Syntax.bopname.divu
                      | Syntax.bopname.remu =>
                          match k with
                          | leak_word x1 :: leak_word x2 :: k' => Some ([leak_word x1; leak_word x2], k')
                          | _ => None
                          end
                      | Syntax.bopname.slu
                      | Syntax.bopname.sru
                      | Syntax.bopname.srs =>
                          match k with
                          | leak_word x2 :: k' => Some ([leak_word x2], k')
                          | _ => None
                          end
                      | _ => Some ([], k)
                      end
                    in
                    match newt_a' with
                    | Some (newt, a') =>
                        f newt
                          (sk_so_far ++
                             leak_load_iarg_reg fpval y ++
                             match oz with 
                             | Var z => leak_load_iarg_reg fpval z
                             | Const _ => []
                             end
                             ++ newt
                             ++ leak_save_ires_reg fpval x)
                    | None => (nil, word.of_Z 0)
                    end
              | SSet x y =>
                  fun _ =>
                    f [] (sk_so_far ++ leak_load_iarg_reg fpval y ++ leak_save_ires_reg fpval x)
              | SIf c thn els =>
                  fun _ =>
                    match k as x return k = x -> _ with
                    | leak_bool b :: k' =>
                        fun _ =>
                          stmt_leakage (if b then thn else els,
                              k',
                              sk_so_far ++ leak_prepare_bcond fpval c ++ leak_spill_bcond ++ [leak_bool b],
                              fpval,
                              (fun skip => f (leak_bool b :: skip))) _
                    | _ => fun _ => (nil, word.of_Z 0)
                    end eq_refl
              | SLoop s1 c s2 =>
                  fun _ =>
                    stmt_leakage (s1, k, sk_so_far, fpval,
                        (fun skip sk_so_far' =>
                           Let_In_pf_nd (List.skipn (length skip) k)
                             (fun k' _ =>
                                match k' as x return k' = x -> _ with
                                | leak_bool true :: k'' =>
                                    fun _ =>
                                      stmt_leakage (s2, k'', sk_so_far' ++ leak_prepare_bcond fpval c ++ leak_spill_bcond ++ [leak_bool true], fpval, 
                                          (fun skip' sk_so_far'' =>
                                             let k''' := List.skipn (length skip') k'' in
                                             stmt_leakage (s, k''', sk_so_far'', fpval,
                                                 (fun skip'' => f (skip ++ leak_bool true :: skip' ++ skip''))) _)) _
                                | leak_bool false :: k'' =>
                                    fun _ =>
                                      f (skip ++ [leak_bool false]) (sk_so_far' ++ leak_prepare_bcond fpval c ++ leak_spill_bcond ++ [leak_bool false])
                                | _ => fun _ => (nil, word.of_Z 0)
                                end eq_refl))) _
              | SSeq s1 s2 =>
                  fun _ =>
                    stmt_leakage (s1, k, sk_so_far, fpval,
                        (fun skip sk_so_far' =>
                           let k' := List.skipn (length skip) k in
                           stmt_leakage (s2, k', sk_so_far', fpval, (fun skip' => f (skip ++ skip'))) _)) _
              | SSkip => fun _ => f [] sk_so_far
              | SCall resvars fname argvars =>
                  fun _ =>
                    match k as x return k = x -> _ with
                    | leak_unit :: k' =>
                        fun _ =>
                          match @map.get _ _ env e fname with
                          | Some (params, rets, fbody) =>
                              let sk_before_salloc := sk_so_far ++ leak_set_reg_range_to_vars fpval argvars ++ [leak_unit] in
                              let fpval' := pick_sp (rev sk_before_salloc) in
                              stmt_leakage (fbody,
                                  k',
                                  sk_before_salloc ++ leak_unit :: leak_set_vars_to_reg_range fpval' params,
                                  fpval',
                                  (fun skip sk_so_far' =>
                                     let k'' := List.skipn (length skip) k' in
                                       f (leak_unit :: skip) (sk_so_far' ++ leak_set_reg_range_to_vars fpval' rets ++ leak_set_vars_to_reg_range fpval resvars))) _
                          | None => (nil, word.of_Z 0)
                          end
                    | _ => fun _ => (nil, word.of_Z 0)
                    end eq_refl
              | SInteract resvars _ argvars =>
                  fun _ =>
                    match k with
                    | leak_list l :: k' =>
                          f [leak_list l] (sk_so_far ++ leak_set_reg_range_to_vars fpval argvars ++ [leak_list l] ++ leak_set_vars_to_reg_range fpval resvars)
                    | _ => (nil, word.of_Z 0)
                    end
              end eq_refl
        end%nat eq_refl).
  Proof.
    Unshelve.
      all: intros.
      all: cbv [lt_tuple project_tuple].
      all: subst.
      all: repeat match goal with
             | t := List.skipn ?n ?k |- _ =>
                      let H := fresh "H" in
                      assert (H := List.skipn_length n k); subst t end.
      all: try (right; constructor; constructor).
      all: try (left; constructor; constructor).
    - assert (H0 := skipn_length (length skip) k). left.
      rewrite H. assert (H1:= @f_equal _ _ (@length _) _ _ e3).
      simpl in H1. blia.
    - assert (H := skipn_length (length skip) k). left.
      assert (H1 := @f_equal _ _ (@length _) _ _ e3). simpl in H1. blia.
    - destruct (length (List.skipn (length skip) k) =? length k)%nat eqn:E.
      + apply Nat.eqb_eq in E. rewrite E. right. constructor. constructor.
      + apply Nat.eqb_neq in E. left. blia.
  Defined.

  Definition stmt_leakage
    {env: map.map String.string (list Z * list Z * stmt)} e pick_sp
    := Fix lt_tuple_wf _ (stmt_leakage_body e pick_sp).

  Definition Equiv (x y : tuple) :=
    let '(x1, x2, x3, x4, fx) := x in
    let '(y1, y2, y3, y4, fy) := y in
    (x1, x2, x3, x4) = (y1, y2, y3, y4) /\
      forall k sk,
        fx k sk = fy k sk.

  Lemma stmt_leakage_body_ext {env: map.map String.string (list Z * list Z * stmt)} e pick_sp :
    forall (x1 x2 : tuple)
           (f1 : forall y : tuple, lt_tuple y x1 -> leakage * word)
           (f2 : forall y : tuple, lt_tuple y x2 -> leakage * word),
      Equiv x1 x2 ->
      (forall (y1 y2 : tuple) (p1 : lt_tuple y1 x1) (p2 : lt_tuple y2 x2),
          Equiv y1 y2 -> f1 y1 p1 = f2 y2 p2) ->
      stmt_leakage_body e pick_sp x1 f1 =
        stmt_leakage_body e pick_sp x2 f2.
  Proof.
    intros. cbv [stmt_leakage_body]. cbv beta.
    destruct x1 as [ [ [ [s_1 k_1] sk_so_far_1] fpval_1] f_1].
    destruct x2 as [ [ [ [s_2 k_2] sk_so_far_2] fpval_2] f_2].
    cbv [Equiv] in H. destruct H as [H1 H2]. injection H1. intros. subst. clear H1.
    repeat (Tactics.destruct_one_match || rewrite H || apply H0 || cbv [Equiv] || intuition auto || match goal with | |- _ :: _ = _ :: _ => f_equal end || intuition auto(*why does putting this here make this work*)).
      apply Let_In_pf_nd_ext.
      repeat (Tactics.destruct_one_match || rewrite H || apply H0 || cbv [Equiv] || intuition auto || match goal with | |- _ :: _ = _ :: _ => f_equal end || intuition auto).
  Qed.

  Lemma sfix_step {env: map.map String.string (list Z * list Z * stmt)} e pick_sp tup :
    stmt_leakage e pick_sp tup = stmt_leakage_body e pick_sp tup (fun y _ => stmt_leakage e pick_sp y).
  Proof.
    cbv [stmt_leakage].
    apply (@Fix_eq'_nondep _ _ lt_tuple_wf _ (stmt_leakage_body e pick_sp) Equiv eq).
    { apply stmt_leakage_body_ext. }
    { cbv [Equiv]. destruct tup as [ [ [x1 x2] x3] fx]. intuition. }
  Qed.

  Lemma stmt_leakage_ext {env: map.map String.string (list Z * list Z * stmt)} e pick_sp x1 x2 :
    Equiv x1 x2 ->
    stmt_leakage e pick_sp x1 = stmt_leakage e pick_sp x2.
  Proof.
    revert x2. induction (lt_tuple_wf x1). intros. do 2 rewrite sfix_step.
    apply stmt_leakage_body_ext.
    - assumption.
    - intros. apply H0; assumption.
  Qed.

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
    | SOp x _ y oz => let vz := match oz with
                                | Var v => v
                                | Const _ => 0
                                end
                      in Z.max x (Z.max y vz)
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
      Forall_vars_stmt (fun x => fp < x /\ (x < a0 \/ a7 < x)) s ->
      Forall_vars_stmt (fun x => fp < x <= max_var s /\ (x < a0 \/ a7 < x)) s.
  Proof.
    induction s; simpl; intros; unfold ForallVars_bcond in *; simpl;
      repeat match goal with
             | H: _ /\ _ |- _ => destruct H
             | c: bcond _ |- _ => destruct c; simpl
             | |- _ /\ _ => split
             | y: operand |- _ => destruct y
             end;
      eauto 4 with max_var_sound.
    all: eapply Forall_and;
         [ eapply Forall_and;
           [ eapply Forall_impl; [|eassumption];
             cbv beta; intros; blia
           | eapply Forall_impl; [|eapply Forall_le_max];
             cbv beta; intros; blia ]
         | eapply Forall_impl; [|eassumption]; cbv beta; blia ].
  Qed.

  Open Scope bool_scope.

  Definition is_valid_src_var(x: Z): bool := Z.ltb fp x && (Z.ltb x a0 || Z.ltb a7 x).

  Definition spill_fun: list Z * list Z * stmt -> result (list Z * list Z * stmt) :=
    fun '(argnames, resnames, body) =>
      (* TODO these checks could also be put into Lang.(Valid), so that there are
         fewer reasons for the compiler to return None *)
      if List.forallb is_valid_src_var argnames &&
         List.forallb is_valid_src_var resnames &&
         forallb_vars_stmt is_valid_src_var body
      then
        if Nat.leb (List.length argnames) 8 && Nat.leb (List.length resnames) 8 then
          let argnames' := List.firstn (List.length argnames) (reg_class.all reg_class.arg) in
          let resnames' := List.firstn (List.length resnames) (reg_class.all reg_class.arg) in
          let maxvar := Z.max (max_var body)
                              (Z.max (fold_left Z.max argnames 0) (fold_left Z.max resnames 0)) in
          Success (argnames', resnames',
              (* `Z.of_nat (Z.to_nat _)` is to to make sure it's not negative.
              We might stackalloc 0 bytes, but that still writes fp, which is required to be
              set by `related`, and we don't want to complicate `related` to accommodate for a
              potentially uninitialized `fp` after a function call happens in a fresh locals env *)
              SStackalloc fp (bytes_per_word * Z.of_nat (Z.to_nat (maxvar - 31))) (
                set_vars_to_reg_range argnames a0;;
                spill_stmt body;;
                set_reg_range_to_vars a0 resnames
              ))
        else
          error:("Number of function arguments and return values must not exceed 8")
      else
        error:("Spilling got input program with invalid var names (please report as a bug)").

  Definition fun_leakage {env : map.map string (list Z * list Z * stmt)} (e : env) (pick_sp : leakage -> word) (f : list Z * list Z * stmt) (k : leakage) (sk_so_far : leakage) : leakage * word :=
    let '(argnames, resnames, body) := f in
    let fpval := pick_sp (rev sk_so_far) in
    stmt_leakage e pick_sp (body,
        k,
        sk_so_far ++ leak_unit :: leak_set_vars_to_reg_range fpval argnames,
        fpval,
        (fun skip sk_so_far' => (sk_so_far' ++ leak_set_reg_range_to_vars fpval resnames, word.of_Z 0))).

  Lemma firstn_min_absorb_length_r{A: Type}: forall (l: list A) n,
      List.firstn (Nat.min n (length l)) l = List.firstn n l.
  Proof.
    intros. destruct (Nat.min_spec n (length l)) as [[? E] | [? E]]; rewrite E.
    - reflexivity.
    - rewrite List.firstn_all. rewrite List.firstn_all2 by assumption. reflexivity.
  Qed.

  Lemma set_reg_range_to_vars_uses_standard_arg_regs: forall args start,
      uses_standard_arg_regs (set_reg_range_to_vars start args).
  Proof.
    induction args; intros; cbn; unfold set_reg_to_var;
      repeat destruct_one_match; cbn; eauto.
  Qed.

  Lemma set_vars_to_reg_range_uses_standard_arg_regs: forall args start,
      uses_standard_arg_regs (set_vars_to_reg_range args start).
  Proof.
    induction args; intros; cbn; unfold set_var_to_reg;
      repeat destruct_one_match; cbn; eauto.
  Qed.

  Lemma spill_stmt_uses_standard_arg_regs: forall s, uses_standard_arg_regs (spill_stmt s).
  Proof.
    induction s; simpl; unfold prepare_bcond, load_iarg_reg, save_ires_reg;
      repeat destruct_one_match; simpl;
      rewrite ?List.firstn_length, ?firstn_min_absorb_length_r;
      eauto using set_reg_range_to_vars_uses_standard_arg_regs,
                  set_vars_to_reg_range_uses_standard_arg_regs.
  Qed.

  Context {locals: map.map Z word}.
  Context {localsOk: map.ok locals}.
  Context {env: map.map String.string (list Z * list Z * stmt)} {env_ok: map.ok env}.
  Context {ext_spec: LeakageSemantics.ExtSpec}.

  Definition spill_functions: env -> result env :=
    map.try_map_values spill_fun.

  Definition valid_vars_src(maxvar: Z): stmt -> Prop :=
    Forall_vars_stmt (fun x => fp < x <= maxvar /\ (x < a0 \/ a7 < x)).

  Definition valid_vars_tgt: stmt -> Prop :=
    Forall_vars_stmt (fun x => 3 <= x < 32).

  Local Arguments Z.of_nat: simpl never.
  Local Ltac fwd_rewrites ::= fwd_rewrites_autorewrite.

  Lemma set_vars_to_reg_range_valid_vars: forall args start,
      3 <= start ->
      start + Z.of_nat (List.length args) <= 32 ->
      Forall (fun x => fp < x) args ->
      valid_vars_tgt (set_vars_to_reg_range args start).
  Proof.
    induction args; simpl; intros.
    - exact I.
    - fwd. split.
      + unfold set_var_to_reg, stack_loc, fp, a0, a7 in *. destr (32 <=? a); simpl; blia.
      + eapply IHargs; try blia. assumption.
  Qed.

  Lemma set_reg_range_to_vars_valid_vars: forall args start,
      3 <= start ->
      start + Z.of_nat (List.length args) <= 32 ->
      Forall (fun x => fp < x) args ->
      valid_vars_tgt (set_reg_range_to_vars start args).
  Proof.
    induction args; simpl; intros.
    - exact I.
    - fwd. split.
      + eapply IHargs; try blia. assumption.
      + unfold set_reg_to_var, stack_loc, fp, a0, a7 in *. destr (32 <=? a); simpl; blia.
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
             | z: operand |- _ => destruct z
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
      end; eauto;   intuition try blia;
      try eapply set_reg_range_to_vars_valid_vars;
      try eapply set_vars_to_reg_range_valid_vars;
      unfold a0, a7 in *;
      eauto;
      rewrite ?List.firstn_length;
      try eapply List.Forall_firstn;
      try (eapply List.Forall_impl; [|eapply arg_range_Forall]; cbv beta);
      try blia;
      (eapply Forall_impl; [|eassumption]); cbv beta; unfold fp; blia.
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

  Implicit Types post : leakage -> Semantics.trace -> mem -> locals -> MetricLog -> Prop.

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

  Lemma load_iarg_reg_correct {pick_sp: PickSp} (i: Z): forall r e2 k2 t1 t2 m1 m2 l1 l2 mc2 fpval post frame maxvar v,
      i = 1 \/ i = 2 ->
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      fp < r <= maxvar /\ (r < a0 \/ a7 < r) ->
      map.get l1 r = Some v ->
      (related maxvar frame fpval t1 m1 l1 t2 m2 (map.put l2 (iarg_reg i r) v) ->
       post (rev (leak_load_iarg_reg fpval r) ++ k2) t2 m2 (map.put l2 (iarg_reg i r) v) (if isRegZ r then mc2 else (mkMetricLog 1 0 2 0 + mc2)%metricsH)) ->
      execpost pick_sp e2 (load_iarg_reg i r) k2 t2 m2 l2 mc2 post.
  Proof.
    intros.
    unfold leak_load_iarg_reg, load_iarg_reg, stack_loc, iarg_reg, related in *. fwd.
    assert (isRegZ (9 + i) = true) by (unfold isRegZ; blia).
    assert (isRegZ fp = true) by (unfold isRegZ; (assert (fp = 5) by auto); blia).
    destr (32 <=? r).
    - eapply exec.load.
      + eapply get_sep. ecancel_assumption.
      + eapply load_from_word_array. 1: ecancel_assumption. 2: blia.
        eapply H0p6. 1: blia.
        unfold sep in H0p4. fwd.
        eapply map.get_split_r. 1,3: eassumption.
        destr (map.get mp r); [exfalso|reflexivity].
        specialize H0p2 with (1 := E0). blia.
      + unfold cost_load.
        assert (isRegZ r = false) by (unfold isRegZ; blia); rewrite H4 in H3.
        unfold spill_tmp in H3. rewrite H0; rewrite H1.
        eapply H3.
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
      assert (isRegZ r = true) by (unfold isRegZ; blia); rewrite H4 in H3.
      eapply H3.
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             | |- _ => eassumption || reflexivity
             end.
  Qed.
  
  (* Lemma load_iarg_reg_correct' {pick_sp: PickSp} (i: Z): forall r e2 k1 k2 t1 t2 m1 m2 l1 l2 mc1 mc2 post frame maxvar v fpval, *)
  (*     i = 1 \/ i = 2 -> *)
  (*     related maxvar frame fpval t1 m1 l1 t2 m2 l2 -> *)
  (*     fp < r <= maxvar /\ (r < a0 \/ a7 < r) -> *)
  (*     map.get l1 r = Some v -> *)
  (*     post k1 t1 m1 l1 mc1 -> *)
  (*     execpost e2 (load_iarg_reg i r) k2 t2 m2 l2 mc2 *)
  (*          (fun k2' t2' m2' l2' mc2' => exists k1' t1' m1' l1' mc1', *)
  (*               related maxvar frame fpval t1' m1' l1' t2' m2' l2' /\ post k1' t1' m1' l1' mc1'). *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold load_iarg_reg, stack_loc, iarg_reg, related in *. fwd. *)
  (*   destr (32 <=? r). *)
  (*   - eapply exec.load. *)
  (*     + eapply get_sep. ecancel_assumption. *)
  (*     + eapply load_from_word_array. 1: ecancel_assumption. 2: blia. *)
  (*       eapply H0p6. 1: blia. *)
  (*       unfold sep in H0p4. fwd. *)
  (*       eapply map.get_split_r. 1,3: eassumption. *)
  (*       destr (map.get mp r); [exfalso|reflexivity]. *)
  (*       specialize H0p2 with (1 := E0). blia. *)
  (*     + repeat match goal with *)
  (*              | |- exists _, _ => eexists *)
  (*              | |- _ /\ _ => split *)
  (*              | |- _ => eassumption || reflexivity *)
  (*              end. *)
  (*       eapply put_tmp; eassumption. *)
  (*   - eapply exec.skip. *)
  (*     replace l2 with (map.put l2 r v) in H0p5|-*. 2: { *)
  (*       apply map.put_idemp. *)
  (*       edestruct (eq_sep_to_split l2) as (l2Rest & S22 & SP22). 1: ecancel_assumption. *)
  (*       eapply map.get_split_grow_r. 1: eassumption. *)
  (*       unfold sep in H0p4. destruct H0p4 as (lRegs' & lStack' & S2 & ? & ?). subst lRegs' lStack'. *)
  (*       eapply map.get_split_l. 1: exact S2. 2: assumption. *)
  (*       destr (map.get lStack r); [exfalso|reflexivity]. *)
  (*       specialize H0p3 with (1 := E0). blia. *)
  (*     } *)
  (*     repeat match goal with *)
  (*            | |- exists _, _ => eexists *)
  (*            | |- _ /\ _ => split *)
  (*            | |- _ => eassumption || reflexivity *)
  (*            end. *)
  (* Qed. *)

  (* Note: if we wanted to use this lemma in subgoals created by exec.loop,
     new postcondition must not mention the original t2, m2, l2, mc2, (even though
     it would be handy to just say t2'=t2, m2=m2', l2' = map.put l2 (iarg_reg i r) v), because
     when the new postcondition is used as a "mid1" in exec.loop, and body1 is a seq
     in which this lemma was used, t2, m2, l2, mc2 are introduced after the evar "?mid1"
     is created (i.e. after exec.loop is applied), so they are not in the scope of "?mid1". *)
  Lemma load_iarg_reg_correct'' {pick_sp: PickSp} (i: Z): forall r e2 k2 t1 t2 m1 m2 l1 l2 mc2 frame maxvar v fpval,
      i = 1 \/ i = 2 ->
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      fp < r <= maxvar /\ (r < a0 \/ a7 < r) ->
      map.get l1 r = Some v ->
      execpost pick_sp e2 (load_iarg_reg i r) k2 t2 m2 l2 mc2 (fun k2' t2' m2' l2' mc2' =>
        k2' = rev (leak_load_iarg_reg fpval r) ++ k2 /\
        t2' = t2 /\ m2' = m2 /\ l2' = map.put l2 (iarg_reg i r) v /\
        related maxvar frame fpval t1 m1 l1 t2' m2' l2' /\
        (mc2' <= (if isRegZ r then mc2 else mkMetricLog 1 0 2 0 + mc2))%metricsH).
  Proof.
    intros.
    unfold load_iarg_reg, leak_load_iarg_reg, stack_loc, iarg_reg, related in *. fwd.
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
        1: eapply put_tmp; eassumption.
        unfold cost_load. assert (isRegZ (9+i) = true) by (unfold isRegZ; blia); rewrite H0.
        assert (fp = 5) by auto; rewrite H1; cbn.
        destr (isRegZ r); solve_MetricLog.
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
      destr (isRegZ r); solve_MetricLog.
  Qed.

  (* SOp does not create an up-to-date `related` before we invoke this one, because after SOp,
     `related` does not hold: the result is already in l1 and lStack, but not yet in stackwords.
     So we request the `related` that held *before* SOp, i.e. the one where the result is not
     yet in l1 and l2. *)
  Lemma save_ires_reg_correct {pick_sp: PickSp} : forall e k1 k2 t1 t2 m1 m2 l1 l2 mc1 mc1' mc2 mc2' x v maxvar frame post fpval,
      post k1 t1 m1 (map.put l1 x v) mc1' ->
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      fp < x <= maxvar /\ (x < a0 \/ a7 < x) ->
      (mc2' - mc2 <= mc1' - (if isRegZ x then mc1 else mkMetricLog 1 1 1 0 + mc1))%metricsH ->
      execpost pick_sp e (save_ires_reg x) k2 t2 m2 (map.put l2 (ires_reg x) v) mc2'
        (fun k2' t2' m2' l2' mc2'' => exists k1' t1' m1' l1' mc1'',
                related maxvar frame fpval t1' m1' l1' t2' m2' l2' /\
                post k1' t1' m1' l1' mc1'' /\
                k2' = rev (leak_save_ires_reg fpval x) ++ k2 /\
                (mc2'' - mc2 <= mc1'' - mc1)%metricsH).
  Proof.
    intros.
    unfold leak_save_ires_reg, save_ires_reg, stack_loc, ires_reg, related in *. fwd.
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
              + blia.
              + specialize H0p3 with (1 := H1). blia.
          }
          1: eassumption.
          1: {
            intros. rewrite map.get_put_dec in H0. destr (x =? x0).
            - blia.
            - eauto.
          }
          2: {
            intros.
            intros. rewrite map.get_put_dec in H1. destr (x =? r).
            - apply Option.eq_of_eq_Some in H1. subst. assumption.
            - eapply Nj. 1: blia. eauto.
          }
          1: { unfold spill_tmp. eapply put_tmp; eauto. }
          1: blia. 1: reflexivity.
          unfold cost_store. unfold spill_tmp; cbn.
          destr (isRegZ x); solve_MetricLog.
      }
      blia.
    - eapply exec.skip.
      (* even though we did nothing, we have to reconstruct the `related` from the `related` that *)
  (*        held *before* the SOp *)
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
          + blia.
          + specialize H0p2 with (1 := H1). blia.
      }
      1: {
        intros. rewrite map.get_put_dec in H0. destr (x =? x0).
        - blia.
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
      all: try eassumption. 1: reflexivity.
      destr (isRegZ x); solve_MetricLog.
  Qed.


  (* SOp does not create an up-to-date `related` before we invoke this one, because after SOp, *)
  (*    `related` does not hold: the result is already in l1 and lStack, but not yet in stackwords. *)
  (*    So we request the `related` that held *before* SOp, i.e. the one where the result is not *)
  (*    yet in l1 and l2. *)
  Lemma save_ires_reg_correct'' {pick_sp: PickSp} : forall e k2 t1 t2 m1 m2 l1 l2 mc2 x v maxvar frame post fpval,
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      fp < x <= maxvar /\ (x < a0 \/ a7 < x) ->
      (forall t2' m2' l2',
          related maxvar frame fpval t1 m1 (map.put l1 x v) t2' m2' l2' ->
          post (rev (leak_save_ires_reg fpval x) ++ k2) t2' m2' l2' (if isRegZ x then mc2 else mkMetricLog 1 1 1 0 + mc2)%metricsH) ->
      execpost pick_sp e (save_ires_reg x) k2 t2 m2 (map.put l2 (ires_reg x) v) mc2 post.
  Proof.
    intros.
    unfold leak_save_ires_reg, save_ires_reg, stack_loc, ires_reg, related in *. fwd.
    destr (32 <=? x).
    - edestruct store_to_word_array as (m' & stackwords' & St & S' & Ni & Nj & L).
      1: ecancel_assumption.
      2: {
        eapply exec.store.
        - rewrite map.get_put_diff by (cbv; congruence).
          eapply get_sep. ecancel_assumption.
        - rewrite map.get_put_same. reflexivity.
        - exact St.
        - unfold cost_store.
          assert (isRegZ (spill_tmp 1) = true) by auto; rewrite H.
          assert (isRegZ fp = true) by auto; rewrite H0.
          clear H H0.
          destr (isRegZ x); try blia.
          eapply H1.
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
              + blia.
              + eauto with zarith.
          }
          1: eassumption.
          1: {
            intros. rewrite map.get_put_dec in H. destr (x =? x0).
            - blia.
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
      destr (isRegZ x); try blia.
      eapply H1.
      (* even though we did nothing, we have to reconstruct the `related` from the `related` that *)
  (*        held *before* the SOp *)
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
          + blia.
          + eauto with zarith.
      }
      1: {
        intros. rewrite map.get_put_dec in H. destr (x =? x0).
        - blia.
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
    - replace z' with y' in * by congruence.
      unfold iarg_reg, spill_tmp. destruct_one_match.
      + rewrite map.get_put_diff by blia. rewrite map.get_put_same. reflexivity.
      + rewrite map.get_put_same. reflexivity.
    - rewrite map.get_put_diff.
      + rewrite map.get_put_same. reflexivity.
      + unfold iarg_reg, spill_tmp, a0, a7, fp in *. repeat destruct_one_match; blia.
  Qed.

  (* Need to repeat in each section because autorewrite does not run typeclass search to
     find key_eqb_spec *)
  Hint Rewrite
       (sep_eq_empty_l (key_eqb := Z.eqb))
       (sep_eq_empty_r (key_eqb := Z.eqb))
    : fwd_rewrites.

  Lemma hide_ll_arg_reg_ptsto_core: forall k v R l,
      (arg_regs * ptsto k v * R)%sep l ->
      10 <= k < 18 ->
      (arg_regs * R)%sep l.
  Proof.
    unfold arg_regs, sep, ptsto, map.split. intros. fwd.
    exists (map.putmany mp0 (map.put map.empty k v)), mq. ssplit; auto.
    intros. rewrite map.get_putmany_dec, map.get_put_dec, map.get_empty in H.
    destr (k =? k0); subst; fwd; eauto.
  Qed.

  Lemma hide_ll_arg_reg_ptsto: forall k v P R l,
      iff1 (arg_regs * R)%sep P ->
      (arg_regs * ptsto k v * R)%sep l ->
      10 <= k < 18 ->
      P l.
  Proof.
    intros. apply H. eapply hide_ll_arg_reg_ptsto_core; eassumption.
  Qed.

  Fixpoint cost_set_vars_to_reg_range (args: list Z) (start : Z) (mc : MetricLog) : MetricLog :=
    match args with
    | [] => mc
    | x :: xs => (if isRegZ x then mkMetricLog 1 0 1 0 else mkMetricLog 1 1 1 0) +
        cost_set_vars_to_reg_range xs (start + 1) mc
    end.

  Lemma cost_set_vars_to_reg_range_commutes:
    forall args start n m,
      (cost_set_vars_to_reg_range args start (n + m) = n + cost_set_vars_to_reg_range args start m)%metricsH.
  Proof.
    induction args; trivial.
    intros; cbn; destr (isRegZ a); cbn; rewrite IHargs;
    do 2 rewrite MetricArith.add_assoc; rewrite (MetricArith.add_comm n); reflexivity.
  Qed.

  Lemma set_vars_to_reg_range_correct {pick_sp: PickSp} :
    forall args start argvs e k2 t1 t2 m1 m2 l1 l1' l2 mc2 maxvar frame post fpval,
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      map.putmany_of_list_zip args argvs l1 = Some l1' ->
      map.getmany_of_list l2 (List.unfoldn (Z.add 1) (List.length args) start) = Some argvs ->
      (List.length args <= 8)%nat ->
      a0 <= start ->
      start + Z.of_nat (List.length args) <= a7 + 1 ->
      Forall (fun x => fp < x <= maxvar /\ (x < a0 \/ a7 < x)) args ->
      (forall k2' m2' l2' mc2',
          related maxvar frame fpval t1 m1 l1' t2 m2' l2' ->
          mc2' = cost_set_vars_to_reg_range args start mc2 ->
          k2' = rev (leak_set_vars_to_reg_range fpval args) ++ k2 ->
          post k2' t2 m2' l2' mc2') ->
      execpost pick_sp e (set_vars_to_reg_range args start) k2 t2 m2 l2 mc2 post.
  Proof.
    induction args; intros.
    - simpl. eapply exec.skip. fwd. eauto.
    - simpl. unfold set_var_to_reg, stack_loc.
      unfold related in H. fwd.
      eapply exec.seq_cps.
      rewrite (Z.add_comm 1 start) in *.
      simpl in H6. cbv [leak_set_var_to_reg stack_loc] in H6.
      destr (32 <=? a).
      + edestruct store_to_word_array with (i := a - 32).
        1: ecancel_assumption. 1: blia.
        fwd.
        eapply exec.store.
        { eapply get_sep. ecancel_assumption. }
        { eassumption. }
        { eassumption. }
        eapply IHargs; try eassumption; try blia.
        (* establish related for IH: *)
        * unfold related.
          eexists (map.put lStack a v), lRegs, _.
          ssplit.
          { reflexivity. }
          { ecancel_assumption. }
          { eassumption. }
          { intros. rewrite map.get_put_dec in H. destr (a =? x0). 1: blia. eauto. }
          { apply sep_comm. eapply sep_eq_put. 1: apply sep_comm; assumption.
            intros lRegs' w ? G. subst lRegs'.
            match goal with H: _ |- _ => specialize H with (1 := G) end. blia. }
          { eassumption. }
          { intros b A0 w B0.
          rewrite map.get_put_dec in B0.
          destr (a =? b). 1: congruence.
          match goal with H: _ |- _ => eapply H end. 1: blia.
          match goal with H: _ |- _ => eapply H end. 1: blia.
          assumption. }
          { blia. }
        * intros. apply H6; auto.
          -- cbn in *. destr (isRegZ start); try blia; destr (isRegZ a); try blia.
             rewrite H0. unfold cost_store, isRegZ. cbn.
             rewrite cost_set_vars_to_reg_range_commutes.
             rewrite (proj2 (Z.leb_le start 31)) by assumption.
             reflexivity.
          -- subst. rewrite rev_app_distr. rewrite <- app_assoc. reflexivity.
      + eapply exec.set.
        { eassumption. }
        eapply IHargs; try eassumption; try blia. 2: {
          eapply map.getmany_of_list_put_diff. 2: eassumption.
          eapply List.not_In_Z_seq. blia.
        }
        * unfold related. eexists lStack, (map.put lRegs a v), _.
          ssplit.
          { reflexivity. }
          { ecancel_assumption. }
          { intros. rewrite map.get_put_dec in H. destr (a =? x). 1: blia. eauto. }
          { eassumption. }
          { eapply sep_eq_put. 1: assumption.
            intros lStack' w ? G. subst lStack'.
            match goal with H: _ |- _ => specialize H with (1 := G) end. blia. }
          { apply sep_assoc. eapply sep_eq_put. 1: ecancel_assumption.
            unfold ptsto, arg_regs.
            intros l w (l_arg_regs & l_fpval & (? & ?) & ? & ?) G. subst.
          rewrite map.get_putmany_dec, map.get_put_dec, map.get_empty in G.
          destr (fp =? a). 1: unfold fp; blia.
          match goal with H: _ |- _ => specialize H with (1 := G) end.
          unfold a0, a7 in *. blia. }
          { assumption. }
          { assumption. }
        * intros. apply H6; auto.
          cbn in *. destr (isRegZ start); try blia; destr (isRegZ a); try blia.
          rewrite H0. unfold cost_set, isRegZ. cbn.
          rewrite cost_set_vars_to_reg_range_commutes.
          rewrite (proj2 (Z.leb_le a 31)) by assumption.
          rewrite (proj2 (Z.leb_le start 31)) by assumption.
          reflexivity.
  Qed.

  Fixpoint cost_set_reg_range_to_vars (start : Z) (args: list Z) (mc : MetricLog) : MetricLog :=
    match args with
    | [] => mc
    | x :: xs => (if isRegZ x then mkMetricLog 1 0 1 0 else mkMetricLog 1 0 2 0) +
        cost_set_reg_range_to_vars (start + 1) xs mc
    end.

  Lemma set_reg_range_to_vars_correct {pick_sp: PickSp} :
    forall args argvs start e k2 t1 t2 m1 m2 l1 l2 mc2 maxvar frame post fpval,
      related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
      (List.length args <= 8)%nat ->
      a0 <= start ->
      start + Z.of_nat (List.length args) <= a7 + 1 ->
      Forall (fun x => fp < x <= maxvar /\ (x < a0 \/ a7 < x)) args ->
      map.getmany_of_list l1 args = Some argvs ->
      (forall k2' l2' mc2',
          related maxvar frame fpval t1 m1 l1 t2 m2 l2' ->
          map.getmany_of_list l2' (List.unfoldn (Z.add 1) (List.length args) start) = Some argvs ->
          mc2' = cost_set_reg_range_to_vars start args mc2 ->
          k2' = rev (leak_set_reg_range_to_vars fpval args) ++ k2 ->
          post k2' t2 m2 l2' mc2') ->
      execpost pick_sp e (set_reg_range_to_vars start args) k2 t2 m2 l2 mc2 post.
  Proof.
    induction args; intros.
    - simpl. eapply exec.skip. eapply H5; eauto.
    - simpl. unfold set_reg_to_var, leak_set_reg_to_var, stack_loc.
      destruct argvs as [|v vs]. {
        unfold map.getmany_of_list in H4. cbn in H4. simp.
        destr (List.option_all (map (map.get l1) args)); discriminate.
      }
      eapply map.invert_getmany_of_list_cons in H4. destruct H4 as [G GM].
      cbn [List.length] in *.
      simp.
      cbn [leak_set_reg_range_to_vars] in H5. cbv [leak_set_reg_to_var stack_loc] in H5.
      destr (32 <=? a).
      + eapply exec.seq_cps.
        eapply IHargs; try eassumption; try blia.
        intros.
        unfold related in H3. simp.
        eapply exec.load.
        * eapply get_sep. ecancel_assumption.
        * eapply load_from_word_array. 1: ecancel_assumption. 2: blia.
          eapply H3p5. 1: blia.
          unfold sep in H3p3. simp.
          eapply map.get_split_r. 1,3: eassumption.
          destr (map.get mp a); [exfalso|reflexivity].
          specialize H3p1 with (1 := E0). blia.
        * eapply H5.
          -- unfold related.
             repeat match goal with
                    | |- exists _, _ => eexists
                    | |- _ /\ _ => split
                    | |- _ => eassumption || reflexivity
                    end.
             eapply put_arg_reg; try eassumption. blia.
          -- cbn [List.unfoldn]. eapply map.getmany_of_list_cons.
             ++ apply map.get_put_same.
             ++ rewrite Z.add_comm.
                eapply map.getmany_of_list_put_diff. 2: eassumption.
                eauto using List.not_In_Z_seq with zarith.
          -- cbn. destr (isRegZ start); destr (isRegZ a); cbn in *; try blia.
             rewrite H6; unfold cost_load, isRegZ; cbn.
             rewrite (proj2 (Z.leb_le start 31)) by assumption.
             reflexivity.
          -- subst. rewrite rev_app_distr. rewrite <- app_assoc. reflexivity.
      + eapply exec.seq_cps.
        eapply IHargs; try eassumption; try blia.
        intros.
        unfold related in H3. simp.
        eapply exec.set.
        * edestruct (eq_sep_to_split l2') as (l2Rest & S22 & SP22). 1: ecancel_assumption.
          eapply map.get_split_grow_r. 1: eassumption.
          unfold sep in H3p3. destruct H3p3 as (lRegs' & lStack' & S2 & ? & ?).
          subst lRegs' lStack'.
          eapply map.get_split_l. 1: exact S2. 2: exact G.
          destr (map.get lStack a); [exfalso|reflexivity].
          specialize H3p2 with (1 := E0). blia.
        * eapply H5. 2: {
            cbn [List.unfoldn].
            eapply map.getmany_of_list_cons.
            - apply map.get_put_same.
            - rewrite Z.add_comm. eapply map.getmany_of_list_put_diff. 2: eassumption.
              eauto using List.not_In_Z_seq with zarith.
          }
          -- unfold related.
             repeat match goal with
                    | |- exists _, _ => eexists
                    | |- _ /\ _ => split
                    | |- _ => eassumption || reflexivity
                    end.
             eapply put_arg_reg; try eassumption. blia.
          -- cbn. destr (isRegZ start); destr (isRegZ a); cbn in *; try blia.
             rewrite H6; unfold cost_set, isRegZ; cbn.
             rewrite (proj2 (Z.leb_le a 31)) by assumption.
             rewrite (proj2 (Z.leb_le start 31)) by assumption.
             reflexivity.
          -- subst. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma cost_set_reg_range_to_vars_bound : forall args start mc len,
    Z.of_nat (Datatypes.length args) <= len ->
    (cost_set_reg_range_to_vars start args mc <= addMetricInstructions len (addMetricLoads (2 * len) mc))%metricsH.
  Proof.
    induction args.
    - unfold cost_set_reg_range_to_vars, Z.of_nat. intros. simpl in H. solve_MetricLog.
    - intros.
      cbn [cost_set_reg_range_to_vars].
      specialize (IHargs (start+1) mc (Z.of_nat (Datatypes.length args)) (Z.le_refl _)).
      subst.
      simpl in H.
      destruct (isRegZ a); solve_MetricLog.
  Qed.

  Lemma cost_set_vars_to_reg_range_bound : forall args start mc len,
    Z.of_nat (Datatypes.length args) <= len ->
    (cost_set_vars_to_reg_range args start mc <= addMetricInstructions len (addMetricLoads len (addMetricStores len mc)))%metricsH.
  Proof.
    induction args.
    - unfold cost_set_vars_to_reg_range, Z.of_nat. intros. simpl in H. solve_MetricLog.
    - intros.
      cbn [cost_set_vars_to_reg_range].
      specialize (IHargs (start+1) mc (Z.of_nat (Datatypes.length args)) (Z.le_refl _)).
      subst.
      simpl in H.
      destruct (isRegZ a); solve_MetricLog.
  Qed.

  (* pulled and modified from Coq.Program.Tactics *)
  Ltac add_hypothesis p :=
    match type of p with
      ?X => match goal with
        | [ H : X |- _ ] => fail 1
        | _ => pose proof p
      end
    end.

  Ltac add_bounds :=
    repeat match goal with
           | _: context[cost_set_reg_range_to_vars ?x ?y ?z] |- _ =>
               add_hypothesis (cost_set_reg_range_to_vars_bound y x z 8 ltac:(blia))
           | _: context[cost_set_vars_to_reg_range ?x ?y ?z] |- _ =>
               add_hypothesis (cost_set_vars_to_reg_range_bound x y z 8 ltac:(blia))
           | |- context[cost_set_reg_range_to_vars ?x ?y ?z] =>
               add_hypothesis (cost_set_reg_range_to_vars_bound y x z 8 ltac:(blia))
           | |- context[cost_set_vars_to_reg_range ?x ?y ?z] =>
               add_hypothesis (cost_set_vars_to_reg_range_bound x y z 8 ltac:(blia))
           end.

  (* end silly seeming section *)

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

  Lemma hide_llArgRegs: forall llArgRegs R l argvals n,
      (eq llArgRegs * arg_regs * R)%sep l ->
      map.of_list_zip (List.unfoldn (Z.add 1) n a0) argvals = Some llArgRegs ->
      (n <= 8)%nat ->
      (arg_regs * R)%sep l.
  Proof.
    unfold arg_regs, sep, map.split. intros. fwd.
    exists (map.putmany mp0 mq0), mq. ssplit; auto.
    intros. rewrite map.get_putmany_dec in H. destr (map.get mq0 k); fwd; eauto.
    eapply map.of_list_zip_forall_keys in H0.
    2: eapply List.unfoldn_Z_seq_Forall.
    unfold map.forall_keys in H0. specialize H0 with (1 := H). unfold a0 in H0. blia.
  Qed.

  (* used at the beginning of a function *)
  Lemma fresh_related: forall maxvar frame fpval t m1 m2 l2 argcount vs stackwords,
      map.of_list_zip (List.firstn argcount (reg_class.all reg_class.arg)) vs = Some l2 ->
      (argcount <= 8)%nat ->
      length stackwords = Z.to_nat (maxvar - 31) ->
      (eq m1 * word_array fpval stackwords * frame)%sep m2 ->
      related maxvar frame fpval t m1 map.empty t m2 (map.put l2 fp fpval).
  Proof.
    unfold related. intros.
    eexists map.empty, map.empty, _. ssplit.
    - reflexivity.
    - eassumption.
    - intros. rewrite map.get_empty in H3. discriminate.
    - intros. rewrite map.get_empty in H3. discriminate.
    - unfold sep, map.split. exists map.empty, map.empty. rewrite map.putmany_empty_l.
      eauto using @map.disjoint_empty_r.
    - fwd. apply sep_comm. eapply sep_on_undef_put.
      + eapply map.not_in_of_list_zip_to_get_None. 1: eassumption.
        eapply not_in_arg_regs; unfold fp, RegisterNames.a0, RegisterNames.a7; blia.
      + unfold arg_regs.
        eapply map.of_list_zip_forall_keys in H. 2: {
          apply List.Forall_firstn.
          apply arg_range_Forall.
        }
        unfold map.forall_keys in *. intros. specialize H with (1 := H3). blia.
    - intros. rewrite map.get_empty in H4. discriminate.
    - assumption.
  Qed.

  Lemma arg_regs_absorbs_putmany_of_list_zip: forall n vs l l' lRegs fpval,
      (forall x v, map.get lRegs x = Some v -> fp < x < 32 /\ (x < a0 \/ a7 < x)) ->
      (eq lRegs * arg_regs * ptsto fp fpval)%sep l ->
      map.putmany_of_list_zip (List.firstn n (reg_class.all reg_class.arg)) vs l = Some l' ->
      (n <= 8)%nat ->
      (eq lRegs * arg_regs * ptsto fp fpval)%sep l'.
  Proof.
    unfold sep, map.split, ptsto. intros.
    destruct H0 as (mp & mq & (? & ?) & (lRegs' & mA & (? & ?) & ? & ?) & ?).
    subst l lRegs' mp mq.
    pose proof H1 as PM.
    eapply map.putmany_of_list_zip_sameLength in PM.
    eapply map.sameLength_putmany_of_list with (st := mA) in PM.
    destruct PM as (mA' & PM).
    assert (arg_regs mA') as AA. {
      unfold arg_regs in *. intros. pose proof H7 as P.
      erewrite map.get_putmany_of_list_zip in H0. 2: exact PM.
      destruct_one_match_hyp. 2: eauto.
      fwd.
      eapply map.zipped_lookup_Some_in in E.
      pose proof arg_range_Forall as Q.
      eapply Forall_forall in Q. 2: eapply List.In_firstn_to_In. 2: exact E. blia.
    }
    repeat match goal with
           | |- exists _, _ => eexists
           | |- _ /\ _ => split
           end.
    all: try reflexivity.
    4: exact AA.
    - apply map.map_ext. intros. erewrite map.get_putmany_of_list_zip. 2: eassumption.
      rewrite ?map.get_putmany_dec, ?map.get_put_dec, map.get_empty.
      destruct_one_match.
      + symmetry.
        pose proof E as F.
        eapply map.zipped_lookup_Some_in in E.
        pose proof arg_range_Forall as Q.
        eapply Forall_forall in Q. 2: eapply List.In_firstn_to_In. 2: exact E.
        destr (fp =? k). 1: unfold fp in *; exfalso; blia.
        erewrite map.get_putmany_of_list_zip. 2: exact PM.
        rewrite F. reflexivity.
      + destr (map.get mA' k).
        * erewrite map.get_putmany_of_list_zip in E0. 2: exact PM.
          rewrite E in E0. rewrite E0. reflexivity.
        * erewrite map.get_putmany_of_list_zip in E0. 2: exact PM.
          rewrite E in E0. rewrite E0. reflexivity.
    - unfold map.disjoint. intros * G1 G2.
      rewrite ?map.get_put_dec, ?map.get_empty in G2. fwd.
      rewrite map.get_putmany_dec in G1. destruct_one_match_hyp; fwd.
      + unfold arg_regs in AA. specialize (AA _ _ E). unfold fp in AA. blia.
      + specialize (H _ _ G1). unfold fp in H. blia.
    - unfold map.disjoint. intros * G1 G2.
      unfold arg_regs in AA.
      specialize (AA _ _ G2).
      specialize (H _ _ G1).
      unfold a0, a7 in H.
      blia.
  Qed.

  Definition spilling_correct_for(e1 e2 : env)(s1 : stmt): Prop :=
      forall pick_sp1 k1 t1 m1 l1 mc1 post,
        execpre pick_sp1 e1 s1 k1 t1 m1 l1 mc1 post ->
        forall (frame : mem -> Prop) (maxvar : Z),
          valid_vars_src maxvar s1 ->
          forall pick_sp2 k2 t2 m2 l2 mc2 fpval f,
            related maxvar frame fpval t1 m1 l1 t2 m2 l2 ->
            (forall k, pick_sp1 (k ++ k1) = snd (stmt_leakage e1 pick_sp2 (s1, rev k, rev k2, fpval, f k))) ->
            execpost pick_sp2 e2 (spill_stmt s1) k2 t2 m2 l2 mc2
                 (fun k2' t2' m2' l2' mc2' =>
                    exists k1' t1' m1' l1' mc1' k1'',
                      related maxvar frame fpval t1' m1' l1' t2' m2' l2' /\
                      post k1' t1' m1' l1' mc1' /\
                      (mc2' - mc2 <= mc1' - mc1)%metricsH /\
                      k1' = k1'' ++ k1 /\
                      forall k f, stmt_leakage e1 pick_sp2 (s1, rev k1'' ++ k, rev k2, fpval, f) = f (rev k1'') (rev k2')).

  (* TODO tighter / non-fixed bound *)
  Definition cost_spill_spec mc :=
    (mkMetricLog 100 100 100 100 + mc)%metricsH.

  Definition call_spec(e: env) '(argnames, retnames, fbody)
    pick_sp k t m argvals mc
    (post : leakage -> Semantics.trace -> mem -> list word -> MetricLog -> Prop) : Prop :=
    forall l, map.of_list_zip argnames argvals = Some l ->
         execpre pick_sp e fbody k t m l (cost_spill_spec mc) (fun k' t' m' l' mc' =>
                   exists retvals, map.getmany_of_list l' retnames = Some retvals /\
                                post k' t' m' retvals mc').

  Definition call_spec_spilled(e: env) '(argnames, retnames, fbody)
    pick_sp k t m argvals mc
    (post : leakage -> Semantics.trace -> mem -> list word -> MetricLog -> Prop) : Prop :=
    forall l, map.of_list_zip argnames argvals = Some l ->
         execpost pick_sp e fbody k t m l mc (fun k' t' m' l' mc' =>
                   exists retvals, map.getmany_of_list l' retnames = Some retvals /\
                                post k' t' m' retvals mc').
  
  (* In exec.call, there are many maps of locals involved:

         H = High-level, L = Low-level, C = Caller, F = called Function

                   H                                       L

                  lCH1                                    lCL1
                                                   set_reg_range_to_vars
                                                          lCL2
             get/putmany_of_list                    get/putmany_of_list
                                                          lFL3
                                                   set_vars_to_reg_range
                  lFH4                                    lFL4
             function body                           function body
                  lFH5                                    lFL5
                                                   set_reg_range_to_vars
                                                          lFL6
           get/putmany_of_list                      get/putmany_of_list
                                                          lCL7
                                                   set_vars_to_reg_range
                  lCH8                                    lCL8

     To simplify, it is helpful to have a separate lemma only talking about
     what happens in the callee. TODO: actually use that lemma in case exec.call.
     Moreover, this lemma will also be used in the pipeline, where phases
     are composed based on the semantics of function calls. *)

  Lemma spill_fun_correct_aux: forall pick_sp2 e1 e2 argnames1 retnames1 body1 argnames2 retnames2 body2,
      spill_fun (argnames1, retnames1, body1) = Success (argnames2, retnames2, body2) ->
      spilling_correct_for e1 e2 body1 ->
      forall argvals kH kL t m mcH mcL (post : leakage -> Semantics.trace -> mem -> list word -> MetricLog -> Prop),
        call_spec e1 (argnames1, retnames1, body1)
          (fun k' => snd (fun_leakage e1 pick_sp2 (argnames1, retnames1, body1) (skipn (length kH) (rev k')) (rev kL))) kH t m argvals mcH post ->
        call_spec_spilled e2 (argnames2, retnames2, body2) pick_sp2 kL t m argvals mcL
          (fun kL' t' m' l' mcL' =>
             exists kH'' mcH',
               post (kH'' ++ kH) t' m' l' mcH' /\
                 metricsLeq (mcL' - mcL) (mcH' - mcH) /\
                 fst (fun_leakage e1 pick_sp2 (argnames1, retnames1, body1) (rev kH'') (rev kL)) = rev kL').
  Proof.
    unfold call_spec, spilling_correct_for. intros * Sp IHexec * Ex lFL3 OL2.
    unfold spill_fun in Sp. fwd.
    apply_in_hyps @map.getmany_of_list_length.
    apply_in_hyps @map.putmany_of_list_zip_sameLength.
    assert (length argnames1 = length argvals) as LA. {
      rewrite List.firstn_length in *.
      change (length (reg_class.all reg_class.arg)) with 8%nat in *.
      blia.
    }
    eapply map.sameLength_putmany_of_list in LA.
    destruct LA as (lFH4 & PA).
    specialize Ex with (1 := PA).
    rewrite !arg_regs_alt by blia.
    assert (bytes_per_word = 4 \/ bytes_per_word = 8) as B48. {
      unfold bytes_per_word. destruct width_cases as [E' | E']; rewrite E'; cbv; auto.
    }
    set (maxvar' := (Z.max (max_var body1)
                           (Z.max (fold_left Z.max argnames1 0)
                                  (fold_left Z.max retnames1 0)))) in *.
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
      destr (0 <=? (maxvar' - 31)).
      - rewrite Z2Nat.id by assumption. rewrite Z.mul_comm. apply Z_mod_mult.
      - replace (Z.of_nat (Z.to_nat (maxvar' - 31))) with 0 by blia.
        rewrite Z.mul_0_r.
        apply Zmod_0_l.
    }
    eapply F in Pt. clear F.
    assert (length words = Z.to_nat (maxvar' - 31)) as L''. {
      Z.to_euclidean_division_equations; blia.
    }
    eapply exec.seq_cps.
    eapply set_vars_to_reg_range_correct. Check set_vars_to_reg_range_correct.
    { eapply fresh_related with (m1 := m) (frame := eq map.empty).
      - eassumption.
      - blia.
      - exact L''.
      - rewrite sep_eq_empty_r.
        unfold sep. eauto. }
    { eassumption. }
    { eapply map.getmany_of_list_put_diff. {
        eapply List.not_In_Z_seq. unfold fp, a0. blia.
      }
      eapply map.putmany_of_list_zip_to_getmany_of_list.
      - rewrite <- arg_regs_alt by blia. exact OL2.
      - eapply List.NoDup_unfoldn_Z_seq.
    }
    { blia. }
    { reflexivity. }
    { unfold a0, a7. blia. }
    { eapply Forall_impl. 2: eapply Forall_and.
      2: eapply List.forallb_to_Forall.
      3: eassumption.
      2: {
        unfold is_valid_src_var.
        intros *. intro F.
        rewrite ?Bool.andb_true_iff, ?Bool.orb_true_iff, ?Z.ltb_lt in F. exact F.
      }
      2: eapply Forall_le_max.
      cbv beta.
      subst maxvar'. clear. blia. }
    intros kL4 mL4 lFL4 mcL4 R Hcost HkL4.
    eapply exec.seq_cps.
    eapply exec.weaken. {
      eapply IHexec with (f := fun _ => _). 1: apply Ex. 2: exact R.
      { unfold valid_vars_src.
        eapply Forall_vars_stmt_impl.
        2: eapply max_var_sound.
        2: eapply forallb_vars_stmt_correct.
        3: eassumption.
        2: {
          unfold is_valid_src_var.
          intros *.
          rewrite ?Bool.andb_true_iff, ?Bool.orb_true_iff, ?Z.ltb_lt. reflexivity.
        }
        cbv beta. subst maxvar'. blia. }
      intros. subst a kL4. simpl. simpl_rev. repeat rewrite <- app_assoc.
      rewrite List.skipn_app_r.
      2: { rewrite rev_length. reflexivity. }
      reflexivity. }
    cbv beta. intros kL5 tL5 mL5 lFL5 mcL5 (kH5 & tH5 & mH5 & lFH5 & mcH5 & kH5'' & R5 & OC & Ek & Emc & CT).
    subst. fwd.
    eapply set_reg_range_to_vars_correct.
    { eassumption. }
    { blia. }
    { reflexivity. }
    { unfold a0, a7. blia. }
    { eapply Forall_impl. 2: eapply Forall_and.
      2: eapply List.forallb_to_Forall.
      3: eassumption.
      2: {
        unfold is_valid_src_var.
        intros *. intro F.
        rewrite ?Bool.andb_true_iff, ?Bool.orb_true_iff, ?Z.ltb_lt in F. exact F.
      }
      2: eapply Forall_le_max.
      cbv beta.
      subst maxvar'. clear. blia. }
    { eassumption. }
    rename R into R0.
    intros kFL6 lFL6 mcL6 R GM HCost HkFL6.
    (* prove that if we remove the additional stack provided by exec.stackalloc
       and store the result vars back into the arg registers, the postcondition holds *)
    unfold related in R. fwd. rename lStack into lStack5, lRegs into lRegs5.
    move A at bottom. move Sp at bottom.
    rename Rp1 into M2.
    rewrite sep_eq_empty_r in M2.
    unfold sep in M2. unfold map.split in M2.
    destruct M2 as (m2Small & mStack' & (? & ?) & ? & M2).
    subst.
    repeat match goal with
           | |- exists _, _ => eexists
           | |- _ /\ _ => split
           end.
    4: eassumption.
    2: {
      unfold map.split. eauto.
    }
    {
      eapply cast_word_array_to_bytes in M2.
      eapply array_1_to_anybytes in M2.
      match goal with
      | H: Memory.anybytes a ?LEN1 mStack' |-
        Memory.anybytes a ?LEN2 mStack' => replace LEN2 with LEN1; [exact H|]
      end.
      erewrite List.flat_map_const_length. 2: {
        intros w. rewrite LittleEndianList.length_le_split; trivial.
      }
      blia. }
    { eassumption. }
    { add_bounds.
      unfold cost_stackalloc, cost_spill_spec in *. (* TODO XXX *)
      destruct (isRegZ fp); solve_MetricLog. }
    subst a. simpl. simpl_rev. repeat rewrite <- app_assoc in * || simpl in *.
    specialize (CT nil). rewrite app_nil_r in CT. rewrite CT. reflexivity.
  Qed.


  Lemma iarg_reg_isReg: forall i a,
      (i <= 20) ->
      (isRegZ (iarg_reg i a) = true).
  Proof.
    intros. unfold isRegZ, iarg_reg. destr (32 <=? a); unfold spill_tmp; blia.
  Qed.

  Lemma ires_reg_isReg: forall r,
      (isRegZ (ires_reg r) = true).
  Proof.
    intros. unfold isRegZ, ires_reg. destr (32 <=? r); unfold spill_tmp; blia.
  Qed.

  Ltac isReg_helper :=
    match goal with
    | |- context[(isRegZ (iarg_reg _ _))] => rewrite iarg_reg_isReg by blia
    | H: context[(isRegZ (iarg_reg _ _))] |- _ => rewrite iarg_reg_isReg in H by blia
    | |- context[(isRegZ (ires_reg _))] => rewrite ires_reg_isReg
    | H: context[(isRegZ (ires_reg _))] |- _ => rewrite ires_reg_isReg in H
    end.

  Ltac irs := cost_unfold; repeat isReg_helper; cost_solve.
  Ltac sirs := scost_unfold; repeat isReg_helper; scost_solve.

  Ltac after_save_ires_reg_correct'' :=
    intros; do 6 eexists; ssplit; [eassumption | eassumption | solve [irs] || solve [sirs] || idtac | align_trace | intros; rewrite sfix_step; simpl; simpl_rev; repeat rewrite <- app_assoc; try reflexivity].
  

  Lemma spilling_correct (e1 e2 : env) (Ev : spill_functions e1 = Success e2) (s1 : stmt) :
    spilling_correct_for e1 e2 s1.
  Proof.
    cbv [spilling_correct_for].
    induction 1; intros; cbn [spill_stmt valid_vars_src Forall_vars_stmt] in *; fwd.
    - (* exec.interact *)
      eapply exec.seq_cps.
      eapply set_reg_range_to_vars_correct; try eassumption; try (unfold a0, a7; blia).
      intros *. intros R GM ? ?. subst. clear l2 H4.
      unfold related in R. fwd.
      spec (subst_split (ok := mem_ok) m) as A.
      1: eassumption. 1: ecancel_assumption.
      edestruct (@sep_def _ _ _ m2 (eq mGive)) as (mGive' & mKeepL & B & ? & C).
      1: ecancel_assumption.
      subst mGive'.
      eapply exec.seq_cps.
      eapply @exec.interact with (mGive := mGive).
      + eapply map.split_comm. exact B.
      + rewrite arg_regs_alt by blia. 1: eassumption.
      + eassumption.
      + intros.
        match goal with
        | H: context[outcome], A: context[outcome] |- _ =>
          specialize H with (1 := A); move H at bottom
        end.
        fwd.
        rename l into l1, l' into l1'.
        rename H2p0 into P.
        assert (List.length (List.firstn (length resvars) (reg_class.all reg_class.arg)) =
                List.length resvals) as HL. {
          eapply map.putmany_of_list_zip_sameLength in P. rewrite <- P.
          rewrite List.firstn_length. change (length (reg_class.all reg_class.arg)) with 8%nat.
          blia.
        }
        eapply map.sameLength_putmany_of_list in HL. destruct HL as (l2'' & ER).
        eexists. split. 1: exact ER.
        intros.
        eapply set_vars_to_reg_range_correct; cycle 1.
        { eassumption. }
        { eapply map.putmany_of_list_zip_to_getmany_of_list.
          - rewrite <- arg_regs_alt by blia. eassumption.
          - eapply List.NoDup_unfoldn_Z_seq. }
        { blia. }
        { reflexivity. }
        { unfold a0, a7. blia. }
        { eassumption. }
        { intros. do 6 eexists. split. 1: eassumption. ssplit.
          - eapply H2p1.
            unfold map.split. split; [reflexivity|].
            move C at bottom.
            unfold sep at 1 in C. destruct C as (mKeepL' & mRest & SC & ? & _). subst mKeepL'.
            move H2 at bottom. unfold map.split in H2. fwd.
            eapply map.shrink_disjoint_l; eassumption.
          - cbn in *. subst. add_bounds. cost_solve.
          (* cost_SInteract constraint: prespill - postspill >= (...32...) i think? *)
          - align_trace.
          - intros. subst. rewrite sfix_step. simpl. simpl_rev.
            repeat rewrite <- app_assoc. reflexivity. }
        (* related for set_vars_to_reg_range_correct: *)
        unfold related.
        eexists _, _, _. ssplit.
        * reflexivity.
        * eenough ((eq _ * (word_array fpval stackwords * frame))%sep m') as En.
          1: ecancel_assumption.
          move C at bottom.
          eapply grow_eq_sep. 1: exact C. eassumption.
        * eassumption.
        * eassumption.
        * eassumption.
        * eapply arg_regs_absorbs_putmany_of_list_zip; try eassumption.
        * eassumption.
        * eassumption.

    - (* exec.call *)
      (* H = High-level, L = Low-level, C = Caller, F = called Function

                   H                                       L

                  lCH1                                    lCL1
                                                   set_reg_range_to_vars
                                                          lCL2
             get/putmany_of_list                    get/putmany_of_list
                                                          lFL3
                                                   set_vars_to_reg_range
                  lFH4                                    lFL4
             function body                           function body
                  lFH5                                    lFL5
                                                   set_reg_range_to_vars
                                                          lFL6
           get/putmany_of_list                      get/putmany_of_list
                                                          lCL7
                                                   set_vars_to_reg_range
                  lCH8                                    lCL8
      *)
      rename l into lCH1, l2 into lCL1, st0 into lFH4.
      rename H4p0 into FR, H4p1 into FA.
      unfold spill_functions in Ev.
      eapply map.try_map_values_fw in Ev. 2: eassumption.
      unfold spill_fun in Ev. fwd.
      eapply exec.seq_cps.
      apply_in_hyps @map.getmany_of_list_length.
      apply_in_hyps @map.putmany_of_list_zip_sameLength.
      eapply set_reg_range_to_vars_correct; try eassumption || (unfold a0, a7 in *; blia).
      intros kCL2 lCL2 ? ? ? ? ?. subst.
      assert (bytes_per_word = 4 \/ bytes_per_word = 8) as B48. {
        unfold bytes_per_word. destruct width_cases as [E' | E']; rewrite E'; cbv; auto.
      }
      eapply exec.seq_cps.
      assert (length (List.firstn (length params) (reg_class.all reg_class.arg)) = length argvs)
        as L. {
        rewrite List.firstn_length. change (length (reg_class.all reg_class.arg)) with 8%nat. blia.
      }
      eapply map.sameLength_putmany_of_list in L.
      destruct L as (lFL3 & P).
      rewrite !arg_regs_alt by blia.
      eapply exec.call_cps; try eassumption.
      set (maxvar' := (Z.max (max_var fbody)
                             (Z.max (fold_left Z.max params 0) (fold_left Z.max rets 0)))) in *.
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
        destr (0 <=? (maxvar' - 31)).
        - rewrite Z2Nat.id by assumption. rewrite Z.mul_comm. apply Z_mod_mult.
        - replace (Z.of_nat (Z.to_nat (maxvar' - 31))) with 0 by blia.
          rewrite Z.mul_0_r.
          apply Zmod_0_l.
      }
      eapply F in Pt. clear F.
      assert (length words = Z.to_nat (maxvar' - 31)) as L''. {
        Z.to_euclidean_division_equations; blia.
      }
      eapply exec.seq_cps.
      unfold related in H4. fwd. rename lStack into lStack1, lRegs into lRegs1.
      eapply set_vars_to_reg_range_correct.
      { eapply fresh_related with (m1 := m) (frame := (word_array fpval stackwords * frame)%sep).
        - eassumption.
        - blia.
        - exact L''.
        - enough ((eq m * word_array fpval stackwords * frame * word_array a words)%sep mCombined).
          1: ecancel_assumption.
          unfold sep at 1. do 2 eexists.
          split. 1: exact Sp.
          split. 1: ecancel_assumption. exact Pt. }
      { eassumption. }
      { eapply map.getmany_of_list_put_diff. {
          eapply List.not_In_Z_seq. unfold fp, a0. blia.
        }
        eapply map.putmany_of_list_zip_to_getmany_of_list.
        - rewrite <- arg_regs_alt by blia. exact P.
        - eapply List.NoDup_unfoldn_Z_seq.
      }
      { blia. }
      { reflexivity. }
      { unfold a0, a7. blia. }
      { eapply Forall_impl. 2: eapply Forall_and.
        2: eapply List.forallb_to_Forall.
        3: eassumption.
        2: {
          unfold is_valid_src_var.
          intros *. intro F.
          rewrite ?Bool.andb_true_iff, ?Bool.orb_true_iff, ?Z.ltb_lt in F. exact F.
        }
        2: eapply Forall_le_max.
        cbv beta.
        subst maxvar'. clear. blia. }
      intros kL4 mL4 lFL4 mcL4 R ? ?. subst.
      eapply exec.seq_cps.
      eapply exec.weaken. {
        eapply IHexec with (f := fun _ => _). 2: exact R.
        - unfold valid_vars_src.
          eapply Forall_vars_stmt_impl.
          2: eapply max_var_sound.
          2: eapply forallb_vars_stmt_correct.
          3: eassumption.
          2: { unfold is_valid_src_var.
               intros *.
               rewrite ?Bool.andb_true_iff, ?Bool.orb_true_iff, ?Z.ltb_lt. reflexivity. }
          cbv beta. subst maxvar'. blia.
        - intros. rewrite associate_one_left. rewrite H6. rewrite sfix_step.
          simpl_rev. simpl. rewrite H. simpl_rev.
          repeat rewrite <- app_assoc. reflexivity. }
      cbv beta. intros kL5 tL5 mL5 lFL5 mcL5 (kH5 & tH5 & mH5 & lFH5 & mcH5 & kH5'' & R5 & OC & Hmetrics & Hk5'' & CT).
      match goal with
      | H: context[outcome], A: context[outcome] |- _ =>
        specialize H with (1 := A); move H at bottom; rename H into Q
      end.
      fwd. rename l' into lCH8.
      eapply set_reg_range_to_vars_correct.
      { eassumption. }
      { blia. }
      { reflexivity. }
      { unfold a0, a7. blia. }
      { eapply Forall_impl. 2: eapply Forall_and.
        2: eapply List.forallb_to_Forall.
        3: eassumption.
        2: {
          unfold is_valid_src_var.
          intros *. intro F.
          rewrite ?Bool.andb_true_iff, ?Bool.orb_true_iff, ?Z.ltb_lt in F. exact F.
        }
        2: eapply Forall_le_max.
        cbv beta.
        subst maxvar'. clear. blia. }
      { eassumption. }
      rename R into R0.
      intros kFL6 lFL6 mcL6 R GM ? ?. subst.
      (* prove that if we remove the additional stack provided by exec.stackalloc
         and store the result vars back into the caller's registers,
         states are still related and postcondition holds *)
      unfold related in R. fwd. rename lStack into lStack5, lRegs into lRegs5.
      move A at bottom. move Sp at bottom.
      assert ((eq mH5 * word_array fpval stackwords * frame * word_array a stackwords0)%sep mL5)
        as M2 by ecancel_assumption.
      unfold sep in M2 at 1. unfold map.split in M2.
      destruct M2 as (m2Small & mStack' & (? & ?) & ? & M2).
      assert (length (List.unfoldn (BinInt.Z.add 1) (length binds) a0) = length retvs) as PM67. {
        apply_in_hyps @map.getmany_of_list_length.
        apply_in_hyps @map.putmany_of_list_zip_sameLength.
        congruence.
      }
      eapply map.sameLength_putmany_of_list with (st := lCL2) in PM67.
      destruct PM67 as (lCL7 & PM67).
      subst mL5. unfold map.split.
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             end.
      2: reflexivity.
      {
        eapply cast_word_array_to_bytes in M2.
        eapply array_1_to_anybytes in M2.
        match goal with
        | H: Memory.anybytes a ?LEN1 mStack' |-
          Memory.anybytes a ?LEN2 mStack' => replace LEN2 with LEN1; [exact H|]
        end.
        erewrite List.flat_map_const_length. 2: {
          intros w. rewrite LittleEndianList.length_le_split; trivial.
        }
        simpl. blia. }
      { eassumption. }
      { rewrite arg_regs_alt by blia. eassumption. }
      { exact PM67. }
      eapply set_vars_to_reg_range_correct.
      { unfold related. eexists lStack1, lRegs1, _. ssplit.
        { reflexivity. }
        { eassumption. }
        { eassumption. }
        { eassumption. }
        { eassumption. }
        { eapply arg_regs_absorbs_putmany_of_list_zip; try eassumption.
          apply_in_hyps @map.getmany_of_list_length.
          apply_in_hyps @map.putmany_of_list_zip_sameLength.
          replace (length rets) with (length binds) by congruence.
          rewrite arg_regs_alt by blia. exact PM67. }
        { eassumption. }
        { eassumption. }
      }
      { eassumption. }
      { eapply map.putmany_of_list_zip_to_getmany_of_list. 1: exact PM67.
        eapply List.NoDup_unfoldn_Z_seq. }
      { blia. }
      { reflexivity. }
      { unfold a0, a7. blia. }
      { eassumption. }
      { intros k22 m22 l22 mc22 R22 ? ?. subst. do 6 eexists. ssplit; try eassumption.
        - move Hmetrics at bottom. add_bounds. cost_solve.
          (* cost_SCall constraint: prespill - postspill >= (...66...) i think? *)
        - align_trace.
        - intros. rewrite sfix_step. simpl. simpl_rev. rewrite H. Search fbody.
          repeat rewrite <- app_assoc in *. simpl in *. rewrite CT.
          reflexivity. }

    - (* exec.load *)
      eapply exec.seq_cps.
      eapply load_iarg_reg_correct; (blia || eassumption || idtac).
      intros.
      eapply exec.seq_cps.
      pose proof H2 as A. unfold related in A. fwd.
      unfold Memory.load, Memory.load_Z, Memory.load_bytes in *. fwd.
      eapply exec.load. {
        rewrite map.get_put_same. reflexivity. }
      { edestruct (@sep_def _ _ _ m2 (eq m)) as (m' & m2Rest & Sp & ? & ?).
        1: ecancel_assumption. unfold map.split in Sp. subst. fwd.
        unfold Memory.load, Memory.load_Z, Memory.load_bytes.
        erewrite map.getmany_of_tuple_in_disjoint_putmany; eauto. }
      eapply save_ires_reg_correct''; eauto. after_save_ires_reg_correct''.
    - (* exec.store *)
      eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac). intros.
      eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac). intros.
      pose proof H6 as A. unfold related in A. fwd.
      unfold Memory.store, Memory.store_Z, Memory.store_bytes in *. fwd.
      edestruct (@sep_def _ _ _ m2 (eq m)) as (m' & m2Rest & Sp & ? & ?).
      1: ecancel_assumption. unfold map.split in Sp. subst. fwd.
      eapply exec.store.
      1: eapply get_iarg_reg_1; eauto with zarith.
      1: apply map.get_put_same.
      { unfold Memory.store, Memory.store_Z, Memory.store_bytes.
        unfold Memory.load_bytes in *.
        erewrite map.getmany_of_tuple_in_disjoint_putmany; eauto. }
      do 6 eexists. ssplit. 2: eassumption.
      + unfold related.
        repeat match goal with
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               end.
        all: try eassumption || reflexivity.
        spec store_bytes_sep_hi2lo as A. 1: eassumption.
        all: ecancel_assumption.
      + irs.
      + align_trace.
      + intros. rewrite sfix_step. simpl. simpl_rev. repeat rewrite <- app_assoc.
        reflexivity.
    - (* exec.inlinetable *)
      eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac). intros.
      eapply exec.seq_cps.
      eapply exec.inlinetable.
      { unfold ires_reg, iarg_reg, spill_tmp, fp, a0, a7 in *. destr (32 <=? x); destr (32 <=? i); try blia. }
      { rewrite map.get_put_same. reflexivity. }
      { eassumption. }
      eapply save_ires_reg_correct''; eauto. after_save_ires_reg_correct''.
    - (* exec.stackalloc *)
      rename H1 into IH.
      eapply exec.stackalloc. 1: assumption.
      intros.
      eapply exec.seq_cps.
      edestruct grow_related_mem as (mCombined1 & ? & ?). 1,2: eassumption.
      eapply save_ires_reg_correct''; eauto.
      assert (Ha : a = pick_sp1 k).
      { subst a. specialize (H4 nil). simpl in H4. rewrite H4.
        rewrite sfix_step. simpl. simpl_rev. reflexivity. }
      rewrite Ha in *. clear Ha a. intros.
      eapply exec.weaken.
      { eapply IH with (f := fun _ => _); eauto.
        intros. rewrite associate_one_left. rewrite H4.
        rewrite sfix_step. simpl. simpl_rev. repeat rewrite <- app_assoc.
        reflexivity. }
      cbv beta. intros. fwd.
      edestruct shrink_related_mem as (mSmall2 & ? & ?). 1,2: eassumption.
      repeat match goal with
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             end.
      1,4,3,2: eassumption.
      + irs.
      + align_trace.
      + intros. rewrite sfix_step. simpl. simpl_rev.
        repeat rewrite <- app_assoc in *. rewrite H8p4. reflexivity.
    - (* exec.lit *)
      eapply exec.seq_cps. eapply exec.lit.
      eapply save_ires_reg_correct''; eauto. after_save_ires_reg_correct''.      
    - (* exec.op *)
      unfold exec.lookup_op_locals in *.
      eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac).
      clear H3. intros. destruct_one_match; fwd.
      { eapply exec.seq_cps. eapply exec.seq_cps.
        eapply load_iarg_reg_correct; (blia || eassumption || idtac).
        clear H2. intros. eapply exec.op.
        { eapply get_iarg_reg_1; eauto with zarith. }
        { unfold exec.lookup_op_locals in *. apply map.get_put_same. }
        { eapply save_ires_reg_correct''; eauto. after_save_ires_reg_correct''.
          destruct op; reflexivity. } }
      { eapply exec.seq_cps. eapply exec.op.
        { apply map.get_put_same. }
        { unfold exec.lookup_op_locals in *. reflexivity. }
        { eapply save_ires_reg_correct''; eauto. after_save_ires_reg_correct''.
          destruct op; reflexivity. } }
    - (* exec.set *)
      eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac). intros.
      eapply exec.seq_cps.
      eapply exec.set. 1: apply map.get_put_same.
      eapply save_ires_reg_correct''; eauto. after_save_ires_reg_correct''.
    - (* exec.if_true *)
      unfold prepare_bcond. destr cond; cbn [ForallVars_bcond eval_bcond spill_bcond] in *; fwd.
      + eapply exec.seq_assoc.
        eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac). intros.
        eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac). intros.
        eapply exec.if_true. {
          cbn. erewrite get_iarg_reg_1 by eauto with zarith. rewrite map.get_put_same. congruence.
        }
        eapply exec.weaken.
        * eapply IHexec with (f := fun _ => _); try eassumption.
          intros. rewrite associate_one_left, H3, sfix_step.
          simpl. simpl_rev. repeat rewrite <- app_assoc. reflexivity.
        * cbv beta; intros; fwd. eexists _, t1', m1', l1', mc1', _.
          ssplit; try eassumption.
          -- sirs.
          -- align_trace.
          -- intros. rewrite sfix_step. simpl. simpl_rev.
             repeat rewrite <- app_assoc in *. rewrite H5p4. reflexivity.
      + eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac). intros.
        eapply exec.if_true. {
          cbn. rewrite map.get_put_same. rewrite word.eqb_ne by assumption. reflexivity.
        }
        eapply exec.weaken.
        * eapply IHexec with (f := fun _ => _); try eassumption.
          intros. rewrite associate_one_left, H3, sfix_step.
          simpl. simpl_rev. repeat rewrite <- app_assoc. reflexivity.
        * cbv beta; intros; fwd. eexists _, t1', m1', l1', mc1', _.
          ssplit; try eassumption.
          -- sirs.
          -- align_trace.
          -- intros. rewrite sfix_step. simpl. simpl_rev.
             repeat rewrite <- app_assoc in *. rewrite H4p4. reflexivity.
    - (* exec.if_false *)
      unfold prepare_bcond. destr cond; cbn [ForallVars_bcond eval_bcond spill_bcond] in *; fwd.
      + eapply exec.seq_assoc.
        eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac). intros.
        eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac). intros.
        eapply exec.if_false. {
          cbn. erewrite get_iarg_reg_1 by eauto with zarith. rewrite map.get_put_same. congruence.
        }
        eapply exec.weaken.
        * eapply IHexec with (f := fun _ => _); try eassumption.
          intros. rewrite associate_one_left, H3, sfix_step.
          simpl. simpl_rev. repeat rewrite <- app_assoc. reflexivity.
        * cbv beta; intros; fwd. eexists _, t1', m1', l1', mc1', _.
          ssplit; try eassumption.
          -- sirs.
          -- align_trace.
          -- intros. rewrite sfix_step. simpl. simpl_rev.
             repeat rewrite <- app_assoc in *. rewrite H5p4. reflexivity.
      + eapply exec.seq_cps. eapply load_iarg_reg_correct; (blia || eassumption || idtac). intros.
        eapply exec.if_false. {
          cbn. rewrite map.get_put_same. rewrite word.eqb_eq; reflexivity.
        }
        eapply exec.weaken.
        * eapply IHexec with (f := fun _ => _); try eassumption.
          intros. rewrite associate_one_left, H3, sfix_step.
          simpl. simpl_rev. repeat rewrite <- app_assoc. reflexivity.
        * cbv beta; intros; fwd. eexists _, t1', m1', l1', mc1', _.
          ssplit; try eassumption.
          -- sirs.
          -- align_trace.
          -- intros. rewrite sfix_step. simpl. simpl_rev.
             repeat rewrite <- app_assoc in *. rewrite H1p6. reflexivity.
    - (* exec.loop *)
      rename IHexec into IH1, H3 into IH2, H5 into IH12.
      eapply exec.loop_cps.
      eapply exec.seq.
      { eapply IH1; try eassumption.
        intros. rewrite H8. rewrite sfix_step. reflexivity. }
      cbv beta. intros. fwd.
      unfold prepare_bcond. destr cond; cbn [ForallVars_bcond] in *; fwd.
      + specialize H0 with (1 := H3p1). cbn in H0. fwd.
        eapply exec.seq.
        { eapply load_iarg_reg_correct''; (blia || eassumption || idtac). }
        cbv beta. intros. fwd.
        eapply exec.weaken. {
          eapply load_iarg_reg_correct''; (blia || eassumption || idtac).
        }
        cbv beta. intros. fwd. cbn [eval_bcond spill_bcond].
        erewrite get_iarg_reg_1 by eauto with zarith.
        rewrite map.get_put_same. eexists. split; [reflexivity|].
        split; intros.
        * do 6 eexists. ssplit.
          -- exact H3p10.
          -- eapply H1. 1: eassumption. cbn. rewrite E, E0. congruence.
          -- sirs.
          -- align_trace.
          -- intros. rewrite sfix_step. simpl. repeat rewrite <- app_assoc in *.
             rewrite H3p4. rewrite List.skipn_app_r by reflexivity.
             cbv [Let_In_pf_nd]. simpl. simpl_rev. repeat rewrite <- app_assoc.
             reflexivity.
        * eapply exec.weaken. 1: eapply IH2; try eassumption.
          -- cbn. rewrite E, E0. congruence.
          -- intros. rewrite associate_one_left. rewrite app_assoc. rewrite H8.
             rewrite sfix_step. simpl. simpl_rev. repeat rewrite <- app_assoc in *.
             rewrite H3p4. rewrite List.skipn_app_r by reflexivity. reflexivity.
          -- cbv beta. intros. fwd. eapply exec.weaken.
             ++ eapply IH12 with (f := fun _ => _); try eassumption.
                { repeat split; eauto; blia. }
                intros. rewrite associate_one_left. repeat rewrite app_assoc.
                rewrite H8. rewrite sfix_step. simpl. simpl_rev. rewrite H3p4.
                rewrite List.skipn_app_r by reflexivity. cbv [Let_In_pf_nd].
                repeat rewrite <- app_assoc in *. rewrite H5p4.
                rewrite List.skipn_app_r by reflexivity. reflexivity.
             ++ cbv beta; intros; fwd. eexists _, t1'1, m1'1, l1'1, mc1'1, _.
                ssplit; try eassumption.
                --- sirs.
                --- align_trace.
                --- intros. rewrite sfix_step. simpl. simpl_rev.
                    repeat rewrite <- app_assoc in *. rewrite H3p4.
                    rewrite List.skipn_app_r by reflexivity. cbv [Let_In_pf_nd].
                    simpl. rewrite H5p4. rewrite List.skipn_app_r by reflexivity.
                    rewrite H5p8. reflexivity.
      + specialize H0 with (1 := H3p1). cbn in H0. fwd.
        eapply exec.weaken. {
          eapply load_iarg_reg_correct''; (blia || eassumption || idtac).
        }
        cbv beta. intros. fwd. cbn [eval_bcond spill_bcond].
        rewrite map.get_put_same. eexists. split; [reflexivity|].
        split; intros.
        * do 6 eexists. ssplit.
          -- exact H3p8.
          -- eapply H1. 1: eassumption. cbn. rewrite E. congruence.
          -- sirs.
          -- align_trace.
          -- intros. rewrite sfix_step. simpl. repeat rewrite <- app_assoc in *.
             rewrite H3p4. rewrite List.skipn_app_r by reflexivity.
             cbv [Let_In_pf_nd]. simpl. simpl_rev. repeat rewrite <- app_assoc.
             reflexivity.
        * eapply exec.weaken. 1: eapply IH2; try eassumption.
          -- cbn. rewrite E. congruence.
          -- intros. rewrite associate_one_left. rewrite app_assoc. rewrite H8.
             rewrite sfix_step. simpl. simpl_rev. repeat rewrite <- app_assoc in *.
             rewrite H3p4. rewrite List.skipn_app_r by reflexivity. reflexivity.
          -- cbv beta. intros. fwd. eapply exec.weaken.
             ++ eapply IH12 with (f := fun _ => _); try eassumption.
                { repeat split; eauto; blia. }
                intros. rewrite associate_one_left. repeat rewrite app_assoc.
                rewrite H8. rewrite sfix_step. simpl. simpl_rev. rewrite H3p4.
                rewrite List.skipn_app_r by reflexivity. cbv [Let_In_pf_nd].
                repeat rewrite <- app_assoc in *. rewrite H5p4.
                rewrite List.skipn_app_r by reflexivity. reflexivity.
             ++ cbv beta; intros; fwd. eexists _, t1'1, m1'1, l1'1, mc1'1, _.
                ssplit; try eassumption.
                --- sirs.
                --- align_trace.
                --- intros. rewrite sfix_step. simpl. simpl_rev.
                    repeat rewrite <- app_assoc in *. rewrite H3p4.
                    rewrite List.skipn_app_r by reflexivity. cbv [Let_In_pf_nd].
                    simpl. rewrite H5p4. rewrite List.skipn_app_r by reflexivity.
                    rewrite H5p8. reflexivity.
    - (* exec.seq *)
      cbn in *. fwd.
      rename H1 into IH2, IHexec into IH1.
      eapply exec.seq.
      + eapply IH1. 1,2: eassumption. intros. rewrite H4.
        rewrite sfix_step. reflexivity.
      + cbn. intros. fwd. eapply exec.weaken.
        * eapply IH2; try eassumption. intros. rewrite app_assoc. rewrite H4.
          rewrite sfix_step. simpl. simpl_rev. rewrite H1p4.
          rewrite List.skipn_app_r by reflexivity. reflexivity.
        * cbv beta. intros. fwd. eexists _, t1'0, m1'0, l1'0, mc1'0, _.
          ssplit; try eassumption.
          -- solve_MetricLog.
          -- align_trace.
          -- intros. rewrite sfix_step. simpl. simpl_rev.
             repeat rewrite <- app_assoc in *. rewrite H1p4.
             rewrite List.skipn_app_r by reflexivity. rewrite H1p8. reflexivity.
    - (* exec.skip *)
      eapply exec.skip. eexists _, t, m, l, mc, _. ssplit; try eassumption.
      + solve_MetricLog.
      + align_trace.
      + intros. rewrite sfix_step. reflexivity.
  Qed.
 
  Lemma spill_fun_correct: forall e1 e2 pick_sp2 argnames1 retnames1 body1 argnames2 retnames2 body2,
      spill_functions e1 = Success e2 ->
      spill_fun (argnames1, retnames1, body1) = Success (argnames2, retnames2, body2) ->
      forall argvals kH kL t m mcH mcL (post: leakage -> Semantics.trace -> mem -> list word -> MetricLog -> Prop),
        call_spec e1 (argnames1, retnames1, body1) (fun k => snd (fun_leakage e1 pick_sp2 (argnames1, retnames1, body1) (skipn (length kH) (rev k)) (rev kL))) kH t m argvals mcH post ->
        call_spec_spilled e2 (argnames2, retnames2, body2) pick_sp2 kL t m argvals mcL
          (fun kL' t' m' l' mcL' =>
             exists kH'' mcH',
               post (kH'' ++ kH) t' m' l' mcH' /\
                 metricsLeq (mcL' - mcL) (mcH' - mcH) /\
                 fst (fun_leakage e1 pick_sp2 (argnames1, retnames1, body1) (rev kH'') (rev kL)) = rev kL').
  Proof.
    intros. eapply spill_fun_correct_aux; try eassumption.
    apply spilling_correct. assumption.
  Qed.

End Spilling.
