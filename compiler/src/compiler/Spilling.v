Require Import Coq.ZArith.ZArith.
Require Import compiler.FlatImp.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.simpl_rewrite.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.Utility.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import compiler.Simp.
Require Import compiler.Simulation.
Require Import compiler.SeparationLogic.
Require Import compiler.SpillingMapGoals.

Open Scope Z_scope.

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

  Context {W: Utility.Words} {mem: map.map word byte}.

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
    | SLoad _ x y _ | SStore _ x y _ | SSet x y => Z.max x y
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
    clear mem locals localsOk env ext_spec.
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

  Definition related_old(maxvar: Z)(frame: mem)(done: bool):
    FlatImp.SimState Z -> FlatImp.SimState Z -> Prop :=
    fun '(t1, m1, l1, mc1) '(t2, m2, l2, mc2) =>
      exists fpval mL mStack,
        t1 = t2 /\
        map.split m2 m1 mL /\ map.split mL mStack frame /\
        (forall r, r < fp -> map.get l1 r = None) /\
        map.get l2 fp = Some fpval /\
        (forall r, fp < r < 32 -> map.get l1 r = map.get l2 r) /\
        (forall r, 32 <= r < maxvar -> exists v,
              Memory.load Syntax.access_size.word mStack
                          (word.add fpval (word.of_Z ((r - 32) * bytes_per_word))) = Some v /\
              forall v', map.get l1 r = Some v' -> v' = v).

  (* could be treated as a separation logic assertion *)
  Definition spilled_vars(fpval: word)(maxvar: Z)(lStack: locals)(mStack: mem): Prop :=
    forall r, 32 <= r <= maxvar -> exists v,
        Memory.load Syntax.access_size.word mStack
                    (word.add fpval (word.of_Z ((r - 32) * bytes_per_word))) = Some v /\
        forall v', map.get lStack r = Some v' -> v' = v.

  Definition split_at(l: locals)(l1: locals)(b: Z)(l2: locals): Prop :=
    map.split l l1 l2 /\
    (forall r v, map.get l1 r = Some v -> r < b) /\
    (forall r v, map.get l2 r = Some v -> b <= r).

  Definition related_old1(maxvar: Z)(frame: mem)(done: bool):
    FlatImp.SimState Z -> FlatImp.SimState Z -> Prop :=
    fun '(t1, m1, l1, mc1) '(t2, m2, l2, mc2) =>
      exists fpval tmp1val tmp2val mL mStack lStack lRegs,
        t1 = t2 /\
        map.split m2 m1 mL /\ map.split mL mStack frame /\
        split_at l1 lRegs 32 lStack /\
        split_at l2 (map.of_list [(tmp1, tmp1val); (tmp2, tmp2val); (fp, fpval)]) regvar0 lRegs.

  Definition map__dom_in(l: locals)(P: Z -> Prop): Prop := forall v r, map.get l r = Some v -> P r.

  Definition map__covers_dom(l: locals)(P: Z -> Prop): Prop := forall r, P r -> exists v, map.get l r = Some v.

  Axiom map__dom_in_put: forall (l: locals) k v P,
      map__dom_in l P ->
      P k ->
      map__dom_in (map.put l k v) P.

  Lemma map__split_dom_in: forall (l l1 l2: locals) P1 P2,
      map.split l l1 l2 ->
      map__dom_in l1 P1 ->
      map__dom_in l2 P2 ->
      map__dom_in l (fun x => P1 x \/ P2 x).
  Proof.
    unfold map.split, map__dom_in, map.disjoint. intros. simp.
    rewrite map.get_putmany_dec in H2.
    destr (map.get l2 r); simp; intuition eauto.
  Qed.

  Lemma map__putmany_of_list_zip_dom_in: forall (l l': locals) ks vs P,
      map.putmany_of_list_zip ks vs l = Some l' ->
      map__dom_in l P ->
      map__dom_in l' (fun x => P x \/ List.In x ks).
  Admitted.

(*
  Lemma map__dom_in_split_l: forall (l l1 l2: locals) P,
      map.split l l1 l2 ->
      map__dom_in l2 P ->
      map__dom_in l1 (fun x => ~ P x).
  Proof.
*)

  Definition related(maxvar: Z)(frame: mem)(done: bool):
    FlatImp.SimState Z -> FlatImp.SimState Z -> Prop :=
    fun '(t1, m1, l1, mc1) '(t2, m2, l2, mc2) =>
      exists fpval tmp1val tmp2val mL mStack lStack lRegs,
        t1 = t2 /\
        map.split m2 m1 mL /\ map.split mL mStack frame /\
        map__dom_in lRegs (fun x => fp < x < 32) /\
        map__dom_in lStack (fun x => 32 <= x <= maxvar) /\
        map.split l1 lRegs lStack /\
        map.split l2 lRegs (map.of_list [(tmp1, tmp1val); (tmp2, tmp2val); (fp, fpval)]) /\
        spilled_vars fpval maxvar lStack mStack.

  Definition envs_related(e1 e2: env): Prop :=
    forall f argvars resvars body1,
      map.get e1 f = Some (argvars, resvars, body1) ->
      map.get e2 f = Some (argvars, resvars, spill_fbody body1).

  Axiom map__split_spec: forall (M A B: mem),
      map.split M A B <-> forall k,
        (exists v, map.get M k = Some v /\
                   ((map.get A k = Some v /\ map.get B k = None) \/
                    (map.get B k = Some v /\ map.get A k = None))) \/
        (map.get M k = None /\ map.get A k = None /\ map.get B k = None).

  Axiom map__putmany_spec: forall (m1 m2: mem) k,
      (exists v, map.get (map.putmany m1 m2) k = Some v /\
                 (map.get m2 k = Some v \/ (map.get m2 k = None /\ map.get m1 k = Some v))) \/
      (map.get (map.putmany m1 m2) k = None /\ map.get m2 k = None /\ map.get m1 k = None).

  Axiom map__getmany_of_list_shrink: forall (l l1 l2: locals) keys,
      map.split l l1 l2 ->
      Forall (fun k => map.get l2 k = None) keys ->
      map.getmany_of_list l keys = map.getmany_of_list l1 keys.

  Axiom map__putmany_of_list_zip_split: forall (l l' l1 l2: locals) keys values,
      map.putmany_of_list_zip keys values l = Some l' ->
      map.split l l1 l2 ->
      Forall (fun k => map.get l2 k = None) keys ->
      exists l1', map.split l' l1' l2 /\ map.putmany_of_list_zip keys values l1 = Some l1'.

  Axiom map__putmany_of_list_zip_grow: forall (l l1 l1' l2: locals) keys values,
      map.putmany_of_list_zip keys values l1 = Some l1' ->
      map.split l l1 l2 ->
      Forall (fun k => map.get l2 k = None) keys ->
      exists l', map.split l' l1' l2 /\ map.putmany_of_list_zip keys values l = Some l'.

  Lemma map__getmany_of_list_preserved: forall (l1 l2: locals) ks,
      (forall k, In k ks -> map.get l1 k = map.get l2 k) ->
      map.getmany_of_list l1 ks = map.getmany_of_list l2 ks.
  Proof.
    induction ks; intros. 1: reflexivity.
    unfold map.getmany_of_list in *. simpl.
    rewrite IHks. 2: {
      intros. eapply H. simpl. auto.
    }
    specialize (H a). simpl in H. rewrite H. 2: auto.
    reflexivity.
  Qed.

  Lemma seq_cps: forall e s1 s2 t m l mc post,
      exec e s1 t m l mc (fun t' m' l' mc' => exec e s2 t' m' l' mc' post) ->
      exec e (SSeq s1 s2) t m l mc post.
  Proof.
    intros. eapply exec.seq. 1: eassumption. simpl. clear. auto.
  Qed.

  (* cps style
  Lemma load_arg_reg1_correct: forall e a t m l mc post,
      post ... ->
      exec e (load_arg_reg1 a) t m l mc post. *)

  (* seq style
  Lemma load_arg_reg1_correct: forall e s a t m l mc post,
      exec e s t
      exec e (SSeq (load_arg_reg1 a) s) t m l mc post. *)

  Lemma spilling_sim(e1 e2: env):
      envs_related e1 e2 ->
      forall frame s1 maxvar,
        valid_vars_src maxvar s1 ->
        simulation (SimExec Z e1 s1) (SimExec Z e2 (spill_stmt s1))
                   (related maxvar frame).
  Proof.
    unfold simulation, SimExec.
    intros Ev frame s1 maxvar V (((t1 & m1) & l1) & mc1) (((t2 & m2) & l2) & mc2) post1 R Exec.
    revert frame maxvar V t2 m2 l2 mc2 R.
    unfold compile_inv, related.
    match type of Exec with
    | exec _ _ _ _ _ _ ?P => remember P as post
    end.
    revert post1 Heqpost.
    induction Exec; simpl; intros; simp; subst.
    - (* exec.interact *)
      eapply @exec.interact with (mGive := mGive) (mKeep := map.putmany mKeep mL).
      + eapply split_interact; eassumption.
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
        pose proof H4 as P.
        eapply map__putmany_of_list_zip_split in P. 2: eassumption. 2: {
          eapply Forall_impl. 2: eassumption.
          simpl.
          clear -localsOk. unfold fp, tmp1, tmp2. intros.
          rewrite ?map.get_put_dec.
          rewrite ?(proj2 (Z.eqb_neq _ _ )) by blia.
          apply map.get_empty.
        }
        simp.
        eapply map__putmany_of_list_zip_grow with (l := l) in Pr. 2: eassumption. 2: {
          eapply Forall_impl. 2: eassumption.
          unfold map__dom_in in *. intros a B.
          destr (map.get lStack a). 2: reflexivity. exfalso.
          assert (32 <= a <= maxvar) by eauto. blia.
        }
        destruct Pr as (l2' & ? & ?).
        repeat match goal with
               | |- exists (_: FlatImp.SimState _), _ => refine (ex_intro _ (_, _, _, _) _)
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               end.
        9: eapply H2.
        1: reflexivity.
        9: eapply split_interact_shrink; eassumption.
        1: eapply split_interact_assoc; eassumption.
        1: eassumption.
        5: eassumption.
        5: eassumption.
        3: eassumption.
        2: eassumption.
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
        move Pl at bottom.
        admit. (* ok, but TODO use map.domain instead of dom_in and dom_covers *)

    - (* exec.call *)
      admit.
    - (* exec.load *)
      eapply seq_cps.
      unfold load_arg_reg1, arg_reg1, save_res_reg, res_reg, stack_loc.
      destr (Z.leb 32 a).
      + match goal with
        | H: spilled_vars _ _ _ _ |- _ => pose proof H as A
        end.
        unfold spilled_vars in A.
        assert (32 <= a <= maxvar) as B by blia. specialize A with (1 := B); clear B. simp.
        eapply exec.load with (addr0 := fpval) (v1 := v0).
        * admit. (* ok *)
        * admit. (* growing from mStack to m2 preserves Memory.load *)
        * eapply seq_cps. eapply exec.load. {
            rewrite map.get_put_same. reflexivity.
          } {
            match goal with
            | |- _ = ?opt => unify opt (Some v)
            end.
            assert (map.get lStack a = Some addr) as B by admit.
            specialize Ar with (1 := B). subst v0.
            (* growing from m to m2 preserves Memory.load *)
            admit.
          } {
            destr (Z.leb 32 x).
            - eapply exec.store.
              + rewrite ?map.get_put_diff by (cbv; discriminate).
                match goal with
                | |- _ = ?opt => unify opt (Some fpval)
                end.
                admit. (* ok *)
              + rewrite map.get_put_same. reflexivity.
              + admit. (* memory stuff... *)
              + repeat match goal with
                       | |- exists (_: FlatImp.SimState _), _ => refine (ex_intro _ (_, _, _, _) _)
                       | |- exists _, _ => eexists
                       | |- _ /\ _ => split
                       end.
                1: reflexivity.
                8: eassumption.
                * admit.
                * admit.
                * admit.
                * admit.
                * admit.
                * rewrite map.put_put_same. admit.
                * admit.
            - admit.
          }
      + admit.
    - (* exec.store *)
      admit.
    - (* exec.stackalloc *)
      rename H1 into IH.
      unfold save_res_reg, res_reg, stack_loc.
      destr (Z.leb 32 x).
      + eapply exec.stackalloc. 1: assumption.
        intros. eapply seq_cps. eapply exec.store.
        * rewrite map.get_put_diff by discriminate.
          match goal with
          | |- _ = ?opt => unify opt (Some fpval)
          end.
          admit. (* ok *)
        * rewrite map.get_put_same. reflexivity.
        * unfold Memory.store, Memory.store_Z, Memory.store_bytes.
          destruct_one_match. 2: admit. (* shouldn't happen *)
          reflexivity.
        * eapply exec.weaken. {
            pose (fun m => (Memory.unchecked_store_bytes (Memory.bytes_per Syntax.access_size.word) m
                      (word.add fpval (word.of_Z ((x - 32) * bytes_per_word)))
            (LittleEndian.split (@Memory.bytes_per width Syntax.access_size.word) (word.unsigned a)))) as upd.
            match goal with
            | |- exec _ _ _ ?M _ _ _ => change M with (upd mCombined)
            end.
            rename mStack0 into mStackHL.
            (* mStack is our stack memory used for spilling, while mStackHL is allocated by this
               SStackalloc and exposed as memory to the source program *)
            eapply IH with (mCombined := map.putmany mSmall mStackHL) (frame := frame)
                           (post2 := fun '(t', m', l', mc') =>
                                       exists mSmall' mStack',
                                         Memory.anybytes a n mStack' /\ map.split m' mSmall' mStack' /\
                                         post1 (t', mSmall', l', mc')).
            1: eassumption.
            1: eapply split_stackalloc_1; eassumption.
            1: reflexivity.
            1: eassumption.
            (* existentials to pick to satisfy relation before invoking IH *)
            eexists fpval, a, tmp2val, (upd mL), (upd mStack), (map.put lStack x a), lRegs.
            ssplit.
            1: reflexivity.
            1: {
              eapply split_stackalloc_2 with (m3 := upd m2). 1,2: admit. (* ok *)
            }
            1: admit. (* ok *)
            1: eassumption.
            1: eapply map__dom_in_put; [assumption|blia].
            1: admit. (* ok *)
            1: admit. (* ok *)
            1: admit. (* ok *)
          }
          simpl. intros. simp.
          exists (map.putmany mSmall' mL0), mStack'.
          repeat match goal with
                 | |- exists (_: FlatImp.SimState _), _ => refine (ex_intro _ (_, _, _, _) _)
                 | |- exists _, _ => eexists
                 | |- _ /\ _ => split
                 end.
          11: eassumption.
          1: eassumption.
          1: eapply split_stackalloc_2; eassumption.
          1: reflexivity.
          1: {
            match goal with
            | |- map.split _ _ ?M => unify M mL0
            end.
            eapply split_stackalloc_1; eassumption.
          }
          1: eassumption.
          5: eassumption.
          all: try eassumption.
      + admit. (* same but without spilling *)
(*
    - (* exec.lit *)
    - (* exec.op *)
    - (* exec.set *)
    - (* exec.if_true *)
    - (* exec.if_false *)
    - (* exec.loop *)
    - (* exec.seq *)
    - (* exec.skip *)
*)
  Abort.

End Spilling.
