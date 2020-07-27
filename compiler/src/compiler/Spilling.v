Require Import Coq.ZArith.ZArith.
Require Import compiler.FlatImp.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.simpl_rewrite.
From Hammer Require Import Tactics.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.Utility.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import compiler.Simp.
Require Import compiler.Simulation.
Require Import compiler.SeparationLogic.
Require Import compiler.SpillingMapGoals.

(* should not be committed usually *)
From Hammer Require Import Hammer.

Open Scope Z_scope.

Section Spilling.

  Notation stmt := (stmt Z).

  Definition zero := 0.
  Definition ra := 1.
  Definition sp := 2.
  Definition tmp1 := 3.
  Definition tmp2 := 4.
  Definition fp := 5. (* returned by stackalloc, always a constant away from sp: a wasted register *)

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
      SStackalloc (res_reg x) n (spill_stmt body);;
      save_res_reg x
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

  Definition related(maxvar: Z)(frame: mem)(done: bool):
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
    induction Exec; simpl; intros; simp; subst.
    - (* exec.interact *)
      eapply @exec.interact with (mGive := mGive) (mKeep := map.putmany mKeep mL).
      +

        rewrite map__split_spec in *.

        Set Hammer ReconstrLimit 20.
        Set Hammer ATPLimit 60.

        pose proof map__putmany_spec.

        (* hammer. Hammer failed: ATPs failed to find a proof. *)

        clear H3.
        (* Time hecrush use: map__putmany_spec. does not return for several minutes *)


        eapply split_interact; eassumption.
      + erewrite map__getmany_of_list_preserved. 1: eassumption.
        intros. eapply Forall_forall in Vr. 2: eassumption. symmetry. eauto.
      + eassumption.
      + intros.
        match goal with
        | H: context[outcome], A: context[outcome] |- _ =>
          specialize H with (1 := A)
        end.
        simp.

        repeat match goal with
               | |- exists (_: FlatImp.SimState _), _ => refine (ex_intro _ (_, _, _, _) _)
               | |- exists _, _ => eexists
               | |- _ /\ _ => split
               end.
        * (* TODO we need a "locals frame" or to say map.only_differ


    - (* exec.call *)
    - (* exec.load *)
    - (* exec.store *)
    - (* exec.stackalloc *)
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
