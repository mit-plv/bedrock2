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
  (* 0: constant 0 *)
  (* 1: return address *)
  (* 2: stack pointer *)
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
      SStackalloc (res_reg x) n body;;
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

  Fixpoint calls_use_registers(s: stmt): bool :=
    match s with
    | SLoad _ _ _ _ | SStore _ _ _ _ | SLit _ _ | SOp _ _ _ _ | SSet _ _ | SSkip => true
    | SStackalloc x n body => calls_use_registers body
    | SIf _ s1 s2 | SLoop s1 _ s2 | SSeq s1 s2 => calls_use_registers s1 && calls_use_registers s2
    | SCall argvars _ resvars | SInteract argvars _ resvars =>
      List.forallb (Z.gtb 32) argvars && List.forallb (Z.gtb 32) resvars
    end.

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

  Definition spill_fbody(s: stmt): option stmt :=
    if calls_use_registers s
    then Some (SStackalloc fp (bytes_per_word * (max_var s - 32)) (spill_stmt s))
    else None.


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

  Definition related(maxvar: Z)(frame: mem)(done: bool):
    FlatImp.SimState Z -> FlatImp.SimState Z -> Prop :=
    fun '(t1, m1, l1, mc1) '(t2, m2, l2, mc2) =>
      exists fpval mL mStack,
        t1 = t2 /\
        map.split m2 m1 mL /\ map.split mL mStack frame /\
        (forall r, r < 5 -> map.get l1 r = None) /\
        map.get l2 5 = Some fpval /\
        (forall r v, 6 <= r < 32 -> map.get l1 r = Some v -> map.get l2 r = Some v) /\
        (forall r, 32 <= r < maxvar -> exists v,
              Memory.load Syntax.access_size.word mStack
                          (word.add fpval (word.of_Z ((r - 32) * bytes_per_word))) = Some v /\
              forall v', map.get l1 r = Some v' -> v' = v).

  Definition envs_related(e1 e2: env): Prop :=
    forall f argvars resvars body1,
      map.get e1 f = Some (argvars, resvars, body1) ->
      exists body2,
        spill_fbody body1 = Some body2 /\
        map.get e2 f = Some (argvars, resvars, body2).

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

  Lemma spilling_sim(e1 e2: env):
      envs_related e1 e2 ->
      forall frame s1 s2,
        spill_stmt s1 = s2 ->
        simulation (SimExec Z e1 s1) (SimExec Z e2 s2)
                   (related (max_var s1) frame).
  Proof.
    unfold simulation, SimExec.
    intros Ev frame s1 s2 E (((t1 & m1) & l1) & mc1) (((t2 & m2) & l2) & mc2) post1 R Exec.
    revert frame s2 E t2 m2 l2 mc2 R.
    unfold compile_inv, related.
    induction Exec; simpl; intros; simp; subst.
    - (* exec.interact *)
      eapply @exec.interact with (mGive := mGive) (mKeep := map.putmany mKeep mL).
      + eapply split_interact; eassumption.

(*
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
