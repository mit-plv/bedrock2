Require Import Coq.ZArith.ZArith.
Require Import compiler.FlatImp.
Require Import coqutil.Decidable.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.Utility.
Require Import coqutil.Macros.unique.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Solver.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Map.TestLemmas.
Require Import bedrock2.Syntax.
Require Import compiler.util.ListLib.
Require Import compiler.Simp.
Require Import compiler.Simulation.


Local Notation "'bind_opt' x <- a ; f" :=
  (match a with
   | Some x => f
   | None => None
   end)
  (right associativity, at level 70, x pattern).

Axiom TODO_sam: False.

Section Live.

  Context {p: unique! Syntax.parameters}.
  Context (veq: varname -> varname -> bool).

  Definition live_bcond(cond: bcond): list varname :=
    match cond with
    | CondBinary _ x y => list_union veq [x] [y]
    | CondNez x => [x]
    end.

  (* set of variables which is live before executing s *)
  Fixpoint live(s: stmt)(usedlater: list varname): list varname :=
    match s with
    | SLoad _ x y  => list_union veq [y] (list_diff veq usedlater [x])
    | SStore _ x y => list_union veq [x] [y]
    | SLit x v     => list_diff veq usedlater [x]
    | SOp x op y z => list_union veq [y] (list_union veq [z] (list_diff veq usedlater [x]))
    | SSet x y     => list_union veq [y] (list_diff veq usedlater [x])
    | SIf cond s1 s2   => list_union veq (live_bcond cond)
                                     (list_union veq (live s1 usedlater) (live s2 usedlater))
    | SLoop s1 cond s2 =>
      (* exponential: we recurse into subterm s1 twice *)
      let L1 := live s1 usedlater in
      let L2 := live s1 (live s2 L1) in
      list_union veq (live_bcond cond) (list_union veq L1 L2)
    | SSeq s1 s2       => live s1 (live s2 usedlater)
    | SSkip => usedlater
    | SCall     argnames _ resnames => list_union veq argnames (list_diff veq usedlater resnames)
    | SInteract argnames _ resnames => list_union veq argnames (list_diff veq usedlater resnames)
    end.

End Live.

Module map.
  Class ops{K V: Type}(M: map.map K V) := {
    intersect: M -> M -> M; (* set intersection when interpreting maps as sets of tuples *)
    default_value: V;
  }.
  Definition putmany_of_pairs{K V: Type}{M: map.map K V}(m: M): list (K * V) -> M :=
    fix rec l :=
    match l with
    | nil => m
    | (k, v) :: rest => map.put (rec rest) k v
    end.

  Lemma putmany_of_pairs_extends{K V: Type}{M: map.map K V}{ok: map.ok M}
        {key_eqb: K -> K -> bool}{key_eq_dec: EqDecider key_eqb}:
    forall (pairs: list (K * V)) (m1 m2: M),
    map.extends m1 m2 ->
    map.extends (putmany_of_pairs m1 pairs) (putmany_of_pairs m2 pairs).
  Proof.
    induction pairs; intros.
    - simpl. assumption.
    - simpl. destruct a as [k v]. apply map.put_extends. eapply IHpairs. assumption.
  Qed.
End map.

Section RegAlloc.

  Context {srcvar: Type}.
  Context (srcvar_eqb: srcvar -> srcvar -> bool).
  Context {impvar: Type}.
  Context (impvar_eqb: impvar -> impvar -> bool).
  Context {func: Type}.
  Context (func_eqb: func -> func -> bool).
  Context {act: Type}.
  Context (act_eqb: act -> act -> bool).

  Context {srcvar_eq_dec : EqDecider srcvar_eqb}.
  Context {impvar_eq_dec : EqDecider impvar_eqb}.

  Context {src2imp: map.map srcvar impvar}.
  Context {src2impOk: map.ok src2imp}.
  Context {src2imp_ops: map.ops src2imp}.

  Instance srcparams: Syntax.parameters := {|
    Syntax.varname := srcvar;
    Syntax.funname := func;
    Syntax.actname := act;
  |}.

  Instance impparams: Syntax.parameters := {|
    Syntax.varname := impvar;
    Syntax.funname := func;
    Syntax.actname := act;
  |}.

  (* annotated statement: each assignment is annotated with impvar which it assigns *)
  Inductive astmt: Type :=
    | ASLoad(sz: Syntax.access_size.access_size)(x: srcvar)(x': impvar)(a: srcvar)
    | ASStore(sz: Syntax.access_size.access_size)(a: srcvar)(v: srcvar)
    | ASLit(x: srcvar)(x': impvar)(v: Z)
    | ASOp(x: srcvar)(x': impvar)(op: Syntax.bopname.bopname)(y z: srcvar)
    | ASSet(x: srcvar)(x': impvar)(y: srcvar)
    | ASIf(cond: @bcond srcparams)(bThen bElse: astmt)
    | ASLoop(body1: astmt)(cond: @bcond srcparams)(body2: astmt)
    | ASSeq(s1 s2: astmt)
    | ASSkip
    | ASCall(binds: list (srcvar * impvar))(f: funname)(args: list srcvar)
    | ASInteract(binds: list (srcvar * impvar))(f: actname)(args: list srcvar).

  Local Notation stmt  := (@FlatImp.stmt srcparams). (* input type *)
  Local Notation stmt' := (@FlatImp.stmt impparams). (* output type *)

(*
  Inductive Update :=
  | Nop
  | Add(x: srcvar)(y: impvar)
  | Remove(x: srcvar)
  | Seq(u1 u2: Update)
  | Par(u1 u2: Update).

  Fixpoint apply(u: Update): src2imp -> src2imp :=
    match u with
    | Nop => id
    | Add x y => fun m => map.put m x y
    | Remove x => fun m => map.remove m x
    | Seq u1 u2 => fun m => apply u2 (apply u1 m)
    | Par u1 u2 => fun m => map.intersect (apply u1 m) (apply u2 m)
    end.

  Lemma apply_idemp: forall u m,
      apply u (apply u m) = apply u m.
  Proof.
    induction u; intros; simpl.
    - reflexivity.
    - apply map.put_put_same.
    - apply map.map_ext; intros; map_solver src2impOk.
    - (* same problem as before.
         we need to turn updates into a canonical form before applying it! *)
  Abort.
*)

  (*
  Inductive Update :=
  | Add(x: srcvar)(y: impvar)
  | Remove(x: srcvar).
  *)

  Inductive Update :=
  | Add(y: impvar)
  | Remove.

  (* Third case: In "option Update", "None" means unchanged. *)

  Context {Updates: map.map srcvar Update}.

  Definition iter{A: Type}(f: srcvar -> Update -> A -> A)(a: A)(m: Updates): A.
  Admitted.

(*
  Lemma iter_iter: forall {A: Type} a f m1 m2,
      iter (iter a f m1) f m2 = iter a f m.
*)

  Definition combine(m1 m2: Updates)(f: srcvar -> option Update -> option Update -> option Update):
    Updates. Admitted.

  (* should be symmetric *)
  Definition Par1(x: srcvar)(u1: option Update)(u2: option Update): option Update :=
    match u1, u2 with
    | Some (Add y1), Some (Add y2) => if impvar_eqb y1 y2 then
                                        Some (Add y1)
                                      else
                                        Some Remove
    | Some (Add y1), Some Remove => Some Remove
    | Some (Add y1), None => None
    | Some Remove, _ => Some Remove
    | None, Some (Add y2) => None
    | None, Some Remove => Some Remove
    | None, None => None
    end.

  Lemma Par1_comm: forall x u1 u2,
      Par1 x u1 u2 = Par1 x u2 u1.
  Proof.
    intros. destruct u1 as [[? |]|]; destruct u2 as [[? |]|]; try reflexivity.
    simpl.
    destruct (impvar_eq_dec y y0); destruct (impvar_eq_dec y0 y); congruence.
  Qed.

  Definition Par(us1 us2: Updates): Updates := combine us1 us2 Par1.
  Definition Seq: Updates -> Updates -> Updates := map.putmany.

  Definition updates: astmt -> Updates :=
    fix rec s :=
      match s with
      | ASLoad _ x x' _ | ASLit x x' _ | ASOp x x' _ _ _ | ASSet x x' _ =>
           map.put map.empty x (Add x')
      | ASStore _ _ _ => map.empty
      | ASIf cond s1 s2 => Par (rec s1) (rec s2)
      | ASLoop s1 cond s2 =>
        let r1 := rec s1 in
        let r2 := rec s2 in
        Par r1 (Seq r1 (Seq r2 r1))
      | ASSeq s1 s2 => map.putmany (rec s1) (rec s2)
      | ASSkip => map.empty
      | ASInteract binds _ _ | ASCall binds _ _ =>
           (map.putmany_of_pairs map.empty (List.map (fun '(x, y) => (x, Add y)) binds))
      end.

  Definition map_values{K V1 V2: Type}{M1: map.map K V1}{M2: map.map K V2}(f: V1 -> option V2):
    M1 -> M2. Admitted.

  Lemma map_values_map_values{K V1 V2 V3: Type}{M1: map.map K V1}{M2: map.map K V2}
        {M3: map.map K V3}(f1: V1 -> option V2)(f2: V2 -> option V3)(m1: M1):
    map_values f2 (map_values f1 m1) = map_values (fun v1 => match f1 v1 with
                                                             | Some v2 => f2 v2
                                                             | None => None
                                                             end)
                                                  m1.
  Admitted.

  Lemma map_values_putmany{K V: Type}{M: map.map K V}: forall f m1 m2,
      map_values f (map.putmany m1 m2) = map.putmany (map_values f m1) (map_values f m2).
  Proof.
    (* doesn't hold:
       if m1[k] = keptValue and m2[k] = droppedValue
       lhs has no k
       rhs has k->keptValue *)
  Abort.

(*
  Definition apply(us: Updates)(m: src2imp): src2imp :=
    map_values (fun u => match u with
                         | Add y => Some y
                         | Remove => None
                         end)
               (map.putmany (map_values (fun y => Some (Add y)) m) us).

  Lemma apply_idemp: forall us m,
      apply us (apply us m) = apply us m.
  Proof.
    intros. unfold apply.
    rewrite map_values_map_values.
    f_equal.
    f_equal.
*)

  Definition apply1(x: srcvar)(u: Update)(m: src2imp): src2imp :=
    match u with
    | Add y => map.put m x y
    | Remove => map.remove m x
    end.

  Definition apply(us: Updates)(m: src2imp): src2imp :=
    iter apply1 m us.
  
  Lemma apply_idemp: forall us m,
      apply us (apply us m) = apply us m.
  Proof.
    intros. unfold apply.
  Abort.
    
  (* not symmetric
  Definition Seq1(x: srcvar)(u1: option Update)(u2: option Update): option Update :=
    match u2 with
    | Some u => u
    | None => match u1 with
    not needed *)

  Definition loop_inv(update: src2imp -> astmt -> src2imp)(m: src2imp)(s1 s2: astmt): src2imp :=
    map.intersect m (update (update m s1) s2).

  (* mappings which are guaranteed to hold after executing statement s (under-approximation) *)
  Definition update: src2imp -> astmt -> src2imp :=
    fix rec m s :=
      match s with
      | ASLoad _ x x' _ | ASLit x x' _ | ASOp x x' _ _ _ | ASSet x x' _ => map.put m x x'
      | ASStore _ _ _ => m
      | ASIf cond s1 s2 => map.intersect (rec m s1) (rec m s2)
      | ASLoop s1 cond s2 => rec (loop_inv rec m s1 s2) s1
      | ASSeq s1 s2 => rec (rec m s1) s2
      | ASSkip => m
      | ASInteract binds _ _ | ASCall binds _ _ => map.putmany_of_pairs m binds
      end.

  Definition cond_checker(s2i: src2imp)(cond: @bcond srcparams): option (@bcond impparams) :=
    match cond with
    | CondBinary op x y =>
        bind_opt x' <- map.get s2i x;
        bind_opt y' <- map.get s2i y;
        Some (CondBinary op x' y')
    | CondNez x =>
        bind_opt x' <- map.get s2i x;
        Some (CondNez x')
    end.

  Definition checker: src2imp -> astmt -> option stmt' :=
    fix rec m s :=
      match s with
      | ASLoad sz x x' a =>
          bind_opt a' <- map.get m a;
          Some (SLoad sz x' a')
      | ASStore sz a v =>
          bind_opt a' <- map.get m a;
          bind_opt v' <- map.get m v;
          Some (SStore sz a' v')
      | ASLit x x' v =>
          Some (SLit x' v)
      | ASOp x x' op y z =>
          bind_opt y' <- map.get m y;
          bind_opt z' <- map.get m z;
          Some (SOp x' op y' z')
      | ASSet x x' y =>
          bind_opt y' <- map.get m y;
          Some (SSet x' y')
      | ASIf cond s1 s2 =>
          bind_opt cond' <- cond_checker m cond;
          bind_opt s1' <- rec m s1;
          bind_opt s2' <- rec m s2;
          Some (SIf cond' s1' s2')
      | ASLoop s1 cond s2 =>
          let m1 := loop_inv update m s1 s2 in
          let m2 := update m1 s1 in
          bind_opt cond' <- cond_checker m2 cond;
          bind_opt s1' <- rec m1 s1;
          bind_opt s2' <- rec m2 s2;
          Some (SLoop s1' cond' s2')
      | ASSeq s1 s2 =>
          bind_opt s1' <- rec m s1;
          bind_opt s2' <- rec (update m s1) s2;
          Some (SSeq s1' s2')
      | ASSkip => Some SSkip
      | ASCall binds f args =>
          bind_opt args' <- map.getmany_of_list m args;
          Some (SCall (List.map snd binds) f args')
      | ASInteract binds f args =>
          bind_opt args' <- map.getmany_of_list m args;
          Some (SInteract (List.map snd binds) f args')
      end.

  Definition erase :=
    fix rec(s: astmt): stmt :=
      match s with
      | ASLoad sz x x' a => @SLoad srcparams sz x a
      | ASStore sz a v => @SStore srcparams sz a v
      | ASLit x x' v => @SLit srcparams x v
      | ASOp x x' op y z => @SOp srcparams x op y z
      | ASSet x x' y => @SSet srcparams x y
      | ASIf cond s1 s2 => SIf cond (rec s1) (rec s2)
      | ASLoop s1 cond s2 => SLoop (rec s1) cond (rec s2)
      | ASSeq s1 s2 => SSeq (rec s1) (rec s2)
      | ASSkip => SSkip
      | ASCall binds f args => @SCall srcparams (List.map fst binds) f args
      | ASInteract binds f args => @SInteract srcparams (List.map fst binds) f args
      end.

  Ltac head e :=
    match e with
    | ?a _ => head a
    | _ => e
    end.

  Goal forall (s: stmt), False.
    intro s.
    destruct s eqn: E;
    match type of E with
    | _ = ?r => let h := head r in idtac (* "| set ( case :=" h ")" *)
    end.
  Abort.

  Definition annotate_assignment(s: stmt)(y: impvar): astmt :=
    match s with
    | SLoad sz x a => ASLoad sz x y a
    | SLit x v => ASLit x y v
    | SOp x op a b => ASOp x y op a b
    | SSet x a => ASSet x y a
    | _ => ASSkip (* not an assignment *)
    end.

  Definition rename_assignment_lhs(m: src2imp)(x: srcvar)(a: list impvar):
    src2imp * impvar * list impvar :=
    match map.get m x with
    | Some y => (m, y, a)
    | None   => match a with
                | y :: rest => (map.put m x y, y, rest)
                | nil => (* error: ran out of registers *)
                  let y := map.default_value in (map.put m x y, y, a)
                end
    end.

  Fixpoint rename_binds(m: src2imp)(binds: list srcvar)(a: list impvar):
    (src2imp * list (srcvar * impvar) * list impvar) :=
    match binds with
    | nil => (m, nil, a)
    | x :: binds =>
      let '(m, y, a) := rename_assignment_lhs m x a in
      let '(m, res, a) := rename_binds m binds a in
      (m, (x, y) :: res, a)
    end.

  (* the simplest dumbest possible "register allocator" *)
  Fixpoint rename
           (m: src2imp)              (* current mapping, growing *)
           (s: stmt)                 (* current sub-statement *)
           (a: list impvar)          (* available registers, shrinking *)
           {struct s}
    : src2imp * astmt * list impvar :=
    match s with
    | SLoad _ x _ | SLit x _ | SOp x _ _ _ | SSet x _ =>
        let '(m, y, a) := rename_assignment_lhs m x a in (m, annotate_assignment s y, a)
    | SStore sz x y => (m, ASStore sz x y, a)
    | SIf cond s1 s2 =>
      let '(m', s1', a') := rename m s1 a in
      let '(m'', s2', a'') := rename m' s2 a' in
      (m'', ASIf cond s1' s2', a'')
    | SSeq s1 s2 =>
      let '(m', s1', a') := rename m s1 a in
      let '(m'', s2', a'') := rename m' s2 a' in
      (m'', ASSeq s1' s2', a'')
    | SLoop s1 cond s2 =>
      let '(m', s1', a') := rename m s1 a in
      let '(m'', s2', a'') := rename m' s2 a' in
      (m'', ASLoop s1' cond s2', a'')
    | SCall binds f args =>
      let '(m, tuples, a) := rename_binds m binds a in
      (map.putmany_of_pairs m tuples, ASCall tuples f args, a)
    | SInteract binds f args =>
      let '(m, tuples, a) := rename_binds m binds a in
      (map.putmany_of_pairs m tuples, ASInteract tuples f args, a)
    | SSkip => (m, ASSkip, a)
    end.

  Variable available_impvars: list impvar.
  Variable dummy_impvar: impvar.

  Fixpoint regalloc
           (m: src2imp)              (* current mapping *)
           (s: stmt)                 (* current sub-statement *)
           (usedlater: list srcvar)  (* variables which have a life after statement s *)
           {struct s}
    : astmt :=                       (* annotated statement *)
    match s with
    | SLoad _ x _ | SLit x _ | SOp x _ _ _ | SSet x _ =>
        match map.get m x with
        | Some y => (* nothing to do because no new interval starts *)
                    annotate_assignment s y
        | None   => (* new interval starts *)
                    match map.getmany_of_list m usedlater with
                    | Some used_impvars =>
                      let av := list_diff impvar_eqb available_impvars used_impvars in
                      match av with
                      | y :: _ => annotate_assignment s y
                      | nil => ASSkip (* error: ran out of vars *)
                      end
                    | None => ASSkip (* error: an uninitialized var is used later *)
                    end
        end
    | SStore sz x y => ASStore sz x y
    | SIf cond s1 s2 =>
      let s1' := regalloc m s1 usedlater in
      let s2' := regalloc m s2 usedlater in
      ASIf cond s1' s2'
    | SSeq s1 s2 =>
      let s1' := regalloc m s1 (@live srcparams srcvar_eqb s2 usedlater) in
      let s2' := regalloc (update m s1') s2 usedlater in
      ASSeq s1' s2'
    | SLoop s1 cond s2 =>
      ASSkip (* TODO *)
      (*
      let s1' := regalloc (loop_inv update m s1 s2) s1 (live s2 (live s1 usedlater)) in
      let s2' := regalloc (update m s1') s2 (live s usedlater) in
      ASLoop s1' cond s2'
      *)
    | _ => ASSkip
    end.

(*
  Definition start_interval(current: srcvars * impvars * map impvar srcvar)(x: srcvar)
    : srcvars * impvars * map impvar srcvar :=
    let '(o, a, m) := current in
    let o := union o (singleton_set x) in
    let '(r, a) := pick_or_else a dummy_impvar in
    let m := put m r x in
    (o, a, m).
*)

  Definition rename_stmt(m: src2imp)(s: stmt)(av: list impvar): option stmt' :=
    let '(_, annotated, _) := rename m s av in checker m annotated.

  Definition rename_fun(F: list srcvar * list srcvar * stmt):
    option (list impvar * list impvar * stmt') :=
    let '(argnames, retnames, body) := F in
    let '(m, argtuples, av) := rename_binds map.empty argnames available_impvars in
    let '(m, rettuples, av) := rename_binds m retnames av in
    match rename_stmt m body av with
    | Some body' => Some (List.map snd argtuples, List.map snd rettuples, body')
    | None => None
    end.

  Definition register_allocation(s: stmt)(usedlater: list srcvar): option (stmt' * list impvar) :=
    let annotated := regalloc map.empty s usedlater in
    match checker map.empty annotated with
    | Some res => match map.getmany_of_list (update map.empty annotated) usedlater with
                  | Some imp_vars => Some (res, imp_vars)
                  | None => None
                  end
    | None => None
    end.

  (* claim: for all astmt a, if checker succeeds and returns s', then
     (erase a) behaves the same as s' *)

  Context {W: Utility.Words} {mem: map.map word byte}.
  Context {srcLocals: map.map srcvar word}.
  Context {impLocals: map.map impvar word}.
  Context {srcLocalsOk: map.ok srcLocals}.
  Context {impLocalsOk: map.ok impLocals}.
  Context {funname_env: forall T: Type, map.map func T}.
  Context (ext_spec:  list (mem * actname * list word * (mem * list word)) ->
                      mem -> actname -> list word -> (mem -> list word -> Prop) -> Prop).

  Instance srcSemanticsParams: Semantics.parameters. refine ({|
    Semantics.syntax := srcparams;
    Semantics.varname_eqb := srcvar_eqb;
    Semantics.funname_eqb := func_eqb;
    Semantics.actname_eqb := act_eqb;
    Semantics.locals := srcLocals;
    Semantics.ext_spec := ext_spec;
  |}).
  Defined.

  Instance impSemanticsParams: Semantics.parameters. refine ({|
    Semantics.syntax := impparams;
    Semantics.varname_eqb := impvar_eqb;
    Semantics.funname_eqb := func_eqb;
    Semantics.actname_eqb := act_eqb;
    Semantics.locals := impLocals;
    Semantics.ext_spec := ext_spec;
  |}).
  Defined.

  Definition rename_function(e: @FlatImp.env srcSemanticsParams)(f: funname):
    (list impvar * list impvar * stmt') :=
    match map.get e f with
    | Some F => match rename_fun F with
                | Some res => res
                | None => (nil, nil, FlatImp.SSkip)
                end
    | None => (nil, nil, FlatImp.SSkip)
    end.

  Definition rename_functions(e: @FlatImp.env srcSemanticsParams):
    list funname -> @FlatImp.env impSemanticsParams :=
    fix rec funs :=
      match funs with
      | f :: rest => map.put (rec rest) f (rename_function e f)
      | nil => map.empty
      end.

  Definition states_compat(st: srcLocals)(m: src2imp)(st': impLocals) :=
    forall (x: srcvar) (x': impvar),
      map.get m x = Some x' ->
      forall w,
        map.get st x = Some w ->
        map.get st' x' = Some w.

(*
  Lemma states_compat_put: forall st1 st1' v x x' r,
      map.get r x = None ->
      states_compat st1 r st1' ->
      states_compat (map.put st1 x v) (map.put r x x') (map.put st1' x' v).
  Proof.
    unfold states_compat.
    intros.
    rewrite (map.get_put_dec (key_eqb := impvar_eqb)).
    do 2 lazymatch goal with
    | H: map.get (map.put _ _ _) _ = _ |- _ => rewrite map.get_put_dec in H
    end.
    destruct_one_match.
    - subst x'0.
      destruct_one_match_hyp; [assumption|].
      specialize H0 with (1 := H1) (2 := H2).


    - destruct_one_match_hyp.
      + subst.
        apply get_in_range in H1.
        contradiction.
      + eauto.
  Qed.

  Lemma states_compat_extends: forall st st' r1 r2,
      extends r1 r2 ->
      states_compat st r1 st' ->
      states_compat st r2 st'.
  Proof.
    unfold states_compat. eauto.
  Qed.
  *)

  Axiom intersect_spec: forall m1 m2 k v,
      map.get (map.intersect m1 m2) k = Some v <-> map.get m1 k = Some v /\ map.get m2 k = Some v.

  Axiom extends_intersect_map_l: forall r1 r2, map.extends r1 (map.intersect r1 r2).
  Axiom extends_intersect_map_r: forall r1 r2, map.extends r2 (map.intersect r1 r2).
  Axiom extends_intersect_split: forall m1 m2 m,
      map.extends m1 m ->
      map.extends m2 m ->
      map.extends (map.intersect m1 m2) m.
  Axiom intersect_map_assoc: forall m1 m2 m3,
      map.intersect (map.intersect m1 m2) m3 = map.intersect m1 (map.intersect m2 m3).
  Axiom intersect_map_comm: forall m1 m2,
      map.intersect m1 m2 = map.intersect m2 m1.

  Lemma extends_intersect_map_l': forall m m1 m2,
      map.extends m m1 ->
      map.extends m (map.intersect m1 m2).
  Proof.
    intros.
    eapply extends_trans.
    1: eassumption.
    eapply extends_intersect_map_l.
  Qed.

  Lemma extends_intersect_map_r': forall m m1 m2,
      map.extends m m2 ->
      map.extends m (map.intersect m1 m2).
  Proof.
    intros.
    eapply extends_trans.
    1: eassumption.
    eapply extends_intersect_map_r.
  Qed.

  Lemma extends_intersect_map_lr: forall m11 m12 m21 m22,
      map.extends m11 m21 ->
      map.extends m12 m22 ->
      map.extends (map.intersect m11 m12) (map.intersect m21 m22).
  Proof.
    intros.
    eapply extends_intersect_split.
    - eapply extends_intersect_map_l'. assumption.
    - eapply extends_intersect_map_r'. assumption.
  Qed.

  (*
  Hint Resolve
       states_compat_put
       not_in_range_of_remove_by_value
       states_compat_extends
       extends_remove_by_value
       extends_intersect_map_l
       extends_intersect_map_r
    : checker_hints.
    *)

  Lemma loop_inv_init: forall r s1 s2,
      map.extends r (loop_inv update r s1 s2).
  Proof.
    intros. unfold loop_inv. apply extends_intersect_map_l.
  Qed.

(*
  (* depends on unproven mappings_intersect_map mappings_mappings_extends_mappings *)
  Lemma loop_inv_step: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      extends (mappings (mappings Inv s1) s2) Inv.
  Proof.
    intros. subst Inv. unfold loop_inv.
    change (mappings (mappings r s1) s2) with (mappings r (ASSeq s1 s2)).
    change (mappings (mappings (intersect_map r (mappings r (ASSeq s1 s2))) s1) s2)
      with (mappings (intersect_map r (mappings r (ASSeq s1 s2))) (ASSeq s1 s2)).
    forget (ASSeq s1 s2) as s. clear s1 s2.
    rewrite mappings_intersect_map.
    eapply extends_trans; [|apply extends_intersect_map_r].
    apply intersect_map_extends.
    - apply extends_refl.
    - apply mappings_mappings_extends_mappings.
  Qed.

  Lemma test: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      False.
  Proof.
    intros.
    pose proof (loop_inv_step r s1 s2) as P. simpl in P.
    change (mappings (mappings (loop_inv mappings r s1 s2) s1) s2) with
           (mappings (mappings Inv s1) s2) in P.
    unfold loop_inv in P.
    (* "extends _ (intersect_map _ _)" is useless *)
  Abort.

  Lemma loop_inv_step_bw: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      bw_extends (mappings (mappings Inv s1) s2) Inv.
  Proof using.
    intros. subst Inv. unfold loop_inv.
  Admitted.
*)

  Lemma extends_loop_inv: forall r s1 s2,
      let Inv := loop_inv update r s1 s2 in
      map.extends Inv (loop_inv update Inv s1 s2).
  Proof.
    intros. apply loop_inv_init.
  Qed.

  Lemma update_monotone: forall s {m1 m2},
      map.extends m1 m2 ->
      map.extends (update m1 s) (update m2 s).
  Proof.
    induction s; intros; simpl in *; unfold loop_inv in *.
    - map_solver src2impOk.
    - map_solver src2impOk.
    - map_solver src2impOk.
    - map_solver src2impOk.
    - map_solver src2impOk.
    - specialize (IHs1 _ _ H).
      specialize (IHs2 _ _ H).
      forget (update m1 s1) as a11.
      forget (update m1 s2) as a12.
      forget (update m2 s1) as a21.
      forget (update m2 s2) as a22.
      apply extends_intersect_map_lr; assumption.
    - pose proof (IHs1 _ _ H) as IHs1'.
      pose proof (IHs2 _ _ IHs1') as IHs2'.
      forget (update m1 s1) as a11.
      forget (update m1 s2) as a12.
      forget (update m2 s1) as a21.
      forget (update m2 s2) as a22.
      forget (update a11 s2) as a112.
      forget (update a21 s2) as a212.
      apply IHs1.
      apply extends_intersect_map_lr; assumption.
    - specialize (IHs1 _ _ H).
      apply (IHs2 _ _ IHs1).
    - map_solver src2impOk.
    - apply map.putmany_of_pairs_extends. assumption.
    - apply map.putmany_of_pairs_extends. assumption.
  Qed.

  Lemma map_extend_to_eq: forall {m1 m2: src2imp},
      map.extends m1 m2 ->
      map.extends m2 m1 ->
      m1 = m2.
  Proof.
    intros.
    unfold map.extends in *.
    apply map.map_ext.
    intros.
    destruct (map.get m2 k) eqn: E2.
    - map_solver src2impOk.
    - destruct (map.get m1 k) eqn: E1. 2: reflexivity. map_solver src2impOk.
  Qed.

  Lemma intersect_no_effect0: forall {r m1 m2},
      map.extends m1 m2 ->
      map.intersect (map.intersect r m1) m2 = map.intersect r m2.
  Proof.
    intros.
    apply map_extend_to_eq.
    - apply extends_intersect_split.
      + apply extends_intersect_map_lr.
        * apply extends_refl.
        * assumption.
      + apply extends_intersect_map_r.
    - apply extends_intersect_map_lr.
      + apply extends_intersect_map_l.
      + apply extends_refl.
  Qed.

  Lemma intersect_no_effect: forall {r m1 m2},
      map.extends m1 m2 ->
      map.intersect (map.intersect r m2) m1 = map.intersect r m2.
  Proof.
    intros.
    apply map_extend_to_eq.
    - apply extends_intersect_split.
      + apply extends_refl.
      + apply extends_intersect_map_r'. assumption.
    - apply extends_intersect_split.
      + apply extends_intersect_map_l'. apply extends_intersect_map_l.
      + apply extends_intersect_map_l'. apply extends_intersect_map_r.
  Qed.

  Lemma intersect_absorb_r: forall m1 m2,
      map.extends m2 m1 ->
      map.intersect m1 m2 = m1.
  Proof.
    intros.
    apply map_extend_to_eq.
    - apply extends_intersect_split.
      + apply extends_refl.
      + assumption.
    - apply extends_intersect_map_l.
  Qed.

  Lemma update_comm: forall s1 s2 m,
      update (update m s1) s2 = update (update m s2) s1.
  Proof.
    induction s1; induction s2; intros; simpl.
    (* clearly doesn't hold *)
  Abort.

  Lemma put_intersect: forall m1 m2 k v,
      map.put (map.intersect m1 m2) k v = map.intersect (map.put m1 k v) (map.put m2 k v).
  Admitted.

  Lemma update_intersect: forall s m1 m2,
      update (map.intersect m1 m2) s = map.intersect (update m1 s) (update m2 s).
  Proof.
    induction s; intros; simpl; eauto using put_intersect.
    - rewrite IHs1.
      rewrite IHs2.
      rewrite? intersect_map_assoc.
      case TODO_sam.
    - unfold loop_inv.
      rewrite IHs1.
      rewrite IHs1.
      rewrite IHs1.
      rewrite IHs1.
      rewrite IHs2.
      rewrite IHs1.
      rewrite? intersect_map_assoc.
      forget (update (update (update m2 s1) s2) s1) as M1.
      forget (update (update (update m1 s1) s2) s1) as M2.
      forget (update m1 s1) as M3.
      forget (update m2 s1) as M4.
      case TODO_sam.
    - rewrite IHs1.
      rewrite IHs2.
      reflexivity.
    - case TODO_sam.
    - case TODO_sam.
  Qed.

  Lemma update_idemp: forall s m,
      update (update m s) s = update m s.
  Proof.
    intros.
    pose proof (update_intersect s (update m s) m).
    (* doesn't seem to help like this *)
  Abort.
(*
  Lemma intersect_update: forall s1 s2 m,
      map.intersect (update m s1) (update m s2) =
  *)

  Lemma update_intersect_update: forall s m1 m2,
      update (map.intersect m1 (update m2 s)) s = update m2 s.
  Proof.
    induction s; intros; simpl.
    (* doesn't hold for kvpair which is in m2 but not in m2 *)
  Abort.

  Lemma update_intersect_update: forall s1 s2 m,
      update (map.intersect (update m s1) (update m s2)) s2 = update m s2.
  Proof.
    induction s1; induction s2; intros; simpl.
    (* doesn't hold if x<>x0 and both of them are in m and the values also differ:
       the puts inside the intersect will make two disagreeing versions of m,
       so the intersect will be smaller by two keys, but we only put back one *)
  Abort.

  Lemma intersect_comm_update: forall s1 s2 m,
      map.intersect (update (update m s2) s1)
                    (update (update m s1) s2)
      = map.intersect (update m s1) (update m s2).
  Proof.
    induction s1; induction s2; intros; simpl.
    (* doesn't hold if x <> x0 (different keys) *)
  Abort.

  Lemma intersect_comm_update_extends: forall s1 s2 m,
      map.extends (map.intersect (update (update m s2) s1)
                                 (update (update m s1) s2))
                  (map.intersect (update m s1) (update m s2)).
  Proof.
    assert (forall m x x' x0 x'0,
               map.extends (map.intersect (map.put (map.put m x0 x'0) x x')
                                          (map.put (map.put m x x') x0 x'0))
                           (map.intersect (map.put m x x') (map.put m x0 x'0))) as A. {
      intros.
      destruct (srcvar_eq_dec x x0).
      - subst x0. rewrite !map.put_put_same. apply extends_refl.
      - unfold map.extends.
        intros.
        rewrite intersect_spec in *.
        map_solver src2impOk.
    }
    induction s1; induction s2; intros; simpl in *;
      try solve [
            unfold map.extends; intros;
            rewrite ?intersect_spec in *;
            map_solver src2impOk].
    {
            unfold map.extends in *; intros;
              rewrite ?intersect_spec in *.
            repeat match goal with
                   | H: _ |- _ => setoid_rewrite intersect_spec in H
                   end.

            map_solver src2impOk.
  Admitted. (* TODO not sure! *)

  Lemma update_121: forall s1 s2 m,
      update (update (update m s1) s2) s1 = update (update m s2) s1.
  Proof.
    induction s2; intros; simpl in *.
  Abort.

  Lemma update_121: forall s1 s2 m,
      update (update (update m s1) s2) s1 = update (update m s2) s1.
  Proof.
    assert (forall (m: src2imp) x x' x0 x'0,
      map.put (map.put (map.put m x x') x0 x'0) x x' = map.put (map.put m x0 x'0) x x') as A. {
      intros.
      apply map.map_ext; intros; map_solver src2impOk.
    }
    induction s2; induction s1; intros; simpl in *; try eapply A;
      try solve [apply map.map_ext; intros; map_solver src2impOk].
    - rewrite put_intersect.
      rewrite update_intersect.
      rewrite update_intersect.
      rewrite IHs1_1.
      rewrite IHs1_2.
      (* cross terms again *)
  Abort.

  Lemma update_121: forall s1 s2 m,
      update (update (update m s1) s2) s1 = update (update m s2) s1.
  Proof.
    assert (forall (m: src2imp) x x' x0 x'0,
      map.put (map.put (map.put m x x') x0 x'0) x x' = map.put (map.put m x0 x'0) x x') as A. {
      intros.
      apply map.map_ext; intros; map_solver src2impOk.
    }
    induction s1; induction s2; intros; simpl in *; try eapply A;
      try solve [apply map.map_ext; intros; map_solver src2impOk].
    - rename s2_1 into s1. rename s2_2 into s2.
      do 2 rewrite put_intersect.
      rewrite IHs2_1.
      rewrite IHs2_2.
      reflexivity.
    - unfold loop_inv.

  Admitted.

  Lemma update_idemp: forall s m,
      update (update m s) s = update m s.
  Proof.
    intros.
    pose proof (update_121 s ASSkip m) as P. simpl in P. exact P.
  Qed.

  Lemma update_idemp': forall s m,
      update (update m s) s = update m s.
  Proof.
    induction s; intros; simpl in *;
      try reflexivity;
      try (apply map.put_put_same).
    - rewrite update_intersect.
      rewrite update_intersect.
      rewrite IHs1.
      rewrite IHs2.
      replace (map.intersect (map.intersect (update m s1) (update (update m s2) s1))
                             (map.intersect (update (update m s1) s2) (update m s2)))
         with (map.intersect (map.intersect (update m s1) (update m s2))
                             (map.intersect (update (update m s2) s1)
                                            (update (update m s1) s2))); cycle 1. {
        apply map_extend_to_eq; unfold map.extends; repeat setoid_rewrite intersect_spec;
        intros; map_solver src2impOk.
      }
      apply intersect_absorb_r.
      apply intersect_comm_update_extends.
    - unfold loop_inv.
      repeat (rewrite update_intersect || rewrite IHs1 || rewrite IHs2).
      (* might be reducible to the Seq case *)
      admit.
    - enough (update (update (update (update m s1) s2) s1) s2 =
              update (update (update m s1) s2) s2). {
        rewrite IHs2 in H. exact H.
      }
      f_equal.
  Abort.

  (* this direction would be needed to get full idempotence of loop_inv *)
  Lemma loop_inv_extends: forall r s1 s2,
      let Inv := loop_inv update r s1 s2 in
      map.extends (loop_inv update Inv s1 s2) Inv.
  Proof.
    intros. subst Inv.
    unfold loop_inv.
    pose proof (extends_intersect_map_l r (update (update r s1) s2)) as A.
    epose proof (update_monotone s2 (update_monotone s1 A)) as B.
    epose proof (intersect_no_effect0 B) as C.

    (* Problem: the smaller (and therefore significant) set is the more complicated one *)
    rewrite C.

    apply extends_intersect_split.
    - apply extends_intersect_map_l.
    - apply extends_intersect_map_r'.
      apply update_monotone.
      apply update_monotone.
      (* NOPE *)
  Abort.
 (*
    change (mappings (mappings r s1) s2) with (mappings r (ASSeq s1 s2)).
    change (mappings (mappings (intersect_map r (mappings r (ASSeq s1 s2))) s1) s2)
      with (mappings (intersect_map r (mappings r (ASSeq s1 s2))) (ASSeq s1 s2)).
    forget (ASSeq s1 s2) as s. clear s1 s2.
    remember (intersect_map r (mappings r s)) as r1.
  (*
  Proof.
    intros. unfold extends, loop_inv. intros.
    apply intersect_map_spec.
    split; [assumption|].

    pose proof mappings_monotone as P. unfold extends in P.
    eapply P.

    subst Inv. unfold loop_inv.
    set (a := (intersect_map r (mappings (mappings r s1) s2))).

    pose proof extends_loop_inv as Q. simpl in Q.*)
  Abort.

  Lemma loop_inv_idemp: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      loop_inv mappings Inv s1 s2 = Inv.
  Proof using .
  Abort.
  *)

  Definition precond(m: src2imp)(s: astmt): src2imp :=
    match s with
    | ASLoop s1 cond s2 => loop_inv update m s1 s2
    | _ => m
    end.

  (*
  Lemma precond_weakens: forall m s,
      extends m (precond m s).
  Proof.
    intros. destruct s; try apply extends_refl.
    unfold precond, loop_inv.
    apply extends_intersect_map_l.
  Qed.

  Hint Resolve precond_weakens : checker_hints.
   *)

  Lemma getmany_of_list_states_compat: forall srcnames impnames r lH lL argvals,
      map.getmany_of_list lH srcnames = Some argvals ->
      map.getmany_of_list r srcnames = Some impnames ->
      states_compat lH r lL ->
      map.getmany_of_list lL impnames = Some argvals.
  Proof.
    induction srcnames; intros;
      destruct argvals as [|argval argvals];
      destruct impnames as [|impname impnames];
      try reflexivity;
      try discriminate;
      unfold map.getmany_of_list, List.option_all in *; simpl in *;
        repeat (destruct_one_match_hyp; try discriminate).
    simp.
    replace (map.get lL impname) with (Some argval); cycle 1. {
      symmetry. unfold states_compat in *; eauto.
    }
    erewrite IHsrcnames; eauto.
  Qed.

  Lemma putmany_of_list_states_compat: forall binds resvals lL lH l' r,
      map.putmany_of_list (map fst binds) resvals lH = Some l' ->
      states_compat lH r lL ->
      exists lL',
        map.putmany_of_list (map snd binds) resvals lL = Some lL' /\
        states_compat l' (map.putmany_of_pairs r binds) lL'.
  Proof.
    induction binds; intros.
    - simpl in H. simp. simpl. eauto.
    - simpl in *. simp.
      specialize IHbinds with (1 := H).
      destruct a as [sv iv].
      rename l' into lH'.
      apply map.putmany_of_list_sameLength in H.
      rewrite map_length in H. rewrite <- (map_length snd) in H.
      eapply map.sameLength_putmany_of_list in H.
      destruct H as (lL' & H).
      exists lL'. split; [exact H|].

  Admitted.
  (*edestruct IHbinds as (lL' & P & C); cycle 1.
      + eexists. split; eauto.
        unfold map.putmany_of_tuples in C.
*)

  Lemma checker_correct: forall e e' s t m lH mc post,
      (forall f argnames retnames body,
          map.get e f = Some (argnames, retnames, body) ->
          exists args body' annotated binds,
            map.get e' f = Some (map snd args, map snd binds, body') /\
            argnames = map fst args /\
            retnames = map fst binds /\
            erase annotated = body /\
            checker (map.putmany_of_pairs map.empty args) annotated = Some body') ->
      @exec srcSemanticsParams e s t m lH mc post ->
      forall lL r annotated s',
      erase annotated = s ->
      checker r annotated = Some s' ->
      states_compat lH (precond r annotated) lL ->
      @exec impSemanticsParams e' s' t m lL mc (fun t' m' lL' mc' =>
        exists lH', states_compat lH' (update r annotated) lL' /\
                    post t' m' lH' mc').
  Proof.
    induction 2; intros;
      match goal with
      | H: erase ?s = _ |- _ =>
        destruct s;
        inversion H;
        subst;
        clear H
      end;
      subst;
      match goal with
      | H: checker _ ?x = _ |- _ => pose proof H as C; remember x as AS in C
      end;
      simpl in *;
      simp.

    - (* SInteract *)
      econstructor; eauto.
      + eauto using getmany_of_list_states_compat.
      + intros *. intro HO.
        match goal with
        | H: _ |- _ => specialize H with (1 := HO)
        end.
        simp.
        pose proof putmany_of_list_states_compat as P.
        specialize P with (1 := H3l) (2 := H6). destruct P as (lL' & P & Co). eauto 10.

    - (* SCall *)
      specialize H with (1 := H0). simp.
      specialize IHexec with (1 := eq_refl) (2 := Hrrrr).
      pose proof putmany_of_list_states_compat as P.
      specialize P with (1 := H2).
      edestruct P as (st0' & Put & Co); cycle 1.

(*
    induction n; intros; [
      match goal with
      | H: eval 0 _ _ _ = Some _ |- _ => solve [inversion H]
      end
    |].
    unfold eval, eval' in *.
    invert_eval_stmt;
      try destruct_pair_eqs;
      match goal with
      | H: erase ?s = _ |- _ =>
        destruct s;
        inversion H;
        subst;
        clear H
      end;
      subst;
      match goal with
      | H: checker _ ?x = _ |- _ => pose proof H as C; remember x as AS in C
      end;
      simpl in *;
      repeat (destruct_one_match_hyp; [|discriminate]);
      repeat match goal with
             | H: Some _ = Some _ |- _ => inversion H; subst; clear H
             | H: reverse_get _ _ = Some _ |- _ =>
                  let H' := fresh H "_rrg" in
                  unique pose proof (reverse_reverse_get _ _ _ H) as H'
             | H: states_compat _ _ _ |- _ => erewrite H by eassumption
             end;
      repeat match goal with
             | H: states_compat _ _ _ |- _ => erewrite H by eassumption
             | H: _ = _ |- _ => rewrite H
             end;
      repeat (rewrite reg_eqb_ne by congruence);
      repeat (rewrite reg_eqb_eq by congruence);
      eauto with checker_hints.
    - clear Case_SIf_Then.
      edestruct IHn as [st2' [? ?]]; eauto with checker_hints.
    - clear Case_SIf_Else.
      edestruct IHn as [st2' [? ?]]; eauto with checker_hints.
    - clear Case_SLoop_Done.
      edestruct IHn as [st2' [? ?]]; eauto with checker_hints.
      rewrite H0.
      pose proof H1 as P.
      unfold states_compat in P.
      specialize P with (2 := H).
      rewrite P.
      + rewrite reg_eqb_eq by reflexivity. eauto.
      + eassumption.

    - clear Case_SLoop_NotDone.
      pose proof E0 as C1. pose proof E1 as C2.
      eapply IHn in E0; [| |reflexivity|]; [|eassumption|]; cycle 1. {
        eapply states_compat_extends; [|eassumption].
        apply precond_weakens.
      }
      destruct_products.
      eapply IHn in E1; [| |reflexivity|]; [|eauto with checker_hints..].
      destruct_products.
      (* get rid of r and replace it by Inv everywhere *)
      remember (loop_inv mappings r annotated1 annotated2) as Inv.
      (* Search r. only HeqInv and C *)
      specialize IHn with (annotated := (ASLoop annotated1 cond annotated2)).
      move IHn at bottom.
      specialize IHn with (r := r).
      specialize IHn with (2 := eq_refl).
      specialize IHn with (1 := H).
      specialize IHn with (s' := SLoop s i s0).
      edestruct IHn as [? [? ?]].
      + exact C.
      + unfold precond.
        eapply states_compat_extends; [|eassumption].
        subst Inv.
        apply loop_inv_step.
      + eexists.
        rewrite_match.
        pose proof E0r as P.
        unfold states_compat in P.
        erewrite P by eassumption. clear P.
        rewrite reg_eqb_ne by congruence.
        split; [eassumption|].
        simpl in H1.
        subst Inv.
        assumption.

    - clear Case_SSeq.
      eapply IHn in E.
      destruct_products.
      eapply IHn in E0.
      destruct_products.
      eexists.
      rewrite El. all: typeclasses eauto with core checker_hints.
    - clear Case_SCall.
      discriminate.
   *)
  Admitted.

  (* code1  <----erase----  annotated  ----checker---->  code2 *)
  Definition code_related code1 m code2 := exists annotated,
      erase annotated = code1 /\ checker m annotated = Some code2.

  Definition related: @FlatImp.SimState srcSemanticsParams ->
                      @FlatImp.SimState impSemanticsParams -> Prop :=
    fun '(e1, c1, done1, t1, m1, l1) '(e2, c2, done2, t2, m2, l2) =>
      done1 = done2 /\
      (forall f argnames retnames body1,
          map.get e1 f = Some (argnames, retnames, body1) ->
          exists args body2 binds,
            map.get e2 f = Some (map snd args, map snd binds, body2) /\
            argnames = map fst args /\
            retnames = map fst binds /\
            code_related body1 (map.putmany_of_pairs map.empty args) body2) /\
      t1 = t2 /\
      m1 = m2 /\
      code_related c1 map.empty c2.
  (* TODO could/should also relate l1 and l2 *)

  Lemma checkerSim: simulation (@FlatImp.SimExec srcSemanticsParams)
                               (@FlatImp.SimExec impSemanticsParams) related.
  Proof.
    unfold simulation.
    intros *. intros R Ex1.
    unfold FlatImp.SimExec, related in *.
    destruct s1 as (((((e1 & c1) & done1) & t1) & m1) & l1).
    destruct s2 as (((((e2 & c2) & done2) & t2) & m2) & l2).
    destruct R as (F & ? & ? & ? & (annotated & Er & Ch)).
    destruct Ex1 as (? & Ex1).
    subst t2 m2 done1 done2. rename t1 into t, m1 into m.
    split; [reflexivity|intros].
    eapply exec.weaken.
    - eapply checker_correct. 2: eapply Ex1. 2,3: eassumption.
      + case TODO_sam.
      + assert (precond map.empty annotated = map.empty) as E by case TODO_sam.
        rewrite E. unfold states_compat. intros.
        rewrite @map.get_empty in * by typeclasses eauto. discriminate.
    - simpl. intros.
      unfold code_related.
      firstorder idtac.
  Qed.

  (*
  Lemma regalloc_respects_afterlife: forall s m l r,
      (* TODO say something about r *)
      subset l (union (range m) (certainly_written s)) ->
      subset l (range (mappings m (regalloc m s l r))).
  Proof.
    induction s; intros;
      [ set ( case := SLoad )
      | set ( case := SStore )
      | set ( case := SLit )
      | set ( case := SOp )
      | set ( case := SSet )
      | set ( case := SIf )
      | set ( case := SLoop )
      | set ( case := SSeq )
      | set ( case := SSkip )
      | set ( case := SCall )
      | set ( case := SInteract ) ];
      move case at top;
      simpl in *;
      repeat (destruct_one_match); simpl in *.
    (*
    {
      rename H into AA.
      pose proof @reverse_get_Some as PP.
      specialize PP with (1 := E). clear E.
      revert AA PP.

      Notation "A ⟹ B" := (A -> B)  (at level 99, right associativity,
                                     format "A  ⟹  '/' B" ).
      (* Nitpick found no counterexample *)
      admit.
    }
    Focus 11. {
      remember (union (certainly_written s1) (certainly_written s2)) as c1.
      remember (union (live s1) (diff (live s2) (certainly_written s1))) as m1.
      remember (remove_values m (diff (range m) (union m1 (diff l c1)))) as m2.
      remember (regalloc m2 s1 (union (live s2) l)) as R1.
      remember (regalloc (mappings m2 R1) s2 l) as R2.
      specialize (IHs1 m2 (union (live s2) l)). rewrite <- HeqR1 in IHs1.
      specialize (IHs2 (mappings m2 R1) l). rewrite <-HeqR2 in IHs2.

      match type of IHs2 with
      | _ -> subset _ ?X => apply subset_trans with (s4 := X)
      end.
      admit.
      admit.
     *)
  Admitted.

  Lemma checker_monotone: forall r1 r2 s s',
      extends r2 r1 ->
      checker r1 s = Some s' ->
      checker r2 s = Some s'.
  Proof using.
  Admitted.

  Lemma regalloc_succeeds: forall s annotated m l r,
      (* TODO restrictions on l and r *)
      subset (live s) (range m) ->
      regalloc m s l r = annotated ->
      exists s', checker m annotated = Some s'.
  Proof.
    induction s; intros; simpl in *;
      [ set ( case := ASLoad )
      | set ( case := ASStore )
      | set ( case := ASLit )
      | set ( case := ASOp )
      | set ( case := ASSet )
      | set ( case := ASIf )
      | set ( case := ASLoop )
      | set ( case := ASSeq )
      | set ( case := ASSkip )
      | set ( case := ASCall )
      | set ( case := ASInteract ) ];
      move case at top;
      repeat (subst ||
              destruct_pair_eqs ||
              (destruct_one_match_hyp; try discriminate) ||
              (destruct_one_match; try discriminate));
      simpl.
    - (* ASLoad: reverse_get of regalloc Some *)
      destruct (reverse_get m a) eqn: F.
      + (* reverse_get of checker Some *)
        eexists. reflexivity.
      + (* reverse_get of checker None *)
        exfalso. map_solver impvar srcvar.
    - (* ASLoad: reverse_get of regalloc None --> a fresh var will be picked *)
      destruct (reverse_get m a) eqn: F.
      + (* reverse_get of checker Some *)
        eexists. reflexivity.
      + (* reverse_get of checker None *)
        exfalso. map_solver impvar srcvar.

    - destruct (reverse_get m a) eqn: F; destruct (reverse_get m v) eqn: G;
        [eexists; reflexivity| (exfalso; map_solver impvar srcvar)..].
    - eauto.
    - eauto.
    - destruct (reverse_get m y) eqn: F; destruct (reverse_get m z) eqn: G;
        [eexists; reflexivity| (exfalso; map_solver impvar srcvar)..].
    - destruct (reverse_get m y) eqn: F; destruct (reverse_get m z) eqn: G;
        [eexists; reflexivity| (exfalso; map_solver impvar srcvar)..].
    - destruct (reverse_get m y) eqn: F;
        [eexists; reflexivity| (exfalso; map_solver impvar srcvar)..].
    - destruct (reverse_get m y) eqn: F;
        [eexists; reflexivity| (exfalso; map_solver impvar srcvar)..].
    - destruct (reverse_get m cond) eqn: F; [| exfalso; map_solver impvar srcvar].
      repeat match goal with
      | IH: _ |- context [ checker _ (regalloc ?m' ?s ?l') ] =>
        specialize IH with (m := m') (l := l') (2 := eq_refl)
      end.
      destruct IHs1 as [s1' IHs1].
      { clear IHs2. map_solver impvar srcvar. }
      destruct IHs2 as [s2' IHs2].
      { clear IHs1. map_solver impvar srcvar. }
      eapply checker_monotone in IHs1; [ rewrite IHs1 | map_solver impvar srcvar ].
      eapply checker_monotone in IHs2; [ rewrite IHs2 | map_solver impvar srcvar ].
      eexists. reflexivity.
    - (* TODO maybe SLoop case of regalloc is bad! *)
      admit.
    - match goal with
      | |- context [ checker _ (regalloc ?m' ?s ?l') ] =>
        specialize IHs1 with (m := m') (l := l') (2 := eq_refl)
      end.
      destruct IHs1 as [s1' IHs1].
      { clear IHs2. map_solver impvar srcvar. }
      eapply checker_monotone in IHs1; [ rewrite IHs1 | map_solver impvar srcvar ].
      clear IHs1.
      match goal with
      | |- context [ checker _ (regalloc ?m' ?s ?l') ] =>
        specialize IHs2 with (m := m') (l := l') (2 := eq_refl)
      end.
      destruct IHs2 as [s2' IHs2].
      {
        remember (remove_values m
             (diff (range m)
                (union (union (live s1) (diff (live s2) (certainly_written s1)))
                       (diff l (union (certainly_written s1) (certainly_written s2))))))
                 as m1.
        specialize (regalloc_respects_afterlife s1 m1 (union (live s2)
                                                             (diff l (certainly_written s2)))).
        intro R.
        match type of R with
        | ?A -> _ => assert A; [| solve [map_solver impvar srcvar] ]
        end.
        clear R.
        subst.
        map_solver impvar srcvar.
        {
          destruct (dec (x \in certainly_written s1)); [solve[ auto ] |].
          left.
          map_solver impvar srcvar.
        }
        {
          destruct (dec (x \in certainly_written s1)); [solve[ auto ] |].
          left.
          destruct Hx as [k Hx].
          - destruct (dec (x \in live s1)); auto.
            destruct (dec (x \in live s2)); auto.
            right.
            exfalso.
            map_solver impvar srcvar.
            admit.
          - exists k.
            map_solver impvar srcvar. (* TODO this one should succeed *)
            exfalso.
            apply c_r.
            destruct (dec (s \in live s1)); auto.
            destruct (dec (s \in live s2)); auto.
            intuition auto.
        }
      }
      eapply checker_monotone in IHs2; [ rewrite IHs2; eexists; reflexivity |  ].
      clear IHs2.
      apply mappings_monotone.
      map_solver impvar srcvar.
    - eauto.
    - eauto.
  Abort.
  *)

End RegAlloc.
