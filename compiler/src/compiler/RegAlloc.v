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
Require Import coqutil.Datatypes.List.
Require Import coqutil.Tactics.Simp.
Require Import compiler.Simulation.


Local Notation "'bind_opt' x <- a ; f" :=
  (match a with
   | Some x => f
   | None => None
   end)
  (right associativity, at level 70, x pattern).

Axiom TODO_sam: False.

Module map. Section WithParams.
  Context {K V: Type}.

  Class ops(M: map.map K V) := {
    (* applies f to all k in (union (dom m1) (dom m2)) and (get m1 k), (get m2 k) *)
    combine(f: K -> option V -> option V -> option V)(m1 m2: M): M;
  }.

  Context {M: map.map K V}.

  (* set intersection when interpreting maps as sets of tuples *)
  Definition intersect{o: ops M}(value_eqb: V -> V -> bool): M -> M -> M :=
    combine (fun k ov1 ov2 => match ov1, ov2 with
                              | Some v1, Some v2 => if value_eqb v1 v2 then Some v1 else None
                              | _, _ => None
                              end).

  Definition putmany_of_pairs(m: M): list (K * V) -> M :=
    fix rec l :=
    match l with
    | nil => m
    | (k, v) :: rest => map.put (rec rest) k v
    end.

  Lemma putmany_of_pairs_extends{ok: map.ok M}
        {key_eqb: K -> K -> bool}{key_eq_dec: EqDecider key_eqb}:
    forall (pairs: list (K * V)) (m1 m2: M),
    map.extends m1 m2 ->
    map.extends (putmany_of_pairs m1 pairs) (putmany_of_pairs m2 pairs).
  Proof.
    induction pairs; intros.
    - simpl. assumption.
    - simpl. destruct a as [k v]. apply map.put_extends. eapply IHpairs. assumption.
  Qed.
End WithParams. End map.


Local Notation srcvar := String.string (only parsing).
Local Notation impvar := Z (only parsing).
Local Notation stmt  := (@FlatImp.stmt srcvar). (* input type *)
Local Notation stmt' := (@FlatImp.stmt impvar). (* output type *)
Local Notation bcond  := (@FlatImp.bcond srcvar).
Local Notation bcond' := (@FlatImp.bcond impvar).

Section RegAlloc.

  Context {src2imp: map.map srcvar impvar}.
  Context {src2impOk: map.ok src2imp}.
  Context {src2imp_ops: map.ops src2imp}.

  (* annotated statement: each assignment is annotated with impvar which it assigns *)
  Inductive astmt: Type :=
    | ASLoad(sz: Syntax.access_size.access_size)(x: srcvar)(x': impvar)(a: srcvar)(ofs: Z)
    | ASStore(sz: Syntax.access_size.access_size)(a: srcvar)(v: srcvar)(ofs: Z)
    | ASLit(x: srcvar)(x': impvar)(v: Z)
    | ASOp(x: srcvar)(x': impvar)(op: Syntax.bopname.bopname)(y z: srcvar)
    | ASSet(x: srcvar)(x': impvar)(y: srcvar)
    | ASIf(cond: bcond)(bThen bElse: astmt)
    | ASLoop(body1: astmt)(cond: bcond)(body2: astmt)
    | ASSeq(s1 s2: astmt)
    | ASSkip
    | ASCall(binds: list (srcvar * impvar))(f: String.string)(args: list srcvar)
    | ASInteract(binds: list (srcvar * impvar))(f: String.string)(args: list srcvar).

  Inductive Update :=
  | Add(y: srcvar)
  | Remove.
  (* Third case: In "option Update", "None" means unchanged. *)

  Context {Updates: map.map impvar Update} {UpdatesOps: map.ops Updates} {UpdatesOk: map.ok Updates}.

  (* If we know that one of the two updates was applied, how can we represent that as a single update? *)
  Definition Either1(u1: option Update)(u2: option Update): option Update :=
    match u1, u2 with
    | Some (Add y1), Some (Add y2) =>
      if String.eqb y1 y2 then Some (Add y1) else Some Remove
    | None, None => None
    | _, _ => Some Remove
    end.

  Lemma Either1_sym: forall u1 u2,
      Either1 u1 u2 = Either1 u2 u1.
  Proof.
    intros. destruct u1 as [[? |]|]; destruct u2 as [[? |]|]; try reflexivity.
    simpl. destr (String.eqb y y0); destr (String.eqb y0 y); congruence.
  Qed.

  Definition Either(us1 us2: Updates): Updates := map.combine (fun _ => Either1) us1 us2.
  Definition Seq: Updates -> Updates -> Updates := map.putmany.

  Definition updates: astmt -> Updates :=
    fix rec s :=
      match s with
      | ASLoad _ x x' _ _ | ASLit x x' _ | ASOp x x' _ _ _ | ASSet x x' _ =>
           map.put map.empty x' (Add x)
      | ASStore _ _ _ _ => map.empty
      | ASIf cond s1 s2 => Either (rec s1) (rec s2)
      | ASLoop s1 cond s2 =>
        let r1 := rec s1 in
        let r2 := rec s2 in
        Either r1 (Seq r1 (Seq r2 r1))
      | ASSeq s1 s2 => Seq (rec s1) (rec s2)
      | ASSkip => map.empty
      | ASInteract binds _ _ | ASCall binds _ _ =>
           (map.putmany_of_pairs map.empty (List.map (fun '(x, x') => (x', Add x)) binds))
      end.

  Definition apply_update(corresp: list (srcvar * impvar))(x': impvar)(u: Update): list (srcvar * impvar) :=
    let corresp' := List.filter (fun '(y, y') => negb (Z.eqb x' y')) corresp in
    match u with
    | Add x => (x, x') :: corresp'
    | Remove => corresp'
    end.

  Definition update(corresp: list (srcvar * impvar))(s: astmt): list (srcvar * impvar) :=
    map.fold apply_update corresp (updates s).

  Lemma update_Seq: forall corresp s1 s2,
      update corresp (ASSeq s1 s2) = update (update corresp s1) s2.
  Proof.
    intros. unfold update. cbn. unfold Seq.
    (* Search map.fold. map.putmany. *)
    (* does not hold because of different orders *)
  Admitted.

  Lemma update_Skip: forall corresp, update corresp ASSkip = corresp.
  Proof.
    intros. unfold update. cbn. apply map.fold_empty.
  Qed.

  Definition get_impvar(l: list (srcvar * impvar))(x: srcvar): option impvar :=
    match List.find (fun '(y, y') => String.eqb x y) l with
    | Some (_, y) => Some y
    | None => None
    end.

  Definition cond_checker(corresp: list (srcvar * impvar))(cond: bcond): option bcond' :=
    match cond with
    | CondBinary op x y =>
        bind_opt x' <- get_impvar corresp x;
        bind_opt y' <- get_impvar corresp y;
        Some (CondBinary op x' y')
    | CondNez x =>
        bind_opt x' <- get_impvar corresp x;
        Some (CondNez x')
    end.

  Definition checker: list (srcvar * impvar) -> astmt -> option stmt' :=
    fix rec corresp s :=
      match s with
      | ASLoad sz x x' a ofs =>
          bind_opt a' <- get_impvar corresp a;
          Some (SLoad sz x' a' ofs)
      | ASStore sz a v ofs =>
          bind_opt a' <- get_impvar corresp a;
          bind_opt v' <- get_impvar corresp v;
          Some (SStore sz a' v' ofs)
      | ASLit x x' v =>
          Some (SLit x' v)
      | ASOp x x' op y z =>
          bind_opt y' <- get_impvar corresp y;
          bind_opt z' <- get_impvar corresp z;
          Some (SOp x' op y' z')
      | ASSet x x' y =>
          bind_opt y' <- get_impvar corresp y;
          Some (SSet x' y')
      | ASIf cond s1 s2 =>
          bind_opt cond' <- cond_checker corresp cond;
          bind_opt s1' <- rec corresp s1;
          bind_opt s2' <- rec corresp s2;
          Some (SIf cond' s1' s2')
      | ASLoop s1 cond s2 =>
          (* TODO need to intersect with corresp because mappings made only in s1 should not be in inv,
             using Either, but Either expects Updates, not `list (srcvar * impvar)`, so
             TODO use Updates (or better-named type) instead of `list (srcvar * impvar)` *)
          let inv := update corresp s in
          let corresp' := update inv s1 in
          bind_opt cond' <- cond_checker corresp' cond;
          bind_opt s1' <- rec inv s1;
          bind_opt s2' <- rec corresp' s2;
          Some (SLoop s1' cond' s2')
      | ASSeq s1 s2 =>
          bind_opt s1' <- rec corresp s1;
          bind_opt s2' <- rec (update corresp s1) s2;
          Some (SSeq s1' s2')
      | ASSkip => Some SSkip
      | ASCall binds f args =>
          bind_opt args' <- List.option_all (List.map (get_impvar corresp) args);
          Some (SCall (List.map snd binds) f args')
      | ASInteract binds f args =>
          bind_opt args' <- List.option_all (List.map (get_impvar corresp) args);
          Some (SInteract (List.map snd binds) f args')
      end.

  Definition erase :=
    fix rec(s: astmt): stmt :=
      match s with
      | ASLoad sz x x' a ofs => SLoad sz x a ofs
      | ASStore sz a v ofs => SStore sz a v ofs
      | ASLit x x' v => SLit x v
      | ASOp x x' op y z => SOp x op y z
      | ASSet x x' y => SSet x y
      | ASIf cond s1 s2 => SIf cond (rec s1) (rec s2)
      | ASLoop s1 cond s2 => SLoop (rec s1) cond (rec s2)
      | ASSeq s1 s2 => SSeq (rec s1) (rec s2)
      | ASSkip => SSkip
      | ASCall binds f args => SCall (List.map fst binds) f args
      | ASInteract binds f args => SInteract (List.map fst binds) f args
      end.

(*
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
  *)

  (* claim: for all astmt a, if checker succeeds and returns s', then
     (erase a) behaves the same as s' *)

  Context {width} {BW: Bitwidth width} {word: word.word width} {word_ok: word.ok word}.
  Context {mem: map.map word byte}.
  Context {srcLocals: map.map srcvar word}.
  Context {impLocals: map.map impvar word}.
  Context {srcLocalsOk: map.ok srcLocals}.
  Context {impLocalsOk: map.ok impLocals}.
  Context {srcEnv: map.map String.string (list srcvar * list srcvar * stmt)}.
  Context {impEnv: map.map String.string (list impvar * list impvar * stmt')}.
  Context {ext_spec: Semantics.ExtSpec}.

(*
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
*)

  Definition states_compat(st: srcLocals)(corresp: list (srcvar * impvar))(st': impLocals) :=
    forall (x: srcvar) (x': impvar),
      get_impvar corresp x = Some x' ->
      forall w,
        map.get st x = Some w ->
        map.get st' x' = Some w.

  Definition precond(corresp: list (srcvar * impvar))(s: astmt): list (srcvar * impvar) :=
    match s with
    | ASLoop _ _ _ => update corresp s
    | _ => corresp
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

(*
  Lemma getmany_of_list_states_compat: forall srcnames impnames corresp lH lL argvals,
      map.getmany_of_list lH srcnames = Some argvals ->
      (*map.getmany_of_list corresp srcnames = Some impnames ->*)
      states_compat lH corresp lL ->
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
  *)

  Lemma states_compat_eval_bcond: forall lH lL c c' b corresp,
      cond_checker corresp c = Some c' ->
      eval_bcond lH c = Some b ->
      states_compat lH corresp lL ->
      eval_bcond lL c' = Some b.
  Proof.
    intros. rename H1 into C. unfold states_compat in C.
    destruct c; cbn in *; simp; cbn;
      erewrite ?C by eassumption; reflexivity.
  Qed.

  Lemma states_compat_eval_bcond_None: forall lH lL c c' corresp,
      cond_checker corresp c = Some c' ->
      eval_bcond lH c <> None ->
      states_compat lH corresp lL ->
      eval_bcond lL c' <> None.
  Proof.
    intros. destr (eval_bcond lH c). 2: congruence.
    erewrite states_compat_eval_bcond; eassumption.
  Qed.

  Lemma states_compat_eval_bcond_bw: forall lH lL c c' b corresp,
      cond_checker corresp c = Some c' ->
      eval_bcond lL c' = Some b ->
      states_compat lH corresp lL ->
      eval_bcond lH c <> None ->
      eval_bcond lH c = Some b.
  Proof.
    intros. destr (eval_bcond lH c). 2: congruence.
    symmetry. rewrite <- H0. eapply states_compat_eval_bcond; eassumption.
  Qed.

  Lemma checker_correct: forall e e' s t m lH mc post,
      (forall f argnames retnames body,
          map.get e f = Some (argnames, retnames, body) ->
          exists args body' annotated binds,
            map.get e' f = Some (map snd args, map snd binds, body') /\
            argnames = map fst args /\
            retnames = map fst binds /\
            erase annotated = body /\
            checker args annotated = Some body') ->
      exec e s t m lH mc post ->
      forall lL corresp annotated s',
      erase annotated = s ->
      checker corresp annotated = Some s' ->
      states_compat lH (precond corresp annotated) lL ->
      exec e' s' t m lL mc (fun t' m' lL' mc' =>
        exists lH', states_compat lH' (update corresp annotated) lL' /\ post t' m' lH' mc').
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

    - (* Case exec.interact *)
      case TODO_sam.
    - (* Case exec.call *)
      case TODO_sam.
    - (* Case exec.load *)
      case TODO_sam.
    - (* Case exec.store *)
      case TODO_sam.

(*
    - (* Case exec.inlinetable *)
      case TODO_sam.
    - (* Case exec.stackalloc *)
      case TODO_sam.
*)

    - (* Case exec.lit *)
      case TODO_sam.
    - (* Case exec.op *)
      case TODO_sam.
    - (* Case exec.set *)
      case TODO_sam.
    - (* Case exec.if_true *)
      eapply exec.if_true. 1: eauto using states_compat_eval_bcond.
      eapply exec.weaken.
      + eapply IHexec. 1: reflexivity. 1: eassumption.
        case TODO_sam.
      + cbv beta. intros. simp. eexists. split. 2: eassumption.
        case TODO_sam.
    - (* Case exec.if_false *)
      case TODO_sam.
    - (* Case exec.loop *)
      rename H4 into IH2, IHexec into IH1, H6 into IH12.
      eapply exec.loop.
      + eapply IH1. 1: reflexivity. 1: eassumption.
        case TODO_sam.
      + cbv beta. intros. simp. eauto using states_compat_eval_bcond_None.
      + cbv beta. intros. simp. eexists. split. 2: eauto using states_compat_eval_bcond_bw.
        case TODO_sam.
      + cbv beta. intros. simp. eapply IH2; eauto using states_compat_eval_bcond_bw.
        case TODO_sam.
      + cbv beta. intros. simp. subst AS. eapply IH12; eauto.
        cbn [precond]. case TODO_sam.
    - (* Case exec.seq *)
      rename H2 into IH2, IHexec into IH1.
      eapply exec.seq.
      + eapply IH1. 2: eassumption. 1: reflexivity. case TODO_sam.
      + cbv beta. intros. simp.
        rewrite update_Seq.
        eapply IH2. 1: eassumption. 1: reflexivity. 1: eassumption. case TODO_sam.
    - (* Case exec.skip *)
      rewrite update_Skip. eapply exec.skip. eauto.
  Qed.

  (* code1  <----erase----  annotated  ----checker---->  code2 *)
  Definition code_related code1 m code2 := exists annotated,
      erase annotated = code1 /\ checker m annotated = Some code2.

  (*
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
