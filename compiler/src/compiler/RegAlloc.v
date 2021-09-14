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
    (* Collects the result of `f (get m1 k) (get m2 k)` for all k in (union (dom m1) (dom m2)).
       Or, in other words: Lifts f key-wise from `option V` to `M`. *)
    lift2(f: option V -> option V -> option V)(m1 m2: M): M;
    reverse_get: M -> V -> option K;
  }.

  Context {M: map.map K V}.

  Class ops_ok(o: ops M) := {
    lift2_spec: forall f m1 m2 k,
      f None None = None ->
      map.get (lift2 f m1 m2) k = f (map.get m1 k) (map.get m2 k);

    (* note: the other direction does not hold *)
    reverse_get_to_get: forall m k v,
        reverse_get m v = Some k -> map.get m k = Some v;
  }.

  Context {mok: map.ok M}{o: ops M}{ook: ops_ok o}.

  Lemma lift2_assoc: forall f,
      f None None = None ->
      (forall a b c, f a (f b c) = f (f a b) c) ->
      forall A B C, lift2 f A (lift2 f B C) = lift2 f (lift2 f A B) C.
  Proof.
    intros. apply map.map_ext. intros. rewrite ?lift2_spec by assumption. apply H0.
  Qed.

  Lemma lift2_idemp: forall f,
      (forall a, f a a = a) ->
      forall A, lift2 f A A = A.
  Proof.
    intros. apply map.map_ext. intros. rewrite lift2_spec; auto.
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
  | Add(y: srcvar)(forSure: bool)
  | Remove.
  (* Third case: In "option Update", "None" means unchanged. *)

  Context {Corresp: map.map impvar Update} {CorrespOps: map.ops Corresp}
          {CorrespOk: map.ok Corresp} {CorrespOpsOk: map.ops_ok CorrespOps}.

  (* If we know that one of the two updates was applied, how can we represent that as a single update? *)
  Definition Either1(u1: option Update)(u2: option Update): option Update :=
    match u1, u2 with
    | Some (Add y1 forSure1), Some (Add y2 forSure2) =>
      if String.eqb y1 y2 then Some (Add y1 (andb forSure1 forSure2)) else Some Remove
    | Some (Add y1 forSure1), None => Some (Add y1 false)
    | None, Some (Add y2 forSure2) => Some (Add y2 false)
    | None, None => None
    | _, _ => Some Remove
    end.

  Definition Seq1(u1: option Update)(u2: option Update): option Update :=
    match u2 with
    | Some (Add _ true) => u2
    | Some (Add y2 false) =>
      match u1 with
      | Some (Add y1 forSure1) => if String.eqb y1 y2 then u1 else Some Remove
      | Some Remove => Some Remove
      | None => u2
      end
    | Some Remove => u2
    | None => u1
    end.

  Definition Either: Corresp -> Corresp -> Corresp := map.lift2 Either1.
  Definition Seq: Corresp -> Corresp -> Corresp := map.lift2 Seq1.

  Ltac t :=
    match goal with
    | |- _ => progress intros
    | |- _ => progress simpl in *
    | |- _ => congruence
    | o: option Update |- _ => destruct o
    | u: Update |- _ => destruct u
    | b: bool |- _ => destruct b
    | |- context[String.eqb ?x ?y] => destr (String.eqb x y)
    | H: context[String.eqb ?x ?y] |- _ => destr (String.eqb x y)
    | |- _ /\ _ => split
    end.

  Lemma Seq1_None_l: forall a, Seq1 None a = a. Proof. repeat t. Qed.
  Lemma Seq1_None_r: forall a, Seq1 a None = a. Proof. repeat t. Qed.

  Lemma Seq_empty_l: forall a, Seq map.empty a = a.
  Proof.
    intros. unfold Seq. apply map.map_ext. intros. rewrite map.lift2_spec by reflexivity.
    rewrite map.get_empty. apply Seq1_None_l.
  Qed.

  Lemma Seq_empty_r: forall a, Seq a map.empty = a.
  Proof.
    intros. unfold Seq. apply map.map_ext. intros. rewrite map.lift2_spec by reflexivity.
    rewrite map.get_empty. apply Seq1_None_r.
  Qed.

  Lemma Seq1_assoc: forall a b c: option Update, Seq1 a (Seq1 b c) = Seq1 (Seq1 a b) c.
  Proof. repeat t. Qed.

  Lemma Seq_assoc: forall a b c: Corresp, Seq a (Seq b c) = Seq (Seq a b) c.
  Proof. apply map.lift2_assoc. 1: reflexivity. apply Seq1_assoc. Qed.

  Lemma Seq1_idemp: forall a: option Update, Seq1 a a = a.
  Proof. repeat t. Qed.

  Lemma Seq_idemp: forall a: Corresp, Seq a a = a.
  Proof. apply map.lift2_idemp. apply Seq1_idemp. Qed.

  Lemma Either1_sym: forall u1 u2,
      Either1 u1 u2 = Either1 u2 u1.
  Proof. repeat t. Qed.

  Lemma Either_sym: forall A B, Either A B = Either B A.
  Proof.
    intros. apply map.map_ext. intros. unfold Either. rewrite ?map.lift2_spec by reflexivity.
    apply Either1_sym.
  Qed.

  Lemma Either1_idemp: forall a, Either1 a a = a. Proof. repeat t. Qed.

  Lemma Either_idemp: forall A, Either A A = A.
  Proof.
    intros. apply map.map_ext. intros. unfold Either. rewrite ?map.lift2_spec by reflexivity.
    apply Either1_idemp.
  Qed.

  Lemma Either_empty_l: forall a, Either map.empty a = a. Abort. (* doesn't hold *)
  Lemma Either_empty_r: forall a, Either a map.empty = a. Abort. (* doesn't hold *)

  Lemma Either1_assoc: forall a b c: option Update, Either1 a (Either1 b c) = Either1 (Either1 a b) c.
  Proof. repeat t. Qed.

  Lemma Either_assoc: forall a b c: Corresp, Either a (Either b c) = Either (Either a b) c.
  Proof. apply map.lift2_assoc. 1: reflexivity. apply Either1_assoc. Qed.

  Lemma Seq1_Either1_l_distrib: forall a b c,
      Seq1 (Either1 a b) c = Either1 (Seq1 a c) (Seq1 b c).
  Proof. repeat t. Qed.

  Lemma Seq_Either_l_distrib: forall A B C,
      Seq (Either A B) C = Either (Seq A C) (Seq B C).
  Proof.
    unfold Seq, Either. intros. apply map.map_ext. intros. rewrite ?map.lift2_spec by reflexivity.
    apply Seq1_Either1_l_distrib.
  Qed.

  Lemma Seq1_Either1_r_distrib: forall a b c,
      Seq1 a (Either1 b c) = Either1 (Seq1 a b) (Seq1 a c).
  Proof. repeat t. Qed.

  Lemma Seq_Either_r_distrib: forall A B C,
      Seq A (Either B C) = Either (Seq A B) (Seq A C).
  Proof.
    unfold Seq, Either. intros. apply map.map_ext. intros. rewrite ?map.lift2_spec by reflexivity.
    apply Seq1_Either1_r_distrib.
  Qed.

  Definition updates: astmt -> Corresp :=
    fix rec s :=
      match s with
      | ASLoad _ x x' _ _ | ASLit x x' _ | ASOp x x' _ _ _ | ASSet x x' _ =>
           map.put map.empty x' (Add x true)
      | ASStore _ _ _ _ => map.empty
      | ASIf cond s1 s2 => Either (rec s1) (rec s2)
      | ASLoop s1 cond s2 =>
        (* We need to compute the infinite Either
           Either r1 (r1;r2;r1) (r1;r2;r1;r2;r1) ...
           But thanks to Seq_assoc and Seq_idemp, all longer seqs equal (r1;r2;r1),
           so using Either_assoc and Either_idemp, we can conclude that the infinite Either equals
           Either r1 (r1;r2;r1) *)
        let r1 := rec s1 in
        let r2 := rec s2 in
        Either r1 (Seq r1 (Seq r2 r1))
      | ASSeq s1 s2 => Seq (rec s1) (rec s2)
      | ASSkip => map.empty
      | ASInteract binds _ _ | ASCall binds _ _ =>
          map.of_list (List.map (fun '(x, x') => (x', Add x true)) binds)
      end.

  Definition update(corresp: Corresp)(s: astmt): Corresp := Seq corresp (updates s).

  Definition get_impvar(corresp: Corresp)(x: srcvar): option impvar := map.reverse_get corresp (Add x true).

  Definition cond_checker(corresp: Corresp)(cond: bcond): option bcond' :=
    match cond with
    | CondBinary op x y =>
        bind_opt x' <- get_impvar corresp x;
        bind_opt y' <- get_impvar corresp y;
        Some (CondBinary op x' y')
    | CondNez x =>
        bind_opt x' <- get_impvar corresp x;
        Some (CondNez x')
    end.

  (* invariant for `(ASLoop s1 _ s2)` which we enter the first time with `corresp` *)
  Definition loop_inv(corresp: Corresp)(s1 s2: astmt): Corresp :=
    (* The invariant should be the infinite Either
         Either corresp
                corresp;s1;s2
                corresp;s1;s2;s1;s2
                ...
       But thanks to Seq_assoc and Seq_idemp, all longer seqs equal `corresp;s1;s2`,
       so using Either_assoc and Either_idemp, we can conclude that the infinite Either equals
         Either corresp (corresp;s1;s2) *)
    Either corresp (Seq corresp (Seq (updates s1) (updates s2))).

  Definition checker: Corresp -> astmt -> option stmt' :=
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
          let inv := loop_inv corresp s1 s2 in
          let corresp' := update inv s1 in
          bind_opt cond' <- cond_checker corresp' cond;
          bind_opt s1' <- rec inv s1;
          bind_opt s2' <- rec corresp' s2;
          Some (SLoop s1' cond' s2')
      | ASSeq s1 s2 =>
          bind_opt s1' <- rec corresp s1;
          bind_opt s2' <- rec (Seq corresp (updates s1)) s2;
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
    (src2imp * Corresp * list impvar) :=
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
      (map.putmany_of_list m tuples, ASCall tuples f args, a)
    | SInteract binds f args =>
      let '(m, tuples, a) := rename_binds m binds a in
      (map.putmany_of_list m tuples, ASInteract tuples f args, a)
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

  Definition states_compat(st: srcLocals)(corresp: Corresp)(st': impLocals) :=
    forall (x: srcvar) (x': impvar),
      map.get corresp x' = Some (Add x true) ->
      forall w,
        map.get st x = Some w ->
        map.get st' x' = Some w.

  Definition precond(corresp: Corresp)(s: astmt): Corresp :=
    match s with
    | ASLoop s1 c s2 => loop_inv corresp s1 s2
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
        states_compat l' (map.putmany_of_list r binds) lL'.
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
    destruct c; cbn in *; simp; cbn; unfold get_impvar in *;
      erewrite ?C by eauto using map.reverse_get_to_get; reflexivity.
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

  Lemma invert_Either1_Add_true: forall u1 u2 x,
      Either1 u1 u2 = Some (Add x true) ->
      u1 = Some (Add x true) /\ u2 = Some (Add x true).
  Proof. repeat t. Qed.

  Lemma invert_Seq1_Add_true: forall u1 u2 x,
      Seq1 u1 u2 = Some (Add x true) ->
      u1 = Some (Add x true) /\ (u2 = None \/ u2 = Some (Add x false)) \/
      u2 = Some (Add x true).
  Proof. repeat t; auto. inversion H. subst. auto. Qed.

  Lemma states_compat_Either_l: forall lH m1 m2 lL,
      states_compat lH m2 lL ->
      states_compat lH (Either m1 m2) lL.
  Proof.
    unfold states_compat. intros. eapply H. 2: eassumption.
    unfold Either in *.
    rewrite map.lift2_spec in H0 by reflexivity.
    eapply invert_Either1_Add_true in H0. destruct H0. assumption.
  Qed.
  Hint Resolve states_compat_Either_l : states_compat.

  Lemma states_compat_Either_r: forall lH m1 m2 lL,
      states_compat lH m1 lL ->
      states_compat lH (Either m1 m2) lL.
  Proof. intros. rewrite Either_sym. apply states_compat_Either_l. assumption. Qed.
  Hint Resolve states_compat_Either_r : states_compat.

  Lemma states_compat_precond: forall lH corresp lL s,
      states_compat lH corresp lL ->
      states_compat lH (precond corresp s) lL.
  Proof.
    intros. destruct s; cbn; try assumption.
    unfold update, loop_inv in *.
    eapply states_compat_Either_r. assumption.
  Qed.
  Hint Resolve states_compat_precond : states_compat.

  Lemma states_compat_get: forall corresp lL lH y y' v,
      states_compat lH corresp lL ->
      get_impvar corresp y = Some y' ->
      map.get lH y = Some v ->
      map.get lL y' = Some v.
  Proof. eauto using map.reverse_get_to_get. Qed.

(* Counterexample (happens if two impvars store the same srcvar):

  [a<--x;       a->1         x->1
   a<--y;       b->2         y->1
   b<--z]                    z->2

   a(x) = b     --->   x = z

  [b<--x;       a->2         x->2
   a<--y;       b->2         y->1             a<--y binding requires y->2 !!
   b<--z]                    z->2

   adding the b<--x binding invalidates the a<--x binding (because impvars equal),
   but also invalidates the a<--y binding!! (because a gets a new value, so y
   now contains the value of the old a) [SSA would solve this because a couldn't be reassigned]

  Updates: key for removal: srcvar
           key for addition: impvar

  a(x) = b
  if (...) {
    a(x) = c
  } else
    skip
  }

  then branch: Rem(a, <>x); Add(a, x)
  whole if: ??

  or: semantics ("apply updates") of Add(a,x) is to remove all bindings with srcvar=x and then add a<--x

  then branch: Add(a,x)
  whole if: MaybeAdd(a,x)

  or: "value of a may change" event: Mod(a)
  Mod does not commute with Add, so it's hard to aggregate updates without knowing current state

  then branch: Mod(a); Add(a, x)
  whole if: Mod(a); MaybeAdd(a, x)
*)

  Lemma states_compat_put: forall lH corresp lL x x' v,
      states_compat lH corresp lL ->
      states_compat (map.put lH x v) (Seq corresp (map.put map.empty x' (Add x true))) (map.put lL x' v).
  Proof using .
    intros. unfold states_compat in *. intros k k'. intros.
    rewrite map.get_put_dec. rewrite map.get_put_dec in H1.
    unfold Seq in H0. rewrite map.lift2_spec in H0 by reflexivity.
    eapply invert_Seq1_Add_true in H0. rewrite map.get_put_dec in H0.
    destr (Z.eqb x' k').
    - subst k'. destruct H0.
      + destruct H0. destruct H2; inversion H2.
      + inversion H0. subst k. rewrite String.eqb_refl in H1. exact H1.
    - rewrite map.get_empty in H0. destruct H0. 2: discriminate.
      apply proj1 in H0.
      eapply H. 1: eassumption.
      destr (String.eqb x k).
      + subst k. admit. (* doesn't hold!! *)
      + assumption.
  Admitted. (* doesn't hold!! *)

  Lemma Seq2_idemp: forall corresp u0 u1,
      Seq corresp (Seq u0 (Seq u1 (Seq u0 u1))) = Seq corresp (Seq u0 u1).
  Proof.
    intros. rewrite <- (Seq_idemp (Seq u0 u1)) at 2.
    rewrite <-?Seq_assoc. reflexivity.
  Qed.

  Hint Rewrite <- Seq_assoc : corresp.
  Hint Rewrite Seq_Either_l_distrib Seq_Either_r_distrib Seq2_idemp Either_idemp : corresp.

  Ltac solve_states_compat :=
    let C := fresh "C" in
    match goal with
    | H: states_compat ?lH _ ?lL |- states_compat ?lH _ ?lL =>
      clear -H CorrespOk CorrespOpsOk; rename H into C
    end;
    cbn [precond] in *;
    unfold update, loop_inv in *;
    cbn [updates] in *;
    repeat match goal with
           | |- context[updates ?s] => let u := fresh "u0" in forget (updates s) as u
           | H: context[updates ?s] |- _ => let u := fresh "u0" in forget (updates s) as u
           end;
    autorewrite with corresp in *;
    eauto with states_compat.

  Hint Constructors exec.exec : checker_hints.
  Hint Resolve states_compat_get : checker_hints.
  Hint Resolve states_compat_put : checker_hints.

  Lemma checker_correct: forall (e: srcEnv) (e': impEnv) s t m lH mc post,
      (forall f argnames retnames body,
          map.get e f = Some (argnames, retnames, body) ->
          exists args body' annotated binds,
            map.get e' f = Some (map snd args, map snd binds, body') /\
            argnames = map fst args /\
            retnames = map fst binds /\
            erase annotated = body /\
            checker (map.of_list (List.map (fun '(x, x') => (x', Add x true)) binds)) annotated = Some body') ->
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
      unfold update. cbn. eauto 10 with checker_hints.
    - (* Case exec.if_true *)
      eapply exec.if_true. 1: eauto using states_compat_eval_bcond.
      eapply exec.weaken.
      + eapply IHexec. 1: reflexivity. 1: eassumption. solve_states_compat.
      + cbv beta. intros. simp. eexists. split. 2: eassumption. solve_states_compat.
    - (* Case exec.if_false *)
      eapply exec.if_false. 1: eauto using states_compat_eval_bcond.
      eapply exec.weaken.
      + eapply IHexec. 1: reflexivity. 1: eassumption. solve_states_compat.
      + cbv beta. intros. simp. eexists. split. 2: eassumption. solve_states_compat.
    - (* Case exec.loop *)
      rename H4 into IH2, IHexec into IH1, H6 into IH12.
      eapply exec.loop.
      + eapply IH1. 1: reflexivity. 1: eassumption. solve_states_compat.
      + cbv beta. intros. simp. eauto using states_compat_eval_bcond_None.
      + cbv beta. intros. simp. eexists. split. 2: eauto using states_compat_eval_bcond_bw. solve_states_compat.
      + cbv beta. intros. simp. eapply IH2; eauto using states_compat_eval_bcond_bw. solve_states_compat.
      + cbv beta. intros. simp. subst AS. eapply IH12; eauto. solve_states_compat.
    - (* Case exec.seq *)
      rename H2 into IH2, IHexec into IH1.
      eapply exec.seq.
      + eapply IH1. 2: eassumption. 1: reflexivity. solve_states_compat.
      + cbv beta. intros. simp.
        unfold update. cbn. rewrite Seq_assoc.
        eapply IH2. 1: eassumption. 1: reflexivity. 1: eassumption. unfold update in *. solve_states_compat.
    - (* Case exec.skip *)
      unfold update. cbn. rewrite Seq_empty_r. eapply exec.skip. eauto.
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
            code_related body1 (map.putmany_of_list map.empty args) body2) /\
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
