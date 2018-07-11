Require compiler.util.Common.

Local Notation "'bind_Some' x <- a ; f" :=
  (match a with
   | Some x => f
   | None => None
   end)
    (right associativity, at level 60, x pattern).

Class ImpParameters :=
  {
    mword : Type;
    mword_nonzero : mword -> bool;

    varname : Type;
    funname : Type;
    actname : Type;
    bopname : Type;
    mem : Type;

    varmap_functions : compiler.util.Map.MapFunctions varname mword;

    interp_binop : bopname -> mword -> mword -> mword;
    load : mword -> mem -> option mword;
    store : mword -> mword -> mem -> option mem;
  }.
Global Existing Instance varmap_functions.
Definition varmap {p:ImpParameters} : Type := Map.map varname mword.

Class ImpWorld (p:ImpParameters) :=
  {
    world : Type;
    external_step : world -> mem*actname*list mword -> mem*list mword -> world -> Prop;
  }.

Section Imp.
  Goal True. let cls := constr:(ImpParameters) in match constr:(Set) with _ => (let none := constr:(_:cls) in idtac); fail 99 "DUPLICATE INSTANCE" | _ => idtac end. Abort.
  Context {p : ImpParameters}.

  Inductive expr  : Type :=
  | ELit(v: mword)
  | EVar(x: varname)
  | EOp(op: bopname) (e1 e2: expr).

  Inductive stmt :=
  | SLoad(x: varname) (addr: expr)
  | SStore(addr val: expr)
  | SSet(x: varname)(e: expr)
  | SIf(cond: expr)(bThen bElse: stmt)
  | SWhile(cond: expr)(body: stmt)
  | SSeq(s1 s2: stmt)
  | SSkip
  | SCall(binds: list varname)(f: funname)(args: list expr)
  | SIO(binds: list varname)(io : actname)(args: list expr).

  Inductive cont :=
  | CSkip
  | CSeq (c1:cont) (c2: stmt)
  | CStack (locals: varmap) (cf: cont) (binds rets: list varname).

  Definition blocked_cont := list mword -> option (varmap * cont).
  Definition BWait (locals : varmap) (binders : list varname) : blocked_cont :=
    fun values => bind_Some l' <- Common.putmany binders values locals; Some (l', CSkip).
  Definition BSeq (c1 : blocked_cont) (c2 : stmt) :=
    fun values => bind_Some (l, c1) <- c1 values; Some (l, CSeq c1 c2).
  Definition BStack (caller_locals : varmap) (callee : blocked_cont) (binds rets: list varname) : blocked_cont :=
    fun values => bind_Some (callee_locals, c) <- callee values; Some (caller_locals, CStack callee_locals c binds rets).

  Class ImpFunctions :=
    {
      lookupFunction : funname -> option (list varname * list varname * stmt)
    }.

  Fixpoint interp_expr (l:varmap) (e:expr) : option mword :=
    match e with
    | ELit v => Some v
    | EVar x => Map.get l x
    | EOp op e1 e2 =>
      bind_Some v1 <- interp_expr l e1;
        bind_Some v2 <- interp_expr l e2;
        Some (interp_binop op v1 v2)
    end.

  Inductive computation_result :=
  | done (_:mem) (_:varmap)
  | blocked (_:mem) (_:actname) (_:list mword) (_:blocked_cont).

  Section WithFunctions.
    Context {F:ImpFunctions}.
    Fixpoint interp_stmt(f: nat)(m: mem)(l: varmap)(s: stmt): option computation_result :=
      match f with
      | 0 => None (* out of fuel *)
      | S f => match s with
        | SLoad x a =>
          bind_Some a <- interp_expr l a;
          bind_Some v <- load a m;
          Some (done m (Map.put l x v))
        | SStore a v =>
          bind_Some a <- interp_expr l a;
          bind_Some v <- interp_expr l v;
          bind_Some m <- store a v m;
          Some (done m l)
        | SSet x e =>
          bind_Some v <- interp_expr l e;
          Some (done m (Map.put l x v))
        | SIf cond bThen bElse =>
          bind_Some v <- interp_expr l cond;
          interp_stmt f m l (if mword_nonzero v then bThen else bElse)
        | SWhile cond body =>
          bind_Some v <- interp_expr l cond;
          if mword_nonzero v
          then
            bind_Some r <- interp_stmt f m l body;
            match r with
            | blocked m action args b => Some (blocked m action args (BSeq b (SWhile cond body)))
            | done m l => interp_stmt f m l (SWhile cond body)
            end
          else Some (done m l)
        | SSeq s1 s2 =>
          bind_Some r <- interp_stmt f m l s1;
          match r with
          | blocked m action args b => Some (blocked m action args (BSeq b s2))
          | done m l => interp_stmt f m l s2
          end
        | SSkip => Some (done m l)
        | SCall binds fname args =>
          bind_Some (params, rets, fbody) <- lookupFunction fname;
            bind_Some argvs <- Common.option_all (List.map (interp_expr l) args);
            bind_Some l0 <- Common.putmany params argvs Map.empty_map;
            bind_Some r <- interp_stmt f m l0 fbody;
            match r with
            | blocked m' action args b => Some (blocked m' action args (BStack l b binds rets))
            | done m l1 => 
              bind_Some retvs <- Common.option_all (List.map (Map.get l1) rets);
              bind_Some l' <- Common.putmany binds retvs l;
              Some (done m l')
            end
        | SIO binds action args =>
          bind_Some argvs <- Common.option_all (List.map (interp_expr l) args);
          Some (blocked m action argvs (BWait l binds))
        end
      end.
    Definition exec_stmt m l c r := exists f, interp_stmt f m l c = Some r.
    
    Fixpoint interp_cont(f: nat)(m: mem)(l: varmap)(c: cont): option computation_result :=
      match f with
      | 0 => None (* out of fuel *)
      | S f =>
        match c with
        | CSkip =>  interp_stmt f m l SSkip
        | CSeq c1 c2 =>
          bind_Some r <- interp_cont f m l c1;
          match r with
          | blocked m action args b => Some (blocked m action args (BSeq b c2))
          | done m l => interp_stmt f m l c2
          end
        | CStack lf cf binds rets =>
          bind_Some r <- interp_cont f m lf cf;
          match r with
          | blocked m action args b => Some (blocked m action args (BStack l b binds rets))
          | done m l1 => 
            bind_Some retvs <- Common.option_all (List.map (Map.get l1) rets);
            bind_Some l' <- Common.putmany binds retvs l;
            Some (done m l')
          end
        end
      end.
    Definition exec_cont m l c r := exists f, interp_cont f m l c = Some r.

    (* If a predicate [P_x : forall b, Prop] identifies the return value of a partial function [f x],
       [arbitraryIfUndefined P_x] identifies the return value of [f x] when [f x] is defined and allows
       arbitrary return values otherwise. *)
    Definition arbitraryIfUndefined {T} (P : T -> Prop) (b:T) := (exists b', P b') -> P b.

    Section WithWorld.
      Context {W:ImpWorld p}.
      (* Definition done (s : world * computation_result) : Prop :=  exists w m l, s = (w, (m, inr l)). *)
      Inductive step : world*computation_result -> world*computation_result -> Prop :=
      | mk_step
          w m action argvs b
          w' retvs m_ (_:external_step w (m, action, argvs) (m_, retvs) w')
          r (_:arbitraryIfUndefined (fun r => exists l' c', b retvs = Some (l', c') /\ exec_cont m_ l' c' r) r)
        : step (w, blocked m action argvs b) (w', r).
      Definition step_alt (s s' : world*computation_result) : Prop :=
        exists w m action argvs b, s = (w, blocked m action argvs b) /\
        exists w' retvs m_, external_step w (m, action, argvs) (m_, retvs) w' /\
        exists r, arbitraryIfUndefined
                        (fun r => exists l' c', b retvs = Some (l', c') /\ exec_cont m_ l' c' r) r
                      /\ s' = (w', r).
    End WithWorld.

    Section LabeledTransitionSystem.
      Definition label : Type := (mem*actname*list mword) * (mem*list mword).
      Definition lts_external_step w i o w' : Prop := w' = @cons label (i, o) w.
      Definition IMPLTS : ImpWorld p :=
        {| world := list label ; external_step := lts_external_step |}.
    End LabeledTransitionSystem.
  End WithFunctions.
End Imp.
Arguments ImpFunctions : clear implicits.

Require Import Coq.micromega.Lia Coq.Arith.Compare_dec.

Tactic Notation "texact" tactic(x) := exact x.
Ltac head_of t :=
  match t with
  | ?t _ => head_of t
  | _ => t
  end.
Notation "'subst!' y 'for' x 'in' f" := (match y with x => f end) (at level 10).
Ltac beta1 x :=
  lazymatch x with
  | (fun a => ?f) ?b => constr:(subst! b for a in f)
  end.
Notation "'beta1!' x" := (ltac:(texact (beta1 x))) (only parsing, at level 10).

Ltac apply_to_args_of f aapp :=
  lazymatch aapp with
  | (?g ?x) ?a => let r := apply_to_args_of f constr:(g x) in constr:(r a)
  | _ ?a => constr:(f a)
  | _ => f
  end.

Ltac induction_principle_definition T :=
  let t := open_constr:(fun H:T => ltac:(induction H; exact I) : True) in
  lazymatch open_constr:(fun H:T =>
                           ltac:(let x := beta1 constr:(t H) in
                                 let h := head_of x in exact h)
                        ) with fun _ => ?v => v end.
Ltac induction_principle_no_indices T :=
  let T_ind := induction_principle_definition T in
  let T_ind_args := apply_to_args_of T_ind T in
  constr:(T_ind_args).
Ltac is_indexed_inductive T :=
  assert_succeeds(idtac; let h := head_of T in is_ind h);
  assert_fails ltac:(idtac; let _ := induction_principle_no_indices T in idtac).

(*
Goal forall x y : nat, False. intros.
  assert_succeeds (is_indexed_inductive (x = y)).
  assert_fails (is_indexed_inductive nat).
  assert_fails (is_indexed_inductive (prod nat nat)).
  assert_fails (is_indexed_inductive (list nat)).
*)

Ltac dsi_step :=
  match goal with
  | _ => progress intros
  | x:?T |- _ =>
    assert_succeeds (let h := head_of T in is_ind h);
    let __ := induction_principle_no_indices T in
    destruct x; [] (* TODO: use dependent elimination and allow indexed inductives *)
  | H: ?x = ?y |- _ =>
    let f := head_of x in
    let g := head_of y in
    is_constructor f; is_constructor g; inversion H;
    subst; (* FIXME: only subst equations generated by inversion *)
    clear H
  | H: ?x = ?y |- _ => is_var x; is_var y; subst y
  end.
Ltac dsi := repeat dsi_step.


(*
Module inversion.
  Section inversion.
    Goal True. let cls := constr:(ImpParameters) in match constr:(Set) with _ => (let none := constr:(_:cls) in idtac); fail 99 "DUPLICATE INSTANCE" | _ => idtac end. Abort.
    Context {p : ImpParameters} {E : ImpFunctions p} {W : ImpWorld p} (G : world -> mem -> Prop).
    
    Lemma invert_interp_stmt f m l s r :
      (interp_stmt f m l s = Some r) <->
      (exists f', f = S f' /\ (
      (
        exists x a, s = SLoad x a /\
        exists a0 , interp_expr l a = Some a0 /\
        exists v , load a0 m = Some v /\
        Some (m, inr (Map.put l x v)) = Some r
      ) \/ (
        exists a v, s = SStore a v /\
        exists a0 , interp_expr l a = Some a0 /\
        exists v0 , interp_expr l v = Some v0 /\
        exists m0 , store a0 v0 m = Some m0 /\
        Some (m0, inr l) = Some r
      ) \/ (
        exists x e, s = SSet x e /\
        exists v , interp_expr l e = Some v /\
        Some (m, inr (Map.put l x v)) = Some r
      ) \/ (
        exists cond bThen bElse, s = SIf cond bThen bElse /\
        exists v , interp_expr l cond = Some v /\
        interp_stmt f' m l (if mword_nonzero v then bThen else bElse) = Some r
      ) \/ (
        exists cond body, s = SWhile cond body /\
        exists v , interp_expr l cond = Some v /\ (
        (
           mword_nonzero v = true /\
           exists m0 r0, interp_stmt f' m l body = Some (m0, r0) /\ (
           (
             exists action args b, r0 = inl (action, args, b) /\
             Some (m0, inl (action, args, BSeq b (SWhile cond body))) = Some r)
           ) \/ (
             exists l0, r0 = inr l0 /\
             interp_stmt f' m0 l0 (SWhile cond body) = Some r
           )
        ) \/ (
          mword_nonzero v = false /\
          Some (m, inr l) = Some r
        ) )
      ) \/ (
        exists s1 s2, s = SSeq s1 s2 /\
        exists m0 r0, interp_stmt f' m l s1 = Some (m0, r0) /\ (
        (
          exists action args b, r0 = inl (action, args, b) /\
          Some (m0, inl (action, args, BSeq b s2)) = Some r
        ) \/ (
          exists l0, r0 = inr l0 /\
          interp_stmt f' m0 l0 s2 = Some r
        ) )
    ) \/ (
        s = SSkip
        /\ Some (m, inr l) = Some r
    ) \/ (
        exists binds fname args, s = SCall binds fname args /\
        exists params rets fbody, lookupFunction fname = Some (params, rets, fbody) /\
        exists argvs, Common.option_all (List.map (interp_expr l) args) = Some argvs /\
        exists l0, Common.putmany params argvs Map.empty_map = Some l0 /\
        exists m' r0, interp_stmt f' m l0 fbody = Some (m', r0) /\ (
        (
          exists action args0 b, r0 = inl (action, args0, b) /\
          Some (m', inl (action, args0, BStack l b binds rets)) = Some r
        ) \/ (
          exists l1, inr l1 = r0 /\
            exists retvs, Common.option_all (List.map (Map.get l1) rets) = Some retvs /\
            exists l', Common.putmany binds retvs l = Some l' /\
            Some (m', inr l') = Some r
        ) )
    ) \/ (
        exists binds action args, s = SIO binds action args /\
        exists argvs, Common.option_all (List.map (interp_expr l) args) = Some argvs /\
        Some (m, inl (action, argvs, BWait l binds)) = Some r
    ) ) ).
  Proof.
    destruct f; cbn [interp_stmt].
    { split; intros; dsi. }
    destruct s; cbn [interp_stmt]; repeat setoid_rewrite invert_bind_Some.
    { split; dsi; try solve [intuition (dsi; eauto 50)]. }
    { split; dsi; try solve [intuition (dsi; eauto 50)]. }
    { split; dsi; try solve [intuition (dsi; eauto 50)]. }
    { split; dsi; try solve [intuition (dsi; eauto 50)]. }
    { split; dsi.
      { destruct (mword_nonzero x) eqn:?; dsi.
        destruct (interp_stmt f m l s) as [[?[[[? ?]?]|?]]|] eqn:?;
          solve [intuition (dsi; eauto 50)].
        solve [intuition (dsi; eauto 50)]. }
      {
        intuition dsi.
        eexists. eexists. eauto.
        destruct H1 as [[Hb HC]|[Hb HC]]; rewrite Hb; dsi; [|solve[eauto]].
        destruct H as [[HC ?] ?|[? [HC ?]]]; dsi; rewrite ?HC; eauto.
        rewrite HC.
        rewrite H. eauto.

        try solve [intuition (dsi; eauto 50)]. }
    { split; dsi; try solve [intuition (dsi; eauto 50)]. }
    *)
        


Require Import Coq.Program.Equality.
Module ht.
  Section HoareLogic.
    Goal True. let cls := constr:(ImpParameters) in match constr:(Set) with _ => (let none := constr:(_:cls) in idtac); fail 99 "DUPLICATE INSTANCE" | _ => idtac end. Abort.
    Context {p : ImpParameters} {E : ImpFunctions p} {W : ImpWorld p} (G : world -> mem -> Prop).
    (* TODO: allow G to guarantee stuff about arguments of external calls *)

    Lemma bind_Some_Some_iff {A B} (oa:option A) (f:A->option B) b :
      (bind_Some x <- oa; f x) = Some b <->
      (exists a, oa = Some a /\ f a = Some b).
    Proof. split; destruct oa eqn:?; dsi; eauto. Qed.

    Lemma step_alt_iff s s' : step s s' <-> step_alt s s'.
    Proof. split; inversion 1; dsi; econstructor; eauto 25. Qed.

    (* TODO: unused *)
    Lemma invert_interp_expr l e r :
      (interp_expr l e = Some r) <->
      ( (exists v, e = ELit v /\ Some v = Some r) \/
        (exists x, e = EVar x /\ Map.get l x = Some r) \/
        (exists op e1 e2, e = EOp op e1 e2 /\
                          exists r1, interp_expr l e1 = Some r1 /\
                                     exists r2, interp_expr l e2 = Some r2 /\
                                                Some (interp_binop op r1 r2) = Some r) ).
    Proof.
      destruct e;
        cbn [interp_expr]; repeat setoid_rewrite bind_Some_Some_iff;
          intuition (dsi; eauto 20).
    Qed.

    Lemma interp_stmt_monotonic {f1 m l c r} (Hinterp:interp_stmt f1 m l c = Some r) f2 (H:f1 <= f2)
      : interp_stmt f2 m l c = Some r.
    Proof.
      revert Hinterp; revert r; revert c; revert l; revert m; revert H; revert f2.
      induction f1; intros; [solve[inversion Hinterp]|].
      destruct f2; [lia|]. specialize (IHf1 f2 ltac:(lia)).
      destruct c; cbn in Hinterp |- * ;
      repeat match goal with
             | _ => progress dsi
             | _ => solve [eauto | congruence]
             | |- exists _, _ /\ _ => eexists; split; [solve[eauto]|cbn]
             | H: _ |- _ => setoid_rewrite bind_Some_Some_iff in H
             | _ => setoid_rewrite bind_Some_Some_iff
             | H: context[match ?x with _ => _ end] |- context[match ?x with _ => _ end] => destruct x eqn:?
             end.
    Qed.

    Lemma interp_cont_monotonic {f1 m l c r} (Hinterp:interp_cont f1 m l c = Some r) f2 (H:f1 <= f2)
      : interp_cont f2 m l c = Some r.
    Proof.
      revert Hinterp; revert r; revert c; revert l; revert m; revert H; revert f2.
      induction f1; intros; [solve[inversion Hinterp]|].
      destruct f2; [lia|]. specialize (IHf1 f2 ltac:(lia)).
      destruct c; cbn in Hinterp |- *;
      repeat match goal with
             | _ => progress dsi
             | _ => solve [eauto | congruence]
             | |- exists _, _ /\ _ => eexists; split; [solve[eauto]|cbn]
             | H: _ |- _ => setoid_rewrite bind_Some_Some_iff in H
             | _ => setoid_rewrite bind_Some_Some_iff
             | H: context[match ?x with _ => _ end] |- context[match ?x with _ => _ end] => destruct x eqn:?
             end.
      eapply interp_stmt_monotonic; eauto; lia.
      eapply interp_stmt_monotonic; eauto; lia.
    Qed.

    Lemma exec_stmt_unique {m l c r1 r2} (H1:exec_stmt m l c r1) (H2:exec_stmt m l c r2) : r1 = r2.
    Proof.
      inversion H1 as [f1 H1']; inversion H2 as [f2 H2']; destruct (Compare_dec.le_le_S_dec f1 f2).
      { pose proof interp_stmt_monotonic H1' f2 ltac:(lia); congruence. }
      { pose proof interp_stmt_monotonic H2' f1 ltac:(lia); congruence. }
    Qed.
    Lemma exec_cont_unique {m l c r1 r2} (H1:exec_cont m l c r1) (H2:exec_cont m l c r2) : r1 = r2.
      inversion H1 as [f1 H1']; inversion H2 as [f2 H2']; destruct (Compare_dec.le_le_S_dec f1 f2).
      { pose proof interp_cont_monotonic H1' f2 ltac:(lia); congruence. }
      { pose proof interp_cont_monotonic H2' f1 ltac:(lia); congruence. }
    Qed.

    Generalizable All Variables.
    Lemma exec_SSeq_1 `(H:exec_stmt m l c1 (blocked m0 a l0 b)) c2
      : exec_stmt m l (SSeq c1 c2) (blocked m0 a l0 (BSeq b c2)).
    Proof. inversion_clear H as [f H']. exists (S f). cbn. rewrite H'. exact eq_refl. Qed.
    Lemma exec_CSeq_1 `(H:exec_cont m l c1 (blocked m0 a l0 b)) c2
      : exec_cont m l (CSeq c1 c2) (blocked m0 a l0 (BSeq b c2)).
    Proof. inversion_clear H as [f H']. exists (S f). cbn. rewrite H'. exact eq_refl. Qed.
    Lemma exec_SSeq_2 `(H1:exec_stmt m l c1 (done m0 v)) `(H2 : exec_stmt m0 v c2 x)
      :  exec_stmt m l (SSeq c1 c2) x.
    Proof.
      inversion_clear H1 as [f1 H1']. inversion_clear H2 as [f2 H2'].
      exists (S (Nat.max f1 f2)); cbn.
      rewrite (interp_stmt_monotonic H1') by lia.
      rewrite (interp_stmt_monotonic H2') by lia.
      exact eq_refl.
    Qed.
    Lemma exec_CSeq_2 `(H1:exec_cont m l c1 (done m0 v)) `(H2 : exec_stmt m0 v c2 x)
      :  exec_cont m l (CSeq c1 c2) x.
    Proof.
      inversion_clear H1 as [f1 H1']. inversion_clear H2 as [f2 H2'].
      exists (S (Nat.max f1 f2)); cbn.
      rewrite (interp_cont_monotonic H1') by lia.
      rewrite (interp_stmt_monotonic H2') by lia.
      exact eq_refl.
    Qed.

    Inductive ht : (world -> mem -> varmap -> Prop) -> stmt -> (world -> mem -> varmap -> Prop) -> Prop :=
    | load (P:_->_->_->Prop) x e (_:forall w m l, P w m l -> exists a, interp_expr l e = Some a /\ exists v, load a m = Some v)
      : ht P (SLoad x e) (fun w m l => exists l', P w m l' /\ exists a, interp_expr l' e = Some a /\ exists v, load a m = Some v /\ l = Map.put l' x v)
    | store (P:_->_->_->Prop) ea ev (_:forall w m l, P w m l -> exists a, interp_expr l ea = Some a /\ exists v, interp_expr l ev = Some v /\ exists m', store a v m = Some m')
      : ht P (SStore ea ev) (fun w m l => exists l' m', P w m' l' /\ exists a, interp_expr l' ea = Some a /\ exists v, interp_expr l' ev = Some v /\ store a v m' = Some m)
    | set (P:_->_->_->Prop) x e (_:forall w m l, P w m l -> exists v, interp_expr l e = Some v)
      : ht P (SSet x e) (fun w m l => exists l', P w m l' /\ exists v, interp_expr l' e = Some v /\ l = Map.put l' x v)
    | while' V R (Hwf:@Coq.Init.Wf.well_founded V R) (P:_->_->_->Prop)
            I (_:forall w m l, P w m l -> exists v, I v w m l)
            e (_:forall v w m l, I v w m l -> exists b, interp_expr l e = Some b)
            c (_:forall v w_, ht (fun w m l => w = w_ /\ I v w m l /\ exists b, interp_expr l e = Some b /\ mword_nonzero b = true) c (fun w m l => exists v', I v' w m l /\ (w = w_ -> R v' v)))
      : ht P (SWhile e c) (fun w m l => exists v, I v w m l /\ exists b, interp_expr l e = Some b /\ mword_nonzero b = false)
    | If (P:world->mem->varmap->Prop) e cf ct Qf Qt (_:forall w m l, P w m l -> exists v, interp_expr l e = Some v)
         (_:ht (fun w m l => P w m l /\ exists b, interp_expr l e = Some b /\ mword_nonzero b = true) ct Qt)
         (_:ht (fun w m l => P w m l /\ exists b, interp_expr l e = Some b /\ mword_nonzero b = false) cf Qf)
      : ht P (SIf e ct cf) (fun w m l => Qt w m l \/ Qf w m l)
    | seq P c1 R (_:ht P c1 R) c2 Q (_:ht R c2 Q) : ht P (SSeq c1 c2) Q
    | skip P : ht P SSkip P
    | call (P:_->_->_->Prop) binds fname args
           params rets fbody
           (* TODO: constrain lengths of binds and args, instead of possibility of putmany in function postcondition *)
           (_ : forall w m l, P w m l ->
                              (lookupFunction fname = Some (params, rets, fbody) /\
                               exists argvs : list mword,
                               Common.option_all (List.map (interp_expr l) args) = Some argvs /\
                               forall l, exists l', Common.putmany params argvs l = Some l'))
           Q (_:ht (fun w m l => exists l_, P w m l_ /\
                                 exists argvs, Common.option_all (List.map (interp_expr l_) args) = Some argvs /\
                                 Common.putmany params argvs Map.empty_map = Some l )
                   fbody (fun w m l => Q w m l /\ exists retvs, Common.option_all (List.map (Map.get l) rets) = Some retvs /\ forall l_, exists l', Common.putmany binds retvs l_ = Some l'))
      : ht P
            (SCall binds fname args)
            (fun w m l =>
               exists w_ m_ l_, P w_ m_ l_ /\ 
               exists l', Q w m l' /\
               exists retvs, Common.option_all (List.map (Map.get l') rets) = Some retvs /\ Common.putmany binds retvs l_ = Some l)
    | io (P:_->_->_->Prop) binds action args
         (_:forall w m l, P w m l -> G w m /\
                          exists argvs, Common.option_all (List.map (interp_expr l) args) = Some argvs /\
                          forall m' retvs w', external_step w (m, action, argvs) (m', retvs) w' ->
                                              exists l', Common.putmany binds retvs l = Some l')
      : ht P (SIO binds action args) (fun w' m' l' =>  exists w m l argvs retvs,
               P w m l /\ Common.option_all (List.map (interp_expr l) args) = Some argvs /\
               external_step w (m, action, argvs) (m', retvs) w' /\
               Common.putmany binds retvs l = Some l')
    | weaken (P Q:_->_->_->Prop) c (_:ht P c Q)
             (P' Q':_->_->_->Prop) (_:forall w m l, P' w m l -> P w m l) (_:forall w m l, Q w m l -> Q' w m l)
      : ht P' c Q'
    .

    Inductive htc : (world -> mem -> varmap -> Prop) -> cont -> (world -> mem -> varmap -> Prop) -> Prop :=
    | cskip P : htc P CSkip P
    | cseq P c1 R (_:htc P c1 R) c2 Q (_:ht R c2 Q) : htc P (CSeq c1 c2) Q
    | cstack P c' l' binds rets Q (_:htc (fun w m l => l = l' /\ exists l_, P w m l_) c' (fun w m l => Q w m l /\ exists retvs, Common.option_all (List.map (Map.get l) rets) = Some retvs /\ forall l_, exists l'', Common.putmany binds retvs l_ = Some l'')) 
      : htc P
            (CStack l' c' binds rets)
            (fun w m l =>
               exists w_ m_ l_, P w_ m_ l_ /\ 
               exists l', Q w m l' /\
               exists retvs, Common.option_all (List.map (Map.get l') rets) = Some retvs /\ Common.putmany binds retvs l_ = Some l)
    | cweaken (P Q:_->_->_->Prop) c (_:htc P c Q)
             (P' Q':_->_->_->Prop) (_:forall w m l, P' w m l -> P w m l) (_:forall w m l, Q w m l -> Q' w m l)
      : htc P' c Q'
    .

    Definition weaken_post P Q c H Q' pf := weaken P Q c H P Q' (fun _ _ _ p => p) pf.
    Definition weaken_pre P Q c P' pf H := weaken P Q c H P' Q pf (fun _ _ _ p => p).
    Definition assert P' P Q c pf H := weaken (fun w m l => P w m l /\ P' w m l) Q c H P Q (fun w m l p => conj p (pf w m l p)) (fun _ _ _ p => p).

    Section Instances.
      Import Coq.Classes.Morphisms.
      Global Instance Proper_ht_impl :
        Proper
          ((pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (Basics.flip Basics.impl))))
             ==> eq ==>
           (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl))) ==> Basics.impl)
          ht.
      Proof. cbv [Proper respectful pointwise_relation Basics.flip Basics.impl]; dsi; eauto using weaken. Qed.

      Global Instance Proper_ht_iff :
        Proper
          ((pointwise_relation _ (pointwise_relation _ (pointwise_relation _ iff)))
             ==> eq ==>
           (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ iff))) ==> iff)
          ht.
      Proof.
        cbv [Proper respectful pointwise_relation Basics.flip Basics.impl iff]; intros.
        split; intros; subst.
        { eapply weaken; intros.
          { eauto. }
          { eapply (proj2(H w m l) H0). }
          { eapply (proj1(H1 w m l) H0). } }
        { eapply weaken; intros.
          { eauto. }
          { eapply (proj1(H w m l) H0). }
          { eapply (proj2(H1 w m l) H0). } }
      Qed.
    End Instances.

    Definition while V R (Hwf:@Coq.Init.Wf.well_founded V R) (P:_->_->_->Prop)
            I (_:forall w m l, P w m l -> exists v, I v w m l)
            b (_:forall v w m l, I v w m l -> exists vb, interp_expr l b = Some vb)
            c (_:forall v w_, exists Q', ht (fun w m l => w = w_ /\ I v w m l /\ exists vb, interp_expr l b = Some vb /\ mword_nonzero vb = true) c Q' /\ forall w m l, Q' w m l -> exists v', I v' w m l /\ (w = w_ -> R v' v))
      : ht P (SWhile b c) (fun w m l => exists v, I v w m l /\ exists vb, interp_expr l b = Some vb /\ mword_nonzero vb = false).
    Proof.
      eapply weaken.
      { eapply while'; eauto.
        intros v w_. destruct (H1 v w_).
        eapply weaken; [eapply H2 | dsi; eauto..]. }
      { dsi; eauto. }
      { dsi; eauto. }
    Qed.
    
    Lemma ht_SSkip P Q (h : ht P SSkip Q) : forall w m l, P w m l -> Q w m l.
    Proof. dependent induction h; intros; (eauto || exfalso; eauto). Qed.

    Lemma htc_SSkip P Q (h : htc P CSkip Q) : forall w m l, P w m l -> Q w m l.
    Proof. dependent induction h; dsi; eauto. Qed.

    Definition invariant Q (s:world * computation_result) :=
      let (w, result) := s in
      match result with
      | blocked m action args bc
        => G w m /\ forall m' retvs w', external_step w (m, action, args) (m', retvs) w'
                                        -> exists l' c', bc retvs = Some (l', c') /\
                                                         htc (fun w_ m_ l_ => w_ = w' /\ m_ = m' /\ l_ = l') c' Q
      | done m l => Q w m l
      end.

    Lemma invariant_weaken (Q Q':_->_->_->Prop) (HQ: forall w m l, Q w m l -> Q' w m l) s (Hs:invariant Q s) : invariant Q' s.
    Proof with dsi.
      destruct s as [?[|]]; dsi; cbv [invariant] in *; eauto...
      progress intuition idtac; []...
      match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
      eauto using cweaken.
    Qed.
    
    Lemma preservation P c Q (h : ht P c Q) w m l (HP: P w m l) :
      exists r, exec_stmt m l c r /\ invariant Q (w, r).
    Proof with dsi.
      dependent induction h.
      { try match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        eexists.
        split. { exists (S O). cbn. repeat setoid_rewrite bind_Some_Some_iff. eauto 9. }
        cbn. eauto 9. }
      { try match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        eexists.
        split. { exists (S O). cbn. repeat setoid_rewrite bind_Some_Some_iff. eauto 9. }
        cbn. eauto 9. }
      { try match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        eexists.
        split. { exists (S O). cbn. repeat setoid_rewrite bind_Some_Some_iff. eauto 9. }
        cbn. eauto 9. }
      { try match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        clear HP; revert H3; revert l; revert m; revert w; revert x.
        refine (@Coq.Init.Wf.well_founded_ind V R ltac:(eassumption) _ _); intros.
        try match goal with H:_ |- _ => pose proof (H _ _ _ _ ltac:(eauto)) end...
        destruct (mword_nonzero x0) eqn:?.
        { edestruct H2; [solve[eauto]|]...
          destruct x1; dsi.
          { cbv [invariant] in H7...
            try match goal with H:_ |- _ => pose proof (H _ ltac:(eauto) _ _ _ ltac:(eauto)) end...
            inversion_clear H6 as [f1 exec1].
            inversion_clear H9 as [f2 exec2].
            exists x2.
            split; [|solve[eauto]].
            { exists (S (Nat.max f1 f2)); cbn.
              repeat (repeat setoid_rewrite bind_Some_Some_iff; eexists; split; [solve[eauto]|]; cbn; trivial).
              rewrite Heqb.
              rewrite (interp_stmt_monotonic exec1) by lia.
              rewrite (interp_stmt_monotonic exec2) by lia.
              reflexivity. } }
          { eexists ((blocked m0 a l0 (BSeq b (SWhile _ c)))).
            inversion_clear H6 as [f exec1].
            split.
            { exists (S f). cbn.
              repeat (repeat setoid_rewrite bind_Some_Some_iff; eexists; split; [solve[eauto]|]; cbn; trivial).
              rewrite Heqb, exec1. reflexivity. }
            cbn [invariant] in H7 |- *...
            progress (intuition idtac); []...
            match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
            eexists _, _.
            split.
            { cbv [BSeq]. match goal with H:_ |- _ => rewrite H; exact eq_refl end. }
            eapply cseq; eauto; [].
            eapply while'; eauto; dsi; eauto. } }
        { exists (done m l).
          split.
          { exists (S O). cbn.
            repeat (repeat setoid_rewrite bind_Some_Some_iff; eexists; split; [solve[eauto]|]; cbn; trivial).
            rewrite Heqb. reflexivity. }
          { cbn.
            repeat (repeat setoid_rewrite bind_Some_Some_iff; eexists; split; [solve[eauto]|]; cbn; trivial). } } }
      { try match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        destruct (mword_nonzero x) eqn:?Hx.
        { match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
          exists x0. destruct H1 as [f H1'].
          split.
          { exists (S f). cbn. repeat setoid_rewrite bind_Some_Some_iff.
            eexists. split. eauto. rewrite Hx. eauto. }
          eapply invariant_weaken; typeclasses eauto with core. }
        { match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
          exists x0. destruct H1 as [f H1'].
          split.
          { exists (S f). cbn. repeat setoid_rewrite bind_Some_Some_iff.
            eexists. split. eauto. rewrite Hx. eauto. }
          eapply invariant_weaken; typeclasses eauto with core. } }
      { match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        destruct x; dsi.
        { try match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
          eauto using exec_SSeq_2. }
        { exists (blocked m0 a l0 (BSeq b c2)).
          progress (intuition (eauto using exec_SSeq_1)); [].
          cbn in H0 |- *...
          progress (intuition idtac); []...
          match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
          eexists _, _.
          split.
          { cbv [BSeq]. match goal with H:_ |- _ => rewrite H; exact eq_refl end. }
          eauto using cseq. } }
      { try match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        eexists.
        split. { exists (S O). cbn. repeat setoid_rewrite bind_Some_Some_iff. eauto 9. }
        cbn. eauto 9. }
      { try match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        destruct (H2 Map.empty_map).
        try match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        destruct x1.
      { cbv [invariant] in *...
        destruct (H2 l) as [x' ?].
        destruct (H7 l).
        exists (done m0 x2).
        split.
        { inversion_clear H4 as [f H4']. exists (S f). cbn.
          repeat (repeat setoid_rewrite bind_Some_Some_iff; try (eexists; split; [solve[eauto]|]; cbn; trivial)). }
        { eauto 20. } }
        { exists (blocked m0 a l0 (BStack l b binds rets)).
          inversion_clear H4 as [f H4'].
          split. exists (S f).
          repeat (repeat setoid_rewrite bind_Some_Some_iff; try (eexists; split; [solve[eauto]|]; cbn; trivial)).
          cbn [invariant] in *.
          progress (intuition idtac); []...
          try match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
          eexists.
          eexists.
          split.
          { cbv [BStack].
            repeat (repeat setoid_rewrite bind_Some_Some_iff; eexists; split; [solve[eauto]|]; cbn; trivial). }
          { eapply cweaken with (P := fun (w_ : world) (m_ : mem) (l_ : varmap) => w_ = w' /\ m_ = m' /\ l_ = l); eauto.
            eapply cstack.
            { eapply cweaken.
              { eapply H8. }
              { dsi; subst. auto. }
              { intros. cbn in *; eauto 9. } }
            { cbn; dsi; subst; eauto 15. } } } }
      { try match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        eexists.
        split. { exists (S O). cbn. repeat setoid_rewrite bind_Some_Some_iff. eauto 9. }
        cbn.
        intros.
        progress (intuition idtac); []...
        match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        eexists _, _.
        cbv [BWait].
        unshelve (idtac; let e := open_constr:(_) in split; [apply e|pose proof e]).
        { match goal with H:_ |- _ => rewrite H; reflexivity end. }
        eapply cweaken with (P := fun w_ m_ l_ => w_ = w' /\ m_ = m' /\ l_ = x0).
        { econstructor. }
        { eauto. }
        cbn; dsi; subst; eauto 9. }
      { match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        pose proof invariant_weaken; typeclasses eauto with core. }
    Qed.

    Lemma cpreservation P c Q (h : htc P c Q) w m l (HP: P w m l) :
      exists r, exec_cont m l c r /\ invariant Q (w, r).
    Proof with dsi.
      dependent induction h.
      { eexists.
        unshelve (idtac; let e := open_constr:(_) in split; [apply e|pose proof e]).
        { exists (S (S O)). cbn. reflexivity. }
        cbn; eauto. }
      { match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        destruct x.
        { pose proof preservation _ _ _ H _ _ _ H1...
          eauto using exec_CSeq_2. }
        { exists (blocked m0 a l0 (BSeq b c2)).
          progress (intuition (eauto using exec_CSeq_1)); [].
          cbn in H1 |- *...
          progress (intuition idtac); []...
          match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
          eexists _, _.
          split.
          { cbv [BSeq]. match goal with H:_ |- _ => rewrite H; exact eq_refl end. }
          eauto using cseq. } }
      { match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        destruct x.
        { cbv [invariant] in *...
          destruct (H2 l) as [x' ?].
          exists (done m0 x').
          split.
          { inversion_clear H as [f H']. exists (S f). cbn. rewrite H', H1, H3. exact eq_refl. }
          eauto 20. }
        { exists (blocked m0 a l0 (BStack l b binds rets)).
        split.
        { inversion_clear H as [f H']. exists (S f). cbn. rewrite H'. exact eq_refl. }
        cbn in H0 |- *...
        progress (intuition idtac); []...
        match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        eexists _, _.
        split.
        { cbv [BStack]. match goal with H:_ |- _ => rewrite H; reflexivity end. }
        eapply cweaken with (P := fun (w_ : world) (m_ : mem) (l_ : varmap) => w_ = w' /\ m_ = m' /\ l_ = l); eauto.
        eapply cstack.
        { eapply cweaken.
          { eapply H4. }
          { dsi; subst. auto. }
          { intros. cbn in H5. eauto. } }
        { cbn; dsi; subst; eauto 15. } } }
      { match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        pose proof invariant_weaken; typeclasses eauto with core. }
    Qed.

    Lemma invariant_step Q s (HI:invariant Q s) s' (Hstep:step s s') : invariant Q s'.
    Proof with dsi.
      inversion Hstep; cbv [invariant] in * |- ; destruct s...
      match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
      pose proof (cpreservation _ _ _ ltac:(eauto) _ _ _ ltac:(repeat constructor))...
      specialize (H0 ltac:(eauto)); cbn in H1...
      cbv beta in *; dsi.
      assert ((x, x0) = (x2, x3)) by congruence...
      match goal with H:_, G:_ |- _ => pose proof exec_cont_unique H G; clear G end...
      subst. eauto. 
     Qed.

    Lemma invariant_guarantees (Q:_->_->_->Prop) (HQ:forall w m l, Q w m l -> G w m) s (HI:invariant Q s) :
      match s with (w, blocked m _ _ _) | (w, done m _) => G w m end.
    Proof. cbv [invariant] in *; destruct s as [?[|]]; dsi; cbn; eauto. Qed.
    
    Lemma invariant_done (Q:_->_->_->Prop) (HQ:forall w m l, Q w m l -> G w m) w m l (HI:invariant Q (w, (done m l))) : Q w m l.
    Proof. assumption. Qed.
  End HoareLogic.

  Module pure.
    Section pure.
      Context {p : ImpParameters} {E : ImpFunctions p}.
      Definition ht := fun (P:mem -> varmap -> Prop) c (Q:mem -> varmap -> Prop)
                       => (forall W G w,
                              ht (W:=W) G
                                 (fun w0 m l => w0 = w /\ P m l)
                                 c
                                 (fun w1 m l => w1 = w /\ Q m l)
                          ).


      Definition soundness P c Q (Hht:ht P c Q) m l (HP:P m l)
        : exists m' l', exec_stmt m l c (done m' l') /\ Q m' l'.
      Proof.
        destruct (ht.preservation _ _ _ _ (Hht {| world := unit; external_step := (fun _ _ _ _ => True) |} (fun _ _ => False) tt) tt m l (conj eq_refl HP)) as [[] [? inv]]; dsi;
          cbn [invariant external_step] in inv; dsi; [ eauto | contradiction ].
      Qed.
    End pure.
  End pure.

  Module Notations.
    Notation "{{ P }} c [ G ] {{ Q }}" := (ht G P c Q)
      (at level 90, c at next level,
      format "{{ P }} '//'   c '//' [ G ] '//' {{ Q }}").
    Notation "[ P ] c [ Q ]" := (pure.ht P c Q)
      (at level 90, c at next level,
      format "[ P ] '//'   c '//' [ Q ]").
  End Notations.

  Section _test_pure.
    Import Notations.
    Context {p : ImpParameters} {E : ImpFunctions p}.
    Goal forall P, [P] (SSeq (SSeq SSkip SSkip) (SSeq SSkip (SSeq SSkip SSkip))) [P].
    Proof.
      repeat econstructor.
    Qed.

    Context (_1 : mword) (one_nonzero : mword_nonzero _1 = true).
    Goal forall a,
        [fun _ _ => True]
          SSeq (SSet a (ELit _1))
          (SIf (EVar a) (
            SSkip
          ) (
            SWhile (ELit _1) SSkip)
          )
        [fun m l => Map.get l a = Some _1].
    Proof.
      intros; intros ???.
      eapply weaken_post.
      { econstructor. econstructor.
        { cbn; dsi. eauto 20 using Map.get_put_same. }
        econstructor.
        { cbn; dsi. eauto 20 using Map.get_put_same. }
        { econstructor. }
        { eapply while' with (I := fun _ _ _ _ => False).
          { eapply PeanoNat.Nat.lt_wf_0. }
          { cbn; dsi. rewrite Map.get_put_same in H0; dsi. congruence. }
          { cbn; dsi. eauto 20 using Map.get_put_same. }
          intros.
          eapply weaken with (P := fun _ _ _ => False).
          econstructor.
          { intros; dsi; contradiction. }
          { intros; dsi; contradiction. } } }
      { dsi; cbn in *.
        destruct H; dsi; [|contradiction].
        eauto 20 using Map.get_put_same. }
    Qed.
  End _test_pure.

  Section _test_max.
    Import Notations.
    Context {p : ImpParameters} {E : ImpFunctions p}.
    Local Existing Instance IMPLTS.

    Lemma well_founded_False T : well_founded (fun _ _ : T => False).
    Proof. constructor. contradiction. Qed.
        
    Context (_0 : mword) (zero_zero : mword_nonzero _0 = false).
    Context (_1 : mword) (one_nonzero : mword_nonzero _1 = true).
    Context (wgt : bopname).

    Context (recv send : actname) (recv_neq_send : recv <> send).
    Context (recv_returns_1 : forall w m o m' w',
                lts_external_step w (m, recv, nil) (m', o) w' -> exists v, o = cons v nil).

    Print label.
    Definition G :=
      fun (trace:list label) (_:mem) => forall init m args m' rets tail,
          trace = (init ++ ((m,send,args, (m', rets))::nil) ++ tail)%list ->
          exists v, args = (v::nil)%list /\
                    forall _init _m _args _m' v' _tail,
                      init = (_init ++ ((_m,recv,_args, (_m', v'::nil))::nil) ++ _tail)%list ->
                      mword_nonzero (interp_binop wgt v' v) = false.
    Goal forall (rax rbx : varname) (Hdiff:rax <> rbx),
      {{ fun w m _ => G w m }}
      SSeq (SSet rax (ELit _0)) (
      SWhile (ELit _1) (
        SSeq (SIO (cons rbx nil) recv nil) (
        SSeq (SIf (EOp wgt (EVar rbx) (EVar rax)) (
          SSet rax (EVar rbx)
        ) SSkip) (
        SIO nil send (cons (EVar rbx) nil)
      ))))
      [ G ]
      {{ fun _ _ _ => False }}.
    Proof.
        intros.
        eapply weaken_post; [|shelve].
        econstructor. { econstructor. cbn. eauto. }
        eapply while with
            (I := fun _ w m l =>  G w m /\ exists v, Map.get l rax = Some v)
            (R := fun (_ _:unit) => False);
          try solve [cbn; dsi; subst; eauto using tt, _1, well_founded_False, Map.get_put_same];
          intros; eexists; split.
        { econstructor. { econstructor. dsi.
                          progress (intuition idtac); []...
                          eexists.
                          split. { cbn. eauto. }
                          intros.
                          cbv [IMPLTS external_step] in *.
                          eapply recv_returns_1 in H; dsi; subst.
                          eexists. reflexivity. }
          econstructor. { { econstructor. { dsi.
                            cbn. dsi.
                            destruct x3; [cbn in *; congruence|].
                            destruct x3; [|cbn in *; congruence].
                            cbn in H2; dsi.
                            repeat (setoid_rewrite bind_Some_Some_iff ||
                                    setoid_rewrite Map.get_put_same ||
                                    setoid_rewrite Map.get_put_diff; [|congruence..]).
                            eexists.
                            eexists.
                            split. { eauto. }
                            eexists.
                            split. { eauto. }
                            eauto.  }
                          econstructor. {  dsi.
                                           destruct x4; [cbn in *; congruence|].
                                           destruct x4; [|cbn in *; congruence].
                                           cbn in H4; dsi.
                                           repeat (setoid_rewrite bind_Some_Some_iff ||
                                                   setoid_rewrite Map.get_put_same ||
                                                   setoid_rewrite Map.get_put_diff; [|congruence..]).
                                           eauto. }
                          econstructor. } }
          econstructor. { dsi.
                          destruct H; dsi.
                          { cbv [external_step IMPLTS lts_external_step] in H5; rewrite H5 in *.
                            split.
                            { cbv [G] in *; intros; destruct init.
                              { rewrite List.app_nil_l in H; cbn in H; dsi; contradiction. }
                              { rewrite <-List.app_comm_cons in H; cbn in H; dsi.
                                specialize (H7 init m0 args m' rets tail ltac:(eauto)); dsi.
                                eexists. split. eauto.
                                dsi.
                                destruct _init; dsi.
                                { rewrite List.app_nil_l in H5; cbn in H5; dsi.
                                  admit.
                                }
                                { rewrite <-List.app_comm_cons in H5; dsi.
                                  eapply H1.
                                  f_equal.
                                  rewrite <-List.app_comm_cons; cbn.
                                  reflexivity. } } }
                            repeat setoid_rewrite bind_Some_Some_iff. dsi. subst l.
                            cbn in H0.
                            eexists.
                            split.
                            { eexists.
                              cbn.
                              split. { rewrite Map.get_put_diff by congruence. eauto using Map.get_put_same. }
                              reflexivity. }
                            { dsi.
                              cbn in H.
                          
                              admit. } }
                          admit. } }
        { cbv beta; dsi; exists tt.
          destruct H; dsi.
          { destruct x3; [|solve[inversion H2]]; cbn in H2; dsi.
            repeat split. { admit. }
            { eauto using Map.get_put_same. }
            cbv [external_step IMPLTS lts_external_step] in H1; rewrite H1; clear H1.
            cbv [external_step IMPLTS lts_external_step] in H8; rewrite H8; clear H8.
            match goal with |- (?a :: ?b :: ?x = ?x)%list -> False => admit end. }
          { destruct x3; [|solve[inversion H2]]; cbn in H2; dsi.
            cbn in H3. repeat setoid_rewrite bind_Some_Some_iff in H3. dsi.
            repeat split. { admit. }
            { eauto. }
            cbv [external_step IMPLTS lts_external_step] in H1; rewrite H1; clear H1.
            cbv [external_step IMPLTS lts_external_step] in H6; rewrite H6; clear H6.
            match goal with |- (?a :: ?b :: ?x = ?x)%list -> False => admit end. } }

        Unshelve.
        cbn; dsi; congruence.
    Admitted.
  End _test_max.
End ht.