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

  Definition cont : Type := list (varmap * list varname * list varname * stmt) * stmt.
  Definition CSkip : cont := (nil, SSkip).
  Definition CSeq (c1:cont) (c2: stmt) : cont := let (stack, c1) := c1 in (stack, SSeq c1 c2).
  Definition CStack (locals: varmap) (cf: cont) (binds rets: list varname) : cont :=
    let '(stack, c1) := cf in (cons (locals, binds, rets, c1) stack, SSkip).

  Definition blocked := list mword -> option (varmap * cont).
  Definition BWait (locals : varmap) (binders : list varname) : blocked :=
    fun values => bind_Some l' <- Common.putmany binders values locals; Some (l', CSkip).
  Definition BSeq (c1 : blocked) (c2 : stmt) :=
    fun values => bind_Some (l, c1) <- c1 values; Some (l, CSeq c1 c2).
  Definition BStack (caller_locals : varmap) (callee : blocked) (binds rets: list varname) : blocked :=
    fun values => bind_Some (callee_locals, c) <- callee values; Some (caller_locals, CStack callee_locals c binds rets).

  Fixpoint interp_expr (l:varmap) (e:expr) : option mword :=
    match e with
    | ELit v => Some v
    | EVar x => Map.get l x
    | EOp op e1 e2 =>
      bind_Some v1 <- interp_expr l e1;
        bind_Some v2 <- interp_expr l e2;
        Some (interp_binop op v1 v2)
    end.

  Definition computation_result : Type := mem * (actname * list mword * blocked + varmap).
  Section WithFunctions.
    Context (lookupFunction : funname -> option (list varname * list varname * stmt)).
    Fixpoint interp_stmt(f: nat)(m: mem)(l: varmap)(s: stmt): option computation_result :=
      match f with
      | 0 => None (* out of fuel *)
      | S f => match s with
        | SLoad x a =>
          bind_Some a <- interp_expr l a;
          bind_Some v <- load a m;
          Some (m, inr (Map.put l x v))
        | SStore a v =>
          bind_Some a <- interp_expr l a;
          bind_Some v <- interp_expr l v;
          bind_Some m <- store a v m;
          Some (m, inr l)
        | SSet x e =>
          bind_Some v <- interp_expr l e;
          Some (m, inr (Map.put l x v))
        | SIf cond bThen bElse =>
          bind_Some v <- interp_expr l cond;
          interp_stmt f m l (if mword_nonzero v then bThen else bElse)
        | SWhile cond body =>
          bind_Some v <- interp_expr l cond;
          if mword_nonzero v
          then
            bind_Some (m, ob) <- interp_stmt f m l body;
            match ob with
            | inl (action, args, b) => Some (m, inl (action, args, BSeq b (SWhile cond body)))
            | inr l => interp_stmt f m l (SWhile cond body)
            end
          else Some (m, inr l)
        | SSeq s1 s2 =>
          bind_Some (m, ob) <- interp_stmt f m l s1;
          match ob with
          | inl (action, args, b) => Some (m, inl (action, args, BSeq b s2))
          | inr l => interp_stmt f m l s2
          end
        | SSkip => Some (m, inr l)
        | SCall binds fname args =>
          bind_Some (params, rets, fbody) <- lookupFunction fname;
            bind_Some argvs <- Common.option_all (List.map (interp_expr l) args);
            bind_Some l0 <- Common.putmany params argvs Map.empty_map;
            bind_Some (m', ob) <- interp_stmt f m l0 fbody;
            match ob with
            | inl (action, args, b) => Some (m', inl (action, args, BStack l b binds rets))
            | inr l1 => 
              bind_Some retvs <- Common.option_all (List.map (Map.get l1) rets);
              bind_Some l' <- Common.putmany binds retvs l;
              Some (m', inr l')
            end
        | SIO binds ionum args =>
          bind_Some argvs <- Common.option_all (List.map (interp_expr l) args);
          Some (m, inl (ionum, argvs, BWait l binds))
        end
      end.
    Definition exec_stmt m l c r := exists f, interp_stmt f m l c = Some r.
    
    Fixpoint interp_cont(f: nat)(m: mem)(l: varmap)(c: cont): option computation_result :=
      match f with
      | 0 => None (* out of fuel *)
      | S f =>
        match c with
        | (nil, c) => interp_stmt f m l c
        | (cons (lf, binds, rets, cf) stack, c) =>
          bind_Some (m', ob) <- interp_cont f m lf (stack, cf);
          match ob with
          | inl (action, args, b) => Some (m', inl (action, args, BStack l b binds rets))
          | inr st1 => 
            bind_Some retvs <- Common.option_all (List.map (Map.get st1) rets);
            bind_Some l' <- Common.putmany binds retvs l;
            interp_stmt f m' l' c
          end
        end
      end.
    Definition exec_cont m l c r := exists f, interp_cont f m l c = Some r.

    (* If a predicate [P_x : forall b, Prop] identifies the return value of a partial function [f x],
       [arbitraryIfUndefined P_x] identifies the return value of [f x] when [f x] is defined and allows
       arbitrary return values otherwise. *)
    Definition arbitraryIfUndefined {T} (P : T -> Prop) (b:T) := (exists b', P b') -> P b.

    Section WithWorld.
      Context {world : Type} (external_step : world -> mem*actname*list mword -> mem*list mword -> world -> Prop).
      (* Definition done (s : world * computation_result) : Prop :=  exists w m l, s = (w, (m, inr l)). *)
      Definition step (s s' : world*computation_result) : Prop :=
        exists w m action argvs b, s = (w, (m, inl (action, argvs, b))) /\
        exists w' retvs m_, external_step w (m, action, argvs) (m_, retvs) w' /\
        exists l' c', b retvs = Some (l', c') /\
        exists m' R', arbitraryIfUndefined (exec_cont m_ l' c') (m', R') /\ s' = (w', (m', R')).
    End WithWorld.

    Section LabeledTransitionSystem.
      Definition label : Type := (mem*actname*list mword) * (mem*list mword).
      Definition trace := list label.
      Definition lts_external_step w i o w' : Prop := w' = @cons label (i, o) w.
      Definition lts_step := @step trace lts_external_step.
    End LabeledTransitionSystem.
  End WithFunctions.
End Imp.





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





Require Import Coq.Program.Equality.
Module ht.
  Section HoareLogic.
    Goal True. let cls := constr:(ImpParameters) in match constr:(Set) with _ => (let none := constr:(_:cls) in idtac); fail 99 "DUPLICATE INSTANCE" | _ => idtac end. Abort.
    Context {p : ImpParameters} (e : funname -> option (list varname * list varname * stmt)) {world : Type} (external_step : world -> mem*actname*list mword -> mem*list mword -> world -> Prop) (G : world -> mem -> Prop).

    Inductive ht : (world -> mem -> varmap -> Prop) -> stmt -> (world -> mem -> varmap -> Prop) -> Prop :=
    | set (P:_->_->_->Prop) x e (_:forall w m l, P w m l -> exists v, interp_expr l e = Some v)
      : ht P (SSet x e) (fun w m l => exists l', P w m l' /\ exists v, interp_expr l' e = Some v /\ l = Map.put l' x v)
    | skip P : ht P SSkip P
    | io (P:_->_->_->Prop) binds action args
         (_:forall w m l, P w m l ->
                          exists argvs, Common.option_all (List.map (interp_expr l) args) = Some argvs /\
                          forall m' retvs w', external_step w (m, action, argvs) (m', retvs) w' ->
                                              G w' m' /\ exists l', Common.putmany binds retvs l = Some l')
      : ht P (SIO binds action args) (fun w' m' l' =>  exists w m l argvs retvs,
               P w m l /\ Common.option_all (List.map (interp_expr l) args) = Some argvs /\
               external_step w (m, action, argvs) (m', retvs) w')
    .
    (* Notation "[ P ] c [ Q ]" := (ht P c Q) (at level 90, c at next level). *)

    Inductive htc : (world -> mem -> varmap -> Prop) -> cont -> (world -> mem -> varmap -> Prop) -> Prop :=
    | cskip P : htc P CSkip P
    | cseq P c1 R (_:htc P c1 R) c2 Q (_:ht R c2 Q) : htc P (CSeq c1 c2) Q
    | cweaken c (P Q P' Q':_->_->_->Prop) (_:htc P c Q) (_:forall w m l, P' w m l -> P w m l) (_:forall w m l, Q w m l -> Q' w m l) : htc P' c Q'
      .

    Lemma exec_cont_unique {m l c r1 r2} (_:exec_cont e m l c r1) (_:exec_cont e m l c r2) : r1 = r2.
    Admitted.

    Ltac t_step :=
      match goal with
      | _ => progress intros
      | x:?T |- _ =>
        assert_succeeds (let h := head_of T in is_ind h);
        destruct x; []; (* TODO: use dependent elimination and allow indexed inductives *)
        assert_fails (is_indexed_inductive T)
      | H: ?x = ?y |- _ =>
        let f := head_of x in
        let g := head_of y in
        is_constructor f; is_constructor g; inversion H;
        subst; (* FIXME: only subst equations generated by inversion *)
        clear H
      end.
    Ltac t := repeat t_step.
    
    Lemma ht_SSkip P Q (h : ht P SSkip Q) : forall w m l, P w m l -> Q w m l.
    Proof. dependent induction h; eauto. Qed.

    Lemma htc_SSkip P Q (h : htc P CSkip Q) : forall w m l, P w m l -> Q w m l.
    Proof. dependent induction h; cbv [cont CSeq CSkip CStack] in *; t; eauto. Qed.

    Definition invariant Q (s:world * computation_result) :=
      let (w, result) := s in
      match result with
      | (m, (inl (action, args, blocked)))
        => forall m' retvs w', external_step w (m, action, args) (m', retvs) w'
                               -> exists l' c', blocked retvs = Some (l', c') /\ G w' m' /\ htc (fun w_ m_ l_ => w_ = w' /\ m_ = m' /\ l_ = l') c' Q
      | (m, (inr l)) => Q w m l
      end.

    Lemma preservation P c Q (h : ht P c Q) w m l (HP: P w m l) :
      exists r, exec_stmt e m l c r /\ invariant Q (w, r).
    Proof with t.
      dependent induction h; cbn in *.

      { match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        eexists.
        split. { exists (S O). cbn. match goal with H:_ |- _ => rewrite H; reflexivity end. }
        cbn. eauto. }
      { eexists.
        split. { exists (S O). cbn. reflexivity. }
        cbn. eauto. }
      { match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        eexists.
        unshelve (idtac; let e := open_constr:(_) in split; [apply e|pose proof e]).
        { exists (S O). cbn. match goal with H:_ |- _ => rewrite H; reflexivity end. }
        cbn.
        intros.
        match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        eexists _, _.
        cbv [BWait].
        unshelve (idtac; let e := open_constr:(_) in split; [apply e|pose proof e]).
        { match goal with H:_ |- _ => rewrite H; reflexivity end. }
        intuition idtac.
        eapply cweaken with (P := fun w_ m_ l_ => w_ = w' /\ m_ = m' /\ l_ = x0).
        { econstructor. }
        { eauto. }
        cbn; intros.
        repeat match goal with
        | H:exists _, _ |- _ => destruct H
        | H:_ /\ _ |- _ => destruct H
        end.
        subst.
        eauto 9. }
    Qed.

    Lemma cpreservation P c Q (h : htc P c Q) w m l (HP: P w m l) :
      exists r, exec_cont e m l c r /\ invariant Q (w, r).
    Proof with t.
      dependent induction h.
      { eexists.
        unshelve (idtac; let e := open_constr:(_) in split; [apply e|pose proof e]).
        { exists (S (S O)). cbn. reflexivity. }
        cbn; eauto. }
      { match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        destruct x as [?[?|?]].
        { cbn in H1 |- *...
          exists ((m0, inl (a, l0, BSeq b c2))).
          split.
          { admit. }
          t.
          match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
          eexists _, _.
          split.
          { cbv [BSeq]. match goal with H:_ |- _ => rewrite H; reflexivity end. }
          intuition idtac.
          eauto using cseq. }
        { pose proof preservation _ _ _ H _ _ _ H1...
          exists x.
          split.
          { admit. }
          eauto. } }
      { match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end.
        cbv [computation_result] in *... destruct s...
        { eexists.
          split; [solve[eauto]|].
          cbn.
          intros.
          match goal with
          | H:_ |- _ => pose proof (H _ _ _ ltac:(eauto))
          end.
          repeat match goal with
                 | H:exists _, _ |- _ => destruct H
                 | H:_ /\ _ |- _ => destruct H
                 | H:_ * _ |- _ => destruct H
                 end.
          eexists _, _.
          split.
          eauto.
          split.
          eauto.
          eapply cweaken.
          eauto.
          eauto.
          eauto. }
        { eexists.
          split.
          eauto.
          cbn.
          eauto. } }
        Qed.

    Lemma invariant_step Q s (HI:invariant Q s) s' (Hstep:step e external_step s s') : invariant Q s'.
    Proof with t.
      cbv [step] in *; destruct s as [? [?[?|?]]]...
      match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
      assert (Some (x7, x8) = Some (x11, x12)) by congruence...
      pose proof (cpreservation _ _ _ H4 _ _ _ ltac:(repeat constructor))...
      specialize (H2 (ex_intro _ _ H5))...
      match goal with H:_, G:_ |- _ => pose proof exec_cont_unique H G; clear G end; subst...
      eauto. 
    Qed.