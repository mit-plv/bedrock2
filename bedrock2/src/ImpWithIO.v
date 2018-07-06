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

  Inductive cont :=
  | CSkip
  | CSeq (c1:cont) (c2: stmt)
  | CStack (locals: varmap) (cf: cont) (binds rets: list varname).

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
        | CSkip =>  interp_stmt f m l SSkip
        | CSeq c1 c2 =>
          bind_Some (m, ob) <- interp_cont f m l c1;
          match ob with
          | inl (action, args, b) => Some (m, inl (action, args, BSeq b c2))
          | inr l => interp_stmt f m l c2
          end
        | CStack lf cf binds rets =>
          bind_Some (m', ob) <- interp_cont f m lf cf;
          match ob with
          | inl (action, args, b) => Some (m', inl (action, args, BStack l b binds rets))
          | inr l1 => 
            bind_Some retvs <- Common.option_all (List.map (Map.get l1) rets);
            bind_Some l' <- Common.putmany binds retvs l;
            Some (m', inr l')
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




Require Import Coq.Program.Equality.
Module ht.
  Section HoareLogic.
    Goal True. let cls := constr:(ImpParameters) in match constr:(Set) with _ => (let none := constr:(_:cls) in idtac); fail 99 "DUPLICATE INSTANCE" | _ => idtac end. Abort.
    Context {p : ImpParameters} (e : funname -> option (list varname * list varname * stmt)) {world : Type} (external_step : world -> mem*actname*list mword -> mem*list mword -> world -> Prop) (G : world -> mem -> Prop).

    Ltac t_step :=
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
      end.
    Ltac t := repeat t_step.

    Lemma bind_Some_Some_iff {A B} (oa:option A) (f:A->option B) b :
      (bind_Some x <- oa; f x) = Some b <->
      (exists a, oa = Some a /\ f a = Some b).
    Proof. split; destruct oa eqn:?; subst; t; eauto. Qed.

    Lemma interp_stmt_monotonic {f1 m l c r} (Hinterp:interp_stmt e f1 m l c = Some r) f2 (H:f1 <= f2)
      : interp_stmt e f2 m l c = Some r.
    Proof.
      revert Hinterp; revert r; revert c; revert l; revert m; revert H; revert f2.
      induction f1; intros; [solve[inversion Hinterp]|].
      destruct f2; [lia|]. specialize (IHf1 f2 ltac:(lia)).
      destruct c; cbn in Hinterp |- * ;
      repeat match goal with
             | _ => progress t
             | _ => solve [eauto | congruence]
             | |- exists _, _ /\ _ => eexists; split; [solve[eauto]|cbn]
             | H: _ |- _ => setoid_rewrite bind_Some_Some_iff in H
             | _ => setoid_rewrite bind_Some_Some_iff
             | H: context[match ?x with _ => _ end] |- context[match ?x with _ => _ end] => destruct x eqn:?
             end.
    Qed.

    Lemma interp_cont_monotonic {f1 m l c r} (Hinterp:interp_cont e f1 m l c = Some r) f2 (H:f1 <= f2)
      : interp_cont e f2 m l c = Some r.
    Proof.
      revert Hinterp; revert r; revert c; revert l; revert m; revert H; revert f2.
      induction f1; intros; [solve[inversion Hinterp]|].
      destruct f2; [lia|]. specialize (IHf1 f2 ltac:(lia)).
      destruct c; cbn in Hinterp |- *;
      repeat match goal with
             | _ => progress t
             | _ => solve [eauto | congruence]
             | |- exists _, _ /\ _ => eexists; split; [solve[eauto]|cbn]
             | H: _ |- _ => setoid_rewrite bind_Some_Some_iff in H
             | _ => setoid_rewrite bind_Some_Some_iff
             | H: context[match ?x with _ => _ end] |- context[match ?x with _ => _ end] => destruct x eqn:?
             end.
      eapply interp_stmt_monotonic; eauto; lia.
      eapply interp_stmt_monotonic; eauto; lia.
    Qed.

    Lemma exec_stmt_unique {m l c r1 r2} (H1:exec_stmt e m l c r1) (H2:exec_stmt e m l c r2) : r1 = r2.
    Proof.
      inversion H1 as [f1 H1']; inversion H2 as [f2 H2']; destruct (Compare_dec.le_le_S_dec f1 f2).
      { pose proof interp_stmt_monotonic H1' f2 ltac:(lia); congruence. }
      { pose proof interp_stmt_monotonic H2' f1 ltac:(lia); congruence. }
    Qed.
    Lemma exec_cont_unique {m l c r1 r2} (H1:exec_cont e m l c r1) (H2:exec_cont e m l c r2) : r1 = r2.
      inversion H1 as [f1 H1']; inversion H2 as [f2 H2']; destruct (Compare_dec.le_le_S_dec f1 f2).
      { pose proof interp_cont_monotonic H1' f2 ltac:(lia); congruence. }
      { pose proof interp_cont_monotonic H2' f1 ltac:(lia); congruence. }
    Qed.

    Generalizable All Variables.
    Lemma exec_cont_SSeq_1 `(H:exec_cont e m l c1 (m0, inl (a, l0, b))) c2
      : exec_cont e m l (CSeq c1 c2) (m0, inl (a, l0, BSeq b c2)).
    Proof. inversion_clear H as [f H']. exists (S f). cbn. rewrite H'. exact eq_refl. Qed.

    Lemma exec_cont_SSeq_2 `(H1:exec_cont e m l c1 (m0, inr v)) `(H2 : exec_stmt e m0 v c2 x)
      :  exec_cont e m l (CSeq c1 c2) x.
    Proof.
      inversion_clear H1 as [f1 H1']. inversion_clear H2 as [f2 H2'].
      exists (S (Nat.max f1 f2)); cbn.
      rewrite (interp_cont_monotonic H1') by lia.
      rewrite (interp_stmt_monotonic H2') by lia.
      exact eq_refl.
    Qed.

    Inductive ht : (world -> mem -> varmap -> Prop) -> stmt -> (world -> mem -> varmap -> Prop) -> Prop :=
    | set (P:_->_->_->Prop) x e (_:forall w m l, P w m l -> exists v, interp_expr l e = Some v)
      : ht P (SSet x e) (fun w m l => exists l', P w m l' /\ exists v, interp_expr l' e = Some v /\ l = Map.put l' x v)
    | skip P : ht P SSkip P
    | io (P:_->_->_->Prop) binds action args
         (_:forall w m l, P w m l -> G w m /\
                          exists argvs, Common.option_all (List.map (interp_expr l) args) = Some argvs /\
                          forall m' retvs w', external_step w (m, action, argvs) (m', retvs) w' ->
                                              exists l', Common.putmany binds retvs l = Some l')
      : ht P (SIO binds action args) (fun w' m' l' =>  exists w m l argvs retvs,
               P w m l /\ Common.option_all (List.map (interp_expr l) args) = Some argvs /\
               external_step w (m, action, argvs) (m', retvs) w')
    .
    Notation "[ P ] c [ Q ]" := (ht P c Q) (at level 90, c at next level).

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
    | cweaken c (P Q P' Q':_->_->_->Prop) (_:htc P c Q) (_:forall w m l, P' w m l -> P w m l) (_:forall w m l, Q w m l -> Q' w m l) : htc P' c Q'
    .

    Lemma ht_SSkip P Q (h : ht P SSkip Q) : forall w m l, P w m l -> Q w m l.
    Proof. dependent induction h; eauto. Qed.

    Lemma htc_SSkip P Q (h : htc P CSkip Q) : forall w m l, P w m l -> Q w m l.
    Proof. dependent induction h; t; eauto. Qed.

    Definition invariant Q (s:world * computation_result) :=
      let (w, result) := s in
      match result with
      | (m, (inl (action, args, blocked)))
        => G w m /\ forall m' retvs w', external_step w (m, action, args) (m', retvs) w'
                                        -> exists l' c', blocked retvs = Some (l', c') /\
                                                         htc (fun w_ m_ l_ => w_ = w' /\ m_ = m' /\ l_ = l') c' Q
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
        progress (intuition idtac); []...
        match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        eexists _, _.
        cbv [BWait].
        unshelve (idtac; let e := open_constr:(_) in split; [apply e|pose proof e]).
        { match goal with H:_ |- _ => rewrite H; reflexivity end. }
        eapply cweaken with (P := fun w_ m_ l_ => w_ = w' /\ m_ = m' /\ l_ = x0).
        { econstructor. }
        { eauto. }
        cbn; t; subst; eauto 9. }
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
        destruct x as [?[?|?]]...
        { exists ((m0, inl (a, l0, BSeq b c2))).
          progress (intuition (eauto using exec_cont_SSeq_1)); [].
          cbn in H1 |- *...
          progress (intuition idtac); []...
          match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
          eexists _, _.
          split.
          { cbv [BSeq]. match goal with H:_ |- _ => rewrite H; exact eq_refl end. }
          eauto using cseq. }
        { pose proof preservation _ _ _ H _ _ _ H1...
          eauto using exec_cont_SSeq_2. } }
      { match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
        destruct x as [?[?|?]]...
        { exists (m0, inl (a, l0, BStack l b binds rets)).
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
          { t; subst. auto. }
          { intros. cbn in H5. eauto. } }
        { cbn; t; subst; eauto 15. } }
        { cbv [invariant] in *...
          destruct (H2 l) as [x' ?].
          exists (m0, inr x').
          split.
          { inversion_clear H as [f H']. exists (S f). cbn. rewrite H', H1, H3. exact eq_refl. }
          eauto 20. } }
      { match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end.
        cbv [computation_result] in *... destruct s...
        { eexists.
          progress (intuition eauto); [].
          cbv [invariant] in *...
        progress (intuition idtac); []...
          match goal with
          | H:_ |- _ => pose proof (H _ _ _ ltac:(eauto))
          end...
          eauto 9 using cweaken. }
        { eexists.
          progress (intuition eauto); [].
          cbv [invariant]...
          eauto. } }
    Qed.

    Lemma invariant_step Q s (HI:invariant Q s) s' (Hstep:step e external_step s s') : invariant Q s'.
    Proof with t.
      cbv [step invariant] in *; destruct s as [? [? [|]]]...
      match goal with H:_ |- _ => pose proof (H _ _ _ ltac:(eauto)) end...
      assert (Some (x7, x8) = Some (x11, x12)) by congruence...
      pose proof (cpreservation _ _ _ ltac:(eauto) _ _ _ ltac:(repeat constructor))...
      specialize (H2 (ex_intro _ _ H6))...
      match goal with H:_, G:_ |- _ => pose proof exec_cont_unique H G; clear G end; subst...
      eauto. 
    Qed.

    Lemma invariant_guarantees (Q:_->_->_->Prop) (HQ:forall w m l, Q w m l -> G w m) s (HI:invariant Q s) : G (fst s) (fst (snd s)).
    Proof. cbv [invariant] in *; destruct s as [? [? [|]]]; t; cbn; eauto. Qed.
  End HoareLogic.
End ht.