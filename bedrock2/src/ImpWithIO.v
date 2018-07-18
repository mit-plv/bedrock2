Require compiler.util.Common.

Notation "'subst!' y 'for' x 'in' f" := (match y with x => f end) (at level 10).

Local Notation "'bind_Some' x <- a | y ; f" :=
  (match a with
   | Some x => f
   | _ => y
   end)
    (right associativity, at level 60, x pattern).

Local Notation "'bind_Some' x <- a ; f" :=
  (match a with
   | Some x => f
   | _ => None
   end)
    (right associativity, at level 60, x pattern).

Local Notation "'bind_S' x <- a | y ; f" :=
  (match a with
   | S x => f
   | _ => y
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

  Fixpoint interp_expr (l:varmap) (e:expr) : option mword :=
    match e with
    | ELit v => Some v
    | EVar x => Map.get l x
    | EOp op e1 e2 =>
      bind_Some v1 <- interp_expr l e1;
        bind_Some v2 <- interp_expr l e2;
        Some (interp_binop op v1 v2)
    end.

  Class ImpFunctions := { lookupFunction : funname -> option (list varname * list varname * stmt) }.
  Section WithFunctions.
    Context {F:ImpFunctions}.
    Definition trace := list ((mem * actname * list mword) * (mem * list mword)).
    Definition oracle := list (mem * list mword).
    Variant outcome :=
    | bad (_:trace)
    | running (_:trace)
    | done (_:oracle) (_:trace) (_:mem) (_:varmap).
    Definition trace_of (r:outcome) := match r with running t | done _ t _ _ | bad t => t end.
    Local Notation "'bind_done' x <- a ; f" :=
      (match a with
       | done m l i t => subst! (m, l, i, t) for x in f
       | _ => a
       end)
        (right associativity, at level 60, x pattern).

    Local Notation putmany := Common.putmany.
    Local Notation option_all := Common.option_all.

    Fixpoint interp_stmt(s: stmt)(o:oracle)(t:trace)(m: mem)(l: varmap)(f: nat): outcome :=
      bind_S f <- f                                                   | running t;
      match s with
      | SLoad x a =>
        bind_Some a <- interp_expr l a                                | bad t;
        bind_Some v <- load a m                                       | bad t;
        done o t m (Map.put l x v)
      | SStore a v =>
        bind_Some a <- interp_expr l a                                | bad t;
        bind_Some v <- interp_expr l v                                | bad t;
        bind_Some m <- store a v m                                    | bad t;
        done o t m l
      | SSet x e =>
        bind_Some v <- interp_expr l e                                | bad t;
        done o t m (Map.put l x v)
      | SIf cond bThen bElse =>
        bind_Some v <- interp_expr l cond                             | bad t;
        interp_stmt (if mword_nonzero v then bThen else bElse) o t m l f
      | SWhile cond body =>
        bind_Some v <- interp_expr l cond                             | bad t;
        if mword_nonzero v
        then
          bind_done (o, t, m, l) <- interp_stmt body o t m l f;
          interp_stmt (SWhile cond body) o t m l f
        else done o t m l
      | SSeq s1 s2 =>
        bind_done (o, t, m, l) <- interp_stmt s1 o t m l f;
        interp_stmt s2 o t m l f
      | SSkip => done o t m l
      | SCall binds fname arges =>
        bind_Some (params, retns, fbody) <- lookupFunction fname      | bad t;
        bind_Some args <- option_all (List.map (interp_expr l) arges) | bad t;
        bind_Some lf <- putmany params args Map.empty_map             | bad t;
        bind_done (o, t, m, lf)  <- interp_stmt fbody o t m lf f;
        bind_Some rets <- option_all (List.map (Map.get lf) retns)    | bad t;
        bind_Some l <- putmany binds rets l                           | bad t;
        done o t m l
      | SIO binds action arges =>
        bind_Some args <- option_all (List.map (interp_expr l) arges) | bad t;
        let output := (m, action, args) in
        let '(m, rets, o) := match o with cons(m,r)o=>(m,r,o) | _=>(m,nil,nil) end in
        let t := cons (output, (m, rets)) t in
        bind_Some l <- putmany binds rets l                           | bad t;
        done o t m l
      end.

    Section RelyGuarantee.
      Context (s : stmt) (oracle: oracle) (t: trace) (m: mem) (l: varmap)
              (R : trace -> Prop) (G : trace -> Prop) (Q : trace -> mem -> varmap -> Prop).
      Local Notation rely := (forall f, R (trace_of (interp_stmt s oracle t m l f))).
      Definition productive_guarantee := rely -> forall f,
        match interp_stmt s oracle t m l f with
        | bad _ => False
        | running t1 => G t1 /\ exists df, interp_stmt s oracle t m l (df+f) <> interp_stmt s oracle t m l f
        | done _ t m l => G t /\ Q t m l
        end.

      Definition partial_guarantee := rely -> forall f,
        match interp_stmt s oracle t m l f with
        | bad _ => False
        | running t => G t
        | done _ t m l => G t /\ Q t m l
        end.
      Definition terminates :=
        rely -> exists f o' t' m' l', interp_stmt s oracle t m l f = done o' t' m' l'.
      Definition terminating_guarantee := partial_guarantee /\ terminates.
      Lemma terminating_productive : terminating_guarantee -> productive_guarantee.
        cbv [terminates partial_guarantee productive_guarantee].
        intros [HP Hterm] Hrely frunning.
        specialize (HP Hrely). specialize (Hterm Hrely).
        destruct Hterm as [fdone [o' [t' [m' [l' H]]]]].
        specialize (HP frunning).
        destruct (interp_stmt s oracle t m l frunning) eqn:Heq; intuition idtac.
        assert (Hdf : exists df, fdone = df + frunning) by admit; destruct Hdf as [df ?]; subst fdone.
        exists df. rewrite H. congruence.
      Admitted.
      Lemma productive_partial : productive_guarantee -> partial_guarantee .
      Proof.
        cbv [partial_guarantee productive_guarantee].
        intros Hpartial Hrely f. specialize (Hpartial Hrely f).
        destruct (interp_stmt s oracle t m l f); intuition idtac.
      Qed.
    End RelyGuarantee.
    Definition perpetual_guarantee s o t m l R G := productive_guarantee s o t m l R G (fun _ _ _ => False).
    Lemma not_terminates_perpetual s o t m l R G (H:perpetual_guarantee s o t m l R G)
          (Hrely : forall f, R (trace_of (interp_stmt s o t m l f))) : ~ terminates s o t m l R.
    Proof.
      cbv [perpetual_guarantee terminates partial_guarantee productive_guarantee] in *; intuition idtac.
      destruct H as [fdone [o' [t' [m' [l' H]]]]].
      specialize (H1 fdone). rewrite H in H1. intuition idtac.
    Qed.
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
  | x:?T |- _ => assert_succeeds (let h := head_of T in is_ind h); solve [destruct x]
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

Module wp.
  Section wp.
    Goal True. let cls := constr:(ImpParameters) in match constr:(Set) with _ => (let none := constr:(_:cls) in idtac); fail 99 "DUPLICATE INSTANCE" | _ => idtac end. Abort.
    Context {p : ImpParameters} {E : ImpFunctions p} {W : ImpWorld p} (G : world -> mem -> actname -> list mword -> Prop).

    Section FuelLemmas. (* TODO: move *)
      
    (* TODO move *)
    Lemma bind_Some_Some_iff {A B} (oa:option A) (f:A->option B) b :
      (bind_Some x <- oa; f x) = Some b <->
      (exists a, oa = Some a /\ f a = Some b).
    Proof. split; destruct oa eqn:?; dsi; eauto. Qed.

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
    End FuelLemmas.
    
    (* it is important the the assertion [a] is parsed before shadowing [x] *)
    Local Notation "'bind_ex' x <- a ; f" :=
      (subst! a for a' in exists x, a' x /\ f)
        (only parsing, right associativity, at level 60, f at level 200).

    Local Notation "'bind_ex_Some' x <- a ; f" :=
      (subst! a for a' in exists x, a' = Some x /\ f)
        (only parsing, right associativity, at level 60, f at level 200).

    Local Notation "'bind_eq' x <- a ; f" :=
      (subst! a for a' in forall x, x = a' -> f)
        (only parsing, right associativity, at level 60, f at level 200).

    (* the postcondition could be [mword -> Prop], the argument [v] encodes [_ = v] *)
    (* the return type could be [varmap -> Prop], the argument [l] is bound directly instead *)
    Fixpoint wp_expr (l:varmap) (e:expr) (v : mword) : Prop :=
      match e with
      | ELit v' => v' = v
      | EVar x => bind_ex_Some v' <- Map.get l x; v' = v
      | EOp op e1 e2 =>
        bind_ex_Some v1 <- interp_expr l e1;
          bind_ex_Some v2 <- interp_expr l e2;
          interp_binop op v1 v2 = v
      end.

    Lemma wp_expr_sound l e v : wp_expr l e v -> interp_expr l e = Some v.
    Proof.
      revert v; induction e; cbn [interp_expr]; intros ? H; inversion H; dsi; eauto; [].
      match goal with H0:_, H1:_, H2:_ |- _ =>  rewrite H0, H1, H2; reflexivity end.
    Qed.

    Lemma wp_expr_complete l e v : interp_expr l e = Some v -> wp_expr l e v.
    Proof.
      revert v; induction e; cbn [wp_expr interp_expr]; intros ? H; inversion H; dsi; eauto; [].
      match goal with H: context[bind_Some _ <- ?x ; _] |- _ => destruct x eqn:?; dsi; [] end.
      match goal with H: context[bind_Some _ <- ?x ; _] |- _ => destruct x eqn:?; dsi; [] end.
      eauto.
    Qed.

    (* the postcondition could be [list T -> Prop], the argument [xs] encodes [_ = xs] *)
    (* the return type could be [list T -> Prop], the arguments [xs] is bound directly instead. *)
    (* this definition relies on [oxs] having computational list structure *)
    Fixpoint wp_option_all {T} (oxs : list (option T)) (xs:list T) {struct oxs} : Prop :=
      match oxs with
      | nil => xs = nil
      | cons ox oxs' =>
        bind_ex_Some x <- ox;
          exists xs', xs = cons x xs' /\
                      wp_option_all oxs' xs'
      end.

    Lemma wp_option_all_sound {T} oxs xs : @wp_option_all T oxs xs -> Common.option_all oxs = Some xs.
    Proof.
      revert xs; induction oxs; cbn [wp_option_all Common.option_all]; dsi; subst; eauto; [].
      erewrite IHoxs; eauto.
    Qed.

    Fixpoint wp_list_map {A B} (wp1: A -> B -> Prop) (xs : list A) (ys : list B) {struct xs} : Prop :=
      match xs with
      | nil => ys = nil
      | cons x xs' =>
        bind_ex y <- wp1 x;
          exists ys', ys = cons y ys' /\
                      wp_list_map wp1 xs' ys'
      end.

    Lemma wp_list_map_sound {A B} {f} {wp1:A->B->Prop} (Hwp1 : forall x y, wp1 x y -> f x = Some y) xs ys : wp_list_map wp1 xs ys -> Common.option_all (List.map f xs) = Some ys.
    Proof.
      revert ys; induction xs; cbn [wp_list_map Common.option_all List.map]; dsi; subst; eauto; [].
      rewrite (Hwp1 _ _ ltac:(eauto): _ = Some _).
      rewrite (IHxs _ (ltac:(eauto))).
      eauto.
    Qed.

    (* TODO: wp_putmany *)
    
    (* the return type could be [mem -> varmap -> Prop], the arguments [m] and [l] are bound directly instead *)
    Fixpoint wp (w: world) (m: mem) (l: varmap) (c: stmt) (post : world -> mem -> varmap -> Prop) {struct c} : Prop :=
      match c with
      | SLoad x ea =>
        bind_ex a <- wp_expr l ea;
          bind_ex_Some v <- load a m;
          bind_eq l <- Map.put l x v;
          post w m l
      | SStore ea ev =>
          bind_ex a <- wp_expr l ea;
          bind_ex v <- wp_expr l ev;
          bind_ex_Some m <- store a v m;
          post w m l
      | SSet x ev =>
          bind_ex v <- wp_expr l ev;
          bind_eq l <- Map.put l x v;
          post w m l
      | SIf br ct cf =>
          bind_ex v <- wp_expr l br; (* path-blasting... :( *)
            (mword_nonzero v = true  -> wp w m l ct post) /\
            (mword_nonzero v = false -> wp w m l cf post)
      | SWhile e c =>
        exists (V:Type) (R:V->V->Prop) (I:V->world->mem->varmap->Prop), 
               Coq.Init.Wf.well_founded R /\
               (exists v, I v w m l) /\
               (forall v w m l, I v w m l ->
                  exists b, wp_expr l e b /\
                  (mword_nonzero b = true -> wp w m l c (fun w' m l => exists v', I v' w' m l /\ (w=w' -> R v' v))) /\
                  (mword_nonzero b = false -> post w m l))
      | SSeq c1 c2 => wp w m l c1 (fun w m l => wp w m l c2 post)
      | SCall binds fname arges =>
        bind_ex args <- wp_list_map (wp_expr l) arges;
        bind_ex_Some finfo <- lookupFunction fname;
        forall params retns cf, finfo = (params, retns, cf) ->
        bind_ex_Some lf <- Common.putmany params args Map.empty_map;
        (* the callee may be proven using wp or some other technique *)
        bind_ex r <- exec_stmt m lf cf;
        ( exists m lf, r = done m lf /\
          bind_ex rets <- wp_list_map (fun k v => Map.get lf k = Some v) retns;
          bind_ex_Some l2 <- Common.putmany binds rets l;
          post w m l2 )
      (* TODO: allow the callee to do i/o
        guarantees G w m lf cf (fun w m lf =>
          bind_ex rets <- wp_list_map (fun k v => Map.get lf k = Some v) retns;
           bind_ex_Some l <- Common.putmany binds rets l;
           post w m l)
         *)
      | SIO binds action arges =>
        bind_ex args <- wp_list_map (wp_expr l) arges;
          G w m action args /\
          forall w' m' rets, external_step w (m, action, args) (m', rets) w' ->
            bind_ex_Some l' <- Common.putmany binds rets l;
            post w' m' l'
      | SSkip => post w m l
      end.

    Fixpoint wpc (w: world) (m: mem) (l: varmap) (c: cont) (post : world -> mem -> varmap -> Prop) {struct c} : Prop :=
      match c with
      | CSkip => post w m l
      | CSeq c1 c2 => wpc w m l c1 (fun w m l => wp w m l c2 post)
      | CStack lf cf binds retns =>
        False
      (* TODO: allow the callee to do i/o
        cont_guarantees G w m lf cf (fun w m lf =>
          bind_ex rets <- wp_list_map (fun k v => Map.get lf k = Some v) retns;
          bind_ex_Some l <- Common.putmany binds rets l;
          post w m l)
       *)
      end.

    Definition invariant (post: world -> mem -> varmap -> Prop) '(w, r) :=
      match r with
      | done m l => post w m l
      | blocked m action args b
        => G w m action args /\
           forall w' m' rets, external_step w (m, action, args) (m', rets) w' ->
             bind_ex_Some l'c' <- b rets;
             forall l' c', l'c' = (l', c') ->
             wpc w' m' l' c' post
      end.

    Ltac t :=
      repeat match goal with
      | _ => progress dsi
      | _ => progress cbn beta iota
      | _ => unshelve erewrite wp_expr_sound by eassumption; []
      | _ => unshelve erewrite (wp_list_map_sound (wp_expr_sound _)) by eassumption; []
      | _ => unshelve erewrite (wp_list_map_sound (f:=(fun (k : varname) => Map.get _ k)) _) by eauto; [solve[eauto]|]
      | H: _ = Some _ |- _ => rewrite H
      | _ => unshelve erewrite (ltac:(eassumption): _ = Some _); []
      | _ => unshelve erewrite (ltac:(eassumption): _ = true); []
      | _ => unshelve erewrite (ltac:(eassumption): _ = false); []
      | _ => progress (erewrite (interp_stmt_monotonic) by (eassumption || lia))
      | _ => progress (erewrite (interp_cont_monotonic) by (eassumption || lia))
      | H: exec_stmt _ _ _ _ |- _ => destruct H
      | H: exec_cont _ _ _ _ |- _ => destruct H
      | H: forall a b c pf, _ |- _ => specialize (H _ _ _ ltac:(eauto using conj, eq_refl with nocore))
      | H: forall a b pf, _ |- _ => specialize (H _ _ ltac:(eauto using conj, eq_refl with nocore))
      | Ht: ?x = true -> _, Hf: ?x = false -> _ |- _ => let Hx := fresh "H" "x" in
        destruct x eqn:Hx; [ specialize (Ht eq_refl) | specialize (Hf eq_refl) ]
      | r:computation_result |- _ => destruct r
      end.

    Ltac s :=
      repeat match goal with
      | |- _ /\ _ => split; [solve[repeat (t;s)]|]
      | |- exists _, _ /\ _ => eexists; split; [solve[repeat (t;s)]|]
      | |- exec_stmt _ _ _ _ => eexists (S _); cbn [interp_stmt exec_stmt]
      | |- exec_cont _ _ _ _ => eexists (S _); cbn [interp_cont exec_cont]
      | _ => solve[typeclasses eauto with core]
      | _ => progress (cbv [invariant BWait BSeq BStack] in *)
      | _ => progress (cbn [wpc] in *)
      end.
      
    Lemma wp_weaken w m l c (post post':_->_->_->Prop) (Hwp: wp w m l c post)
          (Himpl:forall w m l, post w m l -> post' w m l) : wp w m l c post'.
    Proof.
      revert dependent post'; revert dependent post; revert l; revert m; revert w.
      induction c; cbn [wp]; dsi; eauto 8.
      { eexists _, _, _.
        split. eassumption.
        split. { eexists. eassumption. }
        intros.
        specialize (H1 _ _ _ _ ltac:(eauto)); dsi.
        eauto 20. (* FIXME: should be solved by repeat (t; s). *) }
      { eapply IHc1. eassumption. intros.
        eapply IHc2.  match goal with H:_ |- _ => eapply H end. eauto. }
      { repeat (t; s). eexists. split. eexists. typeclasses eauto with core. repeat (t; s). }
      { repeat (t; s). }
    Qed.

    Lemma wpc_weaken w m l c (post post':_->_->_->Prop) (Hwpc: wpc w m l c post) (Himpl:forall w m l, post w m l -> post' w m l)
      : wpc w m l c post'.
    Proof.
      revert dependent post'; revert dependent post; revert l; revert m; revert w.
      induction c; cbn [wpc]; dsi; eauto using wp_weaken.
      { eapply IHc. eassumption. dsi.
        eapply wp_weaken. match goal with H:_ |- _ => eapply H end. eauto. }
    Qed.

    Lemma preservation w m l c post : wp w m l c post ->  exists r, exec_stmt m l c r /\ invariant post (w, r).
    Proof.
      revert post; revert l; revert m; induction c; cbn [wp]; try solve [repeat (t; s)].

      { (* While *)
        intros ? ? ? [V [R [I [wfR [[v HI] Hbody]]]]]. dsi.
        revert dependent l; revert dependent m; revert v.
        refine (Coq.Init.Wf.well_founded_ind wfR _ _); intros v IHwf m l HI.
        destruct (Hbody _ _ _ _ ltac:(eauto)) as [b [Hcond [Htrue Hfalse]]].
        destruct (mword_nonzero b) eqn:Hbb; [specialize (Htrue eq_refl)|specialize(Hfalse eq_refl)]. (* loop continues? *)
        { specialize (IHc m l _ ltac:(eauto)).
          destruct IHc as [r [[f Hexec] Hr]].
          destruct r as [m' l'|]. (* did this iteration get done or blocked? *)
          { cbn [invariant] in Hr. destruct Hr as [v' [HI' Hv']].
            specialize (IHwf _ ltac:(eauto) _ _ ltac:(eauto)).
            destruct IHwf as [rr [[f' ?] ?]].
            eexists. split. {
              eexists (S (Nat.max f f')).
              cbn [interp_stmt].
              repeat (t; s). }
            { eauto. } }
          { repeat (t; s).
            eapply wpc_weaken; [eassumption|].
            cbn [wp]. dsi. exists V, R, I. repeat (t; s). } }
        { repeat (t;s). } }

      { (* SSeq *)
        repeat (t; s).
        { eexists. split. exists (S (Nat.max x0 x1)). cbn [interp_stmt]. all: repeat (t; s). }
        { eexists. split. exists (S (Nat.max x0 x1)). cbn [interp_stmt]. all: repeat (t; s). } }

      { (* SCall *)
        repeat (t; s).
        eexists. split. reflexivity.
        dsi. cbn. eauto. }

      Unshelve. all: exact Datatypes.O. (* putting 42 here makes qed not finish :( *)
    Qed.

    Lemma cpreservation w m l c post : wpc w m l c post ->  exists r, exec_cont m l c r /\ invariant post (w, r).
    Proof.
      revert post; revert l; revert m; induction c; cbn [wpc]; try solve [repeat (t; s)].
      { (* CSeq *)
        repeat (t; s); pose proof (preservation _ _ _ _ _ H1); repeat (t; s).
        { eexists. split. exists (S (Nat.max x0 x1)). cbn [interp_cont]. all: repeat (t; s). }
        { eexists. split. exists (S (Nat.max x0 x1)). cbn [interp_cont]. all: repeat (t; s). } }

      Unshelve. all: exact Datatypes.O.
    Qed.
  End wp.

  Module pure.
    Section pure.
      Context {p : ImpParameters} {E : ImpFunctions p}.
      Definition ht := fun (P:mem -> varmap -> Prop) c (Q:mem -> varmap -> Prop)
                       => (forall W G w m l, P m l -> wp (W:=W) G w m l c (fun w1 m l => w1 = w /\ Q m l)).

      Definition soundness P c Q (Hht:ht P c Q) m l (HP:P m l)
        : exists m' l', exec_stmt m l c (done m' l') /\ Q m' l'.
      Proof.
        cbv [ht] in *.
        specialize (Hht {| world := unit; external_step := (fun _ _ _ _ => True) |} (fun _ _ _ _ => False) tt m l HP).
        eapply wp.preservation in Hht.
        destruct Hht as [r Hht].
        cbv [invariant] in *.
        destruct r; dsi; [].
        eauto.
      Qed.
    End pure.
  End pure.

  Module Notations.
    (*
    Notation "{{ P }} c [ G ] {{ Q }}" := (ht G P c Q)
      (at level 90, c at next level,
      format "{{ P }} '//'   c '//' [ G ] '//' {{ Q }}").
    *)
    Notation "[ P ] c [ Q ]" := (pure.ht P c Q)
      (at level 90, c at next level,
      format "[ P ] '//'   c '//' [ Q ]").
  End Notations.

  Module _test.
  Section _test_pure.
    Import Notations.
    Context {p : ImpParameters} {E : ImpFunctions p}.
    Goal forall P, [P] (SSeq (SSeq SSkip SSkip) (SSeq SSkip (SSeq SSkip SSkip))) [P].
    Proof.
      intros.
      cbv [pure.ht wp].
      typeclasses eauto with core.
    Qed.

    (* TODO: missing cases *)
    Ltac wp1 :=
      match goal with
      | |- wp _ _ _ _ (SSet _ _ ) ?P =>
        let p := fresh in
        set (p := P);
        cbn [wp];
        subst p
      | |- wp _ _ _ _ (SIf _ ?c1 ?c2) ?P =>
        let p := fresh in let s1 := fresh in let s2 := fresh in
        set (p := P);      set (s1 := c2);   set (s2 := c2);
        cbn [wp];
        subst p;          subst s1;          subst s2
      | |- wp _ _ _ _ (SSeq ?c1 ?c2) ?P =>
        let p := fresh in let s1 := fresh in let s2 := fresh in
        set (p := P);      set (s1 := c2);   set (s2 := c2);
        cbn [wp];
        subst p;          subst s1;          subst s2
      end; cbv [wp_expr wp_option_all wp_list_map].

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
      cbv [pure.ht]; intros.
      repeat wp1.
      eexists. split. eauto. intros.
      repeat wp1.
      eexists. split. eexists. split. intros. subst. eauto using Map.get_put_same. eauto.
      split.
      { intros. split. eauto. subst. rewrite Map.get_put_same. eauto. }
      { intros. exfalso. congruence. }
    Qed.
  End _test_pure.

Require Import Coq.Program.Equality.
Module ht.
  Section HoareLogic.
    Goal True. let cls := constr:(ImpParameters) in match constr:(Set) with _ => (let none := constr:(_:cls) in idtac); fail 99 "DUPLICATE INSTANCE" | _ => idtac end. Abort.
    Context {p : ImpParameters} {E : ImpFunctions p} {W : ImpWorld p} (G : world -> mem -> Prop).
    (* TODO: allow G to guarantee stuff about arguments of external calls *)

    (* TODO: move *)
    Lemma invert_putmany_cons_l (x:varname) xs' (ys:list mword) m r
          (H:Common.putmany (x::xs') ys m = Some r)
      : exists y ys', Common.putmany (x::xs') (y::ys') m = Some r.
    Proof. destruct ys; cbn in H; dsi.
           cbn.
           (* TODO: report failure: setoid_rewrite H. *)
           eexists.
           eexists.
           rewrite H.
           reflexivity.
    Qed.

    Lemma step_alt_iff s s' : step s s' <-> step_alt s s'.
    Proof. split; inversion 1; dsi; econstructor; eauto 25. Qed.

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
          cbn [invariant external_step] in inv; dsi; eauto.
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
          { cbn; dsi. }
          intros.
          eapply weaken with (P := fun _ _ _ => False).
          econstructor.
          { intros; dsi; contradiction. }
          { intros; dsi; contradiction. } } }
      { dsi; cbn in *.
        destruct H; dsi; [].
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