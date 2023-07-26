Require Import coqutil.Macros.subst coqutil.Macros.unique coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import Coq.ZArith.BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.dlet bedrock2.Syntax bedrock2.Semantics.

Section WeakestPrecondition.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Implicit Types (t : trace) (m : mem) (l : locals).

  Definition literal v (post : word -> Prop) : Prop :=
    dlet! v := word.of_Z v in post v.
  Definition get (l : locals) (x : String.string) (post : word -> Prop) : Prop :=
    exists v, map.get l x = Some v /\ post v.
  Definition load s m a (post : _ -> Prop) : Prop :=
    exists v, load s m a = Some v /\ post v.
  Definition store sz m a v post :=
    exists m', store sz m a v = Some m' /\ post m'.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).
    Definition expr_body rec (e : Syntax.expr) (post : word -> Prop) : Prop :=
      match e with
      | expr.literal v =>
        literal v post
      | expr.var x =>
        get l x post
      | expr.op op e1 e2 =>
        rec e1 (fun v1 =>
        rec e2 (fun v2 =>
        post (interp_binop op v1 v2)))
      | expr.load s e =>
        rec e (fun a =>
        load s m a post)
      | expr.inlinetable s t e =>
        rec e (fun a =>
        load s (map.of_list_word t) a post)
      | expr.ite c e1 e2 =>
        rec c (fun b => rec (if word.eqb b (word.of_Z 0) then e2 else e1) post)
    end.
    Fixpoint expr e := expr_body expr e.
  End WithMemAndLocals.

  Ltac t :=
    repeat match goal with
      | |- forall _, _ => progress intros
      | H: exists _, _ |- _ => destruct H
      | H: and _ _ |- _ => destruct H
      | H: eq _ ?y |- _ => subst y
      | _ => progress cbn in *
      end; eauto.

  Lemma expr_sound: forall m l e mc post (H : WeakestPrecondition.expr m l e post),
    exists v mc', Semantics.eval_expr m l e mc = Some (v, mc') /\ post v.
  Proof.
    induction e; t.
    { destruct H. destruct H. eexists. eexists. rewrite H. eauto. }
    { eapply IHe in H; t. cbv [WeakestPrecondition.load] in H0; t. rewrite H. rewrite H0. eauto. }
    { eapply IHe in H; t. cbv [WeakestPrecondition.load] in H0; t. rewrite H. rewrite H0. eauto. }
    { eapply IHe1 in H; t. eapply IHe2 in H0; t. rewrite H, H0; eauto. }
    { eapply IHe1 in H; t. rewrite H. Tactics.destruct_one_match.
      { eapply IHe3 in H0; t. }
      { eapply IHe2 in H0; t. } }
  Qed.

  Section WithF.
    Context {A B} (f: A -> (B -> Prop) -> Prop).
    Definition list_map_body rec (xs : list A) (post : list B -> Prop) : Prop :=
      match xs with
      | nil => post nil
      | cons x xs' =>
        f x (fun y =>
        rec xs' (fun ys' =>
        post (cons y ys')))
      end.
    Fixpoint list_map xs := list_map_body list_map xs.
  End WithF.

  Lemma exprs_sound : forall m l args mc P,
      list_map (expr m l) args P ->
      exists x mc', Semantics.evaluate_call_args_log m l args mc = Some (x, mc') /\ P x.
  Proof.
    induction args; cbn; repeat (subst; t).
    unfold Semantics.eval_expr in *.
    eapply expr_sound in H; t; rewrite H.
    eapply IHargs in H0; t; rewrite H0.
    eauto.
  Qed.

  Lemma getmany_sound: forall a l P,
      list_map (get l) a P -> exists vs, map.getmany_of_list l a = Some vs /\ P vs.
  Proof.
    cbv [map.getmany_of_list].
    induction a; cbn; repeat (subst; t).
    cbv [WeakestPrecondition.get] in H; t.
    epose proof (IHa _ _ H0); clear IHa; t.
    rewrite H. erewrite H1. eexists; split; eauto.
  Qed.

  Definition dexpr m l e v := expr m l e (eq v).
  Definition dexprs m l es vs := list_map (expr m l) es (eq vs).

  Section WithFunctionEnv.
    Context (e: env).

    Inductive cmd' (c : Syntax.cmd) (t : trace) (m : mem) (l : locals)
      (post : (trace -> mem -> locals -> Prop)) : Prop :=
    | mk_cmd' (_ : forall mc, exec e c t m l mc (fun t' m' l' mc' => post t' m' l')).

    Lemma invert_cmd': forall c t m l post,
        cmd' c t m l post ->
        forall mc, exec e c t m l mc (fun t' m' l' mc' => post t' m' l').
    Proof. intros. inversion H. apply H0. Qed.

    Definition func' '(innames, outnames, c) (t : trace) (m : mem) (args : list word)
      (post : trace -> mem -> list word -> Prop) :=
      exists l, map.of_list_zip innames args = Some l /\
      cmd' c t m l (fun t m l =>
        list_map (get l) outnames (fun rets =>
        post t m rets)).

    Definition call' (fname: String.string) :=
      match map.get e fname with
      | Some fimpl => func' fimpl
      | None => fun _ _ _ _ => False
      end.

    Implicit Type post : trace -> mem -> locals -> Prop.

    Ltac step :=
      match reverse goal with
      | H: _ /\ _ |- _ => destruct H
      | H: exists x, _ |- _ => let n := fresh x in destruct H as [n H]
      | |- _ => progress unfold dlet, dexpr, store in *
      | H: cmd' _ _ _ _ _ |- _ => pose proof (invert_cmd' _ _ _ _ _ H); clear H
      | |- _ => constructor
      | |- _ => assumption
      | H: forall _: MetricLogging.MetricLog, _ |- _ => apply H
      | |- _ => progress intros
      | |- _ => progress subst
      (* creates an evar for metrics, therefore needs to be applied from top to bottom,
         so we need `match reverse` instead of `match` *)
      | H: expr _ _ _ _ |- _ => eapply expr_sound in H
      | |- _ => solve [econstructor; eauto]
      end.
    Ltac tac := repeat step.

    Lemma wp_skip: forall t m l post, post t m l -> cmd' cmd.skip t m l post.
    Proof. tac. Qed.

    Lemma wp_set: forall x ev t m l post,
        (exists v, dexpr m l ev v /\
        dlet! l := map.put l x v in
        post t m l) ->
        cmd' (cmd.set x ev) t m l post.
    Proof. tac. Qed.

    Lemma wp_unset: forall x t m l post,
        (dlet! l := map.remove l x in
         post t m l) ->
        cmd' (cmd.unset x) t m l post.
    Proof. tac. Qed.

    Lemma wp_store: forall sz ea ev t m l post,
       (exists a, dexpr m l ea a /\
        exists v, dexpr m l ev v /\
        store sz m a v (fun m =>
        post t m l)) ->
       cmd' (cmd.store sz ea ev) t m l post.
    Proof. tac. Qed.

    Lemma wp_stackalloc: forall x n c t m l post,
        (Z.modulo n (bytes_per_word width) = 0 /\
        forall a mStack mCombined,
          anybytes a n mStack -> map.split mCombined m mStack ->
          dlet! l := map.put l x a in
          cmd' c t mCombined l (fun t' mCombined' l' =>
          exists m' mStack',
          anybytes a n mStack' /\ map.split mCombined' m' mStack' /\
          post t' m' l')) ->
          cmd' (cmd.stackalloc x n c) t m l post.
    Proof. tac. specialize H0 with (1 := H1) (2 := H2). tac. Qed.

    Lemma wp_cond: forall br ct cf t m l post,
        (exists v, dexpr m l br v /\
        (word.unsigned v <> 0%Z -> cmd' ct t m l post) /\
        (word.unsigned v = 0%Z -> cmd' cf t m l post)) ->
        cmd' (cmd.cond br ct cf) t m l post.
    Proof.
      tac. destr.destr (Z.eqb (word.unsigned v0) 0).
      - specialize H1 with (1 := E). tac.
      - specialize H0 with (1 := E). tac.
    Qed.

    Lemma wp_seq: forall c1 c2 t m l post,
        cmd' c1 t m l (fun t m l => cmd' c2 t m l post) ->
        cmd' (cmd.seq c1 c2) t m l post.
    Proof.
      tac. eapply exec.weaken.
      { econstructor. 1: eapply H0. tac. }
      tac.
    Qed.

    Lemma wp_while: forall e c t m l post,
       (exists measure (lt:measure->measure->Prop) (inv:measure->trace->mem->locals->Prop),
        Coq.Init.Wf.well_founded lt /\
        (exists v, inv v t m l) /\
        (forall v t m l, inv v t m l ->
          exists b, dexpr m l e b /\
          (word.unsigned b <> 0%Z -> cmd' c t m l (fun t' m l =>
            exists v', inv v' t' m l /\ lt v' v)) /\
          (word.unsigned b = 0%Z -> post t m l))) ->
       cmd' (cmd.while e c) t m l post.
    Proof.
      intros. destruct H as (measure & lt & inv & Hwf & HInit & Hbody).
      destruct HInit as (v0 & HInit).
      econstructor. intros.
      revert t m l mc HInit. pattern v0. revert v0.
      eapply (well_founded_ind Hwf). intros.
      specialize Hbody with (1 := HInit). destruct Hbody as (b & Hb & Ht & Hf).
      eapply expr_sound in Hb. destruct Hb as (b' & mc' & Hb & ?). subst b'.
      destr.destr (Z.eqb (word.unsigned b) 0).
      - specialize Hf with (1 := E). eapply exec.while_false; eassumption.
      - specialize Ht with (1 := E). inversion Ht. clear Ht.
        eapply exec.while_true; eauto.
        cbv beta. intros * (v' & HInv & HLt). eauto.
    Qed.

    Lemma wp_call{env_ok: map.ok env}: forall binds fname arges t m l post,
       (exists args, dexprs m l arges args /\
        call' fname t m args (fun t m rets =>
          exists l', map.putmany_of_list_zip binds rets l = Some l' /\
          post t m l')) ->
       cmd' (cmd.call binds fname arges) t m l post.
    Proof.
      tac.
      unfold dexprs in *.
      eapply exprs_sound in H. destruct H as (argvs & mc' & HEv & ?). subst argvs.
      unfold call' in *.
      Tactics.destruct_one_match_hyp. 2: contradiction.
      unfold func' in *.
      destruct p as ((argnames & retnames) & fbody).
      destruct H0 as (l1 & Hl1 & Hbody).
      inversion Hbody. clear Hbody. rename H into Hbody.
      eapply exec.call; eauto.
      cbv beta. intros. eapply getmany_sound. assumption.
    Qed.

    Lemma wp_interact: forall binds action arges t m l post,
       (exists args, dexprs m l arges args /\
        exists mKeep mGive, map.split m mKeep mGive /\
        ext_spec t mGive action args (fun mReceive rets =>
          exists l', map.putmany_of_list_zip binds rets l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (cons ((mGive, action, args), (mReceive, rets)) t) m' l')) ->
       cmd' (cmd.interact binds action arges) t m l post.
    Proof.
      tac.
      eapply exprs_sound in H. destruct H as (argvs & mc' & HEv & ?). subst argvs.
      tac.
    Qed.
  End WithFunctionEnv.

  Section WithFunctions.
    Context (call : String.string -> trace -> mem -> list word -> (trace -> mem -> list word -> Prop) -> Prop).
    Definition cmd_body (rec:_->_->_->_->_->Prop) (c : cmd) (t : trace) (m : mem) (l : locals)
             (post : trace -> mem -> locals -> Prop) : Prop :=
      (* give value of each pure expression when stating its subproof *)
      match c with
      | cmd.skip => post t m l
      | cmd.set x ev =>
        exists v, dexpr m l ev v /\
        dlet! l := map.put l x v in
        post t m l
      | cmd.unset x =>
        dlet! l := map.remove l x in
        post t m l
      | cmd.store sz ea ev =>
        exists a, dexpr m l ea a /\
        exists v, dexpr m l ev v /\
        store sz m a v (fun m =>
        post t m l)
      | cmd.stackalloc x n c =>
        Z.modulo n (bytes_per_word width) = 0 /\
        forall a mStack mCombined,
          anybytes a n mStack -> map.split mCombined m mStack ->
          dlet! l := map.put l x a in
          rec c t mCombined l (fun t' mCombined' l' =>
          exists m' mStack',
          anybytes a n mStack' /\ map.split mCombined' m' mStack' /\
          post t' m' l')
      | cmd.cond br ct cf =>
        exists v, dexpr m l br v /\
        (word.unsigned v <> 0%Z -> rec ct t m l post) /\
        (word.unsigned v = 0%Z -> rec cf t m l post)
      | cmd.seq c1 c2 =>
        rec c1 t m l (fun t m l => rec c2 t m l post)
      | cmd.while e c =>
        exists measure (lt:measure->measure->Prop) (inv:measure->trace->mem->locals->Prop),
        Coq.Init.Wf.well_founded lt /\
        (exists v, inv v t m l) /\
        (forall v t m l, inv v t m l ->
          exists b, dexpr m l e b /\
          (word.unsigned b <> 0%Z -> rec c t m l (fun t' m l =>
            exists v', inv v' t' m l /\ lt v' v)) /\
          (word.unsigned b = 0%Z -> post t m l))
      | cmd.call binds fname arges =>
        exists args, dexprs m l arges args /\
        call fname t m args (fun t m rets =>
          exists l', map.putmany_of_list_zip binds rets l = Some l' /\
          post t m l')
      | cmd.interact binds action arges =>
        exists args, dexprs m l arges args /\
        exists mKeep mGive, map.split m mKeep mGive /\
        ext_spec t mGive action args (fun mReceive rets =>
          exists l', map.putmany_of_list_zip binds rets l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (cons ((mGive, action, args), (mReceive, rets)) t) m' l')
      end.
    Fixpoint cmd c := cmd_body cmd c.
  End WithFunctions.

  Definition func call '(innames, outnames, c) (t : trace) (m : mem) (args : list word) (post : trace -> mem -> list word -> Prop) :=
      exists l, map.of_list_zip innames args = Some l /\
      cmd call c t m l (fun t m l =>
        list_map (get l) outnames (fun rets =>
        post t m rets)).

  Definition call_body rec (functions : list (String.string * (list String.string * list String.string * cmd.cmd)))
                (fname : String.string) (t : trace) (m : mem) (args : list word)
                (post : trace -> mem -> list word -> Prop) : Prop :=
    match functions with
    | nil => False
    | cons (f, decl) functions =>
      if String.eqb f fname
      then func (rec functions) decl t m args post
      else rec functions fname t m args post
    end.
  Fixpoint call functions := call_body call functions.

  Definition program funcs main t m l post : Prop := cmd (call funcs) main t m l post.
End WeakestPrecondition.

Ltac unfold1_cmd e :=
  lazymatch e with
    @cmd ?width ?BW ?word ?mem ?locals ?ext_spec ?CA ?c ?t ?m ?l ?post =>
    let c := eval hnf in c in
    constr:(@cmd_body width BW word mem locals ext_spec CA
                      (@cmd width BW word mem locals ext_spec CA) c t m l post)
  end.
Ltac unfold1_cmd_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_cmd G in
  change G.

Ltac unfold1_expr e :=
  lazymatch e with
    @expr ?width ?word ?mem ?locals ?m ?l ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@expr_body width word mem locals m l (@expr width word mem locals m l) arg post)
  end.
Ltac unfold1_expr_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_expr G in
  change G.

Ltac unfold1_list_map e :=
  lazymatch e with
    @list_map ?A ?B ?P ?arg ?post =>
    let arg := eval hnf in arg in
    constr:(@list_map_body A B P (@list_map A B P) arg post)
  end.
Ltac unfold1_list_map_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_list_map G in
  change G.

Ltac unfold1_call e :=
  lazymatch e with
    @call ?width ?BW ?word ?mem ?locals ?ext_spec ?fs ?fname ?t ?m ?l ?post =>
    let fs := eval hnf in fs in
    constr:(@call_body width BW word mem locals ext_spec
                       (@call width BW word mem locals ext_spec) fs fname t m l post)
  end.
Ltac unfold1_call_goal :=
  let G := lazymatch goal with |- ?G => G end in
  let G := unfold1_call G in
  change G.

Import Coq.ZArith.ZArith.

Notation "'fnspec!' name a0 .. an '/' g0 .. gn '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall tr mem,
                             pre ->
                             WeakestPrecondition.call
                               functions name tr mem (cons a0 .. (cons an nil) ..)
                               (fun tr' mem' rets =>
                                  (exists r0,
                                      .. (exists rn,
                                             rets = (cons r0 .. (cons rn nil) ..) /\
                                             post) ..)))) ..)) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     g0 binder, gn binder,
     r0 closed binder, rn closed binder,
     tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an '/' g0 .. gn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall tr mem,
                             pre ->
                             WeakestPrecondition.call
                               functions name tr mem (cons a0 .. (cons an nil) ..)
                               (fun tr' mem' rets =>
                                  rets = nil /\ post))) ..)) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     g0 binder, gn binder,
     tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
               (forall tr mem,
                   pre ->
                   WeakestPrecondition.call
                     functions name tr mem (cons a0 .. (cons an nil) ..)
                     (fun tr' mem' rets =>
                        (exists r0,
                            .. (exists rn,
                                   rets = (cons r0 .. (cons rn nil) ..) /\
                                   post) ..)))) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     r0 closed binder, rn closed binder,
     tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name '/' g0 .. gn '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
        (forall an,
              (forall g0,
                  .. (forall gn,
                         (forall tr mem,
                             pre ->
                             WeakestPrecondition.call
                               functions name tr mem nil
                               (fun tr' mem' rets =>
                                  (exists r0,
                                      .. (exists rn,
                                             rets = (cons r0 .. (cons rn nil) ..) /\
                                             post) ..)))) ..)))
    (at level 200,
     name at level 0,
     g0 binder, gn binder,
     r0 closed binder, rn closed binder,
     tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name a0 .. an ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall a0,
        .. (forall an,
               (forall tr mem,
                   pre ->
                   WeakestPrecondition.call
                     functions name tr mem (cons a0 .. (cons an nil) ..)
                     (fun tr' mem' rets =>
                        rets = nil /\ post))) ..))
    (at level 200,
     name at level 0,
     a0 binder, an binder,
     tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name '/' g0 .. gn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
              (forall g0,
                  .. (forall gn,
                         (forall tr mem,
                             pre ->
                             WeakestPrecondition.call
                               functions name tr mem nil
                               (fun tr' mem' rets =>
                                  rets = nil /\ post))) ..))
    (at level 200,
     name at level 0,
     g0 binder, gn binder,
     tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).

Notation "'fnspec!' name '~>' r0 .. rn ',' '{' 'requires' tr mem := pre ';' 'ensures' tr' mem' ':=' post '}'" :=
  (fun functions =>
     (forall tr mem,
         pre ->
         WeakestPrecondition.call
           functions name tr mem nil
           (fun tr' mem' rets =>
              (exists r0,
                  .. (exists rn,
                         rets = (cons r0 .. (cons rn nil) ..) /\
                         post) ..))))
    (at level 200,
     name at level 0,
     r0 closed binder, rn closed binder,
     tr name, tr' name, mem name, mem' name,
     pre at level 200,
     post at level 200).
