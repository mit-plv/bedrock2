Require Import coqutil.Macros.subst coqutil.Macros.unique coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import coqutil.Tactics.fwd.
Require Import Coq.ZArith.BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.dlet bedrock2.Syntax bedrock2.Semantics.

Section WeakestPrecondition.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
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

  Lemma expr_sound: forall m l e post (H : expr m l e post),
    exists v, Semantics.eval_expr m l e = Some v /\ post v.
  Proof.
    induction e; t.
    { eapply IHe in H; t. cbv [load] in H0; t. rewrite H. rewrite H0. eauto. }
    { eapply IHe in H; t. cbv [load] in H0; t. rewrite H. rewrite H0. eauto. }
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

  Lemma exprs_sound : forall m l args P,
      list_map (expr m l) args P ->
      exists x, Semantics.eval_call_args m l args = Some x /\ P x.
  Proof.
    induction args; cbn; repeat (subst; t).
    eapply expr_sound in H; t; rewrite H.
    eapply IHargs in H0; t; rewrite H0.
    eauto.
  Qed.

  Lemma getmany_sound: forall a l P,
      list_map (get l) a P -> exists vs, map.getmany_of_list l a = Some vs /\ P vs.
  Proof.
    cbv [map.getmany_of_list].
    induction a; cbn; repeat (subst; t).
    cbv [get] in H; t.
    epose proof (IHa _ _ H0); clear IHa; t.
    rewrite H. erewrite H1. eexists; split; eauto.
  Qed.

  Definition dexpr m l e v := expr m l e (eq v).
  Definition dexprs m l es vs := list_map (expr m l) es (eq vs).

  Section WithFunctionEnv.
    Context (e: env).
    Notation cmd := (Semantics.exec e).

    Definition func '(innames, outnames, c) (t : trace) (m : mem) (args : list word)
      (post : trace -> mem -> list word -> Prop) :=
      exists l, map.of_list_zip innames args = Some l /\
      cmd c t m l (fun t m l =>
        list_map (get l) outnames (fun rets =>
        post t m rets)).

    Notation call := Semantics.call (only parsing).

    Definition program := cmd.

    Implicit Type post : trace -> mem -> locals -> Prop.

    Ltac step :=
      match reverse goal with
      | H: _ /\ _ |- _ => destruct H
      | H: exists x, _ |- _ => let n := fresh x in destruct H as [n H]
      | |- _ => progress unfold dlet, dexpr, store in *
      | |- _ => constructor
      | |- _ => assumption
      | |- _ => progress intros
      | |- _ => progress subst
      | H: expr _ _ _ _ |- _ => eapply expr_sound in H
      | |- _ => solve [econstructor; eauto]
      end.
    Ltac tac := repeat step.

    Lemma wp_skip: forall t m l post, post t m l -> cmd cmd.skip t m l post.
    Proof. tac. Qed.

    Lemma wp_set: forall x ev t m l post,
        (exists v, dexpr m l ev v /\
        dlet! l := map.put l x v in
        post t m l) ->
        cmd (cmd.set x ev) t m l post.
    Proof. tac. Qed.

    Lemma wp_unset: forall x t m l post,
        (dlet! l := map.remove l x in
         post t m l) ->
        cmd (cmd.unset x) t m l post.
    Proof. tac. Qed.

    Lemma wp_store: forall sz ea ev t m l post,
       (exists a, dexpr m l ea a /\
        exists v, dexpr m l ev v /\
        store sz m a v (fun m =>
        post t m l)) ->
       cmd (cmd.store sz ea ev) t m l post.
    Proof. tac. Qed.

    Lemma wp_stackalloc: forall x n c t m l post,
        (Z.modulo n (bytes_per_word width) = 0 /\
        forall a mStack mCombined,
          anybytes a n mStack -> map.split mCombined m mStack ->
          dlet! l := map.put l x a in
          cmd c t mCombined l (fun t' mCombined' l' =>
          exists m' mStack',
          anybytes a n mStack' /\ map.split mCombined' m' mStack' /\
          post t' m' l')) ->
          cmd (cmd.stackalloc x n c) t m l post.
    Proof. tac. Qed.

    Lemma wp_cond: forall br ct cf t m l post,
        (exists v, dexpr m l br v /\
        (word.unsigned v <> 0%Z -> cmd ct t m l post) /\
        (word.unsigned v = 0%Z -> cmd cf t m l post)) ->
        cmd (cmd.cond br ct cf) t m l post.
    Proof.
      tac. destr.destr (Z.eqb (word.unsigned v0) 0).
      - specialize H1 with (1 := E). tac.
      - specialize H0 with (1 := E). tac.
    Qed.

    Lemma wp_seq: forall c1 c2 t m l post,
        cmd c1 t m l (fun t m l => cmd c2 t m l post) ->
        cmd (cmd.seq c1 c2) t m l post.
    Proof. tac. Qed.

    Lemma wp_call: forall binds fname arges t m l post,
       (exists args, dexprs m l arges args /\
        call e fname t m args (fun t m rets =>
          exists l', map.putmany_of_list_zip binds rets l = Some l' /\
          post t m l')) ->
       cmd (cmd.call binds fname arges) t m l post.
    Proof.
      tac.
      unfold dexprs in *.
      eapply exprs_sound in H. destruct H as (argvs & HEv & ?). subst argvs.
      unfold call in *. fwd.
      econstructor; eauto.
    Qed.

    Lemma wp_interact: forall binds action arges t m l post,
       (exists args, dexprs m l arges args /\
        exists mKeep mGive, map.split m mKeep mGive /\
        ext_spec t mGive action args (fun mReceive rets =>
          exists l', map.putmany_of_list_zip binds rets l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (cons ((mGive, action, args), (mReceive, rets)) t) m' l')) ->
       cmd (cmd.interact binds action arges) t m l post.
    Proof.
      tac.
      eapply exprs_sound in H. destruct H as (argvs & HEv & ?). subst argvs.
      tac.
    Qed.
  End WithFunctionEnv.
End WeakestPrecondition.

Notation cmd := Semantics.exec (only parsing).
Notation call := Semantics.call (only parsing).

Ltac apply_rule_for_command c :=
  lazymatch c with
  | cmd.skip => eapply wp_skip
  | cmd.set ?x ?ev => eapply wp_set
  | cmd.unset ?x => eapply wp_unset
  | cmd.store ?sz ?ea ?ev => eapply wp_store
  | cmd.stackalloc ?x ?n ?c => eapply wp_stackalloc
  | cmd.cond ?br ?ct ?cf => eapply wp_cond
  | cmd.seq ?c1 ?c2 => eapply wp_seq
  | cmd.while ?e ?c => fail "cmd.while is not treated in this tactic"
  | cmd.call ?binds ?fname ?arges => eapply wp_call
  | cmd.interact ?binds ?action ?arges => eapply wp_interact
  end.

Ltac unfold1_cmd_goal :=
  lazymatch goal with
  | |- cmd _ ?c _ _ _ ?post => let c := eval hnf in c in apply_rule_for_command c
  end.

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
