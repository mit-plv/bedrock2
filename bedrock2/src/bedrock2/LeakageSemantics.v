Require Import coqutil.sanity coqutil.Byte.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Properties.
Require coqutil.Map.SortedListString.
Require Import bedrock2.Syntax coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Export bedrock2.Memory.
Require Import bedrock2.Semantics.
Require Import Coq.Lists.List.

Inductive leakage_event {width: Z}{BW: Bitwidth width}{word: word.word width} : Type :=
| leak_unit
| leak_bool (b : bool)
| leak_word (w : word)
| leak_list (l : list word).
(* ^sometimes it's convenient that one io call leaks only one event
   See Interact case of spilling transform_trace function for an example. *)
Definition leakage {width: Z}{BW: Bitwidth width}{word: word.word width} : Type :=
  list leakage_event.

Definition ExtSpec{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} :=
  (* Given a trace of what happened so far,
     the given-away memory, an action label and a list of function call arguments, *)
  trace -> mem -> String.string -> list word ->
  (* and a postcondition on the received memory, function call results, and leakage trace, *)
  (mem -> list word -> list word -> Prop) ->
  (* tells if this postcondition will hold *)
  Prop.

Existing Class ExtSpec.

Module ext_spec.
  Class ok{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte}
          {ext_spec: ExtSpec}: Prop :=
  {
    (* Given a trace of previous interactions, the action name and arguments
       uniquely determine what chunk of memory the ext_spec will chop off from
       the whole memory m *)
    mGive_unique: forall t m mGive1 mKeep1 mGive2 mKeep2 a args post1 post2,
      map.split m mKeep1 mGive1 ->
      map.split m mKeep2 mGive2 ->
      ext_spec t mGive1 a args post1 ->
      ext_spec t mGive2 a args post2 ->
      mGive1 = mGive2;

    #[global] weaken :: forall t mGive act args,
        Morphisms.Proper
          (Morphisms.respectful
             (Morphisms.pointwise_relation Interface.map.rep
                (Morphisms.pointwise_relation (list word)
                   (Morphisms.pointwise_relation (list word) Basics.impl))) Basics.impl)
             (ext_spec t mGive act args);

    intersect: forall t mGive a args
                      (post1 post2: mem -> list word -> list word -> Prop),
        ext_spec t mGive a args post1 ->
        ext_spec t mGive a args post2 ->
        ext_spec t mGive a args (fun mReceive resvals klist =>
                                   post1 mReceive resvals klist /\ post2 mReceive resvals klist);
  }.
End ext_spec.
Arguments ext_spec.ok {_ _ _ _} _.

Definition PickSp {width: Z}{BW: Bitwidth width}{word: word.word width} : Type :=
  leakage -> word.
Existing Class PickSp.

Section binops.
  Context {width : Z} {BW : Bitwidth width} {word : Word.Interface.word width}.
  Definition leak_binop (bop : bopname) (x1 : word) (x2 : word) : leakage :=
    match bop with
    | bopname.divu | bopname.remu => cons (leak_word x2) (cons (leak_word x1) nil)
    | bopname.sru | bopname.slu | bopname.srs => cons (leak_word x2) nil
    | _ => nil
    end.
End binops.

Section semantics.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).

    Local Notation "' x <- a ; f" := (match a with Some x => f | None => None end)
      (right associativity, at level 70, x pattern).

    Fixpoint eval_expr (e : expr) (k : leakage) : option (word * leakage) :=
      match e with
      | expr.literal v => Some (word.of_Z v, k)
      | expr.var x => 'v <- map.get l x; Some (v, k)
      | expr.inlinetable aSize t index =>
          '(index', k') <- eval_expr index k;
          'v <- load aSize (map.of_list_word t) index';
          Some (v, leak_word index' :: k')
      | expr.load aSize a =>
          '(a', k') <- eval_expr a k;
          'v <- load aSize m a';
          Some (v, leak_word a' :: k')
      | expr.op op e1 e2 =>
          '(v1, k') <- eval_expr e1 k;
          '(v2, k'') <- eval_expr e2 k';
          Some (interp_binop op v1 v2, leak_binop op v1 v2 ++ k'')
      | expr.ite c e1 e2 =>
          '(vc, k') <- eval_expr c k;
          let b := word.eqb vc (word.of_Z 0) in
          eval_expr (if b then e2 else e1) (leak_bool b :: k')
      end.

    Fixpoint eval_call_args (arges : list expr) (k : leakage) :=
      match arges with
      | e :: tl =>
        '(v, k') <- eval_expr e k;
        '(args, k'') <- eval_call_args tl k';
        Some (v :: args, k'')
      | _ => Some (nil, k)
      end.

  End WithMemAndLocals.
End semantics.

Module exec. Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec} {pick_sp: PickSp}.
  Section WithEnv.
  Context (e: env).

  Implicit Types post : leakage -> trace -> mem -> locals -> Prop. (* COQBUG: unification finds Type instead of Prop and fails to downgrade *)
  Inductive exec: cmd -> leakage -> trace -> mem -> locals ->
                  (leakage -> trace -> mem -> locals -> Prop) -> Prop :=
  | skip: forall k t m l post,
      post k t m l ->
      exec cmd.skip k t m l post
  | set: forall x e k t m l post v k',
      eval_expr m l e k = Some (v, k') ->
      post k' t m (map.put l x v) ->
      exec (cmd.set x e) k t m l post
  | unset: forall x k t m l post,
      post k t m (map.remove l x) ->
      exec (cmd.unset x) k t m l post
  | store: forall sz ea ev k t m l post a k' v k'' m',
      eval_expr m l ea k = Some (a, k') ->
      eval_expr m l ev k' = Some (v, k'') ->
      store sz m a v = Some m' ->
      post (leak_word a :: k'') t m' l ->
      exec (cmd.store sz ea ev) k t m l post
  | stackalloc: forall x n body k t mSmall l post,
      Z.modulo n (bytes_per_word width) = 0 ->
      (forall mStack mCombined,
        let a := pick_sp k in
        anybytes a n mStack ->
        map.split mCombined mSmall mStack ->
        exec body (leak_unit :: k) t mCombined (map.put l x a)
          (fun k' t' mCombined' l' =>
            exists mSmall' mStack',
              anybytes a n mStack' /\
              map.split mCombined' mSmall' mStack' /\
              post k' t' mSmall' l')) ->
      exec (cmd.stackalloc x n body) k t mSmall l post
  | if_true: forall k t m l e c1 c2 post v k',
      eval_expr m l e k = Some (v, k') ->
      word.unsigned v <> 0 ->
      exec c1 (leak_bool true :: k') t m l post ->
      exec (cmd.cond e c1 c2) k t m l post
  | if_false: forall e c1 c2 k t m l post v k',
      eval_expr m l e k = Some (v, k') ->
      word.unsigned v = 0 ->
      exec c2 (leak_bool false :: k') t m l post ->
      exec (cmd.cond e c1 c2) k t m l post
  | seq: forall c1 c2 k t m l post mid,
      exec c1 k t m l mid ->
      (forall k' t' m' l', mid k' t' m' l' -> exec c2 k' t' m' l' post) ->
      exec (cmd.seq c1 c2) k t m l post
  | while_false: forall e c k t m l post v k',
      eval_expr m l e k = Some (v, k') ->
      word.unsigned v = 0 ->
      post (leak_bool false :: k') t m l ->
      exec (cmd.while e c) k t m l post
  | while_true: forall e c k t m l post v k' mid,
      eval_expr m l e k = Some (v, k') ->
      word.unsigned v <> 0 ->
      exec c (leak_bool true :: k') t m l mid ->
      (forall k'' t' m' l', mid k'' t' m' l' -> exec (cmd.while e c) k'' t' m' l' post) ->
      exec (cmd.while e c) k t m l post
  | call: forall binds fname arges k t m l post params rets fbody args k' lf mid,
      map.get e fname = Some (params, rets, fbody) ->
      eval_call_args m l arges k = Some (args, k') ->
      map.of_list_zip params args = Some lf ->
      exec fbody (leak_unit :: k') t m lf mid ->
      (forall k'' t' m' st1, mid k'' t' m' st1 ->
          exists retvs, map.getmany_of_list st1 rets = Some retvs /\
          exists l', map.putmany_of_list_zip binds retvs l = Some l' /\
          post k'' t' m' l') ->
      exec (cmd.call binds fname arges) k t m l post
  | interact: forall binds action arges args k' k t m l post mKeep mGive mid,
      map.split m mKeep mGive ->
      eval_call_args m l arges k = Some (args, k') ->
      ext_spec t mGive action args mid ->
      (forall mReceive resvals klist, mid mReceive resvals klist ->
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (leak_list klist :: k') (cons ((mGive, action, args), (mReceive, resvals)) t) m' l') ->
      exec (cmd.interact binds action arges) k t m l post.

  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {ext_spec_ok: ext_spec.ok ext_spec}.

  Lemma interact_cps: forall binds action arges args k' k t m l post mKeep mGive,
      map.split m mKeep mGive ->
      eval_call_args m l arges k = Some (args, k') ->
      ext_spec t mGive action args (fun mReceive resvals klist =>
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (leak_list klist :: k') (cons ((mGive, action, args), (mReceive, resvals)) t) m' l') ->
      exec (cmd.interact binds action arges) k t m l post.
  Proof. intros. eauto using interact. Qed.

  Lemma seq_cps: forall c1 c2 k t m l post,
      exec c1 k t m l (fun k' t' m' l' => exec c2 k' t' m' l' post) ->
      exec (cmd.seq c1 c2) k t m l post.
  Proof. intros. eauto using seq. Qed.

  Lemma weaken: forall k t l m s post1,
      exec s k t m l post1 ->
      forall post2,
        (forall k' t' m' l', post1 k' t' m' l' -> post2 k' t' m' l') ->
        exec s k t m l post2.
  Proof.
    induction 1; intros; try solve [econstructor; eauto].
    - eapply stackalloc. 1: assumption.
      intros.
      eapply H1; eauto.
      intros. fwd. eauto 10.
    - eapply call.
      4: eapply IHexec.
      all: eauto.
      intros.
      edestruct H3 as (? & ? & ? & ? & ?); [eassumption|].
      eauto 10.
    - eapply interact; try eassumption.
      intros.
      edestruct H2 as (? & ? & ?); [eassumption|].
      eauto 10.
  Qed.

  Lemma intersect: forall k t l m s post1,
      exec s k t m l post1 ->
      forall post2,
        exec s k t m l post2 ->
        exec s k t m l (fun k' t' m' l' => post1 k' t' m' l' /\ post2 k' t' m' l').
  Proof.
    induction 1;
      intros;
      match goal with
      | H: exec _ _ _ _ _ _ |- _ => inversion H; subst; clear H
      end;
      try match goal with
      | H1: ?e = Some (?x1, ?y1, ?z1), H2: ?e = Some (?x2, ?y2, ?z2) |- _ =>
        replace x2 with x1 in * by congruence;
          replace y2 with y1 in * by congruence;
          replace z2 with z1 in * by congruence;
          clear x2 y2 z2 H2
      end;
      repeat match goal with
             | H1: ?e = Some (?v1, ?k1), H2: ?e = Some (?v2, ?k2) |- _ =>
                 replace v2 with v1 in * by congruence;
                 replace k2 with k1 in * by congruence;
                 clear H2
             end;
      repeat match goal with
             | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
               replace v2 with v1 in * by congruence; clear H2
             end;
      try solve [econstructor; eauto | exfalso; congruence].

    - econstructor. 1: eassumption.
      intros.
      rename H0 into Ex1, H12 into Ex2.
      eapply weaken. 1: eapply H1. 1,2: eassumption.
      1: eapply Ex2. 1,2: eassumption.
      cbv beta.
      intros. fwd.
      lazymatch goal with
      | A: map.split _ _ _, B: map.split _ _ _ |- _ =>
        specialize @map.split_diff with (4 := A) (5 := B) as P
      end.
      edestruct P; try typeclasses eauto. 2: subst; eauto 10.
      eapply anybytes_unique_domain; eassumption.
    - econstructor.
      + eapply IHexec. exact H5. (* not H *)
      + simpl. intros *. intros [? ?]. eauto.
    - eapply while_true. 1, 2: eassumption.
      + eapply IHexec. exact H9. (* not H1 *)
      + simpl. intros *. intros [? ?]. eauto.
    - eapply call. 1, 2, 3: eassumption.
      + eapply IHexec. exact H16. (* not H2 *)
      + simpl. intros *. intros [? ?].
        edestruct H3 as (? & ? & ? & ? & ?); [eassumption|].
        edestruct H17 as (? & ? & ? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
    - pose proof ext_spec.mGive_unique as P.
      specialize P with (1 := H) (2 := H7) (3 := H1) (4 := H14).
      subst mGive0.
      destruct (map.split_diff (map.same_domain_refl mGive) H H7) as (? & _).
      subst mKeep0.
      eapply interact. 1,2: eassumption.
      + eapply ext_spec.intersect; [ exact H1 | exact H14 ].
      + simpl. intros *. intros [? ?].
        edestruct H2 as (? & ? & ?); [eassumption|].
        edestruct H15 as (? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
  Qed.

  End WithEnv.

  Lemma extend_env: forall e1 e2,
      map.extends e2 e1 ->
      forall c k t m l post,
      exec e1 c k t m l post ->
      exec e2 c k t m l post.
  Proof. induction 2; try solve [econstructor; eauto]. Qed.

  End WithParams.
End exec. Notation exec := exec.exec.

Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec} {pick_sp : PickSp}.

  Implicit Types (l: locals) (m: mem) (post: leakage -> trace -> mem -> list word -> Prop).

  Definition call e fname k t m args post :=
    exists argnames retnames body,
      map.get e fname = Some (argnames, retnames, body) /\
      exists l, map.of_list_zip argnames args = Some l /\
        exec e body k t m l (fun k' t' m' l' => exists rets,
          map.getmany_of_list l' retnames = Some rets /\ post k' t' m' rets).

  Lemma weaken_call: forall e fname k t m args post1,
      call e fname k t m args post1 ->
      forall post2, (forall k' t' m' rets, post1 k' t' m' rets -> post2 k' t' m' rets) ->
      call e fname k t m args post2.
  Proof.
    unfold call. intros. fwd.
    do 4 eexists. 1: eassumption.
    do 2 eexists. 1: eassumption.
    eapply exec.weaken. 1: eassumption.
    cbv beta. clear -H0. intros. fwd. eauto.
  Qed.

  Lemma extend_env_call: forall e1 e2,
      map.extends e2 e1 ->
      forall f k t m rets post,
      call e1 f k t m rets post ->
      call e2 f k t m rets post.
  Proof.
    unfold call. intros. fwd. repeat eexists.
    - eapply H. eassumption.
    - eassumption.
    - eapply exec.extend_env; eassumption.
  Qed.
End WithParams.
