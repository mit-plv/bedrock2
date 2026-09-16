Require Import coqutil.sanity coqutil.Byte.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Properties.
Require coqutil.Map.SortedListString.
Require Import bedrock2.Syntax coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import BinIntDef coqutil.Word.Bitwidth.
Require Export bedrock2.Memory.
Require Import Coq.Lists.List.

(* BW is not needed on the rhs, but helps infer width *)
Definition LogItem{width: Z}{BW: Bitwidth width}{mem: map.map (bits width) byte} :=
  ((mem * String.string * list (bits width)) * (mem * list (bits width)))%type.

Definition trace{width: Z}{BW: Bitwidth width}{mem: map.map (bits width) byte} :=
  list LogItem.

Definition ExtSpec{width: Z}{BW: Bitwidth width}{mem: map.map (bits width) byte} :=
  (* Given a trace of what happened so far,
     the given-away memory, an action label and a list of function call arguments, *)
  trace -> mem -> String.string -> list (bits width) ->
  (* and a postcondition on the received memory and function call results, *)
  (mem -> list (bits width) -> Prop) ->
  (* tells if this postcondition will hold *)
  Prop.

Existing Class ExtSpec.

Module ext_spec.
  Class ok{width: Z}{BW: Bitwidth width}{mem: map.map (bits width) byte}
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
               (Morphisms.pointwise_relation (list (bits width)) Basics.impl)) Basics.impl)
          (ext_spec t mGive act args);

    intersect: forall t mGive a args
                      (post1 post2: mem -> list (bits width) -> Prop),
        ext_spec t mGive a args post1 ->
        ext_spec t mGive a args post2 ->
        ext_spec t mGive a args (fun mReceive resvals =>
                                   post1 mReceive resvals /\ post2 mReceive resvals);
  }.
End ext_spec.
Arguments ext_spec.ok {_ _ _} _.

Section operators.
  Context {width : Z}.
  Local Notation word := (bits width).
  (* Shift amounts are taken modulo the bitwidth, as on RISC-V and in C compilers
     for shifts by less than the word size. *)
  Local Notation shamt b := (Zmod.unsigned b mod 2 ^ Z.log2 width).

  Definition slu (a b : word) : word := Zmod.slu a (shamt b).
  Definition sru (a b : word) : word := Zmod.sru a (shamt b).
  Definition srs (a b : word) : word := Zmod.srs a (shamt b).
  Definition ltu (a b : word) : bool := Z.ltb (Zmod.unsigned a) (Zmod.unsigned b).
  Definition lts (a b : word) : bool := Z.ltb (Zmod.signed a) (Zmod.signed b).
  Definition interp_op1 (op : op1) : word -> word :=
    match op with
    | op1.not => Zmod.not
    | op1.opp => Zmod.opp
    end.

  Definition interp_binop (bop : bopname) : word -> word -> word :=
    match bop with
    | bopname.add => Zmod.add
    | bopname.sub => Zmod.sub
    | bopname.mul => Zmod.mul
    | bopname.mulhuu => fun a b =>
      bits.of_Z width (Zmod.unsigned a * Zmod.unsigned b / 2 ^ width)
    | bopname.divu => Zmod.udiv
    | bopname.remu => Zmod.umod
    | bopname.and => Zmod.and
    | bopname.or => Zmod.or
    | bopname.xor => Zmod.xor
    | bopname.sru => sru
    | bopname.slu => slu
    | bopname.srs => srs
    | bopname.lts => fun a b => if lts a b then Zmod.one else Zmod.zero
    | bopname.ltu => fun a b => if ltu a b then Zmod.one else Zmod.zero
    | bopname.eq => fun a b =>
      if Zmod.eqb a b then Zmod.one else Zmod.zero
    end.
End operators.

(* simpl and cbn expose the masked amount and the Z comparison, as the
   program logic's automation expects. *)
Arguments slu {width} a b /.
Arguments sru {width} a b /.
Arguments srs {width} a b /.
Arguments ltu {width} a b /.
Arguments lts {width} a b /.

Section shift_amounts.
  Context {width : Z} {BW : Bitwidth width}.
  Local Notation word := (bits width).

  Lemma shamt_small k :
    0 <= k < width ->
    k mod 2 ^ Z.log2 width = k.
  Proof. destruct width_cases as [-> | ->]; intros; apply Z.mod_small; cbn; lia. Qed.

  Lemma unsigned_slu_shamtZ (x : word) n :
    0 <= n < width ->
    Zmod.unsigned (slu x (bits.of_Z width n)) = Z.shiftl (Zmod.unsigned x) n mod 2 ^ width.
  Proof. intros; unfold slu; rewrite shamt_of_Z_small, Zmod.unsigned_slu by assumption; reflexivity. Qed.

  Lemma unsigned_sru_shamtZ (x : word) n :
    0 <= n < width ->
    Zmod.unsigned (sru x (bits.of_Z width n)) = Z.shiftr (Zmod.unsigned x) n.
  Proof. intros; unfold sru; rewrite shamt_of_Z_small, Zmod.unsigned_sru by lia; reflexivity. Qed.

  Lemma signed_srs_shamtZ (x : word) n :
    0 <= n < width ->
    Zmod.signed (srs x (bits.of_Z width n)) = Z.shiftr (Zmod.signed x) n.
  Proof. intros; unfold srs; rewrite shamt_of_Z_small, Zmod.signed_srs by lia; reflexivity. Qed.
End shift_amounts.

Definition env: map.map String.string Syntax.func := SortedListString.map _.
#[export] Instance env_ok: map.ok env := SortedListString.ok _.

Section semantics.
  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.

  (* this is the expr evaluator that is used to verify execution time, the just-correctness-oriented version is below *)
  Section WithMemAndLocals.
    Context (m : mem) (l : locals).

    Local Notation "x <- a ; f" := (match a with Some x => f | None => None end)
      (right associativity, at level 70).

    Fixpoint eval_expr (e : expr) : option word :=
      match e with
      | expr.literal v => Some (bits.of_Z width v)
      | expr.var x => map.get l x
      | expr.inlinetable aSize t index =>
          index' <- eval_expr index;
          load aSize (map.of_list_word t) index'
      | expr.load aSize a =>
          a' <- eval_expr a;
          load aSize m a'
      | expr.op1 op e =>
          v <- eval_expr e;
          Some (interp_op1 op v)
      | expr.op op e1 e2 =>
          v1 <- eval_expr e1;
          v2 <- eval_expr e2;
          Some (interp_binop op v1 v2)
      | expr.ite c e1 e2 =>
          vc <- eval_expr c;
          eval_expr (if Zmod.eqb vc (bits.of_Z width 0) then e2 else e1)
      end.

    Fixpoint eval_call_args (arges : list expr) :=
      match arges with
      | e :: tl =>
        v <- eval_expr e;
        args <- eval_call_args tl;
        Some (v :: args)
      | _ => Some nil
      end.

  End WithMemAndLocals.
End semantics.

Module exec. Section WithParams.
  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.
  Section WithEnv.
  Context (e: env).

  Implicit Types post : trace -> mem -> locals -> Prop. (* COQBUG: unification finds Type instead of Prop and fails to downgrade *)
  Inductive exec: cmd -> trace -> mem -> locals ->
                  (trace -> mem -> locals -> Prop) -> Prop :=
  | skip: forall t m l post,
      post t m l ->
      exec cmd.skip t m l post
  | set: forall x e t m l post v,
      eval_expr m l e = Some v ->
      post t m (map.put l x v) ->
      exec (cmd.set x e) t m l post
  | unset: forall x t m l post,
      post t m (map.remove l x) ->
      exec (cmd.unset x) t m l post
  | store: forall sz ea ev t m l post a v m',
      eval_expr m l ea = Some a ->
      eval_expr m l ev = Some v ->
      store sz m a v = Some m' ->
      post t m' l ->
      exec (cmd.store sz ea ev) t m l post
  | stackalloc: forall x n body t mSmall l post,
      Z.modulo n (bytes_per_word width) = 0 ->
      (forall a mStack mCombined,
        anybytes a n mStack ->
        map.split mCombined mSmall mStack ->
        exec body t mCombined (map.put l x a)
          (fun t' mCombined' l' =>
            exists mSmall' mStack',
              anybytes a n mStack' /\
              map.split mCombined' mSmall' mStack' /\
              post t' mSmall' l')) ->
      exec (cmd.stackalloc x n body) t mSmall l post
  | if_true: forall t m l e c1 c2 post v,
      eval_expr m l e = Some v ->
      Zmod.unsigned v <> 0 ->
      exec c1 t m l post ->
      exec (cmd.cond e c1 c2) t m l post
  | if_false: forall e c1 c2 t m l post v,
      eval_expr m l e = Some v ->
      Zmod.unsigned v = 0 ->
      exec c2 t m l post ->
      exec (cmd.cond e c1 c2) t m l post
  | seq: forall c1 c2 t m l post mid,
      exec c1 t m l mid ->
      (forall t' m' l', mid t' m' l' -> exec c2 t' m' l' post) ->
      exec (cmd.seq c1 c2) t m l post
  | while_false: forall e c t m l post v,
      eval_expr m l e = Some v ->
      Zmod.unsigned v = 0 ->
      post t m l ->
      exec (cmd.while e c) t m l post
  | while_true: forall e c t m l post v mid,
      eval_expr m l e = Some v ->
      Zmod.unsigned v <> 0 ->
      exec c t m l mid ->
      (forall t' m' l', mid t' m' l' -> exec (cmd.while e c) t' m' l' post) ->
      exec (cmd.while e c) t m l post
  | call: forall binds fname arges t m l post params rets fbody args lf mid,
      map.get e fname = Some (params, rets, fbody) ->
      eval_call_args m l arges = Some args ->
      map.of_list_zip params args = Some lf ->
      exec fbody t m lf mid ->
      (forall t' m' st1, mid t' m' st1 ->
          exists retvs, map.getmany_of_list st1 rets = Some retvs /\
          exists l', map.putmany_of_list_zip binds retvs l = Some l' /\
          post t' m' l') ->
      exec (cmd.call binds fname arges) t m l post
  | interact: forall binds action arges args t m l post mKeep mGive mid,
      map.split m mKeep mGive ->
      eval_call_args m l arges = Some args ->
      ext_spec t mGive action args mid ->
      (forall mReceive resvals, mid mReceive resvals ->
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (cons ((mGive, action, args), (mReceive, resvals)) t) m' l') ->
      exec (cmd.interact binds action arges) t m l post.

  Context {mem_ok: map.ok mem} {ext_spec_ok: ext_spec.ok ext_spec}.

  Lemma interact_cps: forall binds action arges args t m l post mKeep mGive,
      map.split m mKeep mGive ->
      eval_call_args m l arges = Some args ->
      ext_spec t mGive action args (fun mReceive resvals =>
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (cons ((mGive, action, args), (mReceive, resvals)) t) m' l') ->
      exec (cmd.interact binds action arges) t m l post.
  Proof. intros. eauto using interact. Qed.

  Lemma seq_cps: forall c1 c2 t m l post,
      exec c1 t m l (fun t' m' l' => exec c2 t' m' l' post) ->
      exec (cmd.seq c1 c2) t m l post.
  Proof. intros. eauto using seq. Qed.

  Lemma weaken: forall t l m s post1,
      exec s t m l post1 ->
      forall post2,
        (forall t' m' l', post1 t' m' l' -> post2 t' m' l') ->
        exec s t m l post2.
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

  Lemma intersect: forall t l m s post1,
      exec s t m l post1 ->
      forall post2,
        exec s t m l post2 ->
        exec s t m l (fun t' m' l' => post1 t' m' l' /\ post2 t' m' l').
  Proof.
    induction 1;
      intros;
      match goal with
      | H: exec _ _ _ _ _ |- _ => inversion H; subst; clear H
      end;
      try match goal with
      | H1: ?e = Some (?x1, ?y1, ?z1), H2: ?e = Some (?x2, ?y2, ?z2) |- _ =>
        replace x2 with x1 in * by congruence;
          replace y2 with y1 in * by congruence;
          replace z2 with z1 in * by congruence;
          clear x2 y2 z2 H2
      end;
      repeat match goal with
             | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
               replace v2 with v1 in * by congruence; clear H2
             end;
      repeat match goal with
             | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
               replace v2 with v1 in * by congruence; clear H2
             end;
      try solve [econstructor; eauto | exfalso; congruence].

    - econstructor. 1: eassumption.
      intros.
      rename H0 into Ex1, H11 into Ex2.
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
      + eapply IHexec. exact H15. (* not H2 *)
      + simpl. intros *. intros [? ?].
        edestruct H3 as (? & ? & ? & ? & ?); [eassumption|].
        edestruct H16 as (? & ? & ? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
    - pose proof ext_spec.mGive_unique as P.
      specialize P with (1 := H) (2 := H7) (3 := H1) (4 := H13).
      subst mGive0.
      destruct (map.split_diff (map.same_domain_refl mGive) H H7) as (? & _).
      subst mKeep0.
      eapply interact. 1,2: eassumption.
      + eapply ext_spec.intersect; [ exact H1 | exact H13 ].
      + simpl. intros *. intros [? ?].
        edestruct H2 as (? & ? & ?); [eassumption|].
        edestruct H14 as (? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
  Qed.

  End WithEnv.

  Lemma extend_env: forall e1 e2,
      map.extends e2 e1 ->
      forall c t m l post,
      exec e1 c t m l post ->
      exec e2 c t m l post.
  Proof. induction 2; try solve [econstructor; eauto]. Qed.

  End WithParams.
End exec. Notation exec := exec.exec.

Section WithParams.
  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.

  Implicit Types (l: locals) (m: mem) (post: trace -> mem -> list word -> Prop).

  Definition call e fname t m args post :=
    exists argnames retnames body,
      map.get e fname = Some (argnames, retnames, body) /\
      exists l, map.of_list_zip argnames args = Some l /\
        exec e body t m l (fun t' m' l' => exists rets,
          map.getmany_of_list l' retnames = Some rets /\ post t' m' rets).

  Lemma weaken_call: forall e fname t m args post1,
      call e fname t m args post1 ->
      forall post2, (forall t' m' rets, post1 t' m' rets -> post2 t' m' rets) ->
      call e fname t m args post2.
  Proof.
    unfold call. intros. fwd.
    do 4 eexists. 1: eassumption.
    do 2 eexists. 1: eassumption.
    eapply exec.weaken. 1: eassumption.
    cbv beta. clear -H0. intros. fwd. eauto.
  Qed.

  Lemma extend_env_call: forall e1 e2,
      map.extends e2 e1 ->
      forall f t m rets post,
      call e1 f t m rets post ->
      call e2 f t m rets post.
  Proof.
    unfold call. intros. fwd. repeat eexists.
    - eapply H. eassumption.
    - eassumption.
    - eapply exec.extend_env; eassumption.
  Qed.
End WithParams.
