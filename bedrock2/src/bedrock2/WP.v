Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import bedrock2.Syntax bedrock2.Semantics.

(* We want to make the definitions opaque to `hnf` (unfolds any definition, so a plain
   definition doesn't work) and to `repeat split` (applies constructors of all
   1-constructor inductives, so a 1-constructor inductive wrapping exec doesn't
   work). *)
Module Type WP_Sig.
  Section WithParams.
    Context {width: Z} {BW: Bitwidth width} {word: word.word width}
      {mem: map.map word Byte.byte}
      {locals: map.map String.string word}.

    Parameter wp_cmd : forall {ext_spec: ExtSpec} (e: env),
        Syntax.cmd -> trace -> mem -> locals ->
        (trace -> mem -> locals -> Prop) -> Prop.
    Parameter mk_wp_cmd : forall {ext_spec: ExtSpec} (e: env) c t m l post,
        (forall mc, exec e c t m l mc (fun t' m' l' mc' => post t' m' l')) ->
        wp_cmd e c t m l post.
    Parameter invert_wp_cmd: forall {ext_spec: ExtSpec} [e c t m l post],
        wp_cmd e c t m l post ->
        forall mc, exec e c t m l mc (fun t' m' l' mc' => post t' m' l').

    Parameter wp_call : forall {locals: map.map String.string word} {ext_spec: ExtSpec},
        env -> String.string -> trace -> mem -> list word ->
        (trace -> mem -> list word -> Prop) -> Prop.
    Parameter mk_wp_call :
      forall {ext_spec: ExtSpec} (e: env) fname argnames retnames body t m l args post,
        map.get e fname = Some (argnames, retnames, body) ->
        map.of_list_zip argnames args = Some l ->
        wp_cmd e body t m l (fun t' m' l' => exists rets,
          map.getmany_of_list l' retnames = Some rets /\ post t' m' rets) ->
        wp_call e fname t m args post.
    Parameter invert_wp_call : forall {ext_spec: ExtSpec} (e: env) fname t m args post,
        wp_call e fname t m args post ->
        exists argnames retnames body l,
          map.get e fname = Some (argnames, retnames, body) /\
          map.of_list_zip argnames args = Some l /\
          wp_cmd e body t m l (fun t' m' l' => exists rets,
            map.getmany_of_list l' retnames = Some rets /\ post t' m' rets).
  End WithParams.
End WP_Sig.

Module Export WP_Impl : WP_Sig.
  Section WithParams.
    Context {width: Z} {BW: Bitwidth width} {word: word.word width}
      {mem: map.map word Byte.byte}
      {locals: map.map String.string word}
      {ext_spec: ExtSpec}
      (e: env).

    Definition wp_cmd (c : Syntax.cmd) (t : trace) (m : mem) (l : locals)
      (post : (trace -> mem -> locals -> Prop)) : Prop :=
      (forall mc, exec e c t m l mc (fun t' m' l' mc' => post t' m' l')).

    Lemma mk_wp_cmd c t m l post:
      (forall mc, exec e c t m l mc (fun t' m' l' mc' => post t' m' l')) ->
      wp_cmd c t m l post.
    Proof. exact id. Qed.

    Lemma invert_wp_cmd c t m l post:
        wp_cmd c t m l post ->
        forall mc, exec e c t m l mc (fun t' m' l' mc' => post t' m' l').
    Proof. exact id. Qed.

    Definition wp_call fname t m args post :=
        exists argnames retnames body l,
          map.get e fname = Some (argnames, retnames, body) /\
          map.of_list_zip argnames args = Some l /\
          wp_cmd body t m l (fun t' m' l' => exists rets,
            map.getmany_of_list l' retnames = Some rets /\ post t' m' rets).

    Lemma mk_wp_call: forall fname argnames retnames body t m l args post,
        map.get e fname = Some (argnames, retnames, body) ->
        map.of_list_zip argnames args = Some l ->
        wp_cmd body t m l (fun t' m' l' => exists rets,
          map.getmany_of_list l' retnames = Some rets /\ post t' m' rets) ->
        wp_call fname t m args post.
    Proof. intros. unfold wp_call. eauto 8. Qed.

    Lemma invert_wp_call fname t m args post:
        wp_call fname t m args post ->
        exists argnames retnames body l,
          map.get e fname = Some (argnames, retnames, body) /\
          map.of_list_zip argnames args = Some l /\
          wp_cmd body t m l (fun t' m' l' => exists rets,
            map.getmany_of_list l' retnames = Some rets /\ post t' m' rets).
    Proof. exact id. Qed.
  End WithParams.
End WP_Impl.

Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
    {mem: map.map word Byte.byte}
    {locals: map.map String.string word}
    {ext_spec: ExtSpec}.

  Lemma weaken_wp_cmd: forall e c t m l (post1 post2: trace -> mem -> locals -> Prop),
      (forall t' m' l', post1 t' m' l' -> post2 t' m' l') ->
      wp_cmd e t m l c post1 -> wp_cmd e t m l c post2.
  Proof.
    intros. eapply mk_wp_cmd. intros. eapply invert_wp_cmd in H0.
    eapply exec.weaken. 1: eassumption. eauto.
  Qed.

  Lemma weaken_wp_call: forall e f t m args (post1 post2: trace -> mem -> list word -> Prop),
      (forall t' m' rets, post1 t' m' rets -> post2 t' m' rets) ->
      wp_call e f t m args post1 -> wp_call e f t m args post2.
  Proof.
    intros. eapply invert_wp_call in H0. firstorder idtac.
    eapply mk_wp_call; eauto.
    eapply weaken_wp_cmd. 2: eassumption. firstorder eauto.
  Qed.

  Lemma extend_env_wp_cmd: forall e1 e2,
      map.extends e2 e1 ->
      forall c t m l post,
      wp_cmd e1 t m l c post ->
      wp_cmd e2 t m l c post.
  Proof.
    intros. eapply mk_wp_cmd. intros. eapply invert_wp_cmd in H0.
    eapply exec.extend_env; eassumption.
  Qed.

  Lemma extend_env_wp_call: forall e1 e2,
      map.extends e2 e1 ->
      forall f t m args post,
      wp_call e1 f t m args post ->
      wp_call e2 f t m args post.
  Proof.
    intros. eapply invert_wp_call in H0. destruct H0 as (? & ? & ? & ? & ? & ? & ?).
    eapply mk_wp_call; eauto.
    eapply extend_env_wp_cmd; eauto.
  Qed.
End WithParams.
