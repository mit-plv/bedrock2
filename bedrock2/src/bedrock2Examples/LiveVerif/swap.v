Require Import bedrock2Examples.LiveVerif.string_to_ident.

Load LiveVerif.

(* begin move *)

  (* non-unfoldable wrappers, their definition might be swapped with something else later,
     as long as it satisfies the lemmas that follow below *)

  Inductive wp_expr(m: mem)(l: locals)(e: expr)(post: word -> Prop): Prop :=
    mk_wp_expr: WeakestPrecondition.expr m l e post -> wp_expr m l e post.

  Lemma wp_var: forall m l x v (post: word -> Prop),
      map.get l x = Some v ->
      post v ->
      wp_expr m l x post.
  Proof.
    intros. constructor. cbn. unfold WeakestPrecondition.get. eauto.
  Qed.

  Inductive wp_cmd(call: (string -> trace -> mem -> list word ->
                          (trace -> mem -> list word -> Prop) -> Prop))
            (c: cmd)(t: trace)(m: mem)(l: locals)(post: trace -> mem -> locals -> Prop): Prop :=
    mk_wp_cmd: WeakestPrecondition.cmd call c t m l post -> wp_cmd call c t m l post.

  Lemma wp_set: forall call x a t m l rest post,
      wp_expr m l a
        (fun v => wp_cmd call rest t m (map.put l x v) post) ->
      wp_cmd call (cmd.seq (cmd.set x a) rest) t m l post.
  Proof.
    intros. destruct H. constructor. cbn. unfold dexpr, dlet.dlet.
    (* TODO not quite compatible (or requires proof that exprs are deterministic *)
  Admitted.

  Lemma wp_skip: forall call t m l (post: trace -> mem -> locals -> Prop),
      post t m l ->
      wp_cmd call cmd.skip t m l post.
  Proof. intros. constructor. assumption. Qed.

  Definition vc_func call '(innames, outnames, body) (t: trace) (m: mem) (argvs: list word)
                     (post : trace -> mem -> list word -> Prop) :=
    exists l, map.of_list_zip innames argvs = Some l /\
      wp_cmd call body t m l (fun t' m' l' =>
        exists retvs, map.getmany_of_list l' outnames = Some retvs /\ post t' m' retvs).

Ltac make_fresh x :=
  (* TODO: if there's a hypothesis called eg value_of_x, also rename it into value_of_x0 *)
  tryif is_var x then let x' := fresh x "0" in rename x into x' else idtac.

Definition current_locals_marker(l: locals): locals := l.

Ltac put_into_current_locals :=
  lazymatch goal with
  | |- wp_cmd _ _ _ _ (map.put ?l ?x ?v) _ =>
    let i := string_to_ident x in
    make_fresh i;
    let n := fresh "value_of_" i in
    remember v as i eqn: n in |- *
  end;
  lazymatch goal with
  | cl := current_locals_marker (reconstruct _ _) |- _ =>
    subst cl;
    lazymatch goal with
    | |- wp_cmd ?call ?c ?t ?m ?l ?post =>
      let keys := eval vm_compute in (map.keys l) in
      let values := eval vm_compute in (map.getmany_of_list l keys) in
      let values := lazymatch values with Some ?values => values end in
      let values := eval vm_compute in (tuple.of_list values) in
      change (let cl := current_locals_marker (reconstruct keys values) in
              wp_cmd call c t m cl post);
      intro
    end
  end.

Ltac start :=
  let call := fresh "call" in
  intro call;
  let n := fresh "____TODO_hide_defs_above____" in
  pose proof tt as n;
  intros;
  (* since the arguments will get renamed, it is useful to have a list of their
     names, so that we can always see their current renamed names *)
  lazymatch goal with
  | |- vc_func ?call ?f ?t ?m ?argvalues ?post =>
    let arguments := fresh "arguments" in pose argvalues as arguments
  end.

Ltac assign name val :=
  eapply wp_set with (x := name) (a := val);
  eapply wp_var; [ reflexivity |];
  put_into_current_locals.

Declare Scope live_scope.
Delimit Scope live_scope with live.
Open Scope live_scope.

Notation "'ready' 'for' 'next' 'command'" := (wp_cmd _ _ _ _ _ _)
  (at level 0, only printing) : live_scope.

Declare Scope reconstruct_locals_scope.
Delimit Scope reconstruct_locals_scope with reconstruct_locals.

Notation "[ x ]" := (PrimitivePair.pair.mk x tt)
  (only printing) : reconstruct_locals_scope.
Notation "[ x ; y ; .. ; z ]" :=
  (PrimitivePair.pair.mk x (PrimitivePair.pair.mk y .. (PrimitivePair.pair.mk z tt) ..))
  (only printing) : reconstruct_locals_scope.

Notation "l" := (current_locals_marker (reconstruct _ l%reconstruct_locals))
  (at level 100, only printing) : live_scope.

(* end move *)


(* TODO: write down postcondition only at end *)
Definition swap: {f: list string * list string * cmd &
  forall call t m a b,
    vc_func call f t m [a; b] (fun t' m' retvs =>
      t' = t /\ m' = m /\ retvs = [b; a]
  )}.
  (* note: we could just return ["b", "a"] and then the body would be just skip *)
  refine (existT _ (["a"; "b"], ["res1"; "res2"], _) _).
  start.
  unfold vc_func. letexists. split. {
    subst l.
    transitivity (Some (current_locals_marker (reconstruct ["a"; "b"]
                   (PrimitivePair.pair.mk a (PrimitivePair.pair.mk b tt))))).
    all: reflexivity.
  }
  rename l into current_locals, m into current_mem.

  assign "t" "a".
  assign "a" "b".
  assign "b" "t".
  assign "res1" "a".
  assign "res2" "b".

  eapply wp_skip.
  eexists. ssplit; reflexivity.
Defined.

Goal False.
  let r := eval unfold swap in match swap with
                               | existT _ f _ => f
                               end
    in pose r.
Abort.

Definition foo(a b: word): word := a ^+ b.

Lemma test: forall a b, foo a b = foo b a.
Proof. unfold foo. intros. ring. Qed.

About test.
(* test : forall a b : word, foo a b = foo b a *)

End LiveVerif.

About test.
(*
test :
forall
  {word : word
            (BinNums.Zpos
               (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO BinNums.xH))))))},
word.ok word -> forall a b : word, foo a b = foo b a
 *)
