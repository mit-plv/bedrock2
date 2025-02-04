Require Import bedrock2.NotationsCustomEntry.

Import Syntax Syntax.Coercions BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition indirect_add := func! (a, b, c) {
  store(a, load(b) + load(c))
}.

Definition indirect_add_twice := func! (a, b) {
  indirect_add(a, a, b);
  indirect_add(a, a, b)
}.

Require Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Interface coqutil.Map.Interface bedrock2.Map.SeparationLogic.
Require Import coqutil.Tactics.fwd.
Require Import bedrock2.Map.DisjointUnion.
Require Import bedrock2.HeapletwiseHyps.
Require Import bedrock2.enable_frame_trick.
Require Import bedrock2.PurifySep.
Require Import bedrock2.Semantics bedrock2.FE310CSemantics.
Require Import coqutil.Macros.WithBaseName.

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars bedrock2.Array.

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Definition f (a b : word) := word.add (word.add a b) b.

  Instance spec_of_indirect_add : spec_of "indirect_add" :=
    fnspec! "indirect_add" a b c / va Ra vb Rb vc Rc,
    { requires t m :=
        m =* scalar b vb * Rb /\
        m =* scalar c vc * Rc /\
        (* Note: the surviving frame needs to go last for heapletwise callers to work! *)
        m =* scalar a va * Ra;
      ensures t' m' :=
        t = t' /\
        m' =* scalar a (word.add vb vc) * Ra }.
  Instance spec_of_indirect_add_twice : spec_of "indirect_add_twice" :=
    fnspec! "indirect_add_twice" a b / va vb R,
    { requires t m := m =* scalar a va * scalar b vb * R;
      ensures t' m' := t=t' /\ m' =* scalar a (f va vb) * scalar b vb * R }.

  Lemma indirect_add_ok : program_logic_goal_for_function! indirect_add.
  Proof.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    straightline.
    repeat straightline.
    eauto.
    Qed.

  Lemma indirect_add_twice_ok : program_logic_goal_for_function! indirect_add_twice.
  Proof.
    repeat straightline.
    straightline_call.
    { split; [ecancel_assumption|]. split; ecancel_assumption. }
    repeat straightline.
    straightline_call.
    { split; [ecancel_assumption|]. split; ecancel_assumption. }
    repeat straightline.
    { cbv [f]. ecancel_assumption. }
  Qed.

  Example link_both : spec_of_indirect_add_twice
                        (map.of_list &[,indirect_add_twice; indirect_add]).
  Proof. auto using indirect_add_twice_ok, indirect_add_ok. Qed.

  (*
  Require Import bedrock2.ToCString bedrock2.PrintString.
  Goal True. print_string (c_module &[,indirect_add_twice; indirect_add]). Abort.
  *)

  Definition indirect_add_three := func! (a, b, c) {
    indirect_add(a, a, b);
    indirect_add(a, a, c)
  }.

  Definition g (a b c : word) := word.add (word.add a b) c.
  Instance spec_of_indirect_add_three : spec_of "indirect_add_three" :=
    fnspec! "indirect_add_three" a b c / va vb vc Rb R,
    { requires t m := m =* scalar a va * scalar c vc * R /\ m =* scalar b vb * Rb;
      ensures t' m' := t=t' /\ m' =* scalar a (g va vb vc) * scalar c vc * R }.

  Lemma indirect_add_three_ok : program_logic_goal_for_function! indirect_add_three.
  Proof.
    repeat straightline.
    straightline_call.
    { split; [ecancel_assumption|]. split; ecancel_assumption. }
    repeat straightline.
    straightline_call.
    { split; [ecancel_assumption|]. split; ecancel_assumption. }
    repeat straightline.
    { cbv [g]. ecancel_assumption. }
  Qed.

  Definition indirect_add_three' := func! (out, a, b, c) {
    stackalloc 4 as v;
    indirect_add(v, a, b);
    indirect_add(out, v, c)
  }.

  Instance spec_of_indirect_add_three' : spec_of "indirect_add_three'" :=
    fnspec! "indirect_add_three'" out a b c / vout va vb vc Ra Rb Rc R,
    { requires t m :=
        m =* scalar out vout * R /\
        m =* scalar a va * Ra /\
        m =* scalar b vb * Rb /\
        m =* scalar c vc * Rc;
      ensures t' m' := t=t' /\ m' =* scalar out (g va vb vc) * R }.

  Require Import coqutil.Tactics.Tactics.
  Lemma indirect_add_three'_ok : program_logic_goal_for_function! indirect_add_three'.
  Proof.
    repeat straightline.

    (* note: we want to introduce only one variable for stack contents
     * and use it in a all separation-logic facts in the symbolic state *)

    Import symmetry.
    repeat match goal with
           | H : _ |- _ =>
               seprewrite_in_by (symmetry! @Array.bytarray_as_bytes) H Lia.lia;
               seprewrite_in_by scalar_of_bytes H
                 ltac:(Lia.lia);
                 let x := fresh "x" in
                 set (word.of_Z _) as x in H; clearbody x; move x at top
           end.
    clear dependent m.

    (*
H1 : (scalar a0 x ⋆ (scalar out vout ⋆ R))%sep m2
H2 : (scalar a0 x0 ⋆ (scalar a va ⋆ Ra))%sep m2
H3 : (scalar a0 x1 ⋆ (scalar b vb ⋆ Rb))%sep m2
H4 : (scalar a0 x2 ⋆ (scalar c vc ⋆ Rc))%sep m2
     *)

    straightline_call.
    { split; [ecancel_assumption|].
      split; [ecancel_assumption|].
      exact H1. }

    repeat straightline.
    (*
H15 : (scalar a0 (word.add va vb) ⋆ (scalar out vout ⋆ R))%sep a2
     *)
    (* H15 is an updated version of H1,
       but we really wanted to carry over H2,H3, and H4 as well *)
  Abort.

  (*
  Lemma anybytes4_to_scalar: forall a (m: mem),
      anybytes a 4 m -> exists v, with_mem m (scalar a v).
  Proof.
    intros.
    eapply anybytes_to_array_1 in H. fwd.
    eapply scalar_of_bytes in Hp0. 2: rewrite Hp1; reflexivity.
    eauto.
  Qed.

  Lemma scalar_to_anybytes4: forall a (m: mem) v,
      scalar a v m -> anybytes a 4 m.
  Proof.
    intros. eapply scalar_to_anybytes in H. exact H.
  Qed.

  Lemma sep_call: forall funs f t m args
      (calleePre: Prop)
      (calleePost callerPost: trace -> mem -> list word -> Prop),
      (* definition-site format: *)
      (calleePre -> WeakestPrecondition.call funs f t m args calleePost) ->
      (* use-site format: *)
      (calleePre /\ enable_frame_trick
                      (forall t' m' rets, calleePost t' m' rets -> callerPost t' m' rets)) ->
      (* conclusion: *)
      WeakestPrecondition.call funs f t m args callerPost.
  Proof.
    intros. destruct H0. eapply WeakestPreconditionProperties.Proper_call; eauto.
  Qed.

  Lemma purify_scalar: forall (a v: word), purify (scalar a v) True.
  Proof. unfold purify. intros. constructor. Qed.
  Hint Resolve purify_scalar: purify.

  Ltac straightline_stackalloc ::=
    lazymatch goal with
    | Ha : anybytes _ _ ?mStack, Hs : map.split ?mCombined ?m ?mStack |- _ =>
        eapply split_du in Hs
    end.

  Ltac straightline_stackdealloc ::= fail.

  Ltac straightline_call ::=
    lazymatch goal with
    | |- WeakestPrecondition.call ?functions ?callee _ _ _ _ =>
        let callee_spec := lazymatch constr:(_:spec_of callee) with ?s => s end in
        let Hcall := lazymatch goal with H: callee_spec functions |- _ => H end in
        eapply sep_call; [ eapply Hcall | ]
    end.

  Ltac same_pred_and_addr P Q ::=
    lazymatch P with
    | ?pred ?addr ?val1 =>
        lazymatch Q with
        | pred addr ?val2 => idtac
        end
    end.

  Ltac step := first [ heapletwise_step | straightline ].

  (* trying again with non-separating conjunction *)
  Lemma indirect_add_three'_ok : program_logic_goal_for_function! indirect_add_three'.
  Proof.
    repeat step.
    lazymatch goal with
    | H: anybytes _ _ _ |- _ => eapply anybytes4_to_scalar in H; destruct H as (? & H)
    end.
(*
mCombined is the full memory, and its first split into mStack and the rest is unique,
but that rest can be split in 4 different ways:
  H3 : m0 |= scalar out vout
  H4 : m1 |= R
  H5 : m2 |= scalar a va
  H6 : m3 |= Ra
  H2 : m6 |= scalar b vb
  H9 : m7 |= Rb
  H7 : m4 |= scalar c vc
  H8 : m5 |= Rc
  H1 : mStack |= scalar a0 x
  H10 : (((m4 \*/ m5) \=/ (m6 \*/ m7)) \=/ ((m2 \*/ m3) \=/ (m0 \*/ m1))) \*/ mStack =
        mCombined
*)
    straightline_call.

    step. step. step. (* <-- note how this canceling step discards all aliased memory:
       ((((m4 \*/ m5) \=/ (m6 \*/ m7)) \=/ ((m2 \*/ m3) \=/ (m0 \*/ m1))) \*/ mStack)
       becomes
       (m3 \*/ mStack) *)
    step. step. step. step. step. step. step. step. step. step. step.
    repeat step.
    straightline_call.
    repeat step.
    match goal with
    | H: with_mem _ (scalar _ (word.add va vb)) |- _ => eapply scalar_to_anybytes4 in H
    end.
    (* TODO automate *)
    rename D0 into Di.
    rewrite (mmap.du_comm m9 m1) in Di.
    rewrite <- mmap.du_assoc in Di.
    pose proof Di as Dii.
    unfold mmap.du in Di at 1. fwd.
    do 2 eexists.
    split; [eassumption | ].
    split. {
      eapply split_du. simpl. eassumption.
    }
    clear Di.
    repeat step.
    unfold g.
    repeat step.
  Qed.

  (* let's see how this would look like with an alternate spec of [indirect_add] *)

  Remove Hints spec_of_indirect_add : typeclass_instances.
  Instance spec_of_indirect_add_gen : spec_of "indirect_add" :=
    fnspec! "indirect_add" a b c / va Ra vb Rb vc Rc,
    { requires t m := m =* scalar a va * Ra /\ m =* scalar b vb * Rb /\ m =* scalar c vc * Rc;
      ensures t' m' := t=t' /\
        forall va Ra, m =* scalar a va * Ra -> m' =* scalar a (word.add vb vc) * Ra }.

  Lemma indirect_add_gen_ok : program_logic_goal_for_function! indirect_add.
  Proof.
    repeat straightline.
    (* This goal is unprovable as shown.
       It could be made provable by revealing how the memory was updated
         by modifying the straightline rule for store.
       I don't know how I would do this systematically for non-leaf functions, though. *)
 Abort.

  (* an potential alternative to changing this spec would be to
     - prove  wp.call (post:=p) /\ wp.call(post=q) -> wp.call (post:=p/\q)
     - instantiate the spec of indirect_add multiple times at the call site
       (existentials in postcondition are duplicated for each instantiation)
     but for now, let's prototype with changed spec:
  *)

  Lemma indirect_add_three'_ok' : program_logic_goal_for_function! indirect_add_three'.
  Proof.
    repeat straightline.
    (* note: we want to introduce only one variable for stack contents
     * and use it in a all separation-logic facts in the symbolic state.
     * here we get away with doing it wrong anyway. *)

    repeat match goal with
           | H : _ |- _ =>
               seprewrite_in_by scalar_of_bytes H
                 ltac:(Lia.lia);
                 let x := fresh "x" in
                 set (word.of_Z _) as x in H; clearbody x; move x at top
           end.
    clear dependent mStack.

    straightline_call.
    (*
    { split; [exact H1|split]; ecancel_assumption. }
    repeat straightline.
    rename a2 into m.
    (*
H15 : forall (va0 : word) (Ra : mem -> Prop),
      (scalar a0 va0 ⋆ Ra)%sep m2 -> (scalar a0 (word.add va vb) ⋆ Ra)%sep m
     *)
    eapply H15 in H1.
    eapply H15 in H2.
    eapply H15 in H3.
    eapply H15 in H4.
    clear H15.

    straightline_call.
    { split; [>|split]; try ecancel_assumption. }
    repeat straightline.
    rename a3 into m'.
    (*
H15 : forall (va0 : word) (Ra : mem -> Prop),
      (scalar out va0 ⋆ Ra)%sep m ->
      (scalar out (word.add (word.add va vb) vc) ⋆ Ra)%sep m'
     *)
    specialize (H15 _ _ ltac:(ecancel_assumption)).

    (* unrelated: stack deallocation proof, would need scalar-to-bytes lemma *)
    *)
  Abort.

    *)
End WithParameters.
