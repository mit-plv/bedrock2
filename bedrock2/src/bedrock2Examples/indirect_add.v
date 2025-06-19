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
Require Import bedrock2.Semantics bedrock2.FE310CSemantics.

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Definition f (a b : word) := word.add (word.add a b) b.

  Instance spec_of_indirect_add : spec_of "indirect_add" :=
    fnspec! "indirect_add" a b c / va Ra vb Rb vc Rc,
    { requires t m := m =* scalar a va * Ra /\ m =* scalar b vb * Rb /\ m =* scalar c vc * Rc;
      ensures t' m' := t=t' /\ m' =* scalar a (word.add vb vc) * Ra }.
  Instance spec_of_indirect_add_twice : spec_of "indirect_add_twice" :=
    fnspec! "indirect_add_twice" a b / va vb R,
    { requires t m := m =* scalar a va * scalar b vb * R;
      ensures t' m' := t=t' /\ m' =* scalar a (f va vb) * scalar b vb * R }.

  Lemma indirect_add_ok : program_logic_goal_for_function! indirect_add.
  Proof. repeat straightline; []; eauto. Qed.

  Lemma indirect_add_twice_ok : program_logic_goal_for_function! indirect_add_twice.
  Proof.
    repeat straightline.
    straightline_call.
    { split; [ecancel_assumption|]. split; ecancel_assumption. }
    repeat straightline.
    straightline_call.
    { split; [ecancel_assumption|]. split; ecancel_assumption. }
    repeat straightline.
    cbv [f]. ecancel_assumption.
  Qed.

  Example link_both : spec_of_indirect_add_twice (map.of_list  (("indirect_add_twice",indirect_add_twice)::("indirect_add",indirect_add)::nil)).
  Proof. auto using indirect_add_twice_ok, indirect_add_ok. Qed.

  (*
  From bedrock2 Require Import ToCString PrintString.
  Goal True. print_string (c_module (("indirect_add_twice",indirect_add_twice)::("indirect_add",indirect_add)::nil)). Abort.
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
    cbv [g]. ecancel_assumption.
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

  Lemma indirect_add_three'_ok : program_logic_goal_for_function! indirect_add_three'.
  Proof.
    repeat straightline.
    (* note: we want to introduce only one variable for stack contents
     * and use it in a all separation-logic facts in the symbolic state *)

    repeat match goal with
           | H : _ |- _ =>
               seprewrite_in_by scalar_of_bytes H
                 ltac:(Lia.lia);
                 let x := fresh "x" in
                 set (word.of_Z _) as x in H; clearbody x; move x at top
           end.
    clear dependent mStack.

    (*
H1 : (scalar a0 x ⋆ (scalar out vout ⋆ R))%sep m2
H2 : (scalar a0 x0 ⋆ (scalar a va ⋆ Ra))%sep m2
H3 : (scalar a0 x1 ⋆ (scalar b vb ⋆ Rb))%sep m2
H4 : (scalar a0 x2 ⋆ (scalar c vc ⋆ Rc))%sep m2
     *)

    straightline_call.
    { split; [exact H1|split]; ecancel_assumption. }

    repeat straightline.
    (*
H15 : (scalar a0 (word.add va vb) ⋆ (scalar out vout ⋆ R))%sep a2
     *)
    (* H15 is an updated version of H1,
       but we really wanted to carry over H2,H3, and H4 as well *)
  Abort.

  (* trying again with non-separating conjunction *)
  Lemma indirect_add_three'_ok : program_logic_goal_for_function! indirect_add_three'.
  Proof.
    do 12 straightline.

    assert (
      id (fun m => (scalar out vout ⋆ R)%sep m /\ (scalar a va ⋆ Ra)%sep m /\  (scalar b vb ⋆ Rb)%sep m /\  (scalar c vc ⋆ Rc)%sep m) m) by (cbv [id]; eauto); clear H1 H2 H3 H4.


    repeat straightline.
    (* note: we want to introduce only one variable for stack contents
     * and use it in a all separation-logic facts in the symbolic state *)

    repeat match goal with
           | H : _ |- _ =>
               seprewrite_in_by scalar_of_bytes H
                 ltac:(Lia.lia);
                 let x := fresh "x" in
                 set (word.of_Z _) as x in H; clearbody x; move x at top
           end.
    clear dependent mStack.

    cbv [id] in *.
    (*
H7 : (scalar a0 x
      ⋆ (fun m : mem =>
         (scalar out vout ⋆ R) m /\
         (scalar a va ⋆ Ra) m /\ (scalar b vb ⋆ Rb) m /\ (scalar c vc ⋆ Rc) m))%sep
       m
     *)
    pose proof H7 as H7'.
    eapply sep_and_r_fwd in H7; destruct H7 as [? H7].
    eapply sep_and_r_fwd in H7; destruct H7 as [? H7].
    eapply sep_and_r_fwd in H7; destruct H7 as [? H7].

    straightline_call.
    { split; [>|split]; ecancel_assumption. }

    repeat straightline.

    (*
H9 : (scalar a0 (word.add va vb)
      ⋆ (fun m : mem =>
         (scalar out vout ⋆ R) m /\
         (scalar a va ⋆ Ra) m /\ (scalar b vb ⋆ Rb) m /\ (scalar c vc ⋆ Rc) m))%sep
       a2
     *)
    rename m into m'.
    rename a2 into m.
    eapply sep_and_r_fwd in H9; destruct H9 as [? H9].
    eapply sep_and_r_fwd in H9; destruct H9 as [? H9].
    eapply sep_and_r_fwd in H9; destruct H9 as [? H9].

    straightline_call.
    { split; [>|split]; try ecancel_assumption. }
    repeat straightline.

    (* casting scalar to bytes for stack deallocation *)
    cbv [scalar truncated_word truncated_scalar] in *.
    set ((LittleEndianList.le_split (bytes_per access_size.word) (word.unsigned (word.add va vb)))) as stackbytes in *.
    extract_ex1_and_emp_in_hyps.
    assert (Datatypes.length stackbytes = 4%nat) by exact eq_refl.
    Import symmetry.
    Local Ltac t := rewrite ?LittleEndianList.length_le_split, ?bytes_per_width_bytes_per_word; cbv [bytes_per_word]; trivial; try discriminate.
    seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) H16 t.
    seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) H16 t.
    repeat straightline; eauto.
    seprewrite_in_by (@Array.array1_iff_eq_of_list_word_at) H16 t.
    extract_ex1_and_emp_in_goal; eauto.
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
  Abort.

End WithParameters.
