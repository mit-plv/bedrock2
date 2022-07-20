Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Bitwidth32.
Require Import bedrock2.Array.
Require Import bedrock2.SepCalls bedrock2.SepAutoArray bedrock2.SepAuto.
Require Import bedrock2.TransferSepsOrder.
Require Import coqutil.Map.Interface.
Require Import coqutil.Datatypes.OperatorOverloading bedrock2.OperatorOverloading.
Local Open Scope oo_scope.
Local Open Scope conversion_parse_scope. Local Open Scope conversion_print_scope.
Require Import bedrock2.ListIndexNotations. Local Open Scope list_index_scope.
Require Import bedrock2.SepBulletPoints. Local Open Scope sep_bullets_scope.
Close Scope list_scope. Close Scope Z_scope. (* TODO *)

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Add Ring wring : (Properties.word.ring_theory (word := word))
        ((*This preprocessing is too expensive to be always run, especially if
           we do many ring_simplify in a sequence, in which case it's sufficient
           to run it once before the ring_simplify sequence.
           preprocess [autorewrite with rew_word_morphism],*)
         morphism (Properties.word.ring_morph (word := word)),
         constants [Properties.word_cst]).

  Context (cmd: Type).
  Context (wp: cmd -> mem -> (mem -> Prop) -> Prop).

  Context (memmove_call: forall dst src n: word, cmd).

  Hypothesis memmove_ok: forall m (dst src n: word) s d R1 R2 (post: mem -> Prop),
      sep (src :-> s : array ptsto (word.of_Z 1)) R1 m /\
      sep (dst :-> d : array ptsto (word.of_Z 1)) R2 m /\
      List.length s = Z.to_nat (word.unsigned n) /\
      List.length d = Z.to_nat (word.unsigned n) /\
      Z.lt (word.unsigned n * 2) (2 ^ 32) /\ (* TODO inequalities and number literals *)
      (forall m',
          sep (dst :-> s : array ptsto (word.of_Z 1)) R2 m' ->
          post m') ->
      wp (memmove_call dst src n) m post.

  Hint Rewrite Z.div_1_r Nat2Z.id : fwd_rewrites.

  Lemma memmove_usage_correct: forall (n p: nat) addr (vs: list byte) R m,
      List.length vs = (p + n + p + n + p)%nat ->
      (* if p=0, sep disjointness only implies <= but not <, but do we need < ? *)
      Z.lt (Z.of_nat (List.length vs) * 2) (2 ^ 32) ->
      sep (addr :-> vs : array ptsto (word.of_Z 1)) R m ->
      wp (memmove_call (word.add addr (word.of_Z (Z.of_nat p)))
                       (word.add addr (word.of_Z (Z.of_nat (p + n + p))))
                       (word.of_Z (Z.of_nat n)))
         m (fun m' => sep
           (addr :-> vs[p := vs[p + n + p :][:n]] : array ptsto (word.of_Z 1)) R m').
  Proof.
    intros.
    (* apply call lemma *)
    eapply memmove_ok.
    (* precondition #1 (separation logic assertion for src) *)
    scancel_asm.
      (* Currently manual hint: We will only need merging for dst, but not for src, so
         we can remove the split/merge that was posed *)
      clear_split_sepclause_stack.
    (* precondition #2 (separation logic assertion for dst) *)
    scancel_asm.
    (* precondition #3 (length of src) *)
    split; [listZnWords| ].
    (* precondition #4 (length of dst) *)
    split; [listZnWords| ].
    (* precondition #5 (bounds) *)
    split; [ZnWords| ].
    (* introduce postcondition and prettify *)
    intro_new_mem.
    transfer_sep_order. (* also clears old mem hyps and renames mem *)
    list_simpl_in_hyps.
    (* prove that computed state implies final postcondition *)
    list_simpl_in_goal.
    replace (n + p)%nat with (p + n)%nat at 1 by lia. (* TODO canonicalization for nat *)
    scancel_asm.
  Qed.

  Context (sample_call: word -> word -> cmd).

  Hypothesis sample_call_correct:
    forall (m : mem) (a1 n : word) (vs: list word) (R post: mem -> Prop),
      sep (a1 :-> vs : word_array) R m /\
      List.length vs = Z.to_nat (word.unsigned n) /\
      (forall m':mem,
        sep (a1 :-> vs[5 := vs[5] * (word.of_Z (word := word) 2)] : word_array) R m' ->
        post m') ->
      wp (sample_call a1 n) m post.

  (* even this small example needs higher-than-default printing depth to fully display
     the intermediate goals... *)
  Set Printing Depth 100000.

  Definition sample_call_usage_goal :=
    forall (ws: list word) (R: mem -> Prop) (addr: word) (m: mem),
      (16 <= List.length ws)%nat ->
      (addr --> ws * R) m ->
      wp (sample_call (addr + (2 * 4) to word) (10 to word))
         m (fun m' => (addr --> ws[7 := ws[7] * 2 to word] * R) m').

  Lemma use_sample_call_with_tactics_unfolded: sample_call_usage_goal.
  Proof.
    unfold sample_call_usage_goal. intros.
    eapply sample_call_correct.

    (* prove precondition and after intro-ing postcondition, merge back with same lemma
       as used for proving precondition: *)
    use_sep_asm.
    split_ith_left_and_cancel_with_fst_right 0%nat.
    finish_impl_ecancel.
    split. 1: listZnWords.
    intros m' HM'.
    pop_split_sepclause_stack_step m'.
    list_simpl_in_hyps.
    list_simpl_in_goal.
    scancel_asm.
  Qed.

  Lemma use_sample_call_automated: sample_call_usage_goal.
  Proof.
    unfold sample_call_usage_goal. intros.
    eapply sample_call_correct.
    scancel_asm. split. 1: listZnWords.
    intro_new_mem.
    list_simpl_in_hyps.
    list_simpl_in_goal.
    scancel_asm.
  Qed.
End WithParameters.
