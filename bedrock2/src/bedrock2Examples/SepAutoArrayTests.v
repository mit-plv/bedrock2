Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Bitwidth32.
Require Import bedrock2.Array.
Require Import bedrock2.SepAutoArray bedrock2.SepAuto.
Require Import bedrock2.OperatorOverloading. Local Open Scope oo_scope.
Import Coq.Lists.List.ListNotations. Local Open Scope list_scope.
Require Import bedrock2.ListIndexNotations. Local Open Scope list_index_scope.
Require Import bedrock2.SepBulletPoints. Local Open Scope sep_bullets_scope.

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
      word.unsigned n * 2 < 2 ^ 32 /\
      (forall m',
          sep (dst :-> s : array ptsto (word.of_Z 1)) R2 m' ->
          post m') ->
      wp (memmove_call dst src n) m post.

  Context (sample_call: word -> word -> cmd).

  Hypothesis sample_call_correct: forall m a1 n (vs: list word) R (post: mem -> Prop),
      sep (a1 :-> vs : word_array) R m /\
      List.length vs = Z.to_nat (word.unsigned n) /\
      (forall m',
        sep (a1 :-> vs[5 := vs[5] * (word.of_Z (width := 32) 2)] : word_array) R m' ->
        post m') ->
      wp (sample_call a1 n) m post.

  (* even this small example needs higher-than-default printing depth to fully display
     the intermediate goals... *)
  Set Printing Depth 100000.

  Definition sample_call_usage_goal := forall ws R addr m,
      (16 <= List.length ws)%nat ->
      sep (addr :-> ws : word_array) R m ->
      wp (sample_call (word.add addr (word.of_Z (2*4)))
                      (word.of_Z 10))
         m (fun m' => sep
           (addr :-> List.upd ws 7 (List.nth 7 ws default * word.of_Z (width := 32) 2)
                         : word_array) R m').

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
