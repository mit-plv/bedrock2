Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Bitwidth32.
Require Import bedrock2.groundcbv.
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

Ltac word_simpl_step_in_hyps :=
  match goal with
  | H: ?x = ?y |- _ => is_var x; is_var y; subst x
  | H: context[@word.add ?wi ?wo ?x ?y] |- _ =>
      progress (ring_simplify (@word.add wi wo x y) in H)
  | H: context[@word.sub ?wi ?wo ?x ?y] |- _ =>
      progress (ring_simplify (@word.sub wi wo x y) in H)
  | H: context[@word.opp ?wi ?wo ?x   ] |- _ =>
      progress (ring_simplify (@word.opp wi wo x  ) in H)
  | H: context[@word.mul ?wi ?wo ?x ?y] |- _ =>
      progress (ring_simplify (@word.mul wi wo x y) in H)
  | H: context[word.unsigned (word.of_Z _)] |- _ =>
    rewrite word.unsigned_of_Z_nowrap in H by Lia.lia
  | _ => progress groundcbv_in_all
  end.

Ltac word_simpl_step_in_goal :=
  match goal with
  | |- context[@word.add ?wi ?wo ?x ?y] => progress (ring_simplify (@word.add wi wo x y))
  | |- context[@word.sub ?wi ?wo ?x ?y] => progress (ring_simplify (@word.sub wi wo x y))
  | |- context[@word.opp ?wi ?wo ?x   ] => progress (ring_simplify (@word.opp wi wo x  ))
  | |- context[@word.mul ?wi ?wo ?x ?y] => progress (ring_simplify (@word.mul wi wo x y))
  | |- context[word.unsigned (word.of_Z _)] =>
    rewrite word.unsigned_of_Z_nowrap by Lia.lia
  | _ => progress groundcbv_in_goal
  end.

(* makes expressions a bit more complicated by repeating n, but enables detection
   of merge opportunities around ++ *)
#[export] Hint Rewrite List.firstn_skipn_comm : fwd_rewrites.

#[export] Hint Rewrite List.nth_skipn : fwd_rewrites.
#[export] Hint Rewrite List.nth_firstn using lia : fwd_rewrites.

Module List. Section __.
  Context [A: Type].

  (* Rewrite lemmas to merge patterns similar to `xs[i:j] ++ xs[j:k]` into `xs[i:k]`.
     We could normalize everything into `xs[_:_]` form (instead of also allowing `xs[:_]`
     and `xs[_:]`) and insist on writing `xs ++ ys ++ zs ++ []` instead of just
     `xs ++ ys ++ zs`, which would then only require one merging rewrite lemma, but
     then other ad-hoc rewrites might break this form requirement, so we distinguish
     three dimensions along which the rewrite lemma to merge `xs[i:j] ++ xs[j':k]`
     has to vary:
     - On the left, is there only an end index (0) or both a start+end index (1)?
     - On the right, is there only a start index (0) or both a start+end index (1)?
     - Is the right list the last one (0) or is another one appended to it (1)?
     By "is there a start index", we mean "is it wrapped in a List.skipn", and
     by "is there an end index", we mean "is it wrapped in a List.firstn". *)

  Lemma merge_sublist_000: forall j j' (xs: list A),
      j = j' ->
      List.firstn j xs ++ List.skipn j' xs = xs.
  Proof.
    intros. subst j'. apply List.firstn_skipn.
  Qed.

  Lemma merge_sublist_001: forall j j' (xs ys: list A),
      j = j' ->
      List.firstn j xs ++ List.skipn j' xs ++ ys = xs ++ ys.
  Proof.
    intros. subst j'. rewrite List.app_assoc. f_equal. apply List.firstn_skipn.
  Qed.

  Lemma merge_sublist_010: forall j j' k (xs: list A),
      (j = j' /\ j' <= k)%nat ->
      List.firstn j xs ++ List.skipn j' (List.firstn k xs) = List.firstn k xs.
  Proof.
    intros. destruct H as (? & H). subst j'.
    rewrite <- (List.firstn_skipn j (List.firstn k xs)) at 2.
    f_equal. rewrite List.firstn_firstn. f_equal. lia.
  Qed.

  Lemma merge_sublist_011: forall j j' k (xs ys: list A),
      (j = j' /\ j' <= k)%nat ->
      List.firstn j xs ++ List.skipn j' (List.firstn k xs) ++ ys = List.firstn k xs ++ ys.
  Proof.
    intros. rewrite List.app_assoc. f_equal. apply merge_sublist_010. assumption.
  Qed.

  Lemma merge_sublist_100: forall i j j' (xs: list A),
      (i <= j /\ j = j')%nat ->
      List.skipn i (List.firstn j xs) ++ List.skipn j' xs = List.skipn i xs.
  Proof.
    intros. destruct H as (H & ?). subst j'.
    rewrite <- (List.firstn_skipn (j-i) (List.skipn i xs)).
    rewrite List.firstn_skipn_comm.
    rewrite List.skipn_skipn.
    repeat match goal with
           | |- @eq (list _) _ _ => f_equal
           end.
    all: lia.
  Qed.

  Lemma merge_sublist_101: forall i j j' (xs ys: list A),
      (i <= j /\ j = j')%nat ->
      List.skipn i (List.firstn j xs) ++ List.skipn j' xs ++ ys = List.skipn i xs ++ ys.
  Proof.
    intros. rewrite List.app_assoc. f_equal. apply merge_sublist_100. assumption.
  Qed.

  Lemma merge_sublist_110: forall i j j' k (xs: list A),
      (i <= j /\ j = j' /\ j' <= k)%nat ->
      List.skipn i (List.firstn j xs) ++ List.skipn j' (List.firstn k xs) =
        List.skipn i (List.firstn k xs).
  Proof.
    intros. destruct H as (? & ? & ?). subst j'.
    rewrite <- (List.firstn_skipn (j-i) (List.skipn i (List.firstn k xs))).
    rewrite List.firstn_skipn_comm.
    rewrite List.skipn_skipn.
    rewrite List.firstn_firstn.
    repeat match goal with
           | |- @eq (list _) _ _ => f_equal
           end.
    all: lia.
  Qed.

  Lemma merge_sublist_111: forall i j j' k (xs ys: list A),
      (i <= j /\ j = j' /\ j' <= k)%nat ->
      List.skipn i (List.firstn j xs) ++ List.skipn j' (List.firstn k xs) ++ ys =
        List.skipn i (List.firstn k xs) ++ ys.
  Proof.
    intros. rewrite List.app_assoc. f_equal. apply merge_sublist_110. assumption.
  Qed.

  Import List.ListNotations. Local Open Scope list_scope.

  Lemma fold_upd: forall (l: list A) i j v,
      (j = i + 1 /\ i < List.length l)%nat ->
      List.firstn i l ++ [v] ++ List.skipn j l = List.upd l i v.
  Proof.
    intros *. intros (? & ?). subst j. unfold List.upd, List.upds. cbn [List.length].
    f_equal. f_equal.
    - replace (length l - i)%nat with (S (length l - i - 1)) by lia. cbn.
      rewrite List.firstn_nil. reflexivity.
    - f_equal. lia.
  Qed.
End __. End List.

#[export] Hint Rewrite
  List.merge_sublist_000
  List.merge_sublist_001
  List.merge_sublist_010
  List.merge_sublist_011
  List.merge_sublist_100
  List.merge_sublist_101
  List.merge_sublist_110
  List.merge_sublist_111
using lia : fwd_rewrites.

Ltac list_simpl_in_hyps :=
  unfold List.upd, List.upds in *|-;
  repeat (repeat word_simpl_step_in_hyps;
          repeat match goal with
                 | H:_ |- _ => rewrite_db fwd_rewrites in H
                 end);
  repeat match goal with
         | H: _ |- _ => progress rewrite List.fold_upd in H by lia
         end.

Ltac list_simpl_in_goal :=
  unfold List.upd, List.upds;
  repeat (repeat word_simpl_step_in_goal; try rewrite_db fwd_rewrites);
  rewrite ?List.fold_upd by lia.

Ltac list_simpl_in_all := list_simpl_in_hyps; list_simpl_in_goal.

Require Import coqutil.Datatypes.OperatorOverloading.

Section ListRewriterTests.
  Local Open Scope list_index_scope.
  Local Open Scope oo_scope.

  Goal forall [A: Type] {inh: inhabited A}(f: A -> A) ws,
      (16 <= length ws)%nat ->
      ws[:7] ++ [| f ws[7] |] ++ ws[8:] =
        ws[:2] ++ ws[2:][:5] ++ [| f ws[2:][:10][5] |] ++ ws[2:][6:10] ++ ws[12:].
  Proof.
    intros.
    match goal with
    | |- ?G => assert G
    end.
    { list_simpl_in_goal.
      match goal with
      | |- ?x = ?x => reflexivity
      end. }
    { list_simpl_in_all.
      match goal with
      | H: ?A |- ?A => exact H
      end. }
    all: fail.
  Abort.
End ListRewriterTests.

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
