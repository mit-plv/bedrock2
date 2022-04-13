Require Import Coq.ZArith.BinInt.
Require Import Coq.Init.Byte.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Tactics.rewr.
Require Import coqutil.Map.Interface.
Require Import bedrock2.SepAuto.
Require Import bedrock2.Array.
Require Import bedrock2.groundcbv.
Require Import bedrock2.TransferSepsOrder.
Require Import bedrock2.SepCalls.

Section SepLog.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma array_app{E : Type}{elem: sep_predicate mem E}{sz: Z}:
    forall (xs ys: list E) (start : word),
      (start :-> xs ++ ys : array elem (word.of_Z sz)) =
      (sep (start :-> xs : array elem (word.of_Z sz))
           (word.add start (word.of_Z (sz * Z.of_nat (Datatypes.length xs))) :-> ys
             : array elem (word.of_Z sz))).
  Proof.
    intros.
    eapply iff1ToEq.
    etransitivity.
    1: eapply array_append.
    cancel.
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. f_equal.
      destruct width_cases; ZnWords.
    }
    reflexivity.
  Qed.

  Lemma access_elem_in_array: forall a a' E (elem: sep_predicate mem E) sz fullLength,
      0 < sz < 2 ^ width ->
      let i := Z.to_nat (word.unsigned (word.sub a' a) / sz) in
      (word.unsigned (word.sub a' a) mod sz = 0 /\
       (* only here to make sure automation picks the right array *)
       (i < fullLength)%nat) ->
      forall vs vs1 v vs2,
        (* connected with /\ because it needs to be solved by considering both at once *)
        vs = vs1 ++ [v] ++ vs2 /\ List.length vs1 = i ->
        iff1 (a :-> vs : array elem (word.of_Z sz))
             (sep (a' :-> v : elem)
                  (seps [a :-> vs1 : array elem (word.of_Z sz);
                         word.add a (word.of_Z (sz * Z.of_nat (S i))) :-> vs2
                           : array elem (word.of_Z sz)])).
  Proof.
    unfold seps.
    intros. fwd.
    cbn [List.app].
    etransitivity.
    1: eapply array_append.
    cbn [Array.array].
    cancel.
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. rewrite H1p1.
      destruct width_cases; ZnWords.
    }
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. destruct width_cases; ZnWords.
    }
    reflexivity.
  Qed.

  Lemma access_subarray: forall a a' E (elem: sep_predicate mem E) sz n fullLength,
      0 < sz < 2 ^ width ->
      let i := Z.to_nat (word.unsigned (word.sub a' a) / sz) in
      (word.unsigned (word.sub a' a) mod sz = 0 /\
       (* only here to make sure automation picks the right array *)
       (i + n <= fullLength)%nat) ->
      forall vs vs1 vs2 vs3,
        vs = vs1 ++ vs2 ++ vs3 /\ List.length vs1 = i /\ List.length vs2 = n ->
        iff1 (a :-> vs : array elem (word.of_Z sz))
             (sep (a' :-> vs2 : array elem (word.of_Z sz))
                  (seps [a :-> vs1 : array elem (word.of_Z sz);
                         word.add a (word.of_Z (sz * Z.of_nat (i + n))) :-> vs3
                           : array elem (word.of_Z sz)])).
  Proof.
    intros.
    unfold seps.
    intros. fwd.
    rewrite 2array_append.
    cancel.
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. rewrite H1p1.
      destruct width_cases; ZnWords.
    }
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. destruct width_cases; ZnWords.
    }
    reflexivity.
  Qed.

  Lemma access_suffix: forall a a' E (elem: sep_predicate mem E) sz lenPrefix,
      0 < sz < 2 ^ width ->
      word.sub a' a = word.mul (word.of_Z sz) (word.of_Z (Z.of_nat lenPrefix)) ->
      forall vs vs1 vs2,
        vs = vs1 ++ vs2 /\ List.length vs1 = lenPrefix ->
        iff1 (a :-> vs : array elem (word.of_Z sz))
             (sep (a' :-> vs2 : array elem (word.of_Z sz))
                  (seps [a :-> vs1 : array elem (word.of_Z sz)])).
  Proof.
    intros. intros. fwd.
    rewrite array_app. cbn [seps].
    cancel. cbn [seps].
    match goal with
    | |- iff1 (?x :-> _ : _) _ => replace x with a'
    end.
    1: reflexivity.
    destruct width_cases; ZnWords.
  Qed.

  Lemma access_tail: forall a a' E (elem: sep_predicate mem E) sz,
      0 < sz < 2 ^ width ->
      word.sub a' a = word.of_Z sz ->
      forall v vs,
        iff1 (a :-> List.cons v vs : array elem (word.of_Z sz))
             (sep (a' :-> vs : array elem (word.of_Z sz))
                  (seps [a :-> v : elem])).
  Proof.
    intros. intros. cbn.
    cancel. cbn [seps].
    match goal with
    | |- iff1 (Array.array _ _ ?x _) _ => replace x with a'
    end.
    1: reflexivity.
    destruct width_cases; ZnWords.
  Qed.
End SepLog.


Ltac destruct_bool_vars :=
  repeat match goal with
         | H: context[if ?b then _ else _] |- _ =>
             is_var b; let t := type of b in constr_eq t bool; destruct b
         end.

Ltac concrete_list_length l :=
  lazymatch l with
  | cons ?h ?t => let r := concrete_list_length t in constr:(S r)
  | nil => constr:(O)
  | List.app ?l1 ?l2 =>
      let r1 := concrete_list_length l1 in
      let r2 := concrete_list_length l2 in
      let r := eval cbv in (r1 + r2)%nat in constr:(r)
  | List.map _ ?l' => concrete_list_length l'
  | List.unfoldn _ ?n _ =>
      let n' := groundcbv n in
      lazymatch isnatcst n' with
      | true => constr:(n')
      end
  | _ => let l' := eval unfold l in l in concrete_list_length l'
  end.

Ltac rewr_with_eq e :=
  lazymatch type of e with
  | ?LHS = _ => progress (pattern LHS; eapply rew_zoom_bw; [exact e|])
  end.

Ltac list_length_simpl_step_in_goal :=
  match goal with
  | |- context[@List.length ?T ?l] =>
      let n := concrete_list_length l in change (@List.length T l) with n
  | |- context[List.length (List.skipn ?n ?l)] => rewr_with_eq (List.length_skipn n l)
  | |- context[List.length (List.firstn ?n ?l)] => rewr_with_eq (List.firstn_length n l)
  | |- context[List.length (?l1 ++ ?l2)] => rewr_with_eq (List.app_length l1 l2)
  | |- context[List.length (?h :: ?t)] => rewr_with_eq (List.length_cons h t)
  | |- context[List.length (List.map ?f ?l)] => rewr_with_eq (List.map_length f l)
  | |- context[List.length (List.unfoldn ?step ?n ?start)] =>
      rewr_with_eq (List.length_unfoldn step n start)
  | |- context[List.length (List.repeat ?v ?n)] => rewr_with_eq (List.repeat_length v n)
  end.

Goal forall (l1 l2: list Z) (a: Z),
    a + Z.of_nat (List.length (l1 ++ l2)) =
    Z.of_nat (List.length l1) + Z.of_nat (List.length l2) + a.
Proof.
  intros. list_length_simpl_step_in_goal.
Abort.

(* Only rewrites below the line, because rewriting above the line should already
   have been done (or will be done later), but the goal below the line might be the
   sidecondition of another rewrite lemma that's being tried and thus did not yet
   appear anywhere in the context before.
   For example, trying to rewrite with List.firstn_all2 creates a sidecondition
   containing a (List.length l) that did not yet have any chance to get
   simplified.
   For efficiency, we only use rewrite lemmas here that don't have sideconditions
   themselves, and use the simplest possible homemade rewr_with_eq to avoid any
   unexpected performance pitfalls of Coq's existing rewrite tactics. *)
Ltac list_length_rewrites_without_sideconds_in_goal :=
  repeat list_length_simpl_step_in_goal.

Ltac listZnWords :=
  destruct_bool_vars;
  unfold List.upd, List.upds;
  list_length_rewrites_without_sideconds_in_goal;
  ZnWords.

Section WithA.
  Context {A: Type}.

  Lemma list_expose_nth{inhA: inhabited A}: forall (vs: list A) i,
      (i < List.length vs)%nat ->
      vs = List.firstn i vs ++ [List.nth i vs default] ++ List.skipn (S i) vs /\
        List.length (List.firstn i vs) = i.
  Proof.
    intros. rewrite List.firstn_nth_skipn by assumption.
    rewrite List.firstn_length_le by Lia.lia. auto.
  Qed.

  Lemma list_expose_subarray: forall (vs: list A) i n,
      (i + n <= List.length vs)%nat ->
      vs = List.firstn i vs ++ List.firstn n (List.skipn i vs) ++ List.skipn (i + n) vs /\
        List.length (List.firstn i vs) = i /\
        List.length (List.firstn n (List.skipn i vs)) = n.
  Proof.
    intros. list_length_rewrites_without_sideconds_in_goal. ssplit; [ | Lia.lia..].
    rewrite <- (List.firstn_skipn i vs) at 1. f_equal.
    rewrite <- (List.firstn_skipn n (List.skipn i vs)) at 1. f_equal.
    rewrite List.skipn_skipn. f_equal. apply Nat.add_comm.
  Qed.
End WithA.

Notation word_array := (array Scalars.scalar (word.of_Z 4)).

Ltac concrete_sz_bounds :=
  lazymatch goal with
  | |- 0 < ?sz < 2 ^ ?width =>
      lazymatch isZcst sz with
      | true => lazymatch isZcst width with
                | true => split; reflexivity
                end
      end
  end.

(* Hints in three different DBs indicating how to find the rewrite lemma,
   how to solve its sideconditions for the split direction, and how to solve its
   sideconditions for the merge direction: *)

(* split_sepclause_goal: *)

#[export] Hint Extern 1
  (split_sepclause (?a :-> ?vsAll : array ?elem (word.of_Z ?sz)) (?a' :-> _ : ?elem) _ _) =>
  unshelve (epose proof (access_elem_in_array a a' _ elem sz (List.length vsAll) _ _));
  [ concrete_sz_bounds | listZnWords | shelve ]
: split_sepclause_goal.

#[export] Hint Extern 1
  (split_sepclause (?a :-> ?vsAll : array ?elem (word.of_Z ?sz))
                   (?a' :-> ?vsPart : array ?elem (word.of_Z ?sz)) _ ?G) =>
  (* most likely, vsPart is still an evar (because it's universally quantified by the
     callee's correctness lemma), so we have to search for its desired length in G,
     but maybe it has a concrete structure (eg [?a; ?b; ?c]), in which case
     concrete_list_length can find that length *)
  let n := match G with
           | _ /\ ?C => match C with context[List.length vsPart = ?n] => n end
           | _ => concrete_list_length vsPart
           end in
  unshelve (epose proof (access_subarray a a' _ elem sz n (List.length vsAll) _ _));
  [ concrete_sz_bounds | listZnWords | shelve ]
: split_sepclause_goal.

#[export] Hint Extern 1 (split_sepclause (?a  :-> ?vs1 ++ ?vs2 : array ?elem (word.of_Z ?sz))
                                         (?a' :-> ?vs2 : array ?elem (word.of_Z ?sz)) _ _) =>
  unshelve (epose proof (access_suffix a a' _ elem sz (List.length vs1) _ _));
  [ concrete_sz_bounds | listZnWords | shelve ]
: split_sepclause_goal.

#[export] Hint Extern 1
  (split_sepclause (?a  :-> (_ :: ?vsTail) : array ?elem (word.of_Z ?sz))
                   (?a' :-> ?vsTail : array ?elem (word.of_Z ?sz)) _ _) =>
  unshelve (epose proof (access_tail a a' _ elem sz _ _));
  [ concrete_sz_bounds | listZnWords | shelve ]
: split_sepclause_goal.


(* split_sepclause_sidecond: *)

#[export] Hint Extern 1 (_ = ?l ++ [_] ++ _ /\ List.length ?l = _) =>
  eapply list_expose_nth; listZnWords
: split_sepclause_sidecond.

#[export] Hint Extern 1
 (_ = ?l1 ++ ?l2 ++ ?l3 /\ List.length ?l1 = _ /\ List.length ?l2 = _) =>
  eapply list_expose_subarray; listZnWords
: split_sepclause_sidecond.


(* merge_sepclause_sidecond: *)

#[export] Hint Extern 1 (@eq (list _) ?listL ?listR /\ @eq nat ?lenL ?lenR) =>
  assert_fails (has_evar lenL);
  assert_fails (has_evar lenR);
  is_evar listL; split; [ reflexivity | listZnWords ]
: merge_sepclause_sidecond.

(* TODO make more generic *)
#[export] Hint Extern 1 (?listL = ?listR1 ++ ?listR2 /\ ?lenR1 = _ /\ ?lenR2 = _) =>
  apply_in_hyps @map.getmany_of_list_length; rewrite List.length_unfoldn in *;
  is_evar listL; split; [ reflexivity | split; listZnWords ]
: merge_sepclause_sidecond.

(* TODO make more generic *)
#[export] Hint Extern 1
  (?listL = ?listR1 ++ ?listR2 ++ ?listR3 /\ ?lenR1 = ?i /\ ?lenR2 = ?n) =>
  apply_in_hyps @map.getmany_of_list_length; rewrite ?List.length_unfoldn in *;
  is_evar listL; split; [ reflexivity | split; listZnWords ]
: merge_sepclause_sidecond.


(* Hints to simplify/cleanup the expressions that were created by repeated
   splitting and merging of sep clauses: *)
#[export] Hint Rewrite
  List.firstn_all2
  List.skipn_all2
  List.firstn_eq_O
  List.skipn_eq_O
  Nat.min_l
  Nat.min_r
using (unfold List.upd, List.upds;
       list_length_rewrites_without_sideconds_in_goal;
       ZnWords)
: fwd_rewrites.
