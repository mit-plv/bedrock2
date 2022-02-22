Require Import bedrock2.SepAuto.
Require Import bedrock2.Array.
Require Import bedrock2.groundcbv.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Tactics.rewr.

Definition with_len{width}{word: word width}{mem: map.map word byte}{V: Type}
  (n: nat)(array_pred: list V -> word -> mem -> Prop)(vs: list V)(a: word): mem -> Prop :=
  with_pure (a |-> array_pred vs) (List.length vs = n).

Section SepLog.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  (* There's some tradeoff in the choice whether sz should be a Z or a word:
     If it's a Z, lemmas need an explicit sidecondition to upper-bound it,
     which we get for free if it's a word, but then we need to convert it
     back to Z in many places, so when lemmas are used with sz := (word.of_Z n),
     we'll have to rewrite many occurrences of (word.unsigned (word.of_Z n))
     into n, which seems more expensive than simply proving the sidecondition. *)

  Definition array{E: Type}(elem: E -> word -> mem -> Prop)(sz: Z)(vs: list E)
             (addr: word): mem -> Prop :=
    bedrock2.Array.array (fun a e => elem e a) (word.of_Z sz) addr vs.

  Lemma access_elem_in_array: forall a a' E (elem: E -> word -> mem -> Prop) vsOld vOld sz,
      0 < sz < 2 ^ width ->
      word.unsigned (word.sub a' a) mod sz = 0 ->
      let i := Z.to_nat (word.unsigned (word.sub a' a) / sz) in
      (* only here to make sure automation picks the right array *)
      (i < List.length vsOld)%nat ->
      split_sepclause (a |-> array elem sz vsOld) (a' |-> elem vOld)
        (forall vs vs1 v vs2,
           (* connected with /\ because it needs to be solved by considering both at once *)
           vs = vs1 ++ [v] ++ vs2 /\ List.length vs1 = i ->
           iff1 (seps
              [a |-> array elem sz vs1;
               a' |-> elem v;
               word.add a (word.of_Z (sz * Z.of_nat (S i))) |-> array elem sz vs2])
            (a |-> array elem sz vs)).
  Proof.
    unfold split_sepclause.
    unfold array, at_addr, seps.
    intros. fwd.
    cbn [List.app].
    symmetry.
    etransitivity.
    1: eapply array_append.
    cbn [Array.array].
    cancel.
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. rewrite H2p1.
      destruct width_cases; ZnWords.
    }
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. destruct width_cases; ZnWords.
    }
    reflexivity.
  Qed.

  Lemma access_subarray: forall a a' E (elem: E -> word -> mem -> Prop) sz n vsAll vsPart,
      0 < sz < 2 ^ width ->
      word.unsigned (word.sub a' a) mod sz = 0 ->
      let i := Z.to_nat (word.unsigned (word.sub a' a) / sz) in
      (* only here to make sure automation picks the right array *)
      (i + n <= List.length vsAll)%nat ->
      split_sepclause (a |-> array elem sz vsAll)
                      (a' |-> with_len n (array elem sz) vsPart)
        (forall vs vs1 vs2 vs3,
           vs = vs1 ++ vs2 ++ vs3 /\ List.length vs1 = i /\ List.length vs2 = n ->
           iff1 (seps
              [a |-> array elem sz vs1;
               a' |-> with_len n (array elem sz) vs2;
               word.add a (word.of_Z (sz * Z.of_nat (i + List.length vs2))) |->
                        array elem sz vs3])
            (a |-> array elem sz vs)).
  Proof.
    intros.
    unfold split_sepclause.
    unfold with_len, with_pure, array, at_addr, seps.
    intros. fwd.
    symmetry.
    rewrite 2array_append.
    replace (length vs2 = length vs2) with True. 2: {
      eapply PropExtensionality.propositional_extensionality. split; auto.
    }
    cancel.
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. rewrite H2p1.
      destruct width_cases; ZnWords.
    }
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. destruct width_cases; ZnWords.
    }
    reflexivity.
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

Ltac ZnWordsL :=
  destruct_bool_vars;
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

Notation word_array := (array scalar 4).


(* Hints in three different DBs indicating how to find the rewrite lemma,
   how to solve its sideconditions for the split direction, and how to solve its
   sideconditions for the merge direction: *)

#[export] Hint Extern 1 (split_sepclause (_ |-> array ?elem ?sz _) (_ |-> ?elem _) _) =>
  eapply access_elem_in_array;
  [ lazymatch goal with
    | |- 0 < sz < 2 ^ ?width =>
        lazymatch isZcst sz with
        | true => lazymatch isZcst width with
                  | true => split; reflexivity
                  end
        end
    end
  | ZnWordsL
  | ZnWordsL ]
: split_sepclause_goal.

#[export] Hint Extern 1
  (split_sepclause (?a |-> array ?elem ?sz _) (?a' |-> with_len ?n (array ?elem ?sz) _) _) =>
  eapply (access_subarray a a' _ elem sz n);
  [ lazymatch goal with
    | |- 0 < sz < 2 ^ ?width =>
        lazymatch isZcst sz with
        | true => lazymatch isZcst width with
                  | true => split; reflexivity
                  end
        end
    end
  | ZnWordsL
  | ZnWordsL ]
: split_sepclause_goal.

#[export] Hint Extern 1 (_ = ?l ++ [_] ++ _ /\ List.length ?l = _) =>
  eapply list_expose_nth; ZnWordsL
: split_sepclause_sidecond.

#[export] Hint Extern 1
 (_ = ?l1 ++ ?l2 ++ ?l3 /\ List.length ?l1 = _ /\ List.length ?l2 = _) =>
  eapply list_expose_subarray; ZnWordsL
: split_sepclause_sidecond.

#[export] Hint Extern 1 (@eq (list _) ?listL ?listR /\ @eq nat ?lenL ?lenR) =>
  assert_fails (has_evar lenL);
  assert_fails (has_evar lenR);
  is_evar listL; split; [ reflexivity | ZnWordsL ]
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
using (list_length_rewrites_without_sideconds_in_goal; ZnWords) : fwd_rewrites.
