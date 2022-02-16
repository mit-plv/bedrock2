Require Import bedrock2.SepAuto.
Require Import bedrock2.Array.
Require Import bedrock2.groundcbv.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Tactics.rewr.

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

  Lemma access_elem_in_array: forall a a' E (elem: E -> word -> mem -> Prop) sz,
      0 < sz < 2 ^ width ->
      word.unsigned (word.sub a' a) mod sz = 0 ->
      split_sepclause a (array elem sz) a' elem
        (let i := Z.to_nat (word.unsigned (word.sub a' a) / sz) in
         forall vs vs1 v vs2,
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
    intros. destruct H1. subst vs.
    cbn [List.app].
    symmetry.
    etransitivity.
    1: eapply array_append.
    cbn [Array.array].
    cancel.
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. rewrite H2.
      destruct width_cases; ZnWords.
    }
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. destruct width_cases; ZnWords.
    }
    reflexivity.
  Qed.

  Definition array_alternative{E: Type}(elem: E -> word -> mem -> Prop)(sz: word)(vs: list E)
             (addr: word): mem -> Prop :=
    bedrock2.Array.array (fun a e => elem e a) sz addr vs.

  Lemma access_elem_in_array_alternative: forall a a' E (elem: E -> word -> mem -> Prop) sz,
      word.unsigned (word.sub a' a) mod (word.unsigned sz) = 0 ->
      split_sepclause a (array_alternative elem sz) a' elem
        (let i := Z.to_nat (word.unsigned (word.sub a' a) / (word.unsigned sz)) in
         forall vs vs1 v vs2,
           (* connected with /\ because it needs to be solved by considering both at once *)
           vs = vs1 ++ [v] ++ vs2 /\ List.length vs1 = i ->
           iff1 (seps
              [a |-> array_alternative elem sz vs1;
               a' |-> elem v;
               word.add a (word.mul sz (word.of_Z (Z.of_nat (S i)))) |-> array_alternative elem sz vs2])
            (a |-> array_alternative elem sz vs)).
  Proof.
    unfold split_sepclause.
    unfold array_alternative, at_addr, seps.
    intros. destruct H0. subst vs.
    cbn [List.app].
    symmetry.
    etransitivity.
    1: eapply array_append.
    cbn [Array.array].
    cancel.
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. destruct width_cases; ZnWords.
    }
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. destruct width_cases; ZnWords.
    }
    reflexivity.
  Qed.
End SepLog.

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
End WithA.

Notation word_array := (array scalar 4).

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


(* Three hints in three different DBs indicating how to find the rewrite lemma,
   how to solve its sideconditions for the split direction, and how to solve its
   sideconditions for the merge direction: *)

#[export] Hint Extern 1 (split_sepclause _ (array ?elem ?sz) _ ?elem _) =>
  eapply access_elem_in_array;
  [ lazymatch goal with
    | |- 0 < sz < 2 ^ ?width =>
        lazymatch isZcst sz with
        | true => lazymatch isZcst width with
                  | true => split; reflexivity
                  end
        end
    end
  | destruct_bool_vars; ZnWords ]
: split_sepclause_goal.

#[export] Hint Extern 1 (_ = ?l ++ [_] ++ _ /\ List.length ?l = _) =>
  eapply list_expose_nth;
  destruct_bool_vars;
  list_length_rewrites_without_sideconds_in_goal;
  ZnWords
: split_sepclause_sidecond.

#[export] Hint Extern 1 (@eq (list _) ?listL ?listR /\ @eq nat ?lenL ?lenR) =>
  assert_fails (has_evar lenL);
  assert_fails (has_evar lenR);
  is_evar listL; split;
  [ reflexivity
  | destruct_bool_vars; list_length_rewrites_without_sideconds_in_goal; ZnWords ]
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
