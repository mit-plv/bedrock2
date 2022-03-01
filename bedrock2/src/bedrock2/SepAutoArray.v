Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
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

  Lemma with_len_eq[V: Type]: forall (array_pred: list V -> word -> mem -> Prop) vs n,
      List.length vs = n ->
      with_len n array_pred vs = array_pred vs.
  Proof.
    intros. unfold with_len, with_pure, at_addr. extensionality a.
    replace (List.length vs = n) with True.
    - eapply iff1ToEq. cancel.
    - apply propositional_extensionality. split; auto.
  Qed.

  Lemma extract_pure: forall (P: Prop) (R1 R2: mem -> Prop) m,
      sep (with_pure R1 P) R2 m -> P.
  Proof.
    unfold with_pure, sep, emp. intros. fwd. assumption.
  Qed.

  Lemma extract_with_len[V: Type]:
    forall [array_pred: list V -> word -> mem -> Prop] [vs n m R a],
      sep (a |-> with_len n array_pred vs) R m -> List.length vs = n.
  Proof.
    intros. eapply extract_pure in H. exact H.
  Qed.

  (* There's some tradeoff in the choice whether sz should be a Z or a word:
     If it's a Z, lemmas need an explicit sidecondition to upper-bound it,
     which we get for free if it's a word, but then we need to convert it
     back to Z in many places, so when lemmas are used with sz := (word.of_Z n),
     we'll have to rewrite many occurrences of (word.unsigned (word.of_Z n))
     into n, which seems more expensive than simply proving the sidecondition. *)

  Definition array{E: Type}(elem: E -> word -> mem -> Prop)(sz: Z)(vs: list E)
             (addr: word): mem -> Prop :=
    bedrock2.Array.array (fun a e => elem e a) (word.of_Z sz) addr vs.

  Lemma array_app{E : Type}{elem: E -> word ->  mem -> Prop}{sz: Z}:
    forall (xs ys: list E) (start : word),
      (start |-> array elem sz (xs ++ ys)) =
      (sep (start |-> array elem sz xs)
           (word.add start (word.of_Z (sz * Z.of_nat (Datatypes.length xs))) |->
               array elem sz ys)).
  Proof.
    unfold array, at_addr.
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

  Lemma access_subarray_stmt: forall a a' E (elem: E -> word -> mem -> Prop) sz n,
      0 < sz < 2 ^ width ->
      word.unsigned (word.sub a' a) mod sz = 0 ->
      let i := Z.to_nat (word.unsigned (word.sub a' a) / sz) in
      (forall vs vs1 vs2 vs3,
          vs = vs1 ++ vs2 ++ vs3 /\ List.length vs1 = i /\ List.length vs2 = n ->
           iff1 (seps
              [a |-> array elem sz vs1;
               a' |-> array elem sz vs2;
               word.add a (word.of_Z (sz * Z.of_nat (i + n))) |->
                        array elem sz vs3])
            (a |-> array elem sz vs)).
  Proof.
    intros.
    unfold array, at_addr, seps.
    intros. fwd.
    symmetry.
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

  (* used when the length of vsPart can be computed with concrete_length *)
  Lemma access_subarray_concrete_length: forall a a' E (elem: E -> word -> mem -> Prop) sz n
                                                vsAll vsPart,
      0 < sz < 2 ^ width ->
      word.unsigned (word.sub a' a) mod sz = 0 ->
      let i := Z.to_nat (word.unsigned (word.sub a' a) / sz) in
      (* only here to make sure automation picks the right array *)
      (i + n <= List.length vsAll)%nat ->
      split_sepclause (a |-> array elem sz vsAll)
                      (a' |-> array elem sz vsPart)
        (forall vs vs1 vs2 vs3,
           vs = vs1 ++ vs2 ++ vs3 /\ List.length vs1 = i /\ List.length vs2 = n ->
           iff1 (seps
              [a |-> array elem sz vs1;
               a' |-> array elem sz vs2;
               word.add a (word.of_Z (sz * Z.of_nat (i + n))) |->
                        array elem sz vs3])
            (a |-> array elem sz vs)).
  Proof.
    intros. unfold split_sepclause. intros. eapply access_subarray_stmt; eassumption.
  Qed.

  Lemma access_subarray_with_len: forall a a' E (elem: E -> word -> mem -> Prop) sz n
                                         vsAll vsPart,
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
               word.add a (word.of_Z (sz * Z.of_nat (i + n))) |->
                        array elem sz vs3])
            (a |-> array elem sz vs)).
  Proof.
    intros. unfold split_sepclause. intros.
    unfold with_len, with_pure, at_addr. fwd.
    replace (length vs2 = length vs2) with True. 2: {
      eapply PropExtensionality.propositional_extensionality. split; auto.
    }
    etransitivity.
    2: eapply access_subarray_stmt; eauto.
    unfold at_addr.
    cbn [seps]. ecancel.
  Qed.

  Lemma access_suffix: forall a a' E (elem: E -> word -> _ -> Prop) sz vsPrefix vsSuffix,
      0 < sz < 2 ^ width ->
      word.sub a' a = word.mul (word.of_Z sz)
                               (word.of_Z (Z.of_nat (List.length vsPrefix))) ->
      split_sepclause (a |-> array elem sz (List.app vsPrefix vsSuffix))
                      (a' |-> array elem sz vsSuffix)
        (forall vs vs1 vs2,
           vs = vs1 ++ vs2 /\
           List.length vs1 = List.length vsPrefix /\
           List.length vs2 = List.length vsSuffix ->
           iff1 (seps [a |-> array elem sz vs1; a' |-> array elem sz vs2])
                (a |-> array elem sz vs)).
  Proof.
    intros. unfold split_sepclause. intros. fwd.
    rewrite array_app. cbn [seps].
    cancel. cbn [seps].
    match goal with
    | |- iff1 _ (?x |-> _) => replace x with a'
    end.
    1: reflexivity.
    destruct width_cases; ZnWords.
  Qed.

  Lemma access_tail: forall a a' E (elem: E -> word -> _ -> Prop) sz vH vsTail,
      0 < sz < 2 ^ width ->
      word.sub a' a = word.of_Z sz ->
      split_sepclause (a |-> array elem sz (List.cons vH vsTail))
                      (a' |-> array elem sz vsTail)
        (forall v vs,
           iff1 (seps [a |-> elem v; a' |-> array elem sz vs])
                (a |-> array elem sz (List.cons v vs))).
  Proof.
    intros. unfold split_sepclause. intros. unfold at_addr, array. cbn.
    cancel. cbn [seps].
    match goal with
    | |- iff1 _ (Array.array _ _ ?x _) => replace x with a'
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

Notation word_array := (array scalar 4).

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

#[export] Hint Extern 1 (split_sepclause (_ |-> array ?elem ?sz _) (_ |-> ?elem _) _) =>
  eapply access_elem_in_array; [ concrete_sz_bounds | listZnWords | listZnWords ]
: split_sepclause_goal.

#[export] Hint Extern 1
  (split_sepclause (?a |-> array ?elem ?sz ?vsAll)
                   (?a' |-> with_len ?n (array ?elem ?sz) ?vsPart) _) =>
  eapply (access_subarray_with_len a a' _ elem sz n vsAll vsPart);
  [ concrete_sz_bounds | listZnWords | listZnWords ]
: split_sepclause_goal.

#[export] Hint Extern 1
  (split_sepclause (?a |-> array ?elem ?sz ?vsAll) (?a' |-> array ?elem ?sz ?vsPart) _) =>
  let n := concrete_list_length vsPart in
  eapply (access_subarray_concrete_length a a' _ elem sz n vsAll vsPart);
  [ concrete_sz_bounds | listZnWords | listZnWords ]
: split_sepclause_goal.

#[export] Hint Extern 1 (split_sepclause (_ |-> array ?elem ?sz (?vs1 ++ ?vs2))
                                         (_ |-> array ?elem ?sz ?vs2) _) =>
  eapply access_suffix; [ concrete_sz_bounds | listZnWords ]
: split_sepclause_goal.

#[export] Hint Extern 1 (split_sepclause (_ |-> array ?elem ?sz (_ :: ?vsTail))
                                         (_ |-> array ?elem ?sz ?vsTail) _) =>
  eapply access_tail; [ concrete_sz_bounds | listZnWords ]
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
  apply_in_hyps @map.getmany_of_list_length; rewrite List.length_unfoldn in *;
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
