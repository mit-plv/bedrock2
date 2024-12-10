From Coq Require Import ZArith.
From Coq.Init Require Import Byte.
From Coq Require Import Lia.
Require Import coqutil.Word.Bitwidth coqutil.Word.Properties.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Datatypes.ZList.
Require Import coqutil.Datatypes.Inhabited.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.syntactic_unify.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Tactics.fold_hyps.
Require Import coqutil.Datatypes.RecordSetters.
Require Import bedrock2.Lift1Prop bedrock2.Map.Separation bedrock2.Map.DisjointUnion.
Require Import bedrock2.PurifySep.
Require Import bedrock2.SepLib.
Require Import bedrock2.sepapp.
Require bedrock2.ZnWords.
Require Import bedrock2.to_from_anybytes.
Require Import bedrock2.SuppressibleWarnings.
Require Import bedrock2.TacticError.
Require Import bedrock2.HeapletwiseHyps.
Require Import bedrock2.bottom_up_simpl.
Require Import bedrock2.Map.SeparationLogic.

Import ZList.List.ZIndexNotations.
Local Open Scope zlist_scope.
Local Open Scope Z_scope.

Section SepLog.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Import ZnWords.

  Lemma split_array_at_bw{E: Type}{inh: inhabited E} elem {elemSize: PredicateSize elem}:
    forall s n a i (vs vs1 vs2: list E),
      word.unsigned (word.sub s a) / elemSize = i ->
      word.unsigned (word.sub s a) mod elemSize = 0 ->
      impl1 (sep (array elem i vs1 a)
                 (sep (array elem (n-i) vs2 s)
                      (emp (vs1 ++ vs2 = vs))))
            (array elem n vs a).
  Proof.
    unfold impl1. intros.
    purify.
    destruct H1P as (L1 & L2 & ?). subst vs.
    assert (0 <= i <= n) by lia.
    replace n with (i + (n - i)) by lia.
    eapply merge_array.
    eapply sep_assoc in H1.
    eapply sep_emp_r in H1. apply proj1 in H1.
    eqapply H1. f_equal.
    destruct width_cases; subst width; ZnWords.
  Qed.

  (* Different kinds of splitting/merging back:
     a) single array element
     b) subarray
     c) record field in a sepapp
     d) unfolding/folding the name of a record predicate

     Note that c) and d) are separate because if we access two fields of the
     same record, step d) happens once, but step c) happens twice *)

  Lemma split_off_elem_from_array{E: Type}{inh: inhabited E}:
    forall a a' elem {elemSize: PredicateSize elem} n i,
      (* to be solved by reflexivity (instantiates i): *)
      word.unsigned (word.sub a' a) / elemSize = i ->
      (* to be solved by ZnWords: *)
      ((word.unsigned (word.sub a' a)) mod elemSize = 0 /\ 0 <= i < n) ->
      (* split direction: *)
      (forall (vs: list E) m,
          array elem n vs a m ->
          sep (elem vs[i] a')
              (sep (array elem i vs[:i] a)
                  (array elem (n-i-1) vs[i+1:]
                      (word.add a' (word.of_Z elemSize)))) m) /\
      (* merge direction: *)
      (forall vs1 vs2 v m,
          sep (array elem i vs1 a)
              (sep (elem v a')
                  (array elem (n-i-1) vs2
                      (word.add a' (word.of_Z elemSize)))) m ->
          array elem n (vs1 ++ [|v|] ++ vs2) a m).
  Proof.
    split; intros.
    {
      unfold array in *.
      do 3 heapletwise_step.
      rewrite List.len_upto by ZnWords.
      rewrite List.len_from by ZnWords.

      assert (vs = vs[:i] ++ [|vs[i]|] ++ vs[i+1:]) as Hexposed by
        (apply (List.expose_nth vs i); ZnWords).
      rewrite Hexposed in H3.

      apply Array.array_append in H3.
      heapletwise_step.
      simpl in H4.
      unfold with_mem in H4.
      heapletwise_step.

      assert (a' = (word.add a
        (word.of_Z (word.unsigned (width := width)
          (word.of_Z elemSize) * len vs[:i])))) as Ha' by
        (rewrite List.len_upto;
          destruct width_cases as [Ew | Ew]; rewrite Ew in *; ZnWords).
      rewrite <- Ha' in *; clear Ha'.
      repeat heapletwise_step; ZnWords.
    }
    {
      unfold array in *.
      do 6 heapletwise_step.

      epose proof (Array.array_append) as Happ.
      eapply iff1ToEq in Happ.
      rewrite Happ; clear Happ; simpl.

      assert (a' = (word.add a
        (word.of_Z (word.unsigned (width := width)
          (word.of_Z elemSize) * len vs1)))) as Ha' by
        (destruct width_cases as [Ew | Ew]; rewrite Ew in *; ZnWords).
      rewrite <- Ha' in *; clear Ha'.

      repeat heapletwise_step.
      rewrite List.app_length; simpl.
      destruct width_cases as [Ew | Ew]; rewrite Ew in *; ZnWords.
    }
  Qed.

  Lemma split_off_subarray_from_array{E: Type}{inh: inhabited E}:
    (* a = start of the entire array. a' = start of the subarray (i). *)
    (* size = number of elements to split off *)
    forall a a' elem {elemSize: PredicateSize elem} n (nbytes: Z) i (size: Z),
      word.unsigned (word.sub a' a) / elemSize = i ->
      nbytes / elemSize = size ->

      (word.unsigned (word.sub a' a)) mod elemSize = 0 /\
      nbytes mod elemSize = 0 /\
      0 <= size /\
      0 <= i /\ i+size <= n ->

      (forall (vs: list E) m,
        array elem n vs a m ->

        (* first part *)
        sep (array elem i vs[:i] a)
        (* middle subarray part *)
          (sep (array elem size vs[i:][:size] a')
        (* final part *)
            (array elem (n-i-size) vs[i+size:]
              (word.add a' (word.of_Z (elemSize * size))))) m)

      /\

      (forall vsl vsr vsm m,
        (* first part *)
        sep (array elem i vsl a)
        (* middle subarray part *)
          (sep (array elem size vsm a')
        (* final part *)
            (array elem (n-i-size) vsr
              (word.add a' (word.of_Z (elemSize * size))))) m  ->

        array elem n (vsl ++ vsm ++ vsr) a m
      ).
  Proof.
    split; intros.
    {
      unfold array in *.
      repeat heapletwise_step; unfold with_mem in *.

      rewrite List.len_upto by ZnWords.
      rewrite List.len_sized_slice by ZnWords.
      rewrite List.from_upto_comm by ZnWords.
      rewrite List.from_canon with (i := i+size).
      rewrite List.len_indexed_slice with (i := i+size) (j := len vs) by ZnWords.

      assert (vs = vs[:i] ++ vs[i:i+size] ++ vs[i+size:len vs]) as Hsplit.
      {
        rewrite List.merge_adjacent_slices.
        - rewrite <- List.from_canon.
          apply List.split_at_index.
        - ZnWords.
      }
      rewrite Hsplit in H4; clear Hsplit.
      apply Array.array_append in H4.
      heapletwise_step.
      apply Array.array_append in H5.
      heapletwise_step.
      rewrite List.len_add_sized_slice in * by ZnWords.

      replace (word.add a
               (word.of_Z (word.unsigned (width := width)
                 (word.of_Z elemSize) * len vs[:i]))) with a' in * by
        (rewrite List.len_upto by ZnWords;
          destruct width_cases as [Ew | Ew]; rewrite Ew in *; ZnWords).
      replace (word.of_Z (word.unsigned (word.of_Z elemSize) * size))
        with (word.of_Z (word := word) (elemSize * size)) in * by
          (destruct width_cases as [Ew | Ew]; rewrite Ew in *; ZnWords).
      repeat heapletwise_step; ZnWords.
    }
    {
      unfold array in *.
      do 8 heapletwise_step.

      epose proof (Array.array_append) as Happ.
      eapply iff1ToEq in Happ.
      rewrite Happ; clear Happ.

      rewrite <- H5 in H6.
      epose proof (Array.array_append) as Happ.
      eapply iff1ToEq in Happ.
      rewrite Happ; clear Happ.

      replace (word.add a
               (word.of_Z (word.unsigned (width := width)
                 (word.of_Z elemSize) * len vsl))) with a' in * by
        (destruct width_cases as [Ew | Ew]; rewrite Ew in *; ZnWords).
      replace (word.of_Z (word.unsigned (word.of_Z elemSize) * len vsm))
        with (word.of_Z (word := word) (elemSize * len vsm)) in * by
          (destruct width_cases as [Ew | Ew]; rewrite Ew in *; ZnWords).

      collect_heaplets_into_one_sepclause. cbn [seps] in D.
      repeat heapletwise_step.
      rewrite 2 List.app_length; ZnWords.
    }
  Qed.

  Lemma split_anybytes_from_anybytes:
    (* a = start of the entire array. a' = start of the part to split off. *)
    forall a a' (nAll nReq: Z) i,
      word.unsigned (word.sub a' a) = i ->
      0 <= nReq /\ 0 <= i /\ i+nReq <= nAll ->
      (forall m,
        (array (uint 8) nAll ? a) m ->
        sep (array (uint 8) i ? a)
          (sep (array (uint 8) nReq ? a')
             (array (uint 8) (nAll-i-nReq) ? (word.add a' (word.of_Z nReq)))) m) /\
      (* Note: often, this second part will not be used, because the split-off
         bytes get initialized to something, but if the callee just used it as
         scratch space, this second part will be used *)
      (forall m,
        sep (array (uint 8) i ? a)
          (sep (array (uint 8) nReq ? a')
             (array (uint 8) (nAll-i-nReq) ? (word.add a' (word.of_Z nReq)))) m  ->
        array (uint 8) nAll ? a m).
  Proof.
    split; intros.
    - eapply split_anyval_array with (i := i) in H1. 2: lia.
      repeat heapletwise_step.
      eapply split_anyval_array with (i := nReq) in H3. 2: lia.
      repeat heapletwise_step.
      subst i.
      rewrite ?Z.mul_1_l in *.
      rewrite word.of_Z_unsigned in *.
      rewrite word.add_sub_r_same_r in *.
      repeat heapletwise_step.
    - repeat heapletwise_step.
      replace nAll with (i + (nAll - i)) by lia.
      eapply merge_anyval_array.
      repeat heapletwise_step.
      rewrite Z.mul_1_l.
      refine (conj _ I). intros. cbn.
      replace (nAll - i) with (nReq + (nAll - i - nReq)) by lia.
      eapply merge_anyval_array.
      rewrite Z.mul_1_l.
      subst i.
      rewrite word.of_Z_unsigned in *.
      rewrite word.add_sub_r_same_r in *.
      repeat heapletwise_step.
  Qed.

  (* does not depend on any library functions so that we can safely cbn it *)
  Fixpoint sepapps_offset(n: nat)(l: list sized_predicate): Z :=
    match n with
    | O => 0
    | S n' =>
        match l with
        | nil => 0
        | cons (mk_sized_predicate _ sz) t => Z.add sz (sepapps_offset n' t)
        end
    end.

  Lemma sepapps_offset_spec: forall n l,
      sepapps_offset n l = sepapps_size (List.firstn n l).
  Proof.
    induction n; intros.
    - reflexivity.
    - destruct l. 1: reflexivity. simpl. destruct s. rewrite IHn. reflexivity.
  Qed.

  (* does not depend on any library functions so that we can safely cbn it *)
  Fixpoint sepapps_replace(l: list sized_predicate)(n: nat)(p: sized_predicate) :=
    match l with
    | cons h t =>
        match n with
        | O => cons p t
        | S n' => cons h (sepapps_replace t n' p)
        end
    | nil => cons p nil
    end.

  Lemma sepapps_replace_spec: forall l n p,
      sepapps_replace l n p = List.firstn n l ++ cons p (List.skipn (S n) l).
  Proof.
    induction l; intros; destruct n; try reflexivity.
    simpl. rewrite IHl. reflexivity.
  Qed.

  Lemma split_off_field_from_sepapps: forall a a' sz ofs ofs_simpl l_old n,
      word.unsigned (word.sub a' a) = ofs -> (* <- reflexivity determines ofs *)
      sepapps_offset n l_old = ofs_simpl /\ ofs_simpl = ofs -> (* <- determines n, ofs_simpl *)
      (forall P m,
          List.nth_error l_old n = Some (mk_sized_predicate P sz) ->
          sepapps l_old a m ->
          sep (sepapps (sepapps_replace l_old n (mk_sized_predicate (hole sz) sz)) a)
              (P a') m) /\
      (forall l P m,
          sepapps_offset n l = ofs_simpl -> (* <- should be eq_refl *)
          List.nth_error l n = Some (mk_sized_predicate (hole sz) sz) ->
          sep (sepapps l a) (P a') m ->
          sepapps (sepapps_replace l n (mk_sized_predicate P sz)) a m).
  Proof.
    intros * ? [? ->]. split; intros; subst;
      rewrite sepapps_offset_spec in *;
      rewrite sepapps_replace_spec.
    - rewrite (expose_nth_sepapp l_old n a P sz H1) in H2.
      eapply SeparationLogic.sep_comm. eqapply H2. f_equal.
      rewrite H0. rewrite word.of_Z_unsigned, word.add_sub_r_same_r; trivial.
    - rewrite <- (merge_back_nth_sepapp l n a P sz H2).
      eapply SeparationLogic.sep_comm. eqapply H3. f_equal.
      rewrite H1. rewrite word.of_Z_unsigned, word.add_sub_r_same_r; trivial.
  Qed.

(* alternative way of expressing "1 past a'":
  Lemma split_off_elem_from_array{E: Type}{inh: inhabited E}:
    forall a a' elem {elemSize: PredicateSize elem} n i,
      (word.unsigned (word.sub a' a)) mod elemSize = 0 ->
      word.unsigned (word.sub a' a) / elemSize = i ->
      (forall (vs: list E) m,
          array elem n vs a m ->
          sep (elem vs[i] a')
              (sep (array elem i vs[:i] a)
                   (array elem (n-i-1) vs[i+1:]
                      (word.add a (word.of_Z (elemSize * (i + 1)))))) m) /\
      (forall vs1 vs2 v m,
          sep (array elem i vs1 a)
              (sep (elem v a')
                   (array elem (n-i-1) vs2
                      (word.add a (word.of_Z (elemSize * (i + 1)))))) m ->
          array elem n (vs1 ++ [|v|] ++ vs2) a m).
  Proof.
  Admitted.
*)
End SepLog.


Definition find_hyp_for_range{word: Type}(start: word)(size: Z)(tGoal: Prop) := tGoal.
Definition split_range_from_hyp{word: Type}(start: word)(size: Z)(tHyp: Prop)
  (H: tHyp)(tGoal: Prop) := tGoal.
Definition split_concl_at{word: Type}(addr: word)(g: Prop) := g.

Definition merge_step(P: Prop) := P.

Inductive fold_step{SomeRecordType word mem: Type}
  (pred: SomeRecordType -> word -> mem -> Prop) := mk_fold_step.

Ltac fold_in_hyps p :=
  let h := head p in
  let p' := eval cbv beta iota delta [h] in p in
  idtac p';
  match goal with
  | H: context C[?x] |- _ =>
    syntactic_unify p' x;
    let g := context C[p] in
    change g in H
  end.

Ltac prepend_reversed l acc :=
  lazymatch l with
  | nil => acc
  | cons ?h ?t => prepend_reversed t (cons h acc)
  end.

Ltac list_reverse l := prepend_reversed l open_constr:(@nil _).

(* Given
   c: record_constructor ?arg1 ... ?argN
   l: [| mk_sized_predicate (predN vN) sizeN; ...; mk_sized_predicate (pred1 v1) size1 |]
   instantiates the evars ?arg1 ... ?argN with v1 ... vN *)
Ltac instantiate_constructor_with_reversed_sepapps c l :=
  lazymatch l with
  | cons (mk_sized_predicate (?pred ?v) ?size) ?l' =>
      lazymatch c with
      | ?c' ?e => unify e v; instantiate_constructor_with_reversed_sepapps c' l'
      end
  | nil => idtac
  end.

(* Given
   c: record_constructor ?arg1 ... ?argN
   l: [| mk_sized_predicate (pred1 v1) size1; ...; mk_sized_predicate (predN vN) sizeN |]
   instantiates the evars ?arg1 ... ?argN with v1 ... vN *)
Ltac instantiate_constructor_with_sepapps c l :=
  let lrev := list_reverse l in
  instantiate_constructor_with_reversed_sepapps c lrev.

Ltac pick_nat n :=
  multimatch n with
  | S ?m => constr:(m)
  | S ?m => pick_nat m
  end.

Ltac word_lia_hook_for_split_merge :=
  fail 1000 "unimplemented split_merge_word_lia_hook,"
            "do eg Ltac word_lia_hook_for_split_merge ::= ZnWords".

(* instantiates i_ev based on ofs, and instantiates ofs_simpl to a simplified ofs *)
Ltac find_field_index_from_offset :=
  lazymatch goal with
  | |- sepapps_offset ?i_ev ?l = ?ofs_simpl_ev /\ ?ofs_simpl_ev = ?ofs =>
      tryif is_evar i_ev then
        tryif is_evar ofs_simpl_ev then
          lazymatch list_length_option l with
          | Some ?n => once (let i := pick_nat n in
                             unify i_ev i;
                             split;
                             [ cbn [sepapps_offset]; reflexivity
                             | word_lia_hook_for_split_merge ])
          | None => fail 1000 l "is not a concrete list"
          end
        else
          fail 1000 ofs_simpl_ev "is not an evar"
      else
        fail 1000 i_ev "is not an evar"
  end.

Ltac turn_split_merge_lemma_into_merge_step H :=
  tryif will_merge_back_later then
    eapply proj2 in H;
    let t := type of H in
    change (merge_step t) in H
  else clear H.

Ltac split_range_from_hyp_default :=
  lazymatch goal with
  | |- split_range_from_hyp ?start ?size (with_mem ?m ?P) ?H ?g =>
      change g;
      lazymatch P with
      | sepapps _ _ => idtac
      | array _ _ _ _ => idtac
      | anyval _ _ => idtac
      | _ => let h := head P in unfold h in H;
             record.simp_hyp H;
             lazymatch P with
             | ?pred ?v ?addr =>
                 tryif will_merge_back_later then pose proof (mk_fold_step pred) else idtac
             end
      end;
      let pf := fresh in
      lazymatch type of H with
      | with_mem _ (@array _ _ _ _ _ ?elem (*must match:*)size ?n ?vs ?start') =>
          unshelve epose proof
            (split_off_elem_from_array start' start elem n _ _ _) as pf;
          [ (* i *)
          | reflexivity
          | word_lia_hook_for_split_merge
          | eapply (proj1 pf) in H;
            turn_split_merge_lemma_into_merge_step pf ]
      | with_mem _ (@array _ _ _ _ _ ?elem ?elemSize ?n ?vs ?start') =>
          unshelve epose proof
            (split_off_subarray_from_array start' start elem n size _ _ _ _ _) as pf;
          [ (* index of first element *)
          | (* number of elements to split off *)
          | reflexivity
          | bottom_up_simpl_in_goal_nop_ok; reflexivity
          | word_lia_hook_for_split_merge
          | eapply (proj1 pf) in H;
            turn_split_merge_lemma_into_merge_step pf ]
      | with_mem _ (array (uint 8) ?nAll ? ?start') =>
          unshelve epose proof
            (split_anybytes_from_anybytes start' start nAll size _ _ _) as pf;
          [ (* offset of first element *)
          | reflexivity
          | word_lia_hook_for_split_merge
          | eapply (proj1 pf) in H;
            turn_split_merge_lemma_into_merge_step pf ]
      | with_mem _ (sepapps ?l_old ?start') =>
          unshelve epose proof
            (split_off_field_from_sepapps start' start size _ _ l_old _ eq_refl _) as pf;
          [ (* ofs_simpl to be determined below *)
          | (* index to be determined below *)
          | find_field_index_from_offset
          | eapply (proj1 pf) in H;
            [ idtac | reflexivity ];
            cbn [sepapps_replace] in H;
            turn_split_merge_lemma_into_merge_step pf ]
      end
  end.

Ltac split_range_from_hyp_hook := split_range_from_hyp_default.

Ltac split_concl_at_default :=
  lazymatch goal with
  | |- split_concl_at ?s ?g =>
      change g;
      lazymatch g with
      | canceling (cons ?P ?Ps) ?om ?Rest =>
          lazymatch P with
          | array ?elem ?size ?vs ?start =>
              eapply cancel_rew_head;
              [ eapply (split_array_at_bw _ s);
                [ reflexivity | word_lia_hook_for_split_merge ]
              | ]
          end
      end
  end.

Ltac split_concl_at_hook := split_concl_at_default.

Ltac merge_step_in_hyp H :=
  lazymatch type of H with
  (* Special case for records: Need to solve sideconditions SC1 and SC2 (using eq_refl).
     Match for proj2 of split_off_field_from_sepapps: *)
  | merge_step (forall l P m,
          sepapps_offset ?n l = ?ofs -> (* <-SC1 *)
          List.nth_error l ?n = Some (mk_sized_predicate (hole ?sz) ?sz) -> (* <-SC2 *)
          sep (sepapps l ?p) (P ?p_plus_ofs) m ->
          sepapps (sepapps_replace l ?n (mk_sized_predicate P ?sz)) ?p m) =>
      lazymatch goal with
      | _: with_mem _ (sepapps ?l p) |- _ =>
          specialize (H l); specialize H with (1 := eq_refl) (2 := eq_refl);
          cbn [sepapps_replace] in H
      end
  | _ => idtac
  end;
  unfold merge_step in H;
  cancel_in_hyp H.

Lemma rew_with_mem{mem: Type}: forall (P1 P2: mem -> Prop) (m: mem),
    impl1 P1 P2 ->
    with_mem m P1 -> with_mem m P2.
Proof. unfold impl1, with_mem. intros. eauto. Qed.

(* Returns a Prop claiming that start..start+size is a subrange of start'..start'+size'.
   Assumes 0<=size<2^width and 0<=size'<2^width.
   Both ranges may wrap around. *)
Definition subrange{width: Z}{word: word.word width}(start: word)(size: Z)
  (start': word)(size': Z) := word.unsigned (word.sub start start') + size <= size'.

Ltac is_subrange start size start' size' :=
  assert_succeeds (idtac; assert (subrange start size start' size') by
                     (unfold subrange; word_lia_hook_for_split_merge)).

Definition inrange{width: Z}{word: word.word width}(addr: word)(start: word)(size: Z) :=
  word.unsigned (word.sub addr start) <= size.

(* Check that addr is inside the range, and at least sometimes strictly so *)
Ltac is_inside_range addr start size :=
  assert_succeeds (idtac; assert (inrange addr start size) by
                     (unfold inrange; word_lia_hook_for_split_merge));
  assert_fails (idtac; assert (addr = start \/ word.unsigned (word.sub addr start) = size)
                  by word_lia_hook_for_split_merge).

Inductive PredicateSize_not_found{PredTp: Type}(pred: PredTp): Set :=
  mk_PredicateSize_not_found.

Notation "'(PredicateSize'  pred ')'  'cannot'  'be'  'solved'  'by'  'typeclasses' 'eauto'" :=
  (PredicateSize_not_found pred)
  (at level 1, pred at level 9, only printing)
: message_scope.

Ltac _with_PredicateSize_of P k :=
  let maybesize := match constr:(Set) with
                   | _ => lazymatch constr:(_: PredicateSize P) with ?s => s end
                   | _ => constr:(tt)
                   end in
  lazymatch maybesize with
  | tt =>
      (* progress could fail because warning was already posed or because
                 warning is suppressed *)
      progress pose_warning (mk_PredicateSize_not_found P)
  | ?size => k size
  end.

Tactic Notation "with_PredicateSize_of" constr(P) tactic0(k) :=
  _with_PredicateSize_of P k.

Ltac gather_is_subrange_claims_into_error start size :=
  fold_hyps_upwards_cont
    (fun res h tp =>
       lazymatch tp with
       | with_mem ?m (?P' ?start') =>
          match constr:(Set) with
          | _ => lazymatch constr:(_: PredicateSize P') with
                 | ?size' => constr:(cons (subrange start size start' size')
                                    (cons (inrange start' start size) res))
                 end
          | _ => res
          end
       | _ => res
       end)
    (@nil Prop)
    (fun r => pose_err
                Error:("Exactly one of the following claims should hold:" r)).

Ltac is_singleton_record_predicate p :=
  let h := head p in
  lazymatch eval unfold h in p with
  | sepapps (cons _ nil) => idtac
  | _ => fail "not a singleton record predicate"
  end.

(* can be redefined with ::= *)
Ltac sepclause_impl_step_hook := fail.

Ltac split_step :=
  lazymatch goal with
  | |- canceling (cons (?P ?start) _) ?m _ =>
      with_PredicateSize_of P (fun size =>
        let g := lazymatch goal with |- ?x => x end in
        change (find_hyp_for_range start size g))
  | |- find_hyp_for_range ?start ?size ?g =>
      match goal with
      | H: with_mem ?mH (?P' ?start') |- _ =>
          with_PredicateSize_of P' (fun size' =>
              is_subrange start size start' size';
              tryif assert_succeeds (idtac; assert (size = size') by
                                       word_lia_hook_for_split_merge);
                    (* TODO: below check should be more general and see if one of the
                       records is a sub-record of the other, potentially unfolding
                       several singleton-field records *)
                    assert_fails (idtac; is_singleton_record_predicate P')
              then (
                change g;
                let P := lazymatch goal with | |- canceling (cons ?P _) _ _ => P end in
                first
                [ let A := fresh in
                  enough (impl1 (P' start') P) as A;
                  [ (* main goal *)
                    let Hf := fresh in
                    (* We use `pose proof` instead of `eapply ... in ...` because
                       `eapply ... in ...` does an implicit `cbv iota` on the type of the
                       new hypothesis, which might undo exactly what we wanted to achieve
                       (note: if the sep clause in the conclusion is a bit more complicated
                        than the sep clause in a hyp, we actually make the hyp similarly
                        more complicated because we always modify the hyp, even though that's
                        not always the simplest way...) *)
                    pose proof (rew_with_mem (P' start') P mH A H) as Hf;
                    move Hf before H;
                    clear A H;
                    rename Hf into H
                  | (* sidecondition: (impl1 (P' start') P) *)
                    first [ solve [repeat sepclause_impl_step_hook]
                          | (* If we can't solve it right away, we need to be careful
                               not to create an unprovable goal.
                               We already know that the two predicates start at the same
                               address and have the same size, but we need to exclude
                               that they differ in further memory that some of their fields
                               might point to, so we simply disallow all pointers to
                               further memory by requiring that the whole footprint is
                               within [start..start+size): *)
                            is_fake_contiguous P';
                            lazymatch P with
                            | ?P0 ?start0 => is_fake_contiguous P0
                            end ] ]
                | pose_err Error:("Cannot cancel" P "with" (P' start')
                       "even though both span the same range:" size "bytes from" start) ]
              ) else change (split_range_from_hyp start size _ H g))
      | H: with_mem ?mH (?P' ?start') |- _ =>
          is_inside_range start' start size;
          change (split_concl_at start' g)
      | _ => gather_is_subrange_claims_into_error start size
      end
  | |- split_range_from_hyp ?start ?size ?tH ?H ?g => split_range_from_hyp_hook
  | |- split_concl_at ?s ?g => split_concl_at_hook
  end.

Ltac merge_step :=
  match goal with
  | H: merge_step _ |- _ => merge_step_in_hyp H
  | F: @fold_step ?R _ _ ?pred |- _ =>
      let c := lazymatch open_constr:(ltac:(constructor) : R) with ?c => c end in
      lazymatch goal with
      | H: with_mem ?m (sepapps ?l ?a) |- _ =>
          instantiate_constructor_with_sepapps c l;
          change (with_mem m (pred c a)) in H
      end;
      clear F
  end.

Ltac prove_emp_in_hyps :=
  repeat match goal with
         | h: with_mem _ ?p |- _ => prove_emp_in h p
         end.

(* to be called manually to acknowledge that the latest merge step is not needed: *)
Ltac discard_merge_step :=
  lazymatch goal with
  | H: merge_step _ |- _ => clear H
  end;
  prove_emp_in_hyps;
  repeat heapletwise_step.
