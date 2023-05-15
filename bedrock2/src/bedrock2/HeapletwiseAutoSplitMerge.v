Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Byte.
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
Require Import bedrock2.ZnWords.
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
          ZnWords.
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

      collect_heaplets_into_one_sepclause m'.
      repeat heapletwise_step.
      rewrite 2 List.app_length; ZnWords.
    }
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

  Lemma split_off_field_from_sepapps: forall a a' sz ofs n,
      word.unsigned (word.sub a' a) = ofs -> (* <- simplify lhs, then reflexivity
                                                determines ofs *)
      (forall l P m,
          sepapps_offset n l = ofs -> (* <- determines n *)
          List.nth_error l n = Some (mk_sized_predicate P sz) ->
          sepapps l a m ->
          sep (sepapps (sepapps_replace l n (mk_sized_predicate (hole sz) sz)) a)
              (P a') m) /\
      (forall l P m,
          sepapps_offset n l = ofs -> (* <- should be eq_refl *)
          List.nth_error l n = Some (mk_sized_predicate (hole sz) sz) ->
          sep (sepapps l a) (P a') m ->
          sepapps (sepapps_replace l n (mk_sized_predicate P sz)) a m).
  Proof.
    intros. split; intros; subst;
      rewrite sepapps_offset_spec in H0;
      rewrite sepapps_replace_spec.
    - rewrite (expose_nth_sepapp l n a P sz H1) in H2.
      eapply SeparationLogic.sep_comm. eqapply H2. f_equal.
      rewrite H0. rewrite word.of_Z_unsigned, word.add_sub_r_same_r; trivial.
    - rewrite <- (merge_back_nth_sepapp l n a P sz H1).
      eapply SeparationLogic.sep_comm. eqapply H2. f_equal.
      rewrite H0. rewrite word.of_Z_unsigned, word.add_sub_r_same_r; trivial.
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


Definition find_superrange_hyp{word: Type}(start: word)(size: Z)(tGoal: Prop) := tGoal.
Definition split_range_from_hyp{word: Type}(start: word)(size: Z)(tHyp: Prop)
  (H: tHyp)(tGoal: Prop) := tGoal.

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

Ltac find_field_index_from_offset :=
  lazymatch goal with
  | |- sepapps_offset ?i_ev ?l = ?ofs =>
      tryif is_evar i_ev then
        lazymatch list_length_option l with
        | Some ?n => once (let i := pick_nat n in unify i_ev i; reflexivity)
        | None => fail 1000 l "is not a concrete list"
        end
      else
        fail 1000 i_ev "is not an evar"
  end.

Ltac split_range_from_hyp_default :=
  lazymatch goal with
  | |- split_range_from_hyp ?start ?size (with_mem ?m ?P) ?H ?g =>
      lazymatch P with
      | sepapps _ _ => idtac
      | array _ _ _ _ => idtac
      | _ => let h := head P in unfold h in H;
             record.simp_hyp H;
             lazymatch P with
             | ?pred ?v ?addr => pose proof (mk_fold_step pred)
             end
      end;
      let pf := fresh in
      lazymatch type of H with
      | with_mem _ (@array _ _ _ _ _ ?elem (*must match:*)size ?n ?vs ?start') =>
          unshelve epose proof
            (split_off_elem_from_array start' start elem n _ _ _) as pf;
          [ (* i *)
          | bottom_up_simpl_in_goal; reflexivity
          | ZnWords
          | change g;
            eapply (proj1 pf) in H;
            eapply proj2 in pf;
            let t := type of pf in change (merge_step t) in pf ]
      | with_mem _ (@array _ _ _ _ _ ?elem ?elemSize ?n ?vs ?start') =>
          unshelve epose proof
            (split_off_subarray_from_array start' start elem n size _ _ _ _ _) as pf;
          [ (* index of first element *)
          | (* number of elements to split off *)
          | bottom_up_simpl_in_goal; reflexivity
          | bottom_up_simpl_in_goal; reflexivity
          | ZnWords
          | change g;
            eapply (proj1 pf) in H;
            eapply proj2 in pf;
            let t := type of pf in change (merge_step t) in pf ]
      | with_mem _ (sepapps _ ?start') =>
          unshelve epose proof
            (split_off_field_from_sepapps start' start size _ _ _) as pf;
          [ (* offset: dependent evar will be determined by second subgoal *)
          | (* n (index of field): determined later below *)
          | (* address difference equals offset *)
            bottom_up_simpl_in_goal; reflexivity
          | change g;
            eapply (proj1 pf) in H;
            [ eapply proj2 in pf
            | find_field_index_from_offset
            | reflexivity ];
            cbn [sepapps_replace] in H;
            let t := type of pf in change (merge_step t) in pf ]
      end
  end.

Ltac split_range_from_hyp_hook := split_range_from_hyp_default.

Section CancelingInHyp.
  Context {key value: Type} {mem: map.map key value} {mem_ok: map.ok mem}
          {key_eqb: key -> key -> bool} {key_eqb_spec: Decidable.EqDecider key_eqb}.

  Definition canceling_in_hyp(mAll: mem)(omAvailable: mmap mem)
    (Ps: list (mem -> Prop))(Q: mem -> Prop) :=
    exists mUsed, mmap.du omAvailable (mmap.Def mUsed) = mmap.Def mAll /\
                  forall mp mq, mmap.du (mmap.Def mp) (mmap.Def mUsed) = mmap.Def mq ->
                                seps Ps mp -> Q mq.

  Lemma start_canceling_in_hyp: forall Ps (Q: mem -> Prop) omAll mAll,
      omAll = mmap.Def mAll ->
      (forall m, SeparationLogic.Tree.to_sep Ps m -> Q m) ->
      canceling_in_hyp mAll omAll (SeparationLogic.Tree.flatten Ps) Q.
  Proof.
    unfold canceling_in_hyp. intros. exists map.empty. split.
    - rewrite mmap.du_empty_r. exact H.
    - intros. rewrite mmap.du_empty_r in H1. inversion H1. subst mp. clear H1.
      eapply H0. eapply SeparationLogic.Tree.flatten_iff1_to_sep. assumption.
  Qed.

  Lemma canceling_step_in_hyp: forall (P: mem -> Prop) Ps Q mAll m path hs1 hs2,
      with_mem m P ->
      mem_tree_lookup hs1 path = Some m ->
      mem_tree_remove hs1 path = Some (Some hs2) ->
      canceling_in_hyp mAll (interp_mem_tree hs1) (cons P Ps) Q ->
      canceling_in_hyp mAll (interp_mem_tree hs2) Ps Q.
  Proof.
    unfold canceling_in_hyp. intros. fwd.
    unfold mmap.du, mmap.of_option in H2p0. fwd.
    epose proof (split_mem_tree H0 H1 E) as A.
    exists (map.putmany m mUsed).
    unfold map.du in E0. fwd.
    unfold mmap.du, mmap.of_option in A. fwd.
    eapply map.disjointb_spec in E1.
    assert (map.disjoint m mUsed) as D. {
      unfold map.du in E2. fwd. eapply map.disjointb_spec in E3.
      unfold map.disjoint in *. intros. eapply E1. 2: eassumption.
      rewrite map.get_putmany_dec. rewrite H2. reflexivity.
    }
    split.
    - unfold map.du in E2. fwd.
      unfold mmap.du, mmap.of_option, map.du.
      eapply map.disjoint_putmany_l in E1. fwd.
      replace (map.disjointb m1 (map.putmany m mUsed)) with true.
      1: rewrite map.putmany_assoc; reflexivity.
      symmetry. eapply map.disjointb_spec. eapply map.disjoint_putmany_r.
      eapply map.disjointb_spec in E3. auto.
    - intros.
      unfold mmap.du, mmap.of_option, map.du in H2. fwd.
      eapply map.disjointb_spec in E4. eapply map.disjoint_putmany_r in E4. fwd.
      eapply H2p1.
      2: {
        eapply SeparationLogic.seps_cons. eapply sep_from_disjointb. 2,3: eassumption.
        eapply map.disjointb_spec. apply map.disjoint_comm. assumption.
      }
      unfold mmap.du, mmap.of_option, map.du.
      replace (map.disjointb (map.putmany m mp) mUsed) with true.
      + rewrite map.putmany_assoc. f_equal. f_equal. eapply map.putmany_comm.
        eapply map.disjoint_comm. assumption.
      + symmetry. eapply map.disjointb_spec. eapply map.disjoint_putmany_l. auto.
  Qed.

  Lemma canceling_done_in_hyp: forall Q mAll omAvailable,
      canceling_in_hyp mAll omAvailable nil Q ->
      exists m, mmap.du omAvailable (mmap.Def m) = mAll /\ with_mem m Q.
  Proof.
    unfold canceling_in_hyp. intros. fwd. exists mUsed. split. 1: assumption.
    eapply Hp1. 1: eapply mmap.du_empty_l. unfold seps, emp. auto.
  Qed.
End CancelingInHyp.

Ltac start_canceling_in_hyp H :=
  unfold merge_step in H;
  repeat lazymatch type of H with
    | forall m, ?A m -> ?B m => fail (* done *)
    | forall (_: ?A), _ => let x := lazymatch open_constr:(_: A) with ?x => x end in
                           specialize (H x)
    end;
  lazymatch type of H with
  | forall m, ?A m -> ?B m =>
      let clausetree := SeparationLogic.reify A in
      change (forall m, SeparationLogic.Tree.to_sep clausetree m -> B m) in H;
      lazymatch goal with
      | D: _ = mmap.Def _ |- _ =>
          eapply (start_canceling_in_hyp clausetree _ _ _ D) in H;
          clear D;
          cbn [SeparationLogic.Tree.flatten
               SeparationLogic.Tree.interp
               bedrock2.Map.SeparationLogic.app] in H
      end
  end.

Ltac canceling_step_in_hyp C :=
  lazymatch type of C with
  | canceling_in_hyp ?mAll ?om (cons ?P ?Ps) ?Q =>
      let H := match goal with
               | H: with_mem _ ?P' |- _ =>
                   let __ := match constr:(Set) with _ => syntactic_unify P P' end in H
               end in
      let m := lazymatch type of H with with_mem ?m _ => m end in
      let hs := reify_mem_tree om in
      let p := path_in_mem_tree hs m in
      eapply (canceling_step_in_hyp P Ps Q mAll m p hs _ H) in C;
      [ | reflexivity | reflexivity];
      cbn [interp_mem_tree] in C;
      clear H m
  end.

Ltac cancel_in_hyp H :=
  start_canceling_in_hyp H;
  repeat canceling_step_in_hyp H;
  eapply canceling_done_in_hyp in H;
  destruct H as (?m & ?D & ?H).

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
  cancel_in_hyp H.

Lemma f_equal_fun[A B: Type]: forall (f g: A -> B) (x: A), f = g -> f x = g x.
Proof. intros. subst. reflexivity. Qed.

Ltac syntactic_f_equal_step_with_ZnWords :=
  lazymatch goal with
  | |- ?x = ?x => reflexivity
  | |- @eq (@word.rep _ _) _ _ => ZnWords
  | |- @eq Z _ _ => ZnWords
  | |- ?f ?a = ?f ?b => eapply (@f_equal _ _ f a b)
  | |- ?f ?x = ?g ?x => eapply (f_equal_fun f g x)
  end.

Ltac syntactic_f_equal_with_ZnWords := solve [repeat syntactic_f_equal_step_with_ZnWords].

Lemma rew_with_mem{mem: Type}: forall (P1 P2: mem -> Prop) (m: mem),
    P1 = P2 ->
    with_mem m P1 -> with_mem m P2.
Proof. intros. subst. assumption. Qed.

Ltac sepclause_equality_hook := syntactic_f_equal_with_ZnWords.

(* Returns a Prop claiming that start..start+size is a subrange of start'..start'+size'.
   Assumes 0<=size<2^width and 0<=size'<2^width.
   Both ranges may wrap around. *)
Definition subrange{width: Z}{word: word.word width}(start: word)(size: Z)
  (start': word)(size': Z) := word.unsigned (word.sub start start') + size <= size'.

Ltac is_subrange start size start' size' :=
  assert_succeeds (idtac; assert (subrange start size start' size') by
                     (unfold subrange; ZnWords)).

Inductive PredicateSize_not_found{PredTp: Type}(pred: PredTp): Set :=
  mk_PredicateSize_not_found.

Notation "'(PredicateSize'  pred ')'  'cannot'  'be'  'solved'  'by'  'typeclasses' 'eauto'" :=
  (PredicateSize_not_found pred)
  (at level 1, pred at level 9, only printing)
: message_scope.

Ltac gather_is_subrange_claims_into_error start size :=
  fold_hyps_upwards_cont
    (fun res h tp =>
       lazymatch tp with
       | with_mem ?m (?P' ?start') =>
          match constr:(Set) with
          | _ => lazymatch constr:(_: PredicateSize P') with
                 | ?size' => constr:(cons (subrange start size start' size') res)
                 end
          | _ => res
          end
       | _ => res
       end)
    (@nil Prop)
    (fun r => pose_err
                Error:("Exactly one of the following subrange claims should hold:" r)).

Ltac is_singleton_record_predicate p :=
  let h := head p in
  lazymatch eval unfold h in p with
  | sepapps (cons _ nil) => idtac
  | _ => fail "not a singleton record predicate"
  end.

Ltac split_step :=
  lazymatch goal with
  | |- canceling (cons (?P ?start) _) ?m _ =>
      let size := lazymatch constr:(_: PredicateSize P) with ?s => s end in
      let g := lazymatch goal with |- ?x => x end in
      change (find_superrange_hyp start size g)
  | |- find_superrange_hyp ?start ?size ?g =>
      match goal with
      | H: with_mem ?mH (?P' ?start') |- _ =>
          let maybesize' := match constr:(Set) with
                            | _ => lazymatch constr:(_: PredicateSize P') with ?s => s end
                            | _ => constr:(tt)
                            end in
          lazymatch maybesize' with
          | tt =>
              lazymatch goal with
              | _: message_scope_marker (PredicateSize_not_found P') |- _ =>
                  fail (* already warned, ie nothing to do, so this step does not apply *)
              | |- _ => pose_warning (mk_PredicateSize_not_found P')
              end
          | ?size' =>
              is_subrange start size start' size';
              tryif assert_succeeds (idtac; assert (size = size') by ZnWords);
                    (* TODO: below check should be more general and see if one of the
                       records is a sub-record of the other, potentially unfolding
                       several singleton-field records *)
                    assert_fails (idtac; is_singleton_record_predicate P')
              then (
                change g;
                let P := lazymatch goal with | |- canceling (cons ?P _) _ _ => P end in
                eapply (rew_with_mem (P' start') P mH) in H (* <-- leaves 2 open goals *)
              ) else change (split_range_from_hyp start size _ H g)
          end
      | _ => gather_is_subrange_claims_into_error start size
      end
  | |- split_range_from_hyp ?start ?size ?tH ?H ?g => split_range_from_hyp_hook
  | |- @eq (@map.rep (@word.rep _ _) Init.Byte.byte _ -> Prop) _ _ =>
      syntactic_f_equal_with_ZnWords
  end.

Ltac merge_step :=
  lazymatch goal with
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
