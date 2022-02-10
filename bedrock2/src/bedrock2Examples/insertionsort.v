Require Import bedrock2.NotationsCustomEntry.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition insertionsort : func :=
  ("insertionsort", (["a"; "n"], [], bedrock_func_body:(
  i = $0;
  while (i < n) {
    t = load4(a + $4*i);
    j = $0;
    while (load4(a + $4*j) < t) {
      j = j + $1
    };
    while (j < i+$1) {
      u = load4(a + $4*j);
      store4(a + $4*j, t);
      t = u;
      j = j + $1;
      coq:(cmd.unset "u")
    };
    i = i + $1;
    coq:(cmd.unset "t");
    coq:(cmd.unset "j")
  }
))).

Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics bedrock2.FE310CSemantics.
Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars bedrock2.Array bedrock2.Loops.
Require Import bedrock2.ZnWords.
Require Import coqutil.Sorting.Permutation.

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Definition nth(l: list word)(n: nat): word := List.nth n l (word.of_Z 0).

  Definition Sorted(l: list word): Prop :=
    forall i j: nat, (i < j < List.length l)%nat -> word.ltu (nth l j) (nth l i) = false.

  Fixpoint Sorted0(l: list word): Prop :=
    match l with
    | nil => True
    | x :: tl1 => match tl1 with
                  | y :: tl2 => word.ltu y x = false /\ Sorted0 tl1
                  | nil => True
                  end
    end.

  Lemma Sorted_nil: Sorted [].
  Proof. intros i j (? & A). inversion A. Qed.

  Lemma Sorted_snoc: forall l a,
      Sorted l ->
      (forall k, (k < List.length l)%nat -> word.ltu a (nth l k) = false) ->
      Sorted (l ++ [a]).
  Proof.
    unfold Sorted. intros. rewrite List.app_length in *. cbn in *.
    assert (j < List.length l \/ j = List.length l)%nat as C by Lia.lia.
    unfold nth.
    destruct C as [C | C].
    - rewrite ?List.app_nth1 by Lia.lia. apply H. Lia.lia.
    - subst j. rewrite List.nth_middle. rewrite ?List.app_nth1 by Lia.lia.
      apply H0. Lia.lia.
  Qed.

  (* TODO define word.leu and move to coqutil *)
  Lemma word__leu_trans: forall (a b c: word),
      word.ltu b a = false ->
      word.ltu c b = false ->
      word.ltu c a = false.
  Proof.
    intros *. rewrite ?word.unsigned_ltu, ?Z.ltb_ge. Lia.lia.
  Qed.

  Lemma Sorted_insert: forall left a1 a2 right,
      Sorted (left ++ a2 :: right) ->
      (forall k, (k < List.length left)%nat -> word.ltu a1 (nth left k) = false) ->
      word.ltu a2 a1 = false ->
      Sorted (left ++ [a1; a2] ++ right).
  Proof.
    unfold Sorted, nth in *.
    intros. rewrite ?List.app_length in *. cbn in *.
    assert (j < List.length left \/ j = List.length left \/ j = List.length left + 1 \/
            List.length left + 1 < j < List.length left + 2 + List.length right)%nat as C by Lia.lia.
    destruct C as [C | [C | [C | C]]].
    - rewrite ?List.app_nth1 by Lia.lia.
      assert (i < j < Datatypes.length left + S (Datatypes.length right))%nat as A by Lia.lia.
      specialize H with (1 := A). clear A.
      rewrite ?List.app_nth1 in H by Lia.lia. exact H.
    - subst j.
      rewrite List.nth_middle.
      rewrite ?List.app_nth1 by Lia.lia.
      apply H0. Lia.lia.
    - subst j.
      change (left ++ a1 :: a2 :: right) with (left ++ [a1] ++ a2 :: right).
      rewrite List.app_assoc.
      replace (Datatypes.length left + 1)%nat with (List.length (left ++ [a1])). 2: {
        rewrite List.app_length. cbn. reflexivity.
      }
      rewrite List.nth_middle.
      rewrite <- List.app_assoc.
      assert (i < List.length left \/ i = List.length left)%nat as C by Lia.lia. destruct C as [C | C].
      + rewrite List.app_nth1 by Lia.lia.
        eapply word__leu_trans. 2: eassumption. apply H0. assumption.
      + subst i. change (left ++ [a1] ++ a2 :: right) with (left ++ a1 :: a2 :: right).
        rewrite List.nth_middle. assumption.
    - rename j into j0. destruct j0 as [|j]. 1: exfalso; Lia.lia.
      replace (List.nth (S j) (left ++ a1 :: a2 :: right) (word.of_Z 0))
        with (List.nth j (left ++ a2 :: right) (word.of_Z 0)). 2: {
        change (left ++ a2 :: right) with (left ++ [a2] ++ right).
        rewrite List.app_assoc.
        rewrite List.app_nth2; rewrite List.app_length; cbn. 2: Lia.lia.
        change (left ++ a1 :: a2 :: right) with (left ++ [a1] ++ a2 :: right).
        rewrite List.app_assoc.
        rewrite List.app_nth2; rewrite List.app_length. 2: cbn; Lia.lia.
        change (Datatypes.length [a1]) with 1%nat.
        replace (S j - (Datatypes.length left + 1))%nat with (S (j - (Datatypes.length left + 1))) by Lia.lia.
        reflexivity.
      }
      assert (i < List.length left \/ i = List.length left \/ i = List.length left + 1 \/
              List.length left + 1 < i <= j)%nat as D by Lia.lia.
      destruct D as [D | [D | [D | D]]].
      + rewrite (List.app_nth1 left (a1 :: a2 :: right)) by assumption.
        assert (i < j < Datatypes.length left + S (Datatypes.length right))%nat as A by Lia.lia.
        specialize H with (1 := A). clear A.
        rewrite (@List.app_nth1 _ left (a2 :: right) _ i) in H by assumption. exact H.
      + assert (i < j < Datatypes.length left + S (Datatypes.length right))%nat as A by Lia.lia.
        specialize H with (1 := A). clear A.
        subst i. rewrite List.nth_middle. rewrite List.nth_middle in H.
        eapply word__leu_trans; eassumption.
      + subst i. change (left ++ a1 :: a2 :: right) with (left ++ [a1] ++ a2 :: right).
        rewrite List.app_assoc.
        replace (Datatypes.length left + 1)%nat with (List.length (left ++ [a1])). 2: {
          rewrite List.app_length. reflexivity.
        }
        rewrite List.nth_middle.
        replace a2 with (List.nth (List.length left) (left ++ a2 :: right) (word.of_Z 0)) at 2. 2: {
          apply List.nth_middle.
        }
        apply H. Lia.lia.
      + change (left ++ a2 :: right) with (left ++ [a2] ++ right).
        rewrite List.app_assoc.
        rewrite List.app_nth2; rewrite List.app_length; cbn. 2: Lia.lia.
        replace (left ++ a1 :: a2 :: right) with ((left ++ [a1; a2]) ++ right). 2: {
          rewrite <- List.app_assoc. reflexivity.
        }
        rewrite List.app_nth2; rewrite List.app_length; cbn. 2: Lia.lia.
        replace (List.nth (j - (Datatypes.length left + 1)) right (word.of_Z 0)) with
            (List.nth j (left ++ a2 :: right) (word.of_Z 0)). 2: {
          rewrite List.app_nth2 by Lia.lia.
          replace (j - Datatypes.length left)%nat with (S (j - (Datatypes.length left + 1))) by Lia.lia.
          reflexivity.
        }
        replace (List.nth (i - (Datatypes.length left + 2)) right (word.of_Z 0)) with
            (List.nth (i - 1) (left ++ a2 :: right) (word.of_Z 0)). 2: {
          rewrite List.app_nth2 by Lia.lia.
          replace (i - 1 - Datatypes.length left)%nat with (S (i - (Datatypes.length left + 2))) by Lia.lia.
          reflexivity.
        }
        apply H. Lia.lia.
  Qed.

  Lemma ptsto_nonaliasing: forall addr b1 b2 m (R: mem -> Prop),
      (ptsto addr b1 * ptsto addr b2 * R)%sep m ->
      False.
  Proof.
    intros. unfold ptsto, sep, map.split, map.disjoint in *.
    repeat match goal with
           | H: exists _, _ |- _ => destruct H
           | H: _ /\ _ |- _ => destruct H
           end.
    subst.
    specialize (H4 addr b1 b2). rewrite ?map.get_put_same in H4. auto.
  Qed.

  (* TODO generalize *)
  Lemma array_scalar32_max_size: forall addr xs (R: mem -> Prop) m,
      (array scalar32 (word.of_Z 4) addr xs * R)%sep m ->
      4 * Z.of_nat (Datatypes.length xs) <= 2 ^ 32.
  Proof.
    intros.
    assert (4 * Z.of_nat (Datatypes.length xs) <= 2 ^ 32 \/ 2 ^ 32 < 4 * Z.of_nat (Datatypes.length xs))
      as C by Lia.lia. destruct C as [C | C]; [exact C | exfalso].
    pose proof (List.firstn_skipn (Z.to_nat (2 ^ 32 / 4)) xs) as E.
    pose proof @List.firstn_length_le _ xs (Z.to_nat (2 ^ 32 / 4)) as A.
    assert (Z.to_nat (2 ^ 32 / 4) <= Datatypes.length xs)%nat as B by ZnWords.
    specialize (A B). clear B.
    destruct (List.firstn (Z.to_nat (2 ^ 32 / 4)) xs) as [|h1 t1] eqn: E1. {
      ZnWordsL.
    }
    destruct (List.skipn (Z.to_nat (2 ^ 32 / 4)) xs) as [|h2 t2] eqn: E2. {
      pose proof @List.skipn_length _ (Z.to_nat (2 ^ 32 / 4)) xs as B.
      rewrite E2 in B. cbn [List.length] in B. ZnWords.
    }
    rewrite <- E in H.
    SeparationLogic.seprewrite_in @array_append H.
    SeparationLogic.seprewrite_in @array_cons H.
    SeparationLogic.seprewrite_in @array_cons H.
    replace (word.add addr (word.of_Z (word.unsigned (word.of_Z 4) * Z.of_nat (Datatypes.length (h1 :: t1)))))
      with addr in H by ZnWords.
    unfold scalar32 at 1 3 in H.
    unfold truncated_word, truncated_scalar, littleendian, ptsto_bytes.ptsto_bytes in H.
    cbn in H.
    rewrite !HList.tuple.to_list_of_list in H.
    eapply (ptsto_nonaliasing addr (List.hd Byte.x00 (LittleEndianList.le_split 4 (word.unsigned h2))) (List.hd Byte.x00 (LittleEndianList.le_split 4 (word.unsigned h1))) m).
    unfold LittleEndianList.le_split, List.hd, array in *.
    ecancel_assumption.
  Qed.

  Local Infix "*" := sep. Local Infix "*" := sep : type_scope.

  Instance spec_of_insertionsort : spec_of "insertionsort" :=
    fnspec! "insertionsort" addr n / xs R,
    { requires t m := n = word.of_Z (Z.of_nat (List.length xs)) /\ (array scalar32 (word.of_Z 4) addr xs * R) m;
      ensures t' m' := t = t' /\ exists ys,
            Sorted ys /\ Permutation xs ys /\ (array scalar32 (word.of_Z 4) addr ys * R) m' }.

  Definition sorted_except(unsortedLen: nat)(addr: word)(xs: list word)(m: mem)(R: mem -> Prop): Prop :=
    exists sorted unsorted,
      List.length unsorted = unsortedLen /\
      (array scalar32 (word.of_Z 4) addr (sorted ++ unsorted) * R) m /\
      Sorted sorted /\ Permutation xs (sorted ++ unsorted).

  Lemma insertionsort_ok : program_logic_goal_for_function! insertionsort.
  Proof.
    repeat straightline.

    assert (4 * Z.of_nat (List.length xs) <= 2 ^ 32). {
      eapply array_scalar32_max_size. eassumption.
    }

    refine (tailrec HList.polymorphic_list.nil
        ["a"; "i"; "n"]
        (fun unsortedLen t m a i n => PrimitivePair.pair.mk
          (Z.of_nat (List.length xs) = word.unsigned n /\
           word.unsigned i + Z.of_nat unsortedLen = word.unsigned n /\
           a = addr /\
           sorted_except unsortedLen addr xs m R)
          (fun T M A I N => T = t /\ sorted_except 0 addr xs M R))
        lt _ (List.length xs) _ _ _);
    cbn [reconstruct map.putmany_of_list HList.tuple.to_list
         HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
    { repeat straightline. }
    { exact Wf_nat.lt_wf. }
    { (* current state satisfies loop precondition *)
      repeat straightline.
      split. 1: ZnWords. split. 1: ZnWords. split. 1: reflexivity.
      unfold sorted_except. exists nil, xs. cbn [List.app]. eauto using perm_nil, Sorted_nil. }
    { repeat straightline. 2: {
        (* if break, post holds: *)
        clear i n. (* TODO straightline_cleanup should clear these *)
        rename x0 into i, x1 into n.
        replace 0%nat with v. 1: auto. subst br.
        (* COQBUG https://github.com/coq/coq/issues/3051 *)
        let x := constr:(word.unsigned_ltu) in rewrite x in *.
        destruct_one_match_hyp; ZnWords.
      }
      (* if again, execute loop body: *)
      clear i n.
      rename x0 into i, x1 into n.
      subst br.
      match goal with
      | H: context[word.ltu] |- _ =>
        rewrite word.unsigned_ltu in H;
        assert (word.unsigned i < word.unsigned n) by (destruct_one_match_hyp; ZnWords);
        clear H
      end.
      match goal with
      | H: sorted_except _ _ _ _ _ |- _ => destruct H as (sorted & unsorted & ? & ? & ? & ?)
      end.
      destruct unsorted as [|e unsorted].
      { assert (0 = v)%nat by assumption. exfalso. ZnWords. }
      match goal with
      | H: (_ * _)%sep m0 |- _ => rename H into HM
      end.
      change (sorted ++ e :: unsorted) with (sorted ++ [e] ++ unsorted) in HM.
      do 2 seprewrite_in @array_append' HM.
      cbn -[scalar32] in HM.
      match goal with
      | H: Permutation _ _ |- _ => pose proof (Permutation_length H) as PL
      end.
      rewrite List.app_length in PL.
      rewrite @List.length_cons in *.
      match type of HM with
      | context[word.add _ (word.mul _ ?x)] => replace x with i in HM by ZnWords
      end.
      eexists. split. {
        repeat straightline.
      }
      repeat straightline.

      refine (tailrec (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _
                      (HList.polymorphic_list.cons _ HList.polymorphic_list.nil)))
          ["a"; "i"; "j"; "n"; "t"]
          (fun remSortedLen seenSorted remSorted R t m a i0 j n0 e0 => PrimitivePair.pair.mk
            (List.length remSorted = remSortedLen /\
             i0 = i /\ a = addr /\ n0 = n /\ e0 = e /\ sorted = seenSorted ++ remSorted /\
             word.unsigned j + Z.of_nat remSortedLen = word.unsigned i /\
             (forall k: nat, (k < List.length seenSorted)%nat -> word.ltu e (nth sorted k) = false) /\
             (array scalar32 (word.of_Z 4) (word.add addr (word.mul (word.of_Z 4) j)) remSorted *
              scalar32 (word.add addr (word.mul (word.of_Z 4) i)) e * R) m)
            (fun T M A I J N E => T = t /\ I = i /\ N = n /\ e = E /\ a = A /\
              word.unsigned J <= word.unsigned i /\
              List.length remSorted = remSortedLen /\
              sorted = seenSorted ++ remSorted /\
              word.ltu (nth (sorted ++ [e]) (Z.to_nat (word.unsigned J))) e = false /\
              (forall k: nat, (k < Z.to_nat (word.unsigned J))%nat -> word.ltu e (nth sorted k) = false) /\
              (array scalar32 (word.of_Z 4)
                     (word.add addr (word.mul (word.of_Z 4)
                                              (word.of_Z (word.unsigned i - Z.of_nat remSortedLen))))
                     remSorted *
               scalar32 (word.add addr (word.mul (word.of_Z 4) i)) e * R) M))
          lt _ (List.length sorted) _ _ _ _ _ _);
      cbn [reconstruct map.putmany_of_list HList.tuple.to_list
           HList.hlist.foralls HList.tuple.foralls
           HList.hlist.existss HList.tuple.existss
           HList.hlist.apply  HList.tuple.apply
           HList.hlist
           List.repeat Datatypes.length
           HList.polymorphic_list.repeat HList.polymorphic_list.length
           PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
      { repeat straightline. }
      { exact Wf_nat.lt_wf. }
      { (* current state satisfies loop precondition *)
        repeat straightline. ssplit. all: reflexivity || ZnWords || idtac.
        { instantiate (1 := []). reflexivity. }
        { intros k C. inversion C. }
        subst j.
        match goal with
        | |- context[array _ _ ?a] => replace a with addr by ZnWords
        end.
        ecancel_assumption. }
      { repeat straightline.
        clear j. subst sorted.
        rename x4 into j, x into seenSorted, x0 into remSorted, v0 into remSortedLen, x1 into R'.
        destruct remSorted as [|e' remSorted].
        { (* exiting loop because element e itself has been reached *)
          assert (0 = remSortedLen)%nat by assumption. subst remSortedLen.
          assert (j = i) by ZnWords. subst j.
          eexists. split. {
            repeat straightline.
          }
          split; intro C. {
            exfalso.
            rewrite word.unsigned_ltu in C. rewrite Z.ltb_irrefl in C. rewrite word.unsigned_of_Z_0 in C.
            apply C. reflexivity.
          }
          destruct_one_match_hyp. {
            rewrite word.unsigned_of_Z_1 in C. discriminate C.
          }
          ssplit. all: try reflexivity || ZnWords.
          { unfold nth.
            rewrite List.app_nil_r.
            rewrite List.app_nth2 by ZnWordsL.
            match goal with
            | |- context[List.nth ?N _ _] => replace N with O by ZnWordsL
            end.
            assumption. }
          { intros k Hk.
            match goal with
            | H: forall _: nat, _ -> _ |- _ => apply H
            end.
            ZnWordsL. }
          match goal with
          | H: (_ * _) m1 |- _ => rename H into HM1
          end.
          SeparationLogic.seprewrite @array_nil.
          SeparationLogic.seprewrite_in @array_nil HM1.
          exact HM1.
        }
        cbn [List.length] in *.
        match goal with
        | H: (_ * _) m1 |- _ => rename H into HM1
        end.
        seprewrite_in @array_cons HM1.
        eexists. split. {
          repeat straightline.
        }
        split; intro C. 2: {
          (* exiting loop because e' >= e found, so we know where to insert e *)
          destruct_one_match_hyp. {
            rewrite word.unsigned_of_Z_1 in C. discriminate C.
          }
          ssplit. all: try reflexivity || ZnWords.
          { unfold nth.
            replace (Z.to_nat (word.unsigned j)) with (List.length seenSorted) by ZnWordsL.
            rewrite <- List.app_assoc. rewrite <- List.app_comm_cons.
            rewrite List.nth_middle.
            assumption. }
          { intros k Hk.
            match goal with
            | H: forall _: nat, _ -> _ |- _ => apply H
            end.
            ZnWordsL. }
          SeparationLogic.seprewrite @array_cons.
          use_sep_assumption.
          cancel.
          cancel_seps_at_indices 0%nat 0%nat. {
            f_equal. f_equal. ZnWords.
          }
          cancel_seps_at_indices 0%nat 0%nat. {
            f_equal. f_equal. ZnWords.
          }
          reflexivity.
        }
        (* running loop body (just increment j) *)
        rewrite word.unsigned_ltu in C. destruct_one_match_hyp. 2: {
          exfalso. rewrite word.unsigned_of_Z_0 in C. apply C. reflexivity.
        }
        repeat straightline.

        (* at end of first inner loop *)
        eexists (seenSorted ++ [e']), remSorted, _, _. split.
        { (* precondition of next loop iteration holds *)
          ssplit. all: rewrite <-?List.app_assoc; try reflexivity || ZnWords.
          { intros k Hk. assert (k < List.length seenSorted \/ k = List.length seenSorted)%nat as D by ZnWordsL.
            unfold nth in *.
            destruct D as [D | D].
            - auto.
            - subst k. rewrite List.nth_middle.
              rewrite word.unsigned_ltu. apply Z.ltb_ge. ZnWords. }
          subst j.
          use_sep_assumption. cancel.
          cancel_seps_at_indices 1%nat 0%nat. {
            f_equal. ZnWords.
          }
          ecancel_done.
        }
        split.
        { (* measure decreases *) ZnWords. }
        { (* postcondition of previous loop iteration implies postcondition of current loop iteration *)
          rename e into e''.
          intros T M A I J N e.
          repeat straightline.
          ssplit. all: try reflexivity || assumption || ZnWords.
          SeparationLogic.seprewrite @array_cons.
          use_sep_assumption.
          cancel.
          cancel_seps_at_indices 0%nat 1%nat. {
            f_equal. ZnWords.
          }
          cancel_seps_at_indices 0%nat 0%nat. {
            f_equal. ZnWords.
          }
          ecancel_done.
        }
      }
      repeat straightline. clear j.
      rename x into a, x1 into j, x3 into e.
      match goal with
      | H: (_ * _) m1 |- _ => rename H into HM1
      end.
      match type of HM1 with
      | context[array scalar32 _ ?A sorted] => replace A with a in HM1 by ZnWords
      end.

      remember (List.firstn (Z.to_nat (word.unsigned j)) sorted) as smaller.
      remember (List.skipn (Z.to_nat (word.unsigned j)) sorted) as toShift.
      assert (sorted = smaller ++ toShift). {
        subst smaller toShift. symmetry. apply List.firstn_skipn.
      }
      assert (word.unsigned j = Z.of_nat (List.length smaller)) as Ej. {
        subst smaller. ZnWordsL.
      }
      rewrite Ej in *.
      (* WHY do I need width:=width even with   Local Hint Mode word - : typeclass_instances. ? *)
      replace j with (word.of_Z (width := 32) (Z.of_nat (Datatypes.length smaller))) by ZnWords.
      clear j Ej Heqsmaller HeqtoShift.
      rewrite List.app_nil_l in *.
      subst sorted.
      straightline_cleanup.
      rename a into addr.

      (* second inner loop: *)
      refine (tailrec (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ HList.polymorphic_list.nil))
          ["a"; "i"; "j"; "n"; "t"]
          (fun StoShiftLen toShift R t m a i0 j n0 shelf => PrimitivePair.pair.mk
            (i0 = i /\ a = addr /\ n0 = n /\
             match StoShiftLen with
             | S toShiftLen => List.length toShift = toShiftLen /\
                               word.unsigned j + Z.of_nat toShiftLen = word.unsigned i /\
                               (array scalar32 (word.of_Z 4) (word.add addr (word.mul (word.of_Z 4) j))
                                      (toShift ++ [e]) * R) m
             | O => (* special precondition for just before exiting the loop: *)
                    word.unsigned j = word.unsigned i + 1 /\ toShift = [] /\ R m
             end)
            (fun T M A I J N E => T = t /\ I = i /\ N = n /\ A = a /\
               match StoShiftLen with
               | S toShiftLen =>
                 (array scalar32 (word.of_Z 4)
                   (word.add addr (word.mul (word.of_Z 4) (word.of_Z (word.unsigned i - Z.of_nat toShiftLen))))
                   (shelf :: toShift) * R) M
               | O => R M
               end))
          lt _ (S (List.length toShift)) _ _ _ _ _);
      cbn [reconstruct map.putmany_of_list HList.tuple.to_list
           HList.hlist.foralls HList.tuple.foralls
           HList.hlist.existss HList.tuple.existss
           HList.hlist.apply  HList.tuple.apply
           HList.hlist
           List.repeat Datatypes.length
           HList.polymorphic_list.repeat HList.polymorphic_list.length
           PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
      { repeat straightline. }
      { exact Wf_nat.lt_wf. }
      { (* current state satisfies loop precondition *)
        repeat straightline. ssplit. all: reflexivity || ZnWordsL || idtac.
        SeparationLogic.seprewrite @array_append.
        SeparationLogic.seprewrite_in @array_append HM1.
        SeparationLogic.seprewrite @array_cons.
        SeparationLogic.seprewrite @array_nil.
        use_sep_assumption.
        cancel.
        cancel_seps_at_indices 1%nat 1%nat. {
          f_equal. ZnWords.
        }
        cancel_seps_at_indices 1%nat 0%nat. {
          f_equal. ZnWordsL.
        }
        cbn [seps].
        cancel.
      }
      { rename toShift into toShift_orig, R into R_orig, t into t0.
        intros StoShiftLen toShift R t m2 a i0 j n0 shelf.
        repeat straightline. 2: {
          (* if break, postcondition holds *)
          ssplit. all: try reflexivity.
          match goal with
          | H: word.unsigned br = 0 |- _ => rename H into HC
          end.
          subst br. move HC at bottom. destruct_one_match_hyp. {
            rewrite word.unsigned_of_Z_1 in HC. discriminate HC.
          }
          clear HC.
          rewrite word.unsigned_ltu in E. apply Z.ltb_ge in E.
          destruct StoShiftLen as [|toShiftLen]; repeat straightline_cleanup. 2: {
            exfalso. ZnWords.
          }
          assumption.
        }
        (* loop body of second inner loop: *)
        match goal with
        | H: word.unsigned br <> 0 |- _ => rename H into HC
        end.
        subst br. move HC at bottom. destruct_one_match_hyp. 2: {
          exfalso. rewrite word.unsigned_of_Z_0 in HC. apply HC. reflexivity.
        }
        clear HC.
        rewrite word.unsigned_ltu in E. apply Z.ltb_lt in E.
        destruct StoShiftLen as [|toShiftLen]; repeat straightline_cleanup. {
          exfalso. ZnWords.
        }
        assert (exists y ys, toShift ++ [e] = y :: ys) as Ey. {
          destruct toShift.
          - cbn. exists e, nil. reflexivity.
          - exists r, (toShift ++ [e]). reflexivity.
        }
        destruct Ey as (y & ys & Ey).
        match goal with
        | H: (_ * _) m2 |- _ => rename H into HM2
        end.
        rewrite Ey in HM2.
        seprewrite_in @array_cons HM2.
        repeat straightline. (* <- steps through all of second inner loop body *)

        subst toShiftLen.
        destruct toShift as [|e' toShift]; cycle 1; cbn [List.length] in *.
        - subst j.
          rewrite <- List.app_comm_cons in Ey. injection Ey. clear Ey. intros. subst y ys.
          eexists _, _, (S (Datatypes.length toShift)). split.
          { (* precondition of next loop iteration holds *)
            ssplit. all: try reflexivity || ZnWords.
            use_sep_assumption.
            cancel.
            cancel_seps_at_indices 1%nat 0%nat. {
              f_equal. ZnWords.
            }
            ecancel_done.
          }
          split.
          { (* measure decreases *) constructor. }
          { (* postcondition of previous loop iteration implies postcondition of current loop iteration *)
            repeat straightline.
            ssplit. all: try reflexivity.
            SeparationLogic.seprewrite @array_cons.
            use_sep_assumption.
            cancel.
            cancel_seps_at_indices 0%nat 1%nat. {
              f_equal. ZnWords.
            }
            cancel_seps_at_indices 0%nat 0%nat. {
              f_equal. ZnWords.
            }
            reflexivity. }
        - subst j. cbn [List.app] in Ey.
          injection Ey. clear Ey. intros. subst y ys.
          match goal with
          | H: (_ * _) m3 |- _ => rename H into HM3
          end.
          unfold array in HM3.
          eexists [], _, O. split.
          { (* precondition of next loop iteration holds *)
            ssplit. all: try reflexivity || ZnWords. exact HM3. }
          split.
          { (* measure decreases *) constructor. }
          { (* postcondition of previous loop iteration implies postcondition of current loop iteration *)
            repeat straightline.
            ssplit. all: try reflexivity.
            SeparationLogic.seprewrite @array_cons.
            SeparationLogic.seprewrite @array_nil.
            use_sep_assumption.
            cancel.
            cancel_seps_at_indices 0%nat 0%nat. {
              f_equal. ZnWords.
            }
            reflexivity. }
      }

      repeat straightline. (* <-- increment i *)

      (* at end of outer loop *)
      subst v. exists (List.length unsorted). split.
      { (* precondition of next loop iteration holds *)
        ssplit. all: try ZnWords.
        unfold sorted_except.
        exists (smaller ++ [e] ++ toShift), unsorted.
        ssplit. 1: reflexivity.
        { rewrite ?List.app_assoc. repeat SeparationLogic.seprewrite @array_append.
          match goal with
          | H: (_ * _) m2 |- _ => rename H into HM2
          end.
          SeparationLogic.seprewrite_in @array_cons HM2.
          SeparationLogic.seprewrite @array_cons.
          SeparationLogic.seprewrite @array_nil.
          use_sep_assumption. cancel.
          cancel_seps_at_indices 0%nat 0%nat. {
            f_equal. ZnWordsL.
          }
          cancel_seps_at_indices 0%nat 0%nat. {
            f_equal. ZnWordsL.
          }
          cancel_seps_at_indices 0%nat 0%nat. {
            f_equal. ZnWordsL.
          }
          ecancel_done.
        }
        { match goal with
          | H: word.ltu _ _ = false |- _ => rename H into HLt; move HLt at bottom
          end.
          unfold nth in HLt. rewrite Znat.Nat2Z.id in HLt. rewrite <- List.app_assoc in HLt.
          destruct toShift as [|e' toShift]; cycle 1.
          - rewrite <- List.app_comm_cons in HLt.
            rewrite List.nth_middle in HLt.

            eapply Sorted_insert; try eassumption.
            intros k Hk.
            rewrite Znat.Nat2Z.id in *.
            match goal with
            | H: forall _: nat, _ -> _ |- _ => specialize H with (1 := Hk); rename H into B; move B at bottom
            end.
            unfold nth in B.
            rewrite List.app_nth1 in B by assumption. exact B.
          - rewrite List.app_nil_r in *.
            eapply Sorted_snoc. 1: assumption.
            rewrite Znat.Nat2Z.id in *. assumption.
        }
        match goal with
        | H: Permutation _ _ |- _ => rename H into HP; move HP at bottom
        end.
        clear -HP.
        change (e :: unsorted) with ([e] ++ unsorted) in HP.
        rewrite List.app_assoc in HP.
        eapply perm_trans. 1: exact HP.
        clear HP.
        apply Permutation_app. 2: apply Permutation_refl.
        rewrite <- List.app_assoc.
        apply Permutation_app. 1: apply Permutation_refl.
        apply Permutation_app_comm.
      }
      split.
      { (* measure decreases *) constructor. }
      { (* postcondition of previous loop iteration implies postcondition of current loop iteration *)
        repeat straightline. auto. }
    }
    repeat straightline.
    ssplit; try reflexivity.
    match goal with
    | H: sorted_except _ _ _ _ _ |- _ => destruct H as (sorted & unsorted & EL & HM0 & So & Pe)
    end.
    destruct unsorted. 2: discriminate EL.
    rewrite List.app_nil_r in *. eauto.
  Time Qed. (* 4.208 secs *)

  (*
  From bedrock2 Require Import ToCString Bytedump.
  Local Open Scope bytedump_scope.
  Goal True.
    let c_code := eval cbv in (String.list_byte_of_string (c_module [insertionsort])) in
    idtac c_code.
  Abort.
  *)
(* append this driver code for a little test:
#include <stdio.h>

void printlist(uint32_t* a, size_t n) {
  for (size_t i = 0; i < n; i++) {
    printf("%d ", a[i]);
  }
  printf("\n");
}

int main() {
  uint32_t a[] = {12, 50000, 23, 11167, 1000};
  size_t n = 5;
  printlist(a, n);
  insertionsort(a, n);
  printlist(a, n);
}
*)
End WithParameters.
