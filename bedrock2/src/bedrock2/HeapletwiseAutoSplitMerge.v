Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Byte.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Datatypes.ZList.
Require Import coqutil.Datatypes.Inhabited.
Require Import coqutil.Tactics.syntactic_unify.
Require Import coqutil.Tactics.fwd.
Require Import bedrock2.Lift1Prop bedrock2.Map.Separation bedrock2.Map.DisjointUnion.
Require Import bedrock2.PurifySep.
Require Import bedrock2.SepLib.
Require Import bedrock2.sepapp.
Require Import bedrock2.ZnWords.
Require Import bedrock2.HeapletwiseHyps.
Require Import bedrock2.bottom_up_simpl_ltac1.

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
      (word.unsigned (word.sub a' a)) mod elemSize = 0 ->
      word.unsigned (word.sub a' a) / elemSize = i ->
      (forall (vs: list E) m,
          array elem n vs a m ->
          sep (elem vs[i] a')
              (sep (array elem i vs[:i] a)
                   (array elem (n-i-1) vs[i+1:]
                      (word.add a' (word.of_Z elemSize)))) m) /\
      (forall vs1 vs2 v m,
          sep (array elem i vs1 a)
              (sep (elem v a')
                   (array elem (n-i-1) vs2
                      (word.add a' (word.of_Z elemSize)))) m ->
          array elem n (vs1 ++ [|v|] ++ vs2) a m).
  Proof.
  Admitted.

  Lemma split_off_field_from_sepapps: forall n a a' sz ofs,
      word.unsigned (word.sub a' a) = ofs -> (* <- ring proof *)
      (forall l P,
          sepapps_size (List.firstn n l) = ofs -> (* <- determines ofs *)
          List.nth_error l n = Some (mk_sized_predicate P sz) ->
          sepapps l a = sep (P a')
                          (sepapps (List.firstn n l ++
                                      cons (mk_sized_predicate (hole sz) sz)
                                      (List.skipn (S n) l)) a)) /\
      (forall l P,
          sepapps_size (List.firstn n l) = ofs -> (* <- should be eq_refl *)
          List.nth_error l n = Some (mk_sized_predicate (hole sz) sz) ->
          sep (P a') (sepapps l a) =
            (sepapps (List.firstn n l ++
                        cons (mk_sized_predicate P sz)
                        (List.skipn (S n) l)) a)).
  Proof.
    intros. split; intros; subst.
    - rewrite (expose_nth_sepapp l n a P sz H1). f_equal. f_equal.
      rewrite H0. destruct width_cases; subst width; ZnWords.
    - rewrite <- (merge_back_nth_sepapp l n a P sz H1). f_equal. f_equal.
      rewrite H0. destruct width_cases; subst width; ZnWords.
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

(* Is start..start+size a subrange of start'..start'+size' ?
   Assumes 0<=size<2^width and 0<=size'<2^width.
   Both ranges may wrap around. *)
Ltac is_subrange start size start' size' :=
  (* we do the comparison in a different coordinate system, namely relative to start',
     ie we shift (with wrapping) all points so that start' corresponds to zero *)
  assert_succeeds (idtac;
    assert (word.unsigned (word.sub start start') + size <= size') by ZnWords).

Ltac split_range_from_hyp_default :=
  lazymatch goal with
  | |- split_range_from_hyp ?start ?size (with_mem ?m ?P) ?H ?g =>
      let pf := fresh in
      lazymatch P with
      | @array _ _ _ _ _ ?elem (*must match:*)size ?n ?vs ?start' =>
          unshelve epose proof (split_off_elem_from_array start' start elem n _ _ _) as pf;
          [ (* i *)
          | ZnWords
          | bottom_up_simpl_in_goal; reflexivity
          | (* remaining goal *) ]
      end;
      change g;
      eapply (proj1 pf) in H;
      eapply proj2 in pf;
      let t := type of pf in change (merge_step t) in pf
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

Ltac merge_step_in_hyp H :=
  start_canceling_in_hyp H;
  repeat canceling_step_in_hyp H;
  eapply canceling_done_in_hyp in H;
  destruct H as (?m & ?D & ?H).

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

Ltac split_merge_step :=
  lazymatch goal with
  | |- canceling (cons (?P ?start) _) ?m _ =>
      let size := lazymatch constr:(_: PredicateSize P) with ?s => s end in
      let g := lazymatch goal with |- ?x => x end in
      change (find_superrange_hyp start size g)
  | |- find_superrange_hyp ?start ?size ?g =>
      match goal with
      | H: with_mem ?mH (?P' ?start') |- _ =>
          let size' := lazymatch constr:(_: PredicateSize P') with ?s => s end in
          is_subrange start size start' size';
          tryif assert_succeeds (idtac;
            assert (size = size') by ZnWords)
          then (
            change g;
            let P := lazymatch goal with | |- canceling (cons ?P _) _ _ => P end in
            eapply (rew_with_mem (P' start') P mH) in H (* <-- leaves 2 open goals *)
          ) else change (split_range_from_hyp start size _ H g)
      end
  | |- split_range_from_hyp ?start ?size ?tH ?H ?g => split_range_from_hyp_hook
  | |- @eq (@map.rep (@word.rep _ _) Init.Byte.byte _ -> Prop) _ _ =>
      syntactic_f_equal_with_ZnWords
  | H: merge_step _ |- _ => merge_step_in_hyp H
  end.
