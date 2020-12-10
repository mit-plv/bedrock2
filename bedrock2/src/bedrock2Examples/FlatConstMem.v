Require Import bedrock2.Syntax bedrock2.NotationsCustomEntry.
Require Import bedrock2.FE310CSemantics.

Import Syntax BinInt String Datatypes List List.ListNotations ZArith.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion expr.literal : Z >-> expr.
Local Coercion expr.var : String.string >-> expr.
Local Coercion name_of_func (f : func) : String.string := fst f.

Definition silly1 : func :=
    let a := "a" in
    let b := "b" in
    let c := "c" in
  ("silly1", ([a], [c], bedrock_func_body:(
      b = load4(a + coq:(16));
      store4(a + coq:(14), b);
      c = load4(a + coq:(16))
  ))).

Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import bedrock2.Semantics bedrock2.ProgramLogic bedrock2.Array.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import Coq.Lists.List coqutil.Map.OfListWord.
Require Import coqutil.Z.Lia.
Import Map.Interface Interface.map OfFunc.map OfListWord.map.
Section WithParameters.
  Context {p : FE310CSemantics.parameters}.
  Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).

  Local Instance spec_of_silly1 : spec_of "silly1" := fun functions =>
      forall t m a bs R, Z.of_nat (length bs) = 32 ->
      (sep (eq (map.of_list_word_at a bs)) R) m ->
      WeakestPrecondition.call functions silly1 t m [a]
      (fun T M rets => True).
  Require Import coqutil.Tactics.letexists.
  Require Import coqutil.Tactics.rdelta.

  Ltac ring_simplify_unsigned_goal :=
    match goal with
    |- context [word.unsigned ?x] =>
      let Hrw := fresh in
      eassert (let y := _ in x = y) as Hrw by (
        let y := fresh in
        intros y; ring_simplify;
        subst y; trivial);
      rewrite !Hrw; clear Hrw
    end.
  Ltac ring_simplify_unsigned_in H :=
    match type of H with context [word.unsigned ?x] =>
      let Hrw := fresh in
      eassert (let y := _ in x = y) as Hrw by (
        let y := fresh in
        intros y; ring_simplify;
        subst y; trivial);
      rewrite !Hrw in H; clear Hrw
    end.
  Ltac ring_simplify_unsigned :=
    try ring_simplify_unsigned_goal;
    repeat match goal with
           | H: context [word.unsigned ?x] |- _ => ring_simplify_unsigned_in H
           end.

  Ltac unify_and_change lhs rhs :=
    let rhs := match rhs with ?x => x end in
    let __ := constr:(eq_refl : lhs = rhs) in
    change lhs with rhs in *.

  Require Import bedrock2.AbsintWordToZ.

  Ltac change_with_Z_literal W :=
    first [ let e := open_constr:(BinInt.Zpos _) in
            unify_and_change W e;
            requireZcst e
          | unify_and_change W open_constr:(BinInt.Z0)
          | let e := open_constr:(BinInt.Zneg _) in
            unify_and_change W e;
            requireZcst e].

  Ltac simplify_ZcstExpr_goal :=
    match goal with
    |- context [?e] =>
        requireZcstExpr e;
        let Hrw := fresh in
        (* time *) eassert (e = _) by (vm_compute; reflexivity);
        (* idtac "simplified" e "in GOAL"; *)
        progress rewrite Hrw; clear Hrw
    end.

  Ltac simplify_ZcstExpr_in H :=
    match type of H with context [?e] =>
        requireZcstExpr e;
        let Hrw := fresh in
        eassert (e = _) by (vm_compute; reflexivity);
        (* idtac "simplified" e "in" H; *)
        progress rewrite Hrw in H; clear Hrw
    end.

  Ltac simplify_ZcstExpr_hyps :=
    repeat match goal with H : _ |- _ => simplify_ZcstExpr_in H end.

  Ltac simplify_ZcstExpr :=
    simplify_ZcstExpr_hyps; try simplify_ZcstExpr_goal.

  Ltac rewrite_unsigned_of_Z_goal :=
    match goal with
    |- context [@word.unsigned ?w ?W ?X] =>
      let E := constr:(@word.unsigned w W X) in
      let x := rdelta X in
      let z := match x with word.of_Z ?z => z end in
      rewrite ((@word.unsigned_of_Z w W _ z) : E = z mod 2^w)
    end.

  Ltac rewrite_unsigned_of_Z_in H :=
    match type of H with context [@word.unsigned ?w ?W ?X] =>
      let E := constr:(@word.unsigned w W X) in
      let x := rdelta X in
      let z := match x with word.of_Z ?z => z end in
      rewrite ((@word.unsigned_of_Z w W _ z) : E = z mod 2^w) in H
    end.

  Ltac wordcstexpr_tac := (* hacky *)
    repeat first
          [ progress ring_simplify_unsigned
          | rewrite !word.unsigned_add; cbv [word.wrap]
          | rewrite_unsigned_of_Z_goal ];
    try change_with_Z_literal width; repeat simplify_ZcstExpr_goal; trivial.

  Lemma List__splitZ_spec [A] (xsys : list A) i (H : 0 <= i < Z.of_nat (length xsys)) :
    let xs := firstn (Z.to_nat i) xsys in
    let ys := skipn (Z.to_nat i) xsys in
    xsys = xs ++ ys /\
    Z.of_nat (length xs) = i /\
    Z.of_nat (length ys) = Z.of_nat (length xsys) - i.
  Proof.
    pose proof eq_sym (firstn_skipn (Z.to_nat i) xsys).
    split; trivial.
    rewrite length_firstn_inbounds, length_skipn; blia.
  Qed.

  Ltac lift_head_let_in H :=
    match type of H with
    | let x := ?v in ?C =>
        let X := fresh x in
        pose v as X;
        let C := constr:(match X with x => C end) in
        change C in H
    end.

  Ltac flatten_hyps :=
    repeat match goal with
           | H : let x := ?v in ?C |- _ =>
               let X := fresh x in
               pose v as X;
               let C := constr:(match X with x => C end) in
               change C in H
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           end.

  Lemma List__splitZ_spec_n [A] (xsys : list A) i n
    (Hn : Z.of_nat (length xsys) = n) (H : 0 <= i < n) :
    let xs := firstn (Z.to_nat i) xsys in
    let ys := skipn (Z.to_nat i) xsys in
    xsys = xs ++ ys /\
    Z.of_nat (length xs) = i /\
    Z.of_nat (length ys) = n - i.
  Proof.
    pose proof eq_sym (firstn_skipn (Z.to_nat i) xsys).
    split; trivial.
    rewrite length_firstn_inbounds, length_skipn; blia.
  Qed.


  Require Import coqutil.Tactics.rewr.
  Ltac List__splitZ bs n :=
      match goal with H: Z.of_nat (length bs) = _ |- _ =>
          pose proof List__splitZ_spec_n bs n _ H ltac:(blia);
          clear H; flatten_hyps; simplify_ZcstExpr;
          let Hrw := lazymatch goal with H : bs = _ ++ _ |- _ => H end in
          let eqn := type of Hrw in
          rewr ltac:(fun t => match t with
                              | eqn => fail 1
                              | _ => constr:(Hrw) end) in *
      end.

  Lemma map__of_list_word_at_app_n [value] [map : map.map word value] {ok : map.ok map}
    (a : word) (xs ys : list value)
    lxs (Hlxs : Z.of_nat (length xs) = lxs)
    : map.of_list_word_at a (xs ++ ys)
    = putmany (map.of_list_word_at (word.add a (word.of_Z lxs)) ys) (map.of_list_word_at a xs).
  Proof. subst lxs; apply map.of_list_word_at_app. Qed.

  Lemma map__adjacent_arrays_disjoint_n [value] [map : map.map word value] {ok : map.ok map}
    (a : word) (xs ys : list value)
    lxs (Hlxs : Z.of_nat (length xs) = lxs)
    (H :Z.of_nat (length xs) + Z.of_nat (length ys) <= 2 ^ width)
    : disjoint (map.of_list_word_at (word.add a (word.of_Z lxs)) ys) (map.of_list_word_at a xs).
  Proof. subst lxs. auto using map.adjacent_arrays_disjoint. Qed.

      Declare Scope word_scope.
      Bind Scope word_scope with word.
      Delimit Scope word_scope with word.
      Local Notation "a + b" := (word.add a b) (at level 50, left associativity, format "a + b") : word_scope.
      Local Infix "-" := word.sub : word_scope.
      Local Coercion Z.of_nat : nat >-> Z.
      Local Infix "$+" := putmany (at level 70).
      Local Notation "xs $@ a" := (map.of_list_word_at a%word xs) (at level 10, format "xs $@ a").
      Local Notation "! x" := (word.of_Z x) (at level 10, format "! x").
      Local Notation "a * b" := (sep a%type b%type) : type_scope.
      Local Open Scope word_scope.

  Lemma sep_eq_putmany [key value] [map : map.map key value] (a b : map) (H : disjoint a b) : Lift1Prop.iff1 (eq (a $+ b)) (sep (eq a) (eq b)).
  Proof.
    split.
    { intros; subst. eexists _, _; eauto using Properties.map.split_disjoint_putmany. }
    { intros (?&?&(?&?)&?&?); subst; trivial. }
  Qed.

  Lemma sep_eq_of_list_word_at_app [value] [map : map.map word value] {ok : map.ok map}
    (a : word) (xs ys : list value)
    lxs (Hlxs : Z.of_nat (length xs) = lxs) (Htotal : length xs + length ys <= 2^width)
    : Lift1Prop.iff1 (eq (map.of_list_word_at a (xs ++ ys)))
      (sep (eq (map.of_list_word_at a xs)) (eq (map.of_list_word_at (word.add a (word.of_Z lxs)) ys))).
  Proof.
    etransitivity.
    2: eapply sep_comm.
    etransitivity.
    2: eapply sep_eq_putmany, map__adjacent_arrays_disjoint_n; trivial.
    erewrite map__of_list_word_at_app_n by eauto; reflexivity.
  Qed.

  Lemma list_word_at_app_of_adjacent_eq [value] [map : map.map word value] {ok : map.ok map}
    (a b : word) (xs ys : list value)
    (Hl: word.unsigned (word.sub b a) = Z.of_nat (length xs))
    (Htotal : length xs + length ys <= 2^width)
    : Lift1Prop.iff1
        (sep (eq (map.of_list_word_at a xs)) (eq (map.of_list_word_at b ys)) )
        (eq (map.of_list_word_at a (xs ++ ys))).
  Proof.
    etransitivity.
    2:symmetry; eapply sep_eq_of_list_word_at_app; trivial.
    do 3 Morphisms.f_equiv. rewrite <-Hl, word.of_Z_unsigned. ring.
  Qed.

  Lemma of_list_word_nil
    [value] [map : map.map word value] {ok : map.ok map}
    k : []$@k = empty.
  Proof. apply Properties.map.fold_empty. Qed.
  Lemma of_list_word_singleton
    [value] [map : map.map word value] {ok : map.ok map}
    k v : [v]$@k = put empty k v.
  Proof.
    cbv [of_list_word_at of_list_word seq length List.map of_func update].
    rewrite word.unsigned_of_Z_0, Z2Nat.inj_0; cbv [MapKeys.map.map_keys nth_error].
    rewrite Properties.map.fold_singleton.
    f_equal; cbn [Z.of_nat].
    eapply word.unsigned_inj; rewrite word.unsigned_add; cbv [word.wrap]; rewrite word.unsigned_of_Z_0, Z.add_0_r, Z.mod_small; trivial; eapply word.unsigned_range.
  Qed.

  Import ptsto_bytes Lift1Prop Morphisms.
  Lemma eq_of_list_word_iff_array1 [value] [map : map.map word value] {ok : map.ok map}
    (a : word) (bs : list value)
    (H : length bs <= 2 ^ width) :
    iff1 (eq (bs$@a)) (array ptsto (word.of_Z 1) a bs).
  Proof.
    revert H; revert a; induction bs; cbn [array]; intros.
    { rewrite of_list_word_nil; cbv [emp iff1]; intuition auto. }
    { etransitivity.
      2: eapply Proper_sep_iff1.
      3: eapply IHbs.
      2: reflexivity.
      2: cbn [length] in H; blia.
      change (a::bs) with ([a]++bs).
      rewrite of_list_word_at_app.
      etransitivity.
      1: eapply sep_eq_putmany, adjacent_arrays_disjoint; cbn [length] in *; blia.
      etransitivity.
      2:eapply sep_comm.
      f_equiv.
      rewrite of_list_word_singleton; try exact _.
      cbv [ptsto iff1]; intuition auto. }
  Qed.

  Ltac ring_simplify_address_in H :=
    match type of H with context [_ $@ ?x] =>
      let Hrw := fresh in
      eassert (let y := _ in x = y) as Hrw by (
        let y := fresh in
        intros y; ring_simplify;
        subst y; trivial);
      rewrite !Hrw in H; clear Hrw
    end.
  Require Import coqutil.Tactics.Tactics.

  Ltac split_bytes_base_addr bs a0 ai :=
      let raw_i := constr:(word.unsigned (ai-a0)%word) in
      let Hidx := fresh "Hidx" in
      eassert (raw_i = _) as Hidx by (
        ring_simplify_unsigned_goal; repeat rewrite_unsigned_of_Z_goal;
        change_with_Z_literal constr:(width); simplify_ZcstExpr; exact eq_refl);
      let i := match type of Hidx with _ = ?r => r end in
      let Happ := fresh "Happ" in
      match goal with H: Z.of_nat (length bs) = _ |- _ =>
          pose proof List__splitZ_spec_n bs i _ H ltac:(blia) as Happ;
          clear H
      end;
      repeat lift_head_let_in Happ; case Happ as (Happ&?H1l&?H2l);
      simplify_ZcstExpr;
      let eqn := type of Happ in
      rewr ltac:(fun t => match t with
                          | eqn => fail 1
                          | _ => constr:(Happ) end) in *;
      repeat match goal with Hsep : _ |- _ =>
        seprewrite_in_by sep_eq_of_list_word_at_app Hsep ltac:(
          try eassumption; try (change_with_Z_literal constr:(width); blia))
      end.

  Section __.
    Import WithoutTuples.
    Lemma load_bytes_of_putmany_bytes_at bs a mR n (Hn : length bs = n) (Hl : Z.of_nat n < 2^width)
      : load_bytes (mR $+ bs$@a) a n = Some bs.
    Proof.
      destruct (load_bytes (mR $+ bs$@a) a n) eqn:HN in *; cycle 1.
      { exfalso; eapply load_bytes_None in HN; case HN as (i&?&?).
        case (Properties.map.putmany_spec mR (bs$@a) (a+!(BinIntDef.Z.of_nat i))%word) as [(?&?&?)| (?&?) ]; try congruence.
        rewrite get_of_list_word_at in H1; eapply nth_error_None in H1.
        revert H1.
        rewrite word.word_sub_add_l_same_l, word.unsigned_of_Z.
        cbv [word.wrap]; rewrite Z.mod_small, Nat2Z.id; eauto; blia. }
      transitivity (Some l); try congruence; f_equal; subst n.
      symmetry; eapply nth_error_ext_samelength.
      { symmetry; eauto using length_load_bytes. }
      intros.
      pose proof nth_error_load_bytes _ a _ _ HN i ltac:(trivial) as HH.
      epose proof H; eapply nth_error_nth' with (d:=Byte.x00) in H.
      erewrite Properties.map.get_putmany_right in HH; cycle 1.
      { rewrite get_of_list_word_at.
        rewrite word.word_sub_add_l_same_l, word.unsigned_of_Z.
        cbv [word.wrap]; rewrite Z.mod_small, Nat2Z.id; eauto; blia. }
      congruence.
    Qed.

    Lemma load_bytes_of_sep_bytes_at bs a R m (Hsep: (eq(bs$@a)*R) m) n (Hn : length bs = n) (Hl : Z.of_nat n < 2^width)
      : load_bytes m a n = Some bs.
    Proof.
      eapply sep_comm in Hsep.
      destruct Hsep as (mR&?&(?&?)&?&?); subst.
      eapply load_bytes_of_putmany_bytes_at; eauto.
    Qed.
  End __.

  Lemma load_four_bytes_of_sep_at bs a R m (Hsep: (eq(bs$@a)*R) m) (Hl : length bs = 4%nat) :
    load access_size.four m a = Some (word.of_Z (LittleEndian.combine _ (HList.tuple.of_list bs))).
  Proof.
    seprewrite_in (eq_of_list_word_iff_array1) Hsep.
    { change_with_Z_literal width; blia. }
    seprewrite_in open_constr:(Scalars.scalar32_of_bytes _ _ _) Hsep.
    erewrite @Scalars.load_four_of_sep; shelve_unifiable; try exact _; eauto.
    Unshelve. (* where does this evar come from? *)
    2: eauto.
    f_equal.
    f_equal.
    rewrite word.unsigned_of_Z.
    cbv [word.wrap]; rewrite Z.mod_small; trivial.
    pose proof LittleEndian.combine_bound (HList.tuple.of_list bs).
    rewrite Hl in H at 3.
    blia.
  Qed.

  Lemma uncurried_load_four_bytes_of_sep_at bs a R (m : mem)
    (H: (eq(bs$@a)*R) m /\ length bs = 4%nat) :
    load access_size.four m a = Some (word.of_Z (LittleEndian.combine _ (HList.tuple.of_list bs))).
  Proof. eapply load_four_bytes_of_sep_at; eapply H. Qed.

  Lemma Z_uncurried_load_four_bytes_of_sep_at bs a R (m : mem)
    (H: (eq(bs$@a)*R) m /\ Z.of_nat (length bs) = 4) :
    load access_size.four m a = Some (word.of_Z (LittleEndian.combine _ (HList.tuple.of_list bs))).
  Proof. eapply load_four_bytes_of_sep_at; try eapply H; blia. Qed.

  (*
  Lemma store_four_of_sep addr (oldvalue : word32) (value : word) R m (post:_->Prop)
    (Hsep : sep (scalar32 addr oldvalue) R m)
    (Hpost : forall m, sep (scalar32 addr (word.of_Z (word.unsigned value))) R m -> post m)
    : exists m1, Memory.store Syntax.access_size.four m addr value = Some m1 /\ post m1.
  Proof.
  *)

  Ltac split_flat_memory_based_on_goal :=
    lazymatch goal with
    | |- load ?sz ?m ?a = _ =>
        let sz := eval cbv in (Z.of_nat (bytes_per (width:=width) sz)) in
        match goal with H : ?S m |- _ =>
        match S with context[?bs $@ ?a0] =>
        let a_r := constr:(word.add a (word.of_Z sz)) in
        split_bytes_base_addr bs a0 a_r end;
        match type of H with context[?bs $@ ?a0] =>
        split_bytes_base_addr bs a0 a end end
    | |- WeakestPrecondition.store ?sz ?m ?a _ _ =>
        let sz := eval cbv in (Z.of_nat (bytes_per (width:=width) sz)) in
        match goal with H : ?S m |- _ =>
        match S with context[?bs $@ ?a0] =>
        let a_r := constr:(word.add a (word.of_Z sz)) in
        split_bytes_base_addr bs a0 a_r end;
        match type of H with context[?bs $@ ?a0] =>
        split_bytes_base_addr bs a0 a end end
    end.

  Ltac subst_lets :=
    repeat match goal with x := ?v |- _ => assert_fails (is_evar v); subst x end.

  Ltac set_evars :=
    repeat match goal with
           | |- context [?e] => is_evar e; set e in *
           | H: context [?e] |- _ => is_evar e; set e in *
           end.
  Ltac subst_evars :=
    repeat match goal with 
    x := ?e |- _ => is_evar e; subst x
           end.

  Lemma silly1_ok : program_logic_goal_for_function! silly1.
  Proof.
    repeat straightline.

    (* note: creating this evar here means that context variables introduced by flat memory automation can not appear in the value eventually filled in for the evar. Maybe we should not have dexpr for this reason? *)
    letexists. split.
    { repeat straightline.
      eexists; split; trivial.
      subst_lets. (* for rewrite and rewr *)
      eapply Z_uncurried_load_four_bytes_of_sep_at.

      set_evars.
      match goal with |- context[?P m] =>
      match P with context[?e$@?a] => idtac e a;
      match goal with | |- context[Z.of_nat (length e) = ?n] =>
      match goal with H : ?S m |- _ =>
      match S with context[?bs $@ ?a0] =>
      let a_r := constr:(word.add a (word.of_Z n)) in
      split_bytes_base_addr bs a0 a_r end;
      match type of H with context[?bs $@ ?a0] =>
      split_bytes_base_addr bs a0 a end end
      end end end.
      subst_evars.

      split; eauto. (* eauto resolves an evar whose context does not contain ys0 *)
      progress match goal with |- context[?e$@?a] => change e with ys0 end.
      ecancel_assumption. }

    set (firstn (Z.to_nat 20) bs) as xs in *.
    set (skipn (Z.to_nat 16) xs) as ys0 in *.

    repeat straightline.
    subst_lets. (* for rewrite and rewr *)
    split_flat_memory_based_on_goal.

    cbv [WeakestPrecondition.store].

    (* skipping actual store for now: *)
    (* pose proof Scalars.store_four_of_sep. *)

    repeat seprewrite_in_by @list_word_at_app_of_adjacent_eq H0 ltac:(
      rewrite ?app_length; wordcstexpr_tac; change_with_Z_literal width; simplify_ZcstExpr; blia).
  Abort.
End WithParameters.
