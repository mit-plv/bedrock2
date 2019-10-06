Require Import bedrock2.Syntax bedrock2.StringNamesSyntax bedrock2.BasicCSyntax.
Require Import bedrock2.NotationsCustomEntry coqutil.Z.HexNotation.

Import BinInt String List.ListNotations ZArith.
Local Open Scope Z_scope. Local Open Scope string_scope. Local Open Scope list_scope.
Local Existing Instance BasicCSyntax.StringNames_params.
Local Coercion literal (z : Z) : expr := expr.literal z.
Local Coercion var (x : String.string) : expr := expr.var x.
Local Coercion name_of_func (f : function) := fst f.

Local Notation MMIOWRITE := "MMIOWRITE".
Local Notation MMIOREAD := "MMIOREAD".

Require bedrock2Examples.lightbulb_spec.
Local Notation patience := lightbulb_spec.patience.

Definition spi_write : function :=
  let b : varname := "b" in
  let busy : varname := "busy" in
  let i : varname := "i" in
  let SPI_WRITE_ADDR := Ox"10024048" in
  ("spi_write", ((b::nil), (busy::nil), bedrock_func_body:(
    busy = (constr:(-1));
    i = (patience); while (i) { i = (i - constr:(1));
      io! busy = MMIOREAD(SPI_WRITE_ADDR);
      if !(busy >> constr:(31)) {
        i = (i^i)
      }
    };
    if !(busy >> constr:(31)) {
      output! MMIOWRITE(SPI_WRITE_ADDR, b);
      busy = (busy ^ busy)
    }
  ))).

Definition spi_read : function :=
  let b : varname := "b" in
  let busy : varname := "busy" in
  let i : varname := "i" in
  let SPI_READ_ADDR := Ox"1002404c" in
  ("spi_read", (nil, (b::busy::nil), bedrock_func_body:(
    busy = (constr:(-1));
    b = (constr:(Ox"5a"));
    i = (patience); while (i) { i = (i - constr:(1));
      io! busy = MMIOREAD(SPI_READ_ADDR);
      if !(busy >> constr:(31)) {
        b = (busy & constr:(Ox"ff"));
        i = (i^i);
        busy = (busy ^ busy)
      }
    }
  ))).

Definition spi_xchg : function :=
  let b : varname := "b" in
  let busy : varname := "busy" in
  ("spi_xchg", (b::nil, b::busy::nil, bedrock_func_body:(
    unpack! busy = spi_write(b);
    require !busy;
    unpack! b, busy = spi_read()
  ))).

Require Import bedrock2.ProgramLogic.
Require Import bedrock2.FE310CSemantics.
Require Import coqutil.Word.Interface.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.TracePredicate. Import TracePredicateNotations.

Import coqutil.Map.Interface.
Import ReversedListNotations.

Definition mmio_event_abstraction_relation
  (h : lightbulb_spec.OP Semantics.word)
  (l : Semantics.mem * Syntax.actname * list Semantics.word * (Semantics.mem * list Semantics.word)) :=
  Logic.or
    (exists a v, h = lightbulb_spec.st _ a v /\ l = (map.empty, "MMIOWRITE", [a; v], (map.empty, [])))
    (exists a v, h = lightbulb_spec.ld _ a v /\ l = (map.empty, "MMIOREAD", [a], (map.empty, [v]))).
Definition mmio_trace_abstraction_relation := List.Forall2 mmio_event_abstraction_relation.

Instance spec_of_spi_write : spec_of "spi_write" := fun functions => forall t m b,
  word.unsigned b < 2 ^ 8 ->
  WeakestPrecondition.call functions "spi_write" t m [b] (fun T M RETS =>
    M = m /\ exists iol, T = t ;++ iol /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\ exists err, RETS = [err] /\ Logic.or
      (((word.unsigned err <> 0) /\ lightbulb_spec.spi_write_full _ ^* ioh /\ Z.of_nat (length ioh) = patience))
      (word.unsigned err = 0 /\ lightbulb_spec.spi_write Semantics.byte Semantics.word (word.of_Z (word.unsigned b)) ioh)).

Instance spec_of_spi_read : spec_of "spi_read" := fun functions => forall t m,
  WeakestPrecondition.call functions "spi_read" t m [] (fun T M RETS =>
    M = m /\ exists iol, T = t ;++ iol /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\ exists (b:Semantics.byte) (err : Semantics.word), RETS = [word.of_Z (word.unsigned b); err] /\ Logic.or
      (word.unsigned err <> 0 /\ lightbulb_spec.spi_read_empty _ ^* ioh /\ Z.of_nat (length ioh) = patience)
      (word.unsigned err = 0 /\ lightbulb_spec.spi_read Semantics.byte Semantics.word b ioh)).

Lemma nonzero_because_high_bit_set x (H : word.unsigned (word.sru x (word.of_Z 31)) <> 0)
  : word.unsigned x <> 0.
Proof.
  rewrite Properties.word.unsigned_sru_nowrap in H by exact eq_refl.
  intro HX.
  rewrite HX in H.
  exact (H eq_refl).
Qed.

Import coqutil.Tactics.letexists.
Import TailRecursion.
Lemma spi_write_ok : program_logic_goal_for_function! spi_write.
Proof.
  repeat straightline.
  rename H into Hb.

  (* WHY do theese parentheses matter? *)
  refine ((atleastonce ["b"; "busy"; "i"] (fun v T M B BUSY I =>
     b = B /\
     v = word.unsigned I /\
     word.unsigned I <> 0 /\
     M = m /\
     exists tl, T = tl++t /\
     exists th, mmio_trace_abstraction_relation th tl /\
     lightbulb_spec.spi_write_full _ ^* th /\
     Z.of_nat (length th) + word.unsigned I = patience
     )) _ _ _ _ _ _ _);
    cbn [reconstruct map.putmany_of_list HList.tuple.to_list
         HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
  { repeat straightline. }
  { eapply (Z.lt_wf 0). }
  { eexists; split; repeat straightline. inversion H. }
  { repeat (split; trivial; []).
    split.
    { cbv; congruence. }
    split; trivial.
    eexists; split.
    { rewrite app_nil_l; trivial. }
    eexists; split.
    { constructor. }
    split.
    { constructor. }
    exact eq_refl. }
  repeat straightline.
  eapply WeakestPreconditionProperties.interact_nomem; repeat straightline.
  split.
  { cbv. clear. firstorder congruence. }
  repeat straightline. split; trivial.
  letexists. split.
  { repeat straightline. exact eq_refl. }
  (* evaluate condition then split if *) letexists; split; [solve[repeat straightline]|split].
  all: repeat (straightline).
  { do 3 letexists; repeat straightline.
    eexists; split.
    { repeat (split; trivial; []). subst t0.
      eexists (_ ;++ cons _ nil); split; [exact eq_refl|].
      eexists; split.
      { refine (List.Forall2_app _ _); try eassumption.
        econstructor; [|constructor].
        right; eexists _, _; repeat split. }
      split.
      { eapply kleene_app; eauto.
        refine (kleene_step _ _ nil _ (kleene_empty _)).
        repeat econstructor.
        repeat match goal with x:=_|-_=>subst x end.
        rewrite Properties.word.unsigned_sru_nowrap in H by exact eq_refl; eapply H. }
      { rewrite app_length, Znat.Nat2Z.inj_add; cbn [app Datatypes.length]; subst i.
        unshelve erewrite (_ : patience = _); [|symmetry; eassumption|].
        rewrite word.unsigned_sub; cbv [word.wrap]; rewrite Z.mod_small; rewrite Properties.word.unsigned_of_Z_1.
        2: { pose proof Properties.word.unsigned_range x1.
             change Semantics.width with 32 in *. Lia.lia. }
        ring. } }
      { split; try eapply Properties.word.decrement_nonzero_lt;
        try eapply Properties.word.unsigned_range; eauto. } }
  { letexists; split; [solve[repeat straightline]|split]; repeat straightline; try contradiction.
    split; eauto.
    subst t0.
    eexists (_ ;++ cons _ nil); split.
    { rewrite <-app_assoc; cbn [app]; f_equal. }
    eexists. split.
    { eapply Forall2_app; eauto.
      constructor; [|constructor].
      right; eauto. }
    eexists. split; trivial.
    { left; repeat split; eauto using nonzero_because_high_bit_set.
      { (* copied from above -- trace element for "fifo full" *)
        eapply kleene_app; eauto.
        refine (kleene_step _ _ nil _ (kleene_empty _)).
        repeat econstructor.
        repeat match goal with x:=_|-_=>subst x end.
        rewrite Properties.word.unsigned_sru_nowrap in H by exact eq_refl; eapply H. }
      { rewrite app_length, Znat.Nat2Z.inj_add; cbn [app Datatypes.length]; subst i.
        unshelve erewrite (_ : patience = _); [|symmetry; eassumption|].
        change 0 with (word.unsigned (word.of_Z 0)) in H0.
        eapply Properties.word.unsigned_inj in H0.
        assert (HA: word.add (word.sub x1 (word.of_Z 1)) (word.of_Z 1) = word.of_Z 1). {
          match goal with H : _ |- _ => rewrite H; ring end. }
        ring_simplify in HA; subst. ring_simplify; reflexivity. } } }
  { do 3 letexists; repeat straightline.
    subst i.
    rewrite Properties.word.unsigned_xor_nowrap in *; rewrite Z.lxor_nilpotent in *; contradiction. }
  (* evaluate condition then split if *) letexists; split; [solve[repeat straightline]|split].
  1:contradiction.
  repeat straightline.
  eapply WeakestPreconditionProperties.interact_nomem; repeat straightline.
  split.
  { cbv. clear. firstorder congruence. }
  repeat straightline. split; trivial.
  repeat straightline.
  split; trivial. subst t0.
  eexists (_ ;++ cons _ (cons _ nil)). split.
  { rewrite <-app_assoc. cbn [app]. f_equal. }
  eexists. split.
  { eapply List.Forall2_app; eauto.
    { constructor.
      { left. eexists _, _; repeat split. }
      { right; [|constructor].
        right; eexists _, _; repeat split. } } }
  eexists; split; trivial.
  right.
  subst busy.
  split.
  { f_equal. rewrite Properties.word.unsigned_xor_nowrap; rewrite Z.lxor_nilpotent; reflexivity. }
  cbv [lightbulb_spec.spi_write].
  eexists _, _; split; eauto; []; split; eauto.
  eexists (cons _ nil), (cons _ nil); split; cbn [app]; eauto.
  split; repeat econstructor.
  { repeat match goal with x:=_|-_=>subst x end.
    rewrite Properties.word.unsigned_sru_nowrap in H by exact eq_refl; eapply H. }
  { cbv [lightbulb_spec.spi_write_enqueue one].
    repeat f_equal.
    eapply Properties.word.unsigned_inj.
    clear -Hb.
    pose proof Properties.word.unsigned_range x.
    change (Semantics.width) with 32 in *.
    do 2 (rewrite word.unsigned_of_Z; cbv [word.wrap]; rewrite Z.mod_small); Lia.lia. }
  
  Unshelve.
  all : intros; exact True.
Qed.

Local Ltac split_if :=
  lazymatch goal with
    |- WeakestPrecondition.cmd _ ?c _ _ _ ?post =>
    let c := eval hnf in c in
        lazymatch c with
        | cmd.cond _ _ _ => letexists; split; [solve[repeat straightline]|split]
        end
  end.

Lemma spi_read_ok : program_logic_goal_for_function! spi_read.
  repeat straightline.
  refine ((atleastonce ["b"; "busy"; "i"] (fun v T M B BUSY I =>
     v = word.unsigned I /\
     word.unsigned I <> 0 /\
     M = m /\
     B = word.of_Z (word.unsigned (width:=8) (word.of_Z (word.unsigned B))) /\
     exists tl, T = tl++t /\
     exists th, mmio_trace_abstraction_relation th tl /\
     lightbulb_spec.spi_read_empty _ ^* th /\
     Z.of_nat (length th) + word.unsigned I = patience
          ))
          _ _ _ _ _ _ _);
    cbn [reconstruct map.putmany_of_list HList.tuple.to_list
         HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *; repeat straightline.
  { exact (Z.lt_wf 0). }
  { inversion H. }
  { split; trivial.
    split; [inversion 1|].
    split; trivial.
    split; trivial.
    eexists nil; split; trivial.
    eexists nil; split; try split; solve [constructor]. }
  { eapply WeakestPreconditionProperties.interact_nomem; repeat straightline.
    split; change (Naive.word 32) with Semantics.word.
    { cbv; clear; intuition congruence. }
    repeat ((split; trivial; []) || straightline || split_if).
    { repeat letexists.
      split.
      { repeat straightline. }
      repeat ((split; trivial; []) || straightline || split_if).
      letexists. split; split.
      { subst v'; exact eq_refl. }
      { split; trivial.
        split; trivial.
        split; trivial.
        eexists (x2 ;++ cons _ nil); split; cbn [app]; eauto.
        eexists. split.
        { econstructor; try eassumption; right; eauto. }
        split.
        { 
          refine (kleene_app _ (cons _ nil) _ x3 _); eauto.
          refine (kleene_step _ (cons _ nil) nil _ (kleene_empty _)).
          eexists; split.
          { exact eq_refl. }
          { subst v1.
            rewrite Properties.word.unsigned_sru_nowrap in H by exact eq_refl; exact H. } }
        { cbn [Datatypes.length]; subst i.
          unshelve erewrite (_ : patience = _); [|symmetry; eassumption|].
          rewrite word.unsigned_sub; cbv [word.wrap]; rewrite Z.mod_small; rewrite Properties.word.unsigned_of_Z_1.
          2: { pose proof Properties.word.unsigned_range x1.
               change Semantics.width with 32 in *. Lia.lia. }
          Lia.lia. } }
        { eapply Properties.word.unsigned_range. }
        { eapply Properties.word.decrement_nonzero_lt; eassumption. }}
    { letexists; split; repeat straightline.
      split; trivial.
      eexists (x2 ;++ cons _ nil); split; cbn [app]; eauto.
      eexists. split.
      { econstructor; try eassumption; right; eauto. }
      eexists (word.of_Z (word.unsigned x)), _; split.
      { f_equal; congruence. }
      left; repeat split; eauto using nonzero_because_high_bit_set.
      { refine (kleene_app _ (cons _ nil) _ x3 _); eauto.
        refine (kleene_step _ (cons _ nil) nil _ (kleene_empty _)).
        eexists; split.
        { exact eq_refl. }
        { subst v1.
          rewrite Properties.word.unsigned_sru_nowrap in H by exact eq_refl; exact H. } }
      { cbn [Datatypes.length]; subst i.
        unshelve erewrite (_ : patience = _); [|symmetry; eassumption|].
        change 0 with (word.unsigned (word.of_Z 0)) in H1.
        eapply Properties.word.unsigned_inj in H1.
        assert (HA: word.add (word.sub x1 (word.of_Z 1)) (word.of_Z 1) = word.of_Z 1). {
          match goal with H : _ |- _ => rewrite H; ring end. }
        ring_simplify in HA; subst. rewrite Properties.word.unsigned_of_Z_1; Lia.lia. } }
    { repeat straightline.
      repeat letexists; split.
      { repeat straightline. }
      repeat letexists; split.
      1: split.
      { repeat straightline. }
      2: {
        subst v'.
        subst v.
        subst i.
        rewrite Properties.word.unsigned_xor_nowrap, Z.lxor_nilpotent.
        pose proof Properties.word.unsigned_range x1. Lia.lia. }
      repeat straightline.
      repeat (split; trivial; []).
      split.
      { subst b.
        (* automatable: multi-word bitwise *)
        change (255) with (Z.ones 8).
        pose proof Properties.word.unsigned_range v0.
        eapply Properties.word.unsigned_inj;
          repeat (
              cbv [word.wrap];
              rewrite ?word.unsigned_of_Z, ?Properties.word.unsigned_and_nowrap, ?Z.land_ones, ?Z.mod_mod, ?Z.mod_small by Lia.lia;
              change (Z.ones 8 mod 2 ^ Semantics.width) with (Z.ones 8)).
        symmetry; eapply Z.mod_small.
        pose proof Z.mod_pos_bound (word.unsigned v0) (2^8) eq_refl.
        change Semantics.width with 32.
        Lia.lia. }
      { (* copy-paste from above, trace manipulation *)
        eexists (x2 ;++ cons _ nil); split; cbn [app]; eauto.
        eexists. split.
        { econstructor; try eassumption; right; eauto. }
        subst i.
        rewrite Properties.word.unsigned_xor_nowrap, Z.lxor_nilpotent in H1; contradiction. } }
    { eexists _; split.
      { repeat straightline. }
      split; trivial.
      (* copy-paste from above, trace manipulation *)
      eexists (x2 ;++ cons _ nil); split; cbn [app]; eauto.
      eexists. split.
      { econstructor; try eassumption; right; eauto. }
      eexists (word.of_Z (word.unsigned b)), _; split.
      { subst b; f_equal.
        (* automatable: multi-word bitwise *)
        change (255) with (Z.ones 8).
        pose proof Properties.word.unsigned_range v0.
        eapply Properties.word.unsigned_inj;
          repeat (
              cbv [word.wrap];
              rewrite ?word.unsigned_of_Z, ?Properties.word.unsigned_and_nowrap, ?Z.land_ones, ?Z.mod_mod, ?Z.mod_small by Lia.lia;
              change (Z.ones 8 mod 2 ^ Semantics.width) with (Z.ones 8)).
        symmetry; eapply Z.mod_small.
        pose proof Z.mod_pos_bound (word.unsigned v0) (2^8) eq_refl.
        change Semantics.width with 32.
        Lia.lia. }
      { right; split.
        { subst busy. rewrite Properties.word.unsigned_xor_nowrap, Z.lxor_nilpotent; exact eq_refl. }
        eexists x3, (cons _ nil); split; cbn [app]; eauto.
        split; eauto.
        eexists; split; cbv [one]; trivial.
        split.
        { subst v1. rewrite Properties.word.unsigned_sru_nowrap in H by exact eq_refl; exact H. }
        subst b.
        (* automatable: multi-word bitwise *)
        change (255) with (Z.ones 8).
        pose proof Properties.word.unsigned_range v0.
        eapply Properties.word.unsigned_inj;
          repeat (
              cbv [word.wrap];
              rewrite ?word.unsigned_of_Z, ?Properties.word.unsigned_and_nowrap, ?Z.land_ones, ?Z.mod_mod, ?Z.mod_small by Lia.lia;
              change (Z.ones 8 mod 2 ^ Semantics.width) with (Z.ones 8)).
        trivial. } } }
  Unshelve.
  intros. exact True. (* WHY do we have this shelved predicate here? *)
Qed.

Instance spec_of_spi_xchg : spec_of "spi_xchg" := fun functions => forall t m b_out,
  word.unsigned b_out < 2 ^ 8 ->
  WeakestPrecondition.call functions "spi_xchg" t m [b_out] (fun T M RETS =>
    M = m /\ exists iol, T = t ;++ iol /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\ exists (b_in:Semantics.byte) (err : Semantics.word), RETS = [word.of_Z (word.unsigned b_in); err] /\ Logic.or
      (word.unsigned err <> 0 /\ (any +++ lightbulb_spec.spi_timeout _) ioh)
      (word.unsigned err = 0 /\ lightbulb_spec.spi_xchg Semantics.byte Semantics.word (word.of_Z (word.unsigned b_out)) b_in ioh)).

Lemma spi_xchg_ok : program_logic_goal_for_function! spi_xchg.
Proof.
  repeat (
  match goal with
  | |- ?F ?a ?b ?c =>
      match F with WeakestPrecondition.get => idtac end;
      let f := (eval cbv beta delta [WeakestPrecondition.get] in F) in
      change (f a b c); cbv beta
    | H :  _ /\ _ \/ ?Y /\ _, G : not ?X |- _ =>
        constr_eq X Y; let Z := fresh in destruct H as [|[Z ?]]; [|case (G Z)]
    | H :  not ?Y /\ _ \/ _ /\ _, G : ?X |- _ =>
        constr_eq X Y; let Z := fresh in destruct H as [[Z ?]|]; [case (Z G)|]
  end ||

  straightline || straightline_call || split_if || refine (conj _ _) || eauto).

{ eexists. split.
  { exact eq_refl. }
  eexists. split.
  { eauto. }
  eexists. eexists. split.
  { repeat f_equal. 
    instantiate (1 := (word.of_Z (word.unsigned b_out) : Semantics.byte)).
    (* automatable: multi-word bitwise *)
    change (255) with (Z.ones 8).
    pose proof Properties.word.unsigned_range b_out.
    eapply Properties.word.unsigned_inj;
    repeat (
    cbv [word.wrap];
    rewrite ?word.unsigned_of_Z, ?Properties.word.unsigned_and_nowrap, ?Z.land_ones, ?Z.mod_mod, ?Z.mod_small by Lia.lia;
    change (Z.ones 8 mod 2 ^ Semantics.width) with (Z.ones 8)).
    rewrite Z.mod_small; rewrite Z.mod_small; trivial; Lia.lia. }
    left; split; eauto.
    eexists nil, x0; repeat split; cbv [any choice lightbulb_spec.spi_timeout]; eauto.
    rewrite app_nil_r; trivial. }

    { destruct H10; intuition eauto.
      { eexists. split.
        { subst a0. subst a.
          rewrite List.app_assoc; trivial. }
          eexists. split.
          { eapply Forall2_app; eauto. }
          eexists _, _; split.
          { subst v; trivial. }
          left; split; eauto.
          eapply concat_app; cbv [any choice lightbulb_spec.spi_timeout]; eauto. }
          eexists.
          subst a0.
          subst a.
          split.
          { rewrite List.app_assoc; trivial. }
          eexists.
          split.
          { eapply Forall2_app; eauto. }
          eexists _, _; split.
          { subst v. eauto. }
          right. split; eauto.
          cbv [lightbulb_spec.spi_xchg].

assert (Trace__concat_app : forall T (P Q:list T->Prop) x y, P x -> Q y -> (P +++ Q) (y ++ x)). {
  cbv [concat]; eauto. }

  eauto using Trace__concat_app. }
Qed.
