Require Import bedrock2.Syntax bedrock2.NotationsCustomEntry Coq.Strings.String.
Require Import coqutil.Z.div_mod_to_equations.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Byte.

Import BinInt String List.ListNotations ZArith.
Local Open Scope Z_scope. Local Open Scope string_scope. Local Open Scope list_scope.

Local Notation MMIOWRITE := "MMIOWRITE".
Local Notation MMIOREAD := "MMIOREAD".

Require bedrock2Examples.lightbulb_spec.
Local Notation patience := lightbulb_spec.patience.

Definition spi_write : function :=
  let SPI_WRITE_ADDR := 0x10024048 in
  ("spi_write", (["b"], ["busy"], bedrock_func_body:(
    busy = ($-1);
    i = ($patience); while (i) { i = (i - $1);
      io! busy = $MMIOREAD($SPI_WRITE_ADDR);
      if !(busy >> $31) {
        i = (i^i)
      }
    };
    if !(busy >> $31) {
      output! $MMIOWRITE($SPI_WRITE_ADDR, b);
      busy = (busy ^ busy)
    }
  ))).

Definition spi_read : function :=
  let SPI_READ_ADDR := 0x1002404c in
  ("spi_read", (nil, ("b"::"busy"::nil), bedrock_func_body:(
    busy = ($-1);
    b = ($0x5a);
    i = ($patience); while (i) { i = (i - $1);
      io! busy = $MMIOREAD($SPI_READ_ADDR);
      if !(busy >> $31) {
        b = (busy & $0xff);
        i = (i^i);
        busy = (busy ^ busy)
      }
    }
  ))).

Definition spi_xchg : function :=
  ("spi_xchg", ("b"::nil, "b"::"busy"::nil, bedrock_func_body:(
    unpack! busy = spi_write(b);
    require !busy;
    unpack! b, busy = spi_read()
  ))).

Require Import bedrock2.ProgramLogic.
Require Import bedrock2.FE310CSemantics bedrock2.Semantics.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.TracePredicate. Import TracePredicateNotations.
Require Import bedrock2.ZnWords.

Import coqutil.Map.Interface.
Import ReversedListNotations.

Section WithParameters.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Definition mmio_event_abstraction_relation
    (h : lightbulb_spec.OP word)
    (l : mem * string * list word * (mem * list word)) :=
    Logic.or
      (exists a v, h = ("st", a, v) /\ l = (map.empty, "MMIOWRITE", [a; v], (map.empty, [])))
      (exists a v, h = ("ld", a, v) /\ l = (map.empty, "MMIOREAD", [a], (map.empty, [v]))).
  Definition mmio_trace_abstraction_relation := List.Forall2 mmio_event_abstraction_relation.

  Global Instance spec_of_spi_write : spec_of "spi_write" := fun functions => forall t m b,
    word.unsigned b < 2 ^ 8 ->
    WeakestPrecondition.call functions "spi_write" t m [b] (fun T M RETS =>
      M = m /\ exists iol, T = t ;++ iol /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\ exists err, RETS = [err] /\ Logic.or
        (((word.unsigned err <> 0) /\ lightbulb_spec.spi_write_full _ ^* ioh /\ Z.of_nat (length ioh) = patience))
        (word.unsigned err = 0 /\ lightbulb_spec.spi_write word (byte.of_Z (word.unsigned b)) ioh)).

  Global Instance spec_of_spi_read : spec_of "spi_read" := fun functions => forall t m,
    WeakestPrecondition.call functions "spi_read" t m [] (fun T M RETS =>
      M = m /\ exists iol, T = t ;++ iol /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\ exists (b: byte) (err : word), RETS = [word.of_Z (byte.unsigned b); err] /\ Logic.or
        (word.unsigned err <> 0 /\ lightbulb_spec.spi_read_empty _ ^* ioh /\ Z.of_nat (length ioh) = patience)
        (word.unsigned err = 0 /\ lightbulb_spec.spi_read word b ioh)).

  Lemma nonzero_because_high_bit_set (x : word) (H : word.unsigned (word.sru x (word.of_Z 31)) <> 0)
    : word.unsigned x <> 0.
  Proof. ZnWords. Qed.

  Add Ring wring : (Properties.word.ring_theory (word := word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := word)),
         constants [Properties.word_cst]).

  Import coqutil.Tactics.letexists.
  Import Loops.
  Lemma spi_write_ok : program_logic_goal_for_function! spi_write.
  Proof.
    repeat straightline.
    rename H into Hb.

    (* WHY do theese parentheses matter? *)
    refine ((atleastonce ["b"; "busy"; "i"] (fun v T M B BUSY I =>
       b = B /\ v = word.unsigned I /\ word.unsigned I <> 0 /\ M = m /\
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
    { eexists; split; repeat straightline.
      exfalso. ZnWords. }
    { repeat (split; trivial; []).
      subst i. rewrite word.unsigned_of_Z.
      split.
      { discriminate. }
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
    letexists; split; [exact eq_refl|]; split; [split; trivial|].
    {
      cbv [isMMIOAddr addr].
      ZnWords. }
    repeat straightline. split; trivial.
    letexists. split.
    { repeat straightline. exact eq_refl. }
    (* evaluate condition then split if *) letexists; split; [solve[repeat straightline]|split].
    all: intros.
    { (* CASE if-condition was true (word.unsigned v0 <> 0), i.e. NOP, loop exit depends on whether timeout *)
    repeat straightline. (* <-- does split on a postcondition of the form
                        (word.unsigned br <> 0 -> loop invariant still holds) /\
                        (word.unsigned br =  0 -> code after loop is fine)
                        which corresponds to case distinction over whether loop was exited *)
    { (* SUBCASE loop condition was true (do loop again) *)
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
          ZnWords. }
        { ZnWordsL. } }
        { ZnWords. } }
    { (* SUBCASE loop condition was false (exit loop because of timeout *)
      letexists; split; [solve[repeat straightline]|split]; repeat straightline; try contradiction.
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
          ZnWords. }
        { ZnWordsL. } } }
    }
    (* CASE if-condition was false (word.unsigned v0 = 0), i.e. we'll set i=i^i and exit loop *)
    repeat straightline.
    { subst i.
      rewrite Properties.word.unsigned_xor_nowrap in *; rewrite Z.lxor_nilpotent in *; contradiction. }
    (* evaluate condition then split if *) letexists; split; [solve[repeat straightline]|split].
    1:contradiction.
    repeat straightline.
    eapply WeakestPreconditionProperties.interact_nomem; repeat straightline.
    letexists; letexists; split; [exact eq_refl|]; split; [split; trivial|].
    { cbv [isMMIOAddr]. ZnWords. }
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
    { ZnWords. }
    { cbv [lightbulb_spec.spi_write_enqueue one].
      repeat f_equal.
      eapply Properties.word.unsigned_inj.
      rewrite byte.unsigned_of_Z; cbv [byte.wrap]; rewrite Z.mod_small; ZnWords. }
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
       v = word.unsigned I /\ word.unsigned I <> 0 /\ M = m /\
       B = word.of_Z (byte.unsigned (byte.of_Z (word.unsigned B))) /\
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
    { exfalso. ZnWords. }
    { split; trivial.
      subst i. rewrite word.unsigned_of_Z.
      split; [inversion 1|].
      split; trivial.
      subst b; rewrite byte.unsigned_of_Z; cbv [byte.wrap];
        rewrite Z.mod_small; rewrite word.unsigned_of_Z.
      2: { cbv. split; congruence. }
      split; trivial.
      eexists nil; split; trivial.
      eexists nil; split; try split; solve [constructor]. }
    { eapply WeakestPreconditionProperties.interact_nomem; repeat straightline.
      letexists; split; [exact eq_refl|]; split; [split; trivial|].
    { cbv [isMMIOAddr]. ZnWords. }
      repeat ((split; trivial; []) || straightline || split_if).
      {
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
            { ZnWords. } }
          { ZnWordsL. } }
          { ZnWords. }
          { ZnWords. } }
      { letexists; split; repeat straightline.
        split; trivial.
        eexists (x2 ;++ cons _ nil); split; cbn [app]; eauto.
        eexists. split.
        { econstructor; try eassumption; right; eauto. }
        eexists (byte.of_Z (word.unsigned x)), _; split.
        { f_equal. eassumption. }
        left; repeat split; eauto using nonzero_because_high_bit_set.
        { refine (kleene_app _ (cons _ nil) _ x3 _); eauto.
          refine (kleene_step _ (cons _ nil) nil _ (kleene_empty _)).
          eexists; split.
          { exact eq_refl. }
          { ZnWords. } }
        { ZnWordsL. } }
      { repeat straightline.
        repeat letexists; split.
        1: split.
        { repeat straightline. }
        2: {
          subst v'.
          subst v.
          subst i.
          rewrite Properties.word.unsigned_xor_nowrap, Z.lxor_nilpotent.
          ZnWords. }
        repeat straightline.
        repeat (split; trivial; []).
        split.
        { subst b.
          (* automatable: multi-word bitwise *)
          change (255) with (Z.ones 8).
          pose proof Properties.word.unsigned_range v0.
          eapply Properties.word.unsigned_inj.
          repeat (
              cbv [byte.wrap word.wrap];
              rewrite ?byte.unsigned_of_Z, ?word.unsigned_of_Z, ?Properties.word.unsigned_and_nowrap,
                      ?Z.land_ones, ?Z.mod_mod, ?Z.mod_small
                by blia;
              change (Z.ones 8 mod 2 ^ 32) with (Z.ones 8)).
          symmetry; eapply Z.mod_small.
          pose proof Z.mod_pos_bound (word.unsigned v0) (2^8) eq_refl.
          clear. Z.div_mod_to_equations. blia. }
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
        eexists (byte.of_Z (word.unsigned b)), _; split.
        { subst b; f_equal.
          (* tag:bitwise *)
          (* automatable: multi-word bitwise *)
          change (255) with (Z.ones 8).
          pose proof Properties.word.unsigned_range v0.
          eapply Properties.word.unsigned_inj.
          repeat (
              cbv [byte.wrap word.wrap];
              rewrite ?byte.unsigned_of_Z, ?word.unsigned_of_Z, ?Properties.word.unsigned_and_nowrap,
                      ?Z.land_ones, ?Z.mod_mod, ?Z.mod_small
                by blia;
              change (Z.ones 8 mod 2 ^ 32) with (Z.ones 8)).
          symmetry; eapply Z.mod_small.
          pose proof Z.mod_pos_bound (word.unsigned v0) (2^8) eq_refl.
          clear. Z.div_mod_to_equations. blia. }
        (* tag:symex *)
        { right; split.
          { subst busy. rewrite Properties.word.unsigned_xor_nowrap, Z.lxor_nilpotent; exact eq_refl. }
          eexists x3, (cons _ nil); split; cbn [app]; eauto.
          split; eauto.
          eexists; split; cbv [one]; trivial.
          split.
          (* tag:bitwise *)
          { ZnWords. }
          subst b.
          (* automatable: multi-word bitwise *)
          change (255) with (Z.ones 8).
          pose proof Properties.word.unsigned_range v0.
          eapply byte.unsigned_inj.
          repeat (
              cbv [byte.wrap word.wrap];
              rewrite ?byte.unsigned_of_Z, ?word.unsigned_of_Z, ?Properties.word.unsigned_and_nowrap,
                      ?Z.land_ones, ?Z.mod_mod, ?Z.mod_small
                by blia;
              change (Z.ones 8 mod 2 ^ 32) with (Z.ones 8)).
          trivial. } } }
  Qed.

  Global Instance spec_of_spi_xchg : spec_of "spi_xchg" := fun functions => forall t m b_out,
    word.unsigned b_out < 2 ^ 8 ->
    WeakestPrecondition.call functions "spi_xchg" t m [b_out] (fun T M RETS =>
      M = m /\ exists iol, T = t ;++ iol /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\ exists (b_in:byte) (err : word), RETS = [word.of_Z (byte.unsigned b_in); err] /\ Logic.or
        (word.unsigned err <> 0 /\ (any +++ lightbulb_spec.spi_timeout _) ioh)
        (word.unsigned err = 0 /\ lightbulb_spec.spi_xchg word (byte.of_Z (word.unsigned b_out)) b_in ioh)).

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
      instantiate (1 := byte.of_Z (word.unsigned b_out)).
      (* automatable: multi-word bitwise *)
      change (255) with (Z.ones 8).
      pose proof Properties.word.unsigned_range b_out.
      eapply Properties.word.unsigned_inj;
      repeat (
      cbv [word.wrap byte.wrap];
      rewrite ?byte.unsigned_of_Z, ?word.unsigned_of_Z, ?Properties.word.unsigned_and_nowrap, ?Z.land_ones, ?Z.mod_mod, ?Z.mod_small by blia;
      change (Z.ones 8 mod 2 ^ 32) with (Z.ones 8));
      rewrite ?Z.mod_small; rewrite ?Z.mod_small; trivial; blia. }
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
End WithParameters.
