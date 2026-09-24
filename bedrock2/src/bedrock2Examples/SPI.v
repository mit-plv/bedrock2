Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax bedrock2.NotationsCustomEntry Coq.Strings.String.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Byte.

Import BinInt String List.ListNotations ZArith.
Local Open Scope Z_scope. Local Open Scope string_scope. Local Open Scope list_scope.

Require bedrock2Examples.lightbulb_spec.
Local Notation patience := lightbulb_spec.patience.

Definition spi_write := func! (b) ~> busy {
    busy = $-1;
    i = $patience; while i { i = i - $1;
      io! busy = MMIOREAD($0x10024048);
      if !(busy >> $31) { i = i^i }
    };
    if !(busy >> $31) {
      output! MMIOWRITE($0x10024048, b);
      busy = (busy ^ busy)
    }
  }.

Definition spi_read := func! () ~> (b, busy) {
    busy = $-1;
    b = $0x5a;
    i = $patience; while i { i = i - $1;
      io! busy = MMIOREAD($0x1002404c);
      if !(busy >> $31) {
        b = busy & $0xff;
        i = i^i;
        busy = i
      }
    }
  }.

Definition spi_xchg := func! (b) ~> (b, busy) {
    unpack! busy = spi_write(b);
    require !busy;
    unpack! b, busy = spi_read()
  }.

Require Import bedrock2.ProgramLogic.
Require Import bedrock2.FE310CSemantics bedrock2.Semantics.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.TracePredicate. Import TracePredicateNotations.
Require Import bedrock2.ZnWords.

Import coqutil.Map.Interface.
Import ReversedListNotations.

Section WithParameters.
  Local Notation word := (bits 32).
  Context {mem: map.map word Byte.byte}.
  Context {mem_ok: map.ok mem}.

  Definition mmio_event_abstraction_relation
    (h : lightbulb_spec.OP)
    (l : mem * string * list word * (mem * list word)) :=
    Logic.or
      (exists a v, h = ("st", a, v) /\ l = (map.empty, "MMIOWRITE", [a; v], (map.empty, [])))
      (exists a v, h = ("ld", a, v) /\ l = (map.empty, "MMIOREAD", [a], (map.empty, [v]))).
  Definition mmio_trace_abstraction_relation :=
    List.Forall2 mmio_event_abstraction_relation.
  Definition only_mmio_satisfying P t :=
    exists mmios, mmio_trace_abstraction_relation mmios t /\ P mmios.

  Global Instance spec_of_spi_write : spec_of "spi_write" := fun functions => forall t m b,
    Zmod.unsigned b < 2 ^ 8 ->
    WeakestPrecondition.call functions "spi_write" t m [b] (fun T M RETS =>
      M = m /\ exists iol, T = t ;++ iol /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\ exists err, RETS = [err] /\ Logic.or
        (((Zmod.unsigned err <> 0) /\ lightbulb_spec.spi_write_full ^* ioh /\ Z.of_nat (length ioh) = patience))
        (Zmod.unsigned err = 0 /\ lightbulb_spec.spi_write (byte.of_Z (Zmod.unsigned b)) ioh)).

  Global Instance spec_of_spi_read : spec_of "spi_read" := fun functions => forall t m,
    WeakestPrecondition.call functions "spi_read" t m [] (fun T M RETS =>
      M = m /\ exists iol, T = t ;++ iol /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\ exists (b: byte) (err : word), RETS = [bits.of_Z 32 (byte.unsigned b); err] /\ Logic.or
        (Zmod.unsigned err <> 0 /\ lightbulb_spec.spi_read_empty ^* ioh /\ Z.of_nat (length ioh) = patience)
        (Zmod.unsigned err = 0 /\ lightbulb_spec.spi_read b ioh)).

  Lemma nonzero_because_high_bit_set (x : word) (H : Zmod.unsigned (Zmod.sru x 31) <> 0)
    : Zmod.unsigned x <> 0.
  Proof. zlia. Qed.

  Import coqutil.Tactics.letexists.
  Import Loops.
  Lemma spi_write_ok : program_logic_goal_for_function! spi_write.
  Proof.
    repeat straightline.
    rename H into Hb.

    (* WHY do theese parentheses matter? *)
    refine ((atleastonce ["b"; "busy"; "i"] (fun v T M B BUSY I =>
       b = B /\ v = Zmod.unsigned I /\ Zmod.unsigned I <> 0 /\ M = m /\
       exists tl, T = tl++t /\
       exists th, mmio_trace_abstraction_relation th tl /\
       lightbulb_spec.spi_write_full ^* th /\
       Z.of_nat (length th) + Zmod.unsigned I = patience
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
      exfalso. zlia. }
    { repeat (split; trivial; []).
      subst i. rewrite bits.unsigned_of_Z.
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
      zlia. }
    repeat straightline.
    (* The hnf inside this letexists used to substitute

         c := cmd.cond (expr.op bopname.sru "busy" 31) cmd.skip
                (cmd.set "i" (expr.op bopname.xor "i" "i")) : cmd.cmd

       and also unfolded WeakestPrecondition.cmd of c into

         WeakestPrecondition.dexpr m l0 cond letboundEvar /\
         ThenCorrectness /\
         ElseCorrectness
    *)
    letexists. split.
    { repeat straightline. }
    split; intros.
    { (* CASE if-condition was true (Zmod.unsigned v0 <> 0), i.e. NOP, loop exit depends on whether timeout *)
    repeat straightline. (* <-- does split on a postcondition of the form
                        (Zmod.unsigned br <> 0 -> loop invariant still holds) /\
                        (Zmod.unsigned br =  0 -> code after loop is fine)
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
          zlia. }
        { zlia. } }
        { zlia. } }
    { (* SUBCASE loop condition was false (exit loop because of timeout *)
      letexists; split; [solve[repeat straightline]|split]; repeat straightline; try contradiction.
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
          zlia. }
        { zlia. } } }
    }
    (* CASE if-condition was false (Zmod.unsigned v0 = 0), i.e. we'll set i=i^i and exit loop *)
    repeat straightline.
    { subst i.
      rewrite bits.unsigned_xor in *; rewrite Z.lxor_nilpotent in *; contradiction. }
    (* evaluate condition then split if *) letexists; split; [solve[repeat straightline]|split].
    1:contradiction.
    repeat straightline.
    eapply WeakestPreconditionProperties.interact_nomem; repeat straightline.
    letexists; letexists; split; [exact eq_refl|]; split; [split; trivial|].
    { cbv [isMMIOAddr]. zlia. }
    repeat straightline.
    subst t0.
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
    { f_equal. rewrite bits.unsigned_xor; rewrite Z.lxor_nilpotent; reflexivity. }
    cbv [lightbulb_spec.spi_write].
    eexists _, _; split; eauto; []; split; eauto.
    eexists (cons _ nil), (cons _ nil); split; cbn [app]; eauto.
    split; repeat econstructor.
    { zlia. }
    { cbv [lightbulb_spec.spi_write_enqueue one].
      repeat f_equal.
      eapply Zmod.unsigned_inj.
      rewrite byte.unsigned_of_Z; cbv [byte.wrap]; rewrite Z.mod_small; zlia. }
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
       v = Zmod.unsigned I /\ Zmod.unsigned I <> 0 /\ M = m /\
       B = bits.of_Z 32 (byte.unsigned (byte.of_Z (Zmod.unsigned B))) /\
       exists tl, T = tl++t /\
       exists th, mmio_trace_abstraction_relation th tl /\
       lightbulb_spec.spi_read_empty ^* th /\
       Z.of_nat (length th) + Zmod.unsigned I = patience
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
    { exfalso. zlia. }
    { subst i. rewrite bits.unsigned_of_Z.
      split; [inversion 1|].
      split; trivial.
      subst b; rewrite byte.unsigned_of_Z; cbv [byte.wrap];
        rewrite Z.mod_small; rewrite bits.unsigned_of_Z.
      2: { cbv. split; congruence. }
      split; trivial.
      eexists nil; split; trivial.
      eexists nil; split; try split; solve [constructor]. }
    { eapply WeakestPreconditionProperties.interact_nomem; repeat straightline.
      letexists; split; [exact eq_refl|]; split; [split; trivial|].
    { cbv [isMMIOAddr]. zlia. }
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
            { zlia. } }
          { zlia. } }
          { zlia. }
          { zlia. } }
      { eexists (x2 ;++ cons _ nil); split; cbn [app]; eauto.
        eexists. split.
        { econstructor; try eassumption; right; eauto. }
        eexists (byte.of_Z (Zmod.unsigned x)), _; split.
        { f_equal. eassumption. }
        left; repeat split; eauto using nonzero_because_high_bit_set.
        { refine (kleene_app _ (cons _ nil) _ x3 _); eauto.
          refine (kleene_step _ (cons _ nil) nil _ (kleene_empty _)).
          eexists; split.
          { exact eq_refl. }
          { zlia. } }
        { zlia. } }
      { repeat straightline.
        repeat letexists; split.
        1: split.
        { repeat straightline. }
        2: {
          subst v'.
          subst v.
          subst i.
          rewrite bits.unsigned_xor, Z.lxor_nilpotent.
          zlia. }
        repeat straightline.
        repeat (split; trivial; []).
        split.
        { subst b.
          (* automatable: multi-word bitwise *)
          change (255) with (Z.ones 8).
          pose proof (bits.unsigned_range v0 width_nonneg).
          eapply Zmod.unsigned_inj.
          repeat (
              cbv [byte.wrap];
              rewrite ?byte.unsigned_of_Z, ?bits.unsigned_of_Z, ?bits.unsigned_and,
                      ?Z.land_ones, ?Z.mod_mod, ?Z.mod_small
                by lia;
              change (Z.ones 8 mod 2 ^ 32) with (Z.ones 8)).
          symmetry; eapply Z.mod_small.
          pose proof Z.mod_pos_bound (Zmod.unsigned v0) (2^8) eq_refl.
          clear. Z.div_mod_to_equations. lia. }
        { (* copy-paste from above, trace manipulation *)
          eexists (x2 ;++ cons _ nil); split; cbn [app]; eauto.
          eexists. split.
          { econstructor; try eassumption; right; eauto. }
          subst i.
          rewrite bits.unsigned_xor, Z.lxor_nilpotent in H1; contradiction. } }
      { (* copy-paste from above, trace manipulation *)
        eexists (x2 ;++ cons _ nil); split; cbn [app]; eauto.
        eexists. split.
        { econstructor; try eassumption; right; eauto. }
        eexists (byte.of_Z (Zmod.unsigned b)), _; split.
        { subst b; f_equal.
          (* tag:bitwise *)
          (* automatable: multi-word bitwise *)
          change (255) with (Z.ones 8).
          pose proof (bits.unsigned_range v0 width_nonneg).
          eapply Zmod.unsigned_inj.
          repeat (
              cbv [byte.wrap];
              rewrite ?byte.unsigned_of_Z, ?bits.unsigned_of_Z, ?bits.unsigned_and,
                      ?Z.land_ones, ?Z.mod_mod, ?Z.mod_small
                by lia;
              change (Z.ones 8 mod 2 ^ 32) with (Z.ones 8)).
          symmetry; eapply Z.mod_small.
          pose proof Z.mod_pos_bound (Zmod.unsigned v0) (2^8) eq_refl.
          clear. Z.div_mod_to_equations. lia. }
        (* tag:symex *)
        { right; split.
          { subst_words. rewrite bits.unsigned_xor, Z.lxor_nilpotent; exact eq_refl. }
          eexists x3, (cons _ nil); split; cbn [app]; eauto.
          split; eauto.
          eexists; split; cbv [one]; trivial.
          split.
          (* tag:bitwise *)
          { zlia. }
          subst b.
          (* automatable: multi-word bitwise *)
          change (255) with (Z.ones 8).
          pose proof (bits.unsigned_range v0 width_nonneg).
          eapply byte.unsigned_inj.
          repeat (
              cbv [byte.wrap];
              rewrite ?byte.unsigned_of_Z, ?bits.unsigned_of_Z, ?bits.unsigned_and,
                      ?Z.land_ones, ?Z.mod_mod, ?Z.mod_small
                by lia;
              change (Z.ones 8 mod 2 ^ 32) with (Z.ones 8)).
          trivial. } } }
  Qed.

  Global Instance spec_of_spi_xchg : spec_of "spi_xchg" := fun functions => forall t m b_out,
    Zmod.unsigned b_out < 2 ^ 8 ->
    WeakestPrecondition.call functions "spi_xchg" t m [b_out] (fun T M RETS =>
      M = m /\ exists iol, T = t ;++ iol /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\ exists (b_in:byte) (err : word), RETS = [bits.of_Z 32 (byte.unsigned b_in); err] /\ Logic.or
        (Zmod.unsigned err <> 0 /\ (any +++ lightbulb_spec.spi_timeout) ioh)
        (Zmod.unsigned err = 0 /\ lightbulb_spec.spi_xchg (byte.of_Z (Zmod.unsigned b_out)) b_in ioh)).

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
      instantiate (1 := byte.of_Z (Zmod.unsigned b_out)).
      (* automatable: multi-word bitwise *)
      change (255) with (Z.ones 8).
      pose proof (bits.unsigned_range b_out width_nonneg).
      eapply Zmod.unsigned_inj;
      repeat (
      cbv [byte.wrap];
      rewrite ?byte.unsigned_of_Z, ?bits.unsigned_of_Z, ?bits.unsigned_and, ?Z.land_ones, ?Z.mod_mod, ?Z.mod_small by lia;
      change (Z.ones 8 mod 2 ^ 32) with (Z.ones 8));
      rewrite ?Z.mod_small; rewrite ?Z.mod_small; trivial; lia. }
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
