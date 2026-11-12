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

Require Import bedrock2.LeakageProgramLogic.
Require Import bedrock2.FE310CSemantics bedrock2.Semantics bedrock2.LeakageSemantics.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.TracePredicate. Import TracePredicateNotations.
Require Import bedrock2.ZnWords.

Import coqutil.Map.Interface.
Import ReversedListNotations.

Section WithParameters.
  Local Notation word := (bits 32).
  Context {mem: map.map word Byte.byte}.
  Context {mem_ok: map.ok mem}.
  Context {pick_sp: PickSp}.

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

  (* Leakage of the SPI functions, as a function of the abstract I/O segment [ioh]
     (newest event first) that their specifications already expose. *)

  Local Notation SPI_TX_FIFO_ADDR := (bits.of_Z 32 0x10024048).
  Local Notation SPI_RX_FIFO_ADDR := (bits.of_Z 32 0x1002404c).

  (* One poll of a FIFO status register at [addr] that found the busy bit set,
     newest event first: the branch on the busy bit, the shift amount, the MMIO
     address, and the loop condition that let this iteration run. *)
  Definition spi_poll_leakage (addr : word) : leakage :=
    [leak_bool true; leak_word (bits.of_Z 32 31); leak_list [addr]; leak_bool true].
  Fixpoint spi_polls_leakage (addr : word) (polls : list lightbulb_spec.OP) : leakage :=
    match polls with
    | nil => nil
    | _ :: polls' => spi_poll_leakage addr ++ spi_polls_leakage addr polls'
    end.

  (* [ioh] is either the write and the ready poll on top of the full polls, or
     (timeout) [patience] full polls. *)
  Definition spi_write_leakage (ioh : list lightbulb_spec.OP) : leakage :=
    match ioh with
    | ("st", _, _) :: _ :: polls =>
        [leak_list [SPI_TX_FIFO_ADDR]; leak_bool false; leak_word (bits.of_Z 32 31); leak_bool false;
         leak_bool false; leak_word (bits.of_Z 32 31); leak_list [SPI_TX_FIFO_ADDR]; leak_bool true]
        ++ spi_polls_leakage SPI_TX_FIFO_ADDR polls
    | _ =>
        [leak_bool true; leak_word (bits.of_Z 32 31); leak_bool false]
        ++ spi_polls_leakage SPI_TX_FIFO_ADDR ioh
    end.

  (* [ioh] is a nonempty poll on top of the empty polls, or (timeout) [patience]
     empty polls; the two cases are told apart by the busy bit of the last poll. *)
  Definition spi_read_leakage (ioh : list lightbulb_spec.OP) : leakage :=
    match ioh with
    | (_, _, v) :: polls =>
        if Z.shiftr (Zmod.unsigned v) 31 =? 0
        then [leak_bool false; leak_bool false; leak_word (bits.of_Z 32 31); leak_list [SPI_RX_FIFO_ADDR]; leak_bool true]
             ++ spi_polls_leakage SPI_RX_FIFO_ADDR polls
        else leak_bool false :: spi_polls_leakage SPI_RX_FIFO_ADDR ioh
    | nil => [leak_bool false]
    end.

  (* Splits off the leading run of "ld" events (the segment of [spi_read], if any). *)
  Fixpoint spi_split_reads (ioh : list lightbulb_spec.OP) : list lightbulb_spec.OP * list lightbulb_spec.OP :=
    match ioh with
    | (("ld", _, _) as e) :: ioh' => let '(r, w) := spi_split_reads ioh' in (e :: r, w)
    | _ => (nil, ioh)
    end.

  Definition spi_xchg_leakage (fw fr : list lightbulb_spec.OP -> leakage) (ioh : list lightbulb_spec.OP) : leakage :=
    let '(r, w) := spi_split_reads ioh in
    match w with
    | nil => leak_bool true :: fw ioh ++ [leak_unit]
    | _ => fr r ++ leak_unit :: leak_bool false :: fw w ++ [leak_unit]
    end.

  Global Instance spec_of_spi_write : spec_of "spi_write" := fun functions => exists f, forall k t m b,
    Zmod.unsigned b < 2 ^ 8 ->
    LeakageWeakestPrecondition.call functions "spi_write" k t m [b] (fun K T M RETS =>
      M = m /\ exists iol, T = t ;++ iol /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\ K = f ioh ++ k /\ exists err, RETS = [err] /\ Logic.or
        (((Zmod.unsigned err <> 0) /\ lightbulb_spec.spi_write_full ^* ioh /\ Z.of_nat (length ioh) = patience))
        (Zmod.unsigned err = 0 /\ lightbulb_spec.spi_write (byte.of_Z (Zmod.unsigned b)) ioh)).

  Global Instance spec_of_spi_read : spec_of "spi_read" := fun functions => exists f, forall k t m,
    LeakageWeakestPrecondition.call functions "spi_read" k t m [] (fun K T M RETS =>
      M = m /\ exists iol, T = t ;++ iol /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\ K = f ioh ++ k /\ exists (b: byte) (err : word), RETS = [bits.of_Z 32 (byte.unsigned b); err] /\ Logic.or
        (Zmod.unsigned err <> 0 /\ lightbulb_spec.spi_read_empty ^* ioh /\ Z.of_nat (length ioh) = patience)
        (Zmod.unsigned err = 0 /\ lightbulb_spec.spi_read b ioh)).

  Lemma nonzero_because_high_bit_set (x : word) (H : Zmod.unsigned (Zmod.sru x 31) <> 0)
    : Zmod.unsigned x <> 0.
  Proof. ZnWords. Qed.

  Import coqutil.Tactics.letexists.
  Import LeakageLoops.

  (* The first [straightline] would instantiate the leakage function with an
     evar; we name it up front instead, after [enter] and before this. *)
  Local Ltac start_func :=
    intros;
    match goal with
    | H: map.get ?functions ?fname = Some _ |- _ =>
        eapply LeakageWeakestPreconditionProperties.start_func; [exact H | clear H]
    end;
    cbv match beta delta [LeakageWeakestPrecondition.func].

  (* Same as the [Markers.unique (Markers.left _)] case of [straightline], but
     without [eabstract]: here the kernel takes seconds to recheck the
     abstracted [enforce] proof. *)
  Local Ltac loop_again :=
    lazymatch goal with
    | |- Markers.unique (Markers.left ?G) =>
      change G;
      unshelve (idtac; repeat match goal with
                       | |- Markers.split (?P /\ Markers.right ?Q) =>
                         split; [solve [repeat straightline] | change Q]
                       | |- exists _, _ => letexists
                       end); []
    end.

  Lemma spi_write_ok : program_logic_goal_for_function! spi_write.
  Proof.
    enter spi_write. exists spi_write_leakage. start_func.
    repeat straightline.
    rename H into Hb.

    refine (atleastonce ["b"; "busy"; "i"] (fun v K T M B BUSY I =>
       b = B /\ v = Zmod.unsigned I /\ Zmod.unsigned I <> 0 /\ M = m /\
       exists tl, T = tl++t /\
       exists th, mmio_trace_abstraction_relation th tl /\
       lightbulb_spec.spi_write_full ^* th /\
       Z.of_nat (length th) + Zmod.unsigned I = patience /\
       K = leak_bool true :: spi_polls_leakage SPI_TX_FIFO_ADDR th ++ k
       ) _ _ _ _ _);
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
    { eexists; eexists; cbv [Markers.split]; split; [repeat straightline|]; split; intros.
      { exfalso. ZnWords. }
      repeat (split; trivial; []).
      subst i. rewrite bits.unsigned_of_Z.
      eexists; split.
      { rewrite app_nil_l; trivial. }
      eexists; split.
      { constructor. }
      split.
      { constructor. }
      split.
      { exact eq_refl. }
      align_trace. }
    repeat straightline.
    eapply LeakageWeakestPreconditionProperties.interact_nomem; repeat straightline.
    letexists; split; [exact eq_refl|]; split; [split; trivial|].
    {
      cbv [isMMIOAddr addr].
      ZnWords. }
    repeat straightline.
    letexists. letexists. split.
    { repeat straightline. }
    split; intros.
    { (* CASE if-condition was true (Zmod.unsigned v0 <> 0), i.e. NOP, loop exit depends on whether timeout *)
    repeat (loop_again || straightline). (* <-- does split on a postcondition of the form
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
          ZnWords. }
        split.
        { ZnWordsL. }
        align_trace. }
        { ZnWords. } }
    { (* SUBCASE loop condition was false (exit loop because of timeout *)
      letexists; letexists; split; [solve[repeat straightline]|split]; repeat straightline; try contradiction.
      subst t0.
      eexists (_ ;++ cons _ nil); split.
      { rewrite <-app_assoc; cbn [app]; f_equal. }
      eexists. split.
      { eapply Forall2_app; eauto.
        constructor; [|constructor].
        right; eauto. }
      split.
      { align_trace. }
      eexists. split; trivial.
      { left; repeat split; eauto using nonzero_because_high_bit_set.
        { (* copied from above -- trace element for "fifo full" *)
          eapply kleene_app; eauto.
          refine (kleene_step _ _ nil _ (kleene_empty _)).
          repeat econstructor.
          ZnWords. }
        { ZnWordsL. } } }
    }
    (* CASE if-condition was false (Zmod.unsigned v0 = 0), i.e. we'll set i=i^i and exit loop *)
    repeat (loop_again || straightline).
    { subst i.
      rewrite bits.unsigned_xor in *; rewrite Z.lxor_nilpotent in *; contradiction. }
    (* evaluate condition then split if *) letexists; letexists; split; [solve[repeat straightline]|split].
    1:contradiction.
    repeat straightline.
    eapply LeakageWeakestPreconditionProperties.interact_nomem; repeat straightline.
    letexists; letexists; split; [exact eq_refl|]; split; [split; trivial|].
    { cbv [isMMIOAddr]. ZnWords. }
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
    split.
    { align_trace. }
    eexists; split; trivial.
    right.
    subst busy.
    split.
    { f_equal. rewrite bits.unsigned_xor; rewrite Z.lxor_nilpotent; reflexivity. }
    cbv [lightbulb_spec.spi_write].
    eexists _, _; split; eauto; []; split; eauto.
    eexists (cons _ nil), (cons _ nil); split; cbn [app]; eauto.
    split; repeat econstructor.
    { ZnWords. }
    { cbv [lightbulb_spec.spi_write_enqueue one].
      repeat f_equal.
      eapply Zmod.unsigned_inj.
      rewrite byte.unsigned_of_Z; cbv [byte.wrap]; rewrite Z.mod_small; ZnWords. }
  Qed.

  Lemma spi_read_leakage_empty s a v th (H : Z.shiftr (Zmod.unsigned v) 31 <> 0) :
    spi_read_leakage ((s, a, v) :: th) = leak_bool false :: spi_polls_leakage SPI_RX_FIFO_ADDR ((s, a, v) :: th).
  Proof.
    cbv [spi_read_leakage]. destruct (Z.eqb_spec (Z.shiftr (Zmod.unsigned v) 31) 0); congruence.
  Qed.

  Lemma spi_read_leakage_dequeue s a v th (H : Z.shiftr (Zmod.unsigned v) 31 = 0) :
    spi_read_leakage ((s, a, v) :: th) =
    [leak_bool false; leak_bool false; leak_word (bits.of_Z 32 31); leak_list [SPI_RX_FIFO_ADDR]; leak_bool true]
    ++ spi_polls_leakage SPI_RX_FIFO_ADDR th.
  Proof.
    cbv [spi_read_leakage]. destruct (Z.eqb_spec (Z.shiftr (Zmod.unsigned v) 31) 0); congruence.
  Qed.

  Local Ltac split_if :=
    lazymatch goal with
      |- LeakageWeakestPrecondition.cmd _ ?c _ _ _ _ ?post =>
      let c := eval hnf in c in
          lazymatch c with
          | cmd.cond _ _ _ => letexists; letexists; split; [solve[repeat straightline]|split]
          end
    end.

  Lemma spi_read_ok : program_logic_goal_for_function! spi_read.
    enter spi_read. exists spi_read_leakage. start_func.
    repeat straightline.
    refine (atleastonce ["b"; "busy"; "i"] (fun v K T M B BUSY I =>
       v = Zmod.unsigned I /\ Zmod.unsigned I <> 0 /\ M = m /\
       B = bits.of_Z 32 (byte.unsigned (byte.of_Z (Zmod.unsigned B))) /\
       exists tl, T = tl++t /\
       exists th, mmio_trace_abstraction_relation th tl /\
       lightbulb_spec.spi_read_empty ^* th /\
       Z.of_nat (length th) + Zmod.unsigned I = patience /\
       K = leak_bool true :: spi_polls_leakage SPI_RX_FIFO_ADDR th ++ k
            ) _ _ _ _ _);
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
    { subst i. rewrite bits.unsigned_of_Z.
      split; [inversion 1|].
      split; trivial.
      subst b; rewrite byte.unsigned_of_Z; cbv [byte.wrap];
        rewrite Z.mod_small; rewrite bits.unsigned_of_Z.
      2: { cbv. split; congruence. }
      split; trivial.
      eexists nil; split; trivial.
      eexists nil; split; [constructor|]; split; [constructor|]; split; [exact eq_refl|].
      align_trace. }
    { eapply LeakageWeakestPreconditionProperties.interact_nomem; repeat straightline.
      letexists; split; [exact eq_refl|]; split; [split; trivial|].
    { cbv [isMMIOAddr]. ZnWords. }
      repeat ((split; trivial; []) || loop_again || straightline || split_if).
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
          split.
          { ZnWordsL. }
          align_trace. }
          { ZnWords. }
          { ZnWords. } }
      { eexists (x2 ;++ cons _ nil); split; cbn [app]; eauto.
        eexists. split.
        { econstructor; try eassumption; right; eauto. }
        split.
        { rewrite spi_read_leakage_empty by ZnWords. align_trace. }
        eexists (byte.of_Z (Zmod.unsigned x)), _; split.
        { f_equal. eassumption. }
        left; repeat split; eauto using nonzero_because_high_bit_set.
        { refine (kleene_app _ (cons _ nil) _ x3 _); eauto.
          refine (kleene_step _ (cons _ nil) nil _ (kleene_empty _)).
          eexists; split.
          { exact eq_refl. }
          { ZnWords. } }
        { ZnWordsL. } }
      { exfalso. subst i.
        rewrite bits.unsigned_xor, Z.lxor_nilpotent in H1; contradiction. }
      { eexists (x2 ;++ cons _ nil); split; cbn [app]; eauto.
        eexists. split.
        { econstructor; try eassumption; right; eauto. }
        split.
        { rewrite spi_read_leakage_dequeue by ZnWords. align_trace. }
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
          { ZnWords. }
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

  (* The timeout cases of [spi_write] and [spi_read], as in their specifications
     above, and hence of [spi_xchg]: either the write timed out, or the write
     succeeded and the read timed out. *)
  Definition spi_write_timeout (ioh : list lightbulb_spec.OP) : Prop :=
    lightbulb_spec.spi_write_full ^* ioh /\ Z.of_nat (length ioh) = patience.
  Definition spi_read_timeout (ioh : list lightbulb_spec.OP) : Prop :=
    lightbulb_spec.spi_read_empty ^* ioh /\ Z.of_nat (length ioh) = patience.
  Definition spi_xchg_timeout (tx : byte) : list lightbulb_spec.OP -> Prop :=
    spi_write_timeout ||| (lightbulb_spec.spi_write tx +++ spi_read_timeout).

  Lemma spi_xchg_timeout_any tx ioh (H : spi_xchg_timeout tx ioh) : (any +++ lightbulb_spec.spi_timeout) ioh.
  Proof.
    cbv [spi_xchg_timeout spi_write_timeout spi_read_timeout choice concat any lightbulb_spec.spi_timeout] in *.
    destruct H as [[H1 H2] | (l1 & l2 & -> & H1 & H2 & H3)].
    { exists nil, ioh. rewrite app_nil_r. auto. }
    { exists l1, l2. auto. }
  Qed.

  Global Instance spec_of_spi_xchg : spec_of "spi_xchg" := fun functions => exists f, forall k t m b_out,
    Zmod.unsigned b_out < 2 ^ 8 ->
    LeakageWeakestPrecondition.call functions "spi_xchg" k t m [b_out] (fun K T M RETS =>
      M = m /\ exists iol, T = t ;++ iol /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\ K = f ioh ++ k /\ exists (b_in:byte) (err : word), RETS = [bits.of_Z 32 (byte.unsigned b_in); err] /\ Logic.or
        (Zmod.unsigned err <> 0 /\ spi_xchg_timeout (byte.of_Z (Zmod.unsigned b_out)) ioh)
        (Zmod.unsigned err = 0 /\ lightbulb_spec.spi_xchg (byte.of_Z (Zmod.unsigned b_out)) b_in ioh)).

  (* [spi_split_reads] recovers the segments of [spi_read] and [spi_write] from
     their concatenation. *)
  Definition ld_event (e : lightbulb_spec.OP) : Prop := exists a v, e = ("ld", a, v).

  Lemma spi_split_reads_app r w (Hr : Forall ld_event r) (Hw : spi_split_reads w = (nil, w)) :
    spi_split_reads (r ++ w) = (r, w).
  Proof.
    induction Hr as [|e r [a [v ->]] Hr IH]; cbn [app spi_split_reads]; [exact Hw|].
    rewrite IH; reflexivity.
  Qed.

  Lemma spi_write_full_star_ld ioh (H : lightbulb_spec.spi_write_full ^* ioh) : Forall ld_event ioh.
  Proof.
    induction H as [|l1 l2 [v [<- _]] _ IH]; [constructor|].
    apply Forall_app; split; trivial. repeat constructor. eexists _, _; reflexivity.
  Qed.

  Lemma spi_read_empty_star_ld ioh (H : lightbulb_spec.spi_read_empty ^* ioh) : Forall ld_event ioh.
  Proof.
    induction H as [|l1 l2 [v [<- _]] _ IH]; [constructor|].
    apply Forall_app; split; trivial. repeat constructor. eexists _, _; reflexivity.
  Qed.

  Lemma spi_read_ld b ioh (H : lightbulb_spec.spi_read b ioh) : Forall ld_event ioh.
  Proof.
    destruct H as (l1 & l2 & -> & H1 & v & <- & _).
    apply Forall_app; split; eauto using spi_read_empty_star_ld.
    repeat constructor. eexists _, _; reflexivity.
  Qed.

  Lemma spi_split_reads_reads r (Hr : Forall ld_event r) : spi_split_reads r = (r, nil).
  Proof. rewrite <-(app_nil_r r) at 1. apply spi_split_reads_app; trivial. Qed.

  Lemma spi_write_split b ioh (H : lightbulb_spec.spi_write b ioh) : spi_split_reads ioh = (nil, ioh).
  Proof.
    destruct H as (l1 & l2 & -> & _ & l3 & l4 & -> & _ & <-). reflexivity.
  Qed.

  Lemma spi_write_nonempty b ioh (H : lightbulb_spec.spi_write b ioh) : ioh <> nil.
  Proof.
    destruct H as (l1 & l2 & -> & _ & l3 & l4 & -> & _ & <-). discriminate.
  Qed.

  Lemma spi_xchg_leakage_timeout fw fr r (Hr : Forall ld_event r) :
    spi_xchg_leakage fw fr r = leak_bool true :: fw r ++ [leak_unit].
  Proof. cbv [spi_xchg_leakage]. rewrite spi_split_reads_reads by assumption. reflexivity. Qed.

  Lemma spi_xchg_leakage_app fw fr r w (Hr : Forall ld_event r)
    (Hw : spi_split_reads w = (nil, w)) (Hw' : w <> nil) :
    spi_xchg_leakage fw fr (r ++ w) = fr r ++ leak_unit :: leak_bool false :: fw w ++ [leak_unit].
  Proof.
    cbv [spi_xchg_leakage]. rewrite spi_split_reads_app by assumption.
    destruct w; congruence.
  Qed.

  Lemma spi_xchg_ok : program_logic_goal_for_function! spi_xchg.
  Proof.
    enter spi_xchg. exists (spi_xchg_leakage f f0). start_func.
    repeat (
    match goal with
    | |- ?F ?a ?b ?c =>
        match F with LeakageWeakestPrecondition.get => idtac end;
        let f := (eval cbv beta delta [LeakageWeakestPrecondition.get] in F) in
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
    split.
    { rewrite spi_xchg_leakage_timeout by eauto using spi_write_full_star_ld. align_trace. }
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
      left; split; eauto. }

      { destruct H11; intuition eauto.
        { eexists. split.
          { subst a1. subst a0.
            rewrite List.app_assoc; trivial. }
            eexists. split.
            { eapply Forall2_app; eauto. }
            split.
            { rewrite spi_xchg_leakage_app by eauto using spi_read_empty_star_ld, spi_write_split, spi_write_nonempty.
              align_trace. }
            eexists _, _; split.
            { subst v; trivial. }
            left; split; eauto.
            right; eapply concat_app; eauto. split; eauto. }
            eexists.
            subst a1.
            subst a0.
            split.
            { rewrite List.app_assoc; trivial. }
            eexists.
            split.
            { eapply Forall2_app; eauto. }
            split.
            { rewrite spi_xchg_leakage_app by eauto using spi_read_ld, spi_write_split, spi_write_nonempty.
              align_trace. }
            eexists _, _; split.
            { subst v. eauto. }
            right. split; eauto.
            cbv [lightbulb_spec.spi_xchg].

  assert (Trace__concat_app : forall T (P Q:list T->Prop) x y, P x -> Q y -> (P +++ Q) (y ++ x)). {
    cbv [concat]; eauto. }

    eauto using Trace__concat_app. }
  Qed.

  (* The previous, plain specification of spi_xchg (with its weaker description
     of the timeout case), for the plain callers in LAN9250.v: it follows from
     the leakage specification by forgetting the leakage, which needs the
     callee to be free of stackalloc (SemanticsRelations.plain_of_leakage_call),
     a side condition on the concrete function list. This is not an instance
     of [spec_of "spi_xchg"]; that name is the leakage specification. *)
  Definition spi_xchg_plain_spec : spec_of "spi_xchg" := fun functions => forall t m b_out,
    Zmod.unsigned b_out < 2 ^ 8 ->
    Semantics.call functions "spi_xchg" t m [b_out] (fun T M RETS =>
      M = m /\ exists iol, T = t ;++ iol /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\ exists (b_in:byte) (err : word), RETS = [bits.of_Z 32 (byte.unsigned b_in); err] /\ Logic.or
        (Zmod.unsigned err <> 0 /\ (any +++ lightbulb_spec.spi_timeout) ioh)
        (Zmod.unsigned err = 0 /\ lightbulb_spec.spi_xchg (byte.of_Z (Zmod.unsigned b_out)) b_in ioh)).

  Lemma spi_xchg_plain_spec_of_leakage functions
    (Hsf : SemanticsRelations.stackalloc_free_env functions)
    (H : spec_of_spi_xchg functions) : spi_xchg_plain_spec functions.
  Proof.
    destruct H as [f H]. intros t m b_out Hb.
    eapply Semantics.weaken_call.
    { eapply SemanticsRelations.plain_of_leakage_call_env with (k := nil);
        [ exact Hsf | eapply H; exact Hb ]. }
    intros ? ? ? (k' & HM & iol & HT & ioh & Hrel & _ & b_in & err & Hrets & Hor).
    split; [exact HM|]. exists iol; split; [exact HT|]. exists ioh; split; [exact Hrel|].
    exists b_in, err; split; [exact Hrets|].
    destruct Hor as [[Herr Hto] | Hok]; [left; split; [exact Herr | exact (spi_xchg_timeout_any _ _ Hto)] | right; exact Hok].
  Qed.

End WithParameters.
