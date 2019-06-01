Require Import bedrock2.Syntax bedrock2.StringNamesSyntax bedrock2.BasicCSyntax.
Require Import bedrock2.NotationsCustomEntry coqutil.Z.HexNotation.

Import BinInt String List.ListNotations.
Local Open Scope Z_scope. Local Open Scope string_scope. Local Open Scope list_scope.
Local Existing Instance BasicCSyntax.StringNames_params.
Local Coercion literal (z : Z) : expr := expr.literal z.
Local Coercion var (x : String.string) : expr := expr.var x.
Local Coercion name_of_func (f : function) := fst f.

Local Notation MMIOWRITE := "MMIOWRITE".
Local Notation MMIOREAD := "MMIOREAD".

Definition spi_write : function :=
  let b : varname := "b" in
  let busy : varname := "busy" in
  let i : varname := "i" in
  let patience := -1 in
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
  let patience := -1 in
  let SPI_READ_ADDR := Ox"0x1002404c" in
  ("spi_read", (nil, (b::busy::nil), bedrock_func_body:(
    busy = (constr:(-1));
    b = (busy);
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
    unpack! b, busy = spi_read(b)
  ))).

Require Import bedrock2.ProgramLogic.
Require Import bedrock2.FE310CSemantics.
Require Import coqutil.Word.Interface.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.TracePredicate. Import TracePredicateNotations.
Require bedrock2.Examples.lightbulb_spec.

Import coqutil.Map.Interface.

Definition mmio_event_abstraction_relation
  (h : lightbulb_spec.OP Semantics.word)
  (l : Semantics.mem * Syntax.actname * list Semantics.word * (Semantics.mem * list Semantics.word)) :=
  Logic.or
    (exists a v, h = lightbulb_spec.st _ a v /\ l = (map.empty, "MMIOWRITE", [a; v], (map.empty, [])))
    (exists a v, h = lightbulb_spec.ld _ a v /\ l = (map.empty, "MMIOREAD", [a], (map.empty, [v]))).
Definition mmio_trace_abstraction_relation := List.Forall2 mmio_event_abstraction_relation.

Import ReversedListNotations.
Instance spec_of_spi_write : spec_of "spi_write" := fun functions => forall t m b,
  word.unsigned b < 2 ^ 8 ->
  WeakestPrecondition.call functions "spi_write" t m [b] (fun T M RETS =>
    M = m /\ exists iol, T = t ;++ iol /\ exists ioh, mmio_trace_abstraction_relation ioh iol /\ Logic.or
      ((exists err, RETS = [err] /\ word.unsigned (word.sru err (word.of_Z 31)) <> 0))
      (RETS = [word.of_Z 0] /\ lightbulb_spec.spi_write Semantics.byte Semantics.word (word.of_Z (word.unsigned b)) ioh)).

Import coqutil.Tactics.letexists.
Import TailRecursion.
Lemma spi_write_ok : Semantics.parameters_ok parameters -> program_logic_goal_for_function! spi_write.
Proof.
  intros p_ok.
  repeat straightline.
  rename H into Hb.
  show_program.

  (* WHY do theese parentheses matter? *)
  Fail refine (atleastonce ["b"; "busy"; "i"] (fun v t m b busy i => True) _ _ _ _ _ _ _).
  refine ((atleastonce ["b"; "busy"; "i"] (fun v T M B BUSY I =>
     b = B /\
     v = word.unsigned I /\
     word.unsigned I <> 0 /\
     M = m /\
     exists tl, T = tl++t /\
     exists th, mmio_trace_abstraction_relation th tl /\
     lightbulb_spec.spi_write_full _ ^* th))
          _ _ _ _ _ _ _);
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
    eexists; split; constructor. }
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
      eapply kleene_app; eauto.
      refine (kleene_step _ _ nil _ (kleene_empty _)).
      repeat econstructor.
      repeat match goal with x:=_|-_=>subst x end.
      rewrite Properties.word.unsigned_sru_nowrap in H by exact eq_refl; eapply H. }
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
    { left; repeat split; eauto. } }
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
  right.
  subst busy.
  split.
  { f_equal. eapply Properties.word.unsigned_inj.
    rewrite Properties.word.unsigned_xor_nowrap; rewrite Z.lxor_nilpotent; reflexivity. }
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
    pose proof Properties.word.unsigned_range b.
    change (Semantics.width) with 32 in *.
    do 2 (rewrite word.unsigned_of_Z; cbv [word.wrap]; rewrite Z.mod_small); Lia.lia. }
  
  Unshelve.
  all : intros; exact True.
Qed.
