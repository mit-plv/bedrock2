Require Import bedrock2.NotationsCustomEntry.

Import Syntax Syntax.Coercions BinInt String List List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Require Import bedrock2.WeakestPrecondition bedrock2.Semantics bedrock2.ProgramLogic.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface bedrock2.Map.SeparationLogic.
Require Import coqutil.Macros.symmetry.
Require Import bedrock2.ZnWords.
Import Coq.Init.Byte coqutil.Byte.
Local Notation string := String.string.

(*Require Import bedrock2.ptsto_bytes.*)
Require Import coqutil.Map.OfListWord.
Local Notation "xs $@ a" := (map.of_list_word_at a xs) (at level 10, format "xs $@ a").

Section WithParameters.
  Context {width} {BW: Bitwidth width}.
  Context {word: word.word width} {mem: map.map word byte} {locals: map.map string word}.
  Context {ext_spec: ExtSpec}.
  Import ProgramLogic.Coercions.


  Local Instance spec_of_memmove : spec_of "memmove" :=
    fnspec! "memmove" (dst src n : word) / (d s : list byte) (R Rs : mem -> Prop),
    { requires t m := m =* s$@src * Rs /\ m =* d$@dst * R /\
        length s = n :> Z /\ length d = n :> Z /\ n <= 2^(width-1);
      ensures t' m := m =* s$@dst * R /\ t=t' }.


  Definition memmove := func! (dst, src, n) {
    x = src-dst;
    require x;
    if x < x+n {
      while n {
        store1(dst, load1(src));
        src = src + $1;
        dst = dst + $1;
        n = n - $1
      }
    } else {
      dst = dst + (n - $1);
      src = src + (n - $1);
      while n {
        store1(dst, load1(src));
        src = src - $1;
        dst = dst - $1;
        n = n - $1
      }
    }
  }.


  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {locals_ok : map.ok locals}
    {ext_spec_ok : ext_spec.ok ext_spec}.

  Import coqutil.Tactics.letexists coqutil.Tactics.Tactics coqutil.Tactics.autoforward.
  Import coqutil.Word.Properties coqutil.Map.Properties.

  Local Ltac ZnWords := destruct width_cases; bedrock2.ZnWords.ZnWords.
  Lemma memmove_ok : program_logic_goal_for_function! memmove.
  Proof.
    repeat straightline.

    case H as (ms&mRs&?&?&?), H0 as (md&mRd&?&?&?);
      cbv [sepclause_of_map] in *; subst; clear dependent Rs.

    eapply WeakestPreconditionProperties.dexpr_expr.
    repeat straightline.
    letexists; split.
    { subst l; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
    letexists; split.
    { subst l; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
    repeat straightline.

    set (x := word.sub src dst) in *.
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    eapply WeakestPreconditionProperties.dexpr_expr.
    letexists; split.
    { subst l0; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
    repeat straightline.

    (* x = 0 *)
    split; intros Hx; cycle 1.
    { replace src with dst in * by ZnWords.
      cbn; ssplit; eauto.
      eexists _, _; ssplit; eauto.
      eapply map.split_same_footprint; eauto.
      intros k.
      rewrite 2map.get_of_list_word_at, 2List.nth_error_None.
      Morphisms.f_equiv. ZnWords. }

    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    eapply WeakestPreconditionProperties.dexpr_expr.
    letexists; split.
    { subst l0; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
    repeat straightline.
    letexists; split.
    { subst l0; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
    letexists; split.
    { subst l0 l; rewrite ?Properties.map.get_put_dec. exact eq_refl. }
    repeat straightline.

    rewrite word.unsigned_ltu, word.unsigned_add; cbv [word.wrap].
    split; intros Hbr;
      [apply word.if_nonzero in Hbr | apply word.if_zero in Hbr];
      autoforward with typeclass_instances in Hbr.

    { assert (x + n < 2^width) by ZnWords.
      refine ((Loops.tailrec
        (HList.polymorphic_list.cons _
        (HList.polymorphic_list.cons _
        (HList.polymorphic_list.cons _
        (HList.polymorphic_list.cons _
        HList.polymorphic_list.nil))))
        ["dst";"src";"n";"x"])
        (fun (v:nat) s mRs d mRd t m dst src n _x => PrimitivePair.pair.mk (
          x + n < 2^width /\ map.split m (s$@src) mRs /\  map.split m (d$@dst) mRd /\
          x = word.sub src dst /\ v=n :> Z /\ length s = n :> Z /\ length d = n :> Z
        )
        (fun                     T M DST SRC N X => t = T   /\  map.split M (s$@dst) mRd))
        lt
        _ _ _ _ _ _ _ _ _);
        (* TODO wrap this into a tactic with the previous refine *)
        cbn [HList.hlist.foralls HList.tuple.foralls
             HList.hlist.existss HList.tuple.existss
             HList.hlist.apply  HList.tuple.apply
             HList.hlist
             List.repeat Datatypes.length
             HList.polymorphic_list.repeat HList.polymorphic_list.length
             PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
        { cbv [Loops.enforce]; cbn.
          subst l l0.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn); split.
          { exact eq_refl. }
          { eapply map.map_ext; intros k.
            repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
            repeat (destruct String.eqb; trivial). } }
        { eapply Wf_nat.lt_wf. }
        { cbn; ssplit; eauto. }
        { intros ?v ?s ?mRs ?d ?mRd ?t ?m ?dst ?src ?n ?x.
          repeat straightline.
          cbn in localsmap.
          eexists n0; split; cbv [expr expr_body localsmap get].
          { rewrite ?Properties.map.get_put_dec. exists n0; cbn. auto. }
          split; cycle 1.
          { intros Ht; rewrite Ht in *.
            intuition idtac; destruct s0, d0; cbn in *; try discriminate; [].
            eauto. }
          repeat straightline.
          eapply WeakestPreconditionProperties.dexpr_expr.
          repeat straightline.
          letexists; split.
          { rewrite ?Properties.map.get_put_dec; exact eq_refl. }
          eapply WeakestPreconditionProperties.dexpr_expr.
          repeat straightline.
          letexists; split.
          { rewrite ?Properties.map.get_put_dec; cbn. exact eq_refl. }
          repeat straightline.

          cbv [WeakestPrecondition.load load load_Z]; cbn.
          destruct s0 as [|b s0], d0 as [|B d0]; try (cbn in *; congruence); [].
          exists (word.of_Z (byte.unsigned b)).
          pose proof map.get_split src0 _ _ _ H6.
          rewrite map.get_of_list_word_at in H14.
          progress replace (Z.to_nat (word.sub src0 src0)) with O in H14 by ZnWords;
            cbn in H14; case H14 as [[? ?]|[? ?]]; try discriminate.
          rewrite Properties.word.add_0_r.
          rewrite H14. split. { rewrite LittleEndianList.le_combine_1. trivial. }

          cbv [WeakestPrecondition.store load load_Z coqutil.Map.Memory.load_bytes store store_Z coqutil.Map.Memory.store_bytes coqutil.Map.Memory.unchecked_store_bytes LittleEndianList.le_split]; cbn.
          pose proof map.get_split dst0 _ _ _ H8.
          rewrite map.get_of_list_word_at in H16.
          progress replace (Z.to_nat (word.sub dst0 dst0)) with O in H16 by ZnWords;
            cbn in H16; case H16 as [[? ?]|[? ?]]; try discriminate.
          rewrite Properties.word.add_0_r.
          eexists. rewrite H16. split.
          { rewrite word.unsigned_of_Z, Scalars.wrap_byte_unsigned.
            rewrite byte.of_Z_unsigned; trivial. }

          eapply map.split_remove_put in H6; [|eapply H14].
          eapply map.split_remove_put in H8; [|eapply H16].
          rewrite map.remove_head_of_list_word_at_cons in H6,H8 by (cbn in *; ZnWords).
          assert (map.split (map.put m0 dst0 b) (s0$@(word.add src0 (word.of_Z 1))) (map.put (map.put mRs0 src0 b) dst0 b)).
          { eapply map.split_put_None; trivial.
            rewrite map.get_of_list_word_at, List.nth_error_None.
            cbn in *; ZnWords. }
          assert (map.split (map.put m0 dst0 b) (d0$@(word.add dst0 (word.of_Z 1))) (map.put mRd0 dst0 b)).
          { rewrite <-map.put_put_same with (m:=mRd0) (v1 := B).
            eapply map.split_put_Some; rewrite ?map.get_put_same; eauto. }

          cbv [get literal dlet.dlet].
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn).
          eexists.
          eexists.
          { eauto. }
          eexists.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn).
          eexists.
          { eauto. }
          eexists.
          eexists.
          { eauto. }
          eexists _, _, _, _.
          split.
          { cbv [Loops.enforce]; cbn.
            repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn); split.
            { exact eq_refl. }
            { eapply map.map_ext; intros k.
              repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
              repeat (destruct String.eqb; trivial). } }
          eexists _, _, _, _, (length s0); split; ssplit.
          { ZnWords. }
          { rewrite map.of_list_word_singleton, <-map.put_putmany_commute, map.putmany_empty_r; eassumption. }
          { rewrite map.of_list_word_singleton, <-map.put_putmany_commute, map.putmany_empty_r; eassumption. }
          { ZnWords. }
          { cbn in *; ZnWords. }
          { cbn in *; ZnWords. }
          { cbn in *; ZnWords. }
          split.
          { cbn in *; ZnWords. }
          intuition idtac; repeat straightline_cleanup.
          eapply map.split_put_r2l in H22; trivial.
          rewrite <-map.of_list_word_at_cons in H22. exact H22. }
        { cbn. intuition idtac. eexists _, _; ssplit; eauto. } }

    { assert (n <= x) by ZnWords.

      unfold1_cmd_goal; cbv beta match delta [cmd_body].
      eapply WeakestPreconditionProperties.dexpr_expr.
      repeat straightline.
      letexists; split.
      { subst l0 l; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
      letexists; split.
      { subst l0 l; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
      repeat straightline.

      eapply WeakestPreconditionProperties.dexpr_expr.
      repeat straightline.
      letexists; split.
      { subst l1 l0 l; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
      letexists; split.
      { subst l1 l0 l; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
      repeat straightline.

      refine ((Loops.tailrec
        (HList.polymorphic_list.cons _
        (HList.polymorphic_list.cons _
        (HList.polymorphic_list.cons _
        (HList.polymorphic_list.cons _
        HList.polymorphic_list.nil))))
        ["dst";"src";"n";"x"])
        (fun (v:nat) s mRs d mRd t m dst src n _x => PrimitivePair.pair.mk (
          n <= x /\ map.split m (s$@(word.sub src (word.sub n (word.of_Z 1)))) mRs /\
                    map.split m (d$@(word.sub dst (word.sub n (word.of_Z 1)))) mRd /\
          x = word.sub src dst /\ v=n :> Z /\ length s = n :> Z /\ length d = n :> Z
        )
        (fun                     T M DST SRC N X => t = T   /\  map.split M (s$@(word.sub dst (word.sub n (word.of_Z 1)))) mRd))
        lt
        _ _ _ _ _ _ _ _ _);
        (* TODO wrap this into a tactic with the previous refine *)
        cbn [HList.hlist.foralls HList.tuple.foralls
             HList.hlist.existss HList.tuple.existss
             HList.hlist.apply  HList.tuple.apply
             HList.hlist
             List.repeat Datatypes.length
             HList.polymorphic_list.repeat HList.polymorphic_list.length
             PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
        { cbv [Loops.enforce]; cbn.
          subst l l0 l1 l2.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn); split.
          { exact eq_refl. }
          { eapply map.map_ext; intros k.
            repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
            repeat (destruct String.eqb; trivial). } }
        { eapply Wf_nat.lt_wf. }
        { cbn. subst v0 v. rewrite !word.word_sub_add_l_same_r. ssplit; eauto. ZnWords. }
        { intros ?v ?s ?mRs ?d ?mRd ?t ?m ?dst ?src ?n ?x.
          repeat straightline.
          cbn in localsmap.
          eexists n0; split; cbv [expr expr_body localsmap get].
          { rewrite ?Properties.map.get_put_dec. exists n0; cbn. auto. }
          split; cycle 1.
          { intros Ht; rewrite Ht in *.
            intuition idtac; destruct s0, d0; cbn in *; try discriminate; [].
            rewrite map.of_list_word_nil in *; trivial. }
          repeat straightline.
          eapply WeakestPreconditionProperties.dexpr_expr.
          repeat straightline.
          letexists; split.
          { rewrite ?Properties.map.get_put_dec; exact eq_refl. }
          eapply WeakestPreconditionProperties.dexpr_expr.
          repeat straightline.
          letexists; split.
          { rewrite ?Properties.map.get_put_dec; cbn. exact eq_refl. }
          repeat straightline.

          cbv [WeakestPrecondition.load load load_Z]; cbn.
          destruct (@List.exists_last _ s0) as (s0'&b&H's) in *.
          { intro. subst. cbn in *. ZnWords. }
          destruct (@List.exists_last _ d0) as (d0'&B&H'd) in *.
          { intro. subst. cbn in *. ZnWords. }
          subst s0 d0; rename s0' into s0; rename d0' into d0; rewrite List.app_length in *; cbn [List.length] in *.
          exists (word.of_Z (byte.unsigned b)).
          pose proof map.get_split src0 _ _ _ H6.
          rewrite !map.get_of_list_word_at, !List.nth_error_app2 in H14 by ZnWords.
          match goal with H : context[List.nth_error [_] ?i = None] |- _ =>
              replace i with O in H by ZnWords; cbn [List.nth_error] in H end.
          cbn in H14; case H14 as [[? ?]|[? ?]]; try discriminate.
          rewrite Properties.word.add_0_r.
          rewrite H14. split. { rewrite LittleEndianList.le_combine_1. trivial. }

          cbv [WeakestPrecondition.store load load_Z coqutil.Map.Memory.load_bytes store store_Z coqutil.Map.Memory.store_bytes coqutil.Map.Memory.unchecked_store_bytes LittleEndianList.le_split]; cbn.
          pose proof map.get_split dst0 _ _ _ H8.
          rewrite !map.get_of_list_word_at, !List.nth_error_app2 in H16 by ZnWords.
          match goal with H : context[List.nth_error [_] ?i = None] |- _ =>
              replace i with O in H by ZnWords; cbn [List.nth_error] in H end.
          case H16 as [[? ?]|[? ?]]; try discriminate.
          rewrite Properties.word.add_0_r.
          eexists. rewrite H16. split.
          { rewrite word.unsigned_of_Z, Scalars.wrap_byte_unsigned.
            rewrite byte.of_Z_unsigned; trivial. }

          eapply map.split_remove_put in H6; [|eapply H14].
          eapply map.split_remove_put in H8; [|eapply H16].
          rewrite !map.remove_last_of_list_word_at_snoc in H6,H8 by ZnWords.
          assert (map.split (map.put m0 dst0 b) (s0$@(word.sub src0 (word.sub n0 (word.of_Z 1)))) (map.put (map.put mRs0 src0 b) dst0 b)).
          { eapply map.split_put_None; trivial.
            rewrite map.get_of_list_word_at, List.nth_error_None.
            cbn in *; ZnWords. }
          assert (map.split (map.put m0 dst0 b) (d0$@(word.sub dst0 (word.sub n0 (word.of_Z 1)))) (map.put mRd0 dst0 b)).
          { rewrite <-map.put_put_same with (m:=mRd0) (v1 := B).
            eapply map.split_put_Some; rewrite ?map.get_put_same; eauto. }

          cbv [get literal dlet.dlet].
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn).
          eexists.
          eexists.
          { eauto. }
          eexists.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn).
          eexists.
          { eauto. }
          eexists.
          eexists.
          { eauto. }
          eexists _, _, _, _.
          split.
          { cbv [Loops.enforce]; cbn.
            repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn); split.
            { exact eq_refl. }
            { eapply map.map_ext; intros k.
              repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
              repeat (destruct String.eqb; trivial). } }
          eexists _, _, _, _, (length s0); split; ssplit.
          { ZnWords. }
          { replace (word.sub (word.sub src0 (word.of_Z 1))(word.sub (word.sub n0 (word.of_Z 1)) (word.of_Z 1)))
              with (word.sub src0 (word.sub n0 (word.of_Z 1))) by ZnWords.
            rewrite map.of_list_word_singleton, <-map.put_putmany_commute, map.putmany_empty_r; eassumption. }
          { replace (word.sub (word.sub dst0 (word.of_Z 1)) (word.sub (word.sub n0 (word.of_Z 1)) (word.of_Z 1)))
              with (word.sub dst0 (word.sub n0 (word.of_Z 1))) by ZnWords.
            rewrite map.of_list_word_singleton, <-map.put_putmany_commute, map.putmany_empty_r; eassumption. }
          { ZnWords. }
          { cbn in *; ZnWords. }
          { cbn in *; ZnWords. }
          { cbn in *; ZnWords. }
          split.
          { cbn in *; ZnWords. }
          intuition idtac; repeat straightline_cleanup.
          eapply map.split_put_r2l in H22; trivial.
          rewrite map.of_list_word_at_snoc by ZnWords.
          progress replace (word.add (word.sub dst0 (word.sub n0 (word.of_Z 1))) (word.of_Z (length s0))) with dst0 by ZnWords.
          progress replace (word.sub (word.sub dst0 (word.of_Z 1)) (word.sub (word.sub n0 (word.of_Z 1)) (word.of_Z 1))) with (word.sub dst0 (word.sub n0 (word.of_Z 1))) in H22 by ZnWords.
          exact H22. }
        { cbn. intuition idtac. eexists _, _; ssplit; eauto. f_equal. ZnWords. } }
  Qed.

  Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").
  Global Instance spec_of_memmove_array : spec_of "memmove" :=
    fnspec! "memmove" (dst src n : word) / (d s : list byte) (R Rs : mem -> Prop),
    { requires t m := m =* s$@src * Rs /\ m =* d$@dst * R /\
        length s = n :> Z /\ length d = n :> Z /\ n <= 2^(width-1);
      ensures t' m := m =* s$@dst * R /\ t=t' }.

  Lemma memmove_ok_array : program_logic_goal_for_function! memmove.
  Proof.
    cbv [program_logic_goal_for spec_of_memmove_array]; intros.
    eapply WeakestPreconditionProperties.Proper_call; cycle 1; [eapply memmove_ok|].
    { eassumption. }
    { intuition idtac.
      - seprewrite_in_by @Array.array1_iff_eq_of_list_word_at H0 ZnWords; eassumption.
      - seprewrite_in_by @Array.array1_iff_eq_of_list_word_at H ZnWords; eassumption.
      - trivial.
      - trivial. }
    { intros ? ? ? ?. intuition idtac.
      seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) H2 ZnWords; eassumption. }
  Qed.
End WithParameters.
