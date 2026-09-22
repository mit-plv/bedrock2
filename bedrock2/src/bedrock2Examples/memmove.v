Require Import bedrock2.NotationsCustomEntry.

Import Syntax Syntax.Coercions BinInt String List List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Require Import bedrock2.LeakageWeakestPrecondition bedrock2.LeakageSemantics.
Require Import bedrock2.LeakageLoops bedrock2.LeakageProgramLogic.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface bedrock2.Map.SeparationLogic.
Require Import coqutil.Macros.symmetry.
Require Import bedrock2.ZnWords.
Import Coq.Init.Byte coqutil.Byte.
Local Notation string := String.string.

Require Import coqutil.Map.OfListWord.
Local Notation "xs $@ a" := (map.of_list_word_at a xs) (at level 10, format "xs $@ a").

Section WithParameters.
  Context {width} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word byte} {locals: map.map string word}.
  Context {ext_spec: ExtSpec} {pick_sp: PickSp}.
  Import LeakageProgramLogic.Coercions.


  Local Instance spec_of_memmove : spec_of "memmove" :=
    fnspec! exists f, "memmove" (dst src n : word) / (d s : list byte) (R Rs : mem -> Prop),
    { requires k t m := m =* s$@src * Rs /\ m =* d$@dst * R /\
        length s = n :> Z /\ length d = n :> Z /\ n <= 2^(width-1);
      ensures k' t' m' := m' =* s$@dst * R /\ t = t' /\ k' = f dst src n ++ k }.


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

  (* Leakage of one copy loop: [n] iterations, each leaking the store
     address [dst] and the load address [src], with the pointers moving by
     [step] (1 forward, -1 backward) after each iteration. *)
  Local Fixpoint memmove_loop_trace (step dst src : word) (n : nat) : leakage :=
    match n with
    | S n' => memmove_loop_trace step (Zmod.add dst step) (Zmod.add src step) n' ++
              [leak_word dst; leak_word src; leak_bool true]
    | O => [leak_bool false]
    end.

  (* Leakage of [memmove]: it depends only on the two pointers and the
     length, never on the bytes being moved. *)
  Definition memmove_trace (dst src n : word) : leakage :=
    let x := Zmod.sub src dst in
    if Zmod.unsigned x =? 0 then [leak_bool false] else
    if Zmod.unsigned x <? Zmod.unsigned (Zmod.add x n)
    then memmove_loop_trace (bits.of_Z width 1) dst src (Z.to_nat (Zmod.unsigned n)) ++
         [leak_bool true; leak_bool true]
    else memmove_loop_trace (bits.of_Z width (-1))
           (Zmod.add dst (Zmod.sub n (bits.of_Z width 1)))
           (Zmod.add src (Zmod.sub n (bits.of_Z width 1)))
           (Z.to_nat (Zmod.unsigned n)) ++
         [leak_bool false; leak_bool true].


  Context {mem_ok: map.ok mem} {locals_ok : map.ok locals}
    {ext_spec_ok : ext_spec.ok ext_spec}.

  Import coqutil.Tactics.letexists coqutil.Tactics.Tactics coqutil.Tactics.autoforward.
  Import coqutil.Word.Properties coqutil.Map.Properties.

  Local Ltac ZnWords := destruct width_cases; bedrock2.ZnWords.ZnWords.
  Lemma memmove_ok : program_logic_goal_for_function! memmove.
  Proof.
    enter memmove. exists memmove_trace. intros.
    match goal with
    | H: map.get ?functions ?fname = Some _ |- _ =>
        eapply LeakageWeakestPreconditionProperties.start_func; [exact H | clear H]
    end.
    cbv match beta delta [LeakageWeakestPrecondition.func].
    repeat straightline.

    case H as (ms&mRs&?&?&?), H0 as (md&mRd&?&?&?);
      cbv [sepclause_of_map] in *; subst; clear dependent Rs.

    eapply LeakageWeakestPreconditionProperties.dexpr_expr.
    repeat straightline.
    letexists; split.
    { subst l; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
    letexists; split.
    { subst l; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
    repeat straightline.

    set (x := Zmod.sub src dst) in *.
    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    eapply LeakageWeakestPreconditionProperties.dexpr_expr.
    letexists; split.
    { subst l0; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
    repeat straightline.

    (* x = 0 *)
    split; intros Hx; cycle 1.
    { replace src with dst in * by ZnWords.
      cbn; ssplit; eauto.
      { eexists _, _; ssplit; eauto.
        eapply map.split_same_footprint; eauto.
        intros kk.
        rewrite 2(map.get_of_list_word_at width_pos), 2List.nth_error_None.
        Morphisms.f_equiv. ZnWords. }
      cbv [memmove_trace]. subst x.
      rewrite (proj2 (Z.eqb_eq _ _)) by ZnWords. reflexivity. }

    unfold1_cmd_goal; cbv beta match delta [cmd_body].
    eapply LeakageWeakestPreconditionProperties.dexpr_expr.
    letexists; split.
    { subst l0; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
    repeat straightline.
    letexists; split.
    { subst l0; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
    letexists; split.
    { subst l0 l; rewrite ?Properties.map.get_put_dec. exact eq_refl. }
    repeat straightline.

    rewrite Zmod.unsigned_add.
    split; intros Hbr;
      [apply word.if_nonzero in Hbr | apply (word.if_zero _ width_pos) in Hbr];
      autoforward with typeclass_instances in Hbr.

    { assert (x + n < 2^width) by ZnWords.
      refine ((LeakageLoops.tailrec
        (HList.polymorphic_list.cons _
        (HList.polymorphic_list.cons _
        (HList.polymorphic_list.cons _
        (HList.polymorphic_list.cons _
        HList.polymorphic_list.nil))))
        ["dst";"src";"n";"x"])
        (fun (v:nat) s mRs d mRd k t m dst src n _x => PrimitivePair.pair.mk (
          x + n < 2^width /\ map.split m (s$@src) mRs /\  map.split m (d$@dst) mRd /\
          x = Zmod.sub src dst /\ v=n :> Z /\ length s = n :> Z /\ length d = n :> Z
        )
        (fun                     K T M DST SRC N X => t = T   /\  map.split M (s$@dst) mRd /\
          K = memmove_loop_trace (bits.of_Z width 1) dst src (Z.to_nat (Zmod.unsigned n)) ++ k))
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
        { cbv [LeakageLoops.enforce]; cbn.
          subst l l0.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn); split.
          { exact eq_refl. }
          { eapply map.map_ext; intros kk.
            repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
            repeat (destruct String.eqb; trivial). } }
        { eapply Wf_nat.lt_wf. }
        { cbn; ssplit; eauto. }
        { intros ?v ?s ?mRs ?d ?mRd ?k ?t ?m ?dst ?src ?n ?x.
          repeat straightline.
          cbn in localsmap.
          eexists n0; exists k0; split; cbv [dexpr expr expr_body localsmap get].
          { rewrite ?Properties.map.get_put_dec. exists n0; cbn. auto. }
          split; cycle 1.
          { intros Ht; rewrite Ht in *.
            intuition idtac; destruct s0, d0; cbn in *; try discriminate; [].
            eauto. }
          repeat straightline.
          eapply LeakageWeakestPreconditionProperties.dexpr_expr.
          repeat straightline.
          letexists; split.
          { rewrite ?Properties.map.get_put_dec; exact eq_refl. }
          eapply LeakageWeakestPreconditionProperties.dexpr_expr.
          repeat straightline.
          letexists; split.
          { rewrite ?Properties.map.get_put_dec; cbn. exact eq_refl. }
          repeat straightline.

          cbv [LeakageWeakestPrecondition.load load load_Z]; cbn.
          destruct s0 as [|b s0], d0 as [|B d0]; try (cbn in *; congruence); [].
          exists (bits.of_Z width (byte.unsigned b)).
          pose proof map.get_split src0 _ _ _ H6.
          rewrite (map.get_of_list_word_at width_pos) in H14.
          progress replace (Z.to_nat (Zmod.sub src0 src0)) with O in H14 by ZnWords;
            cbn in H14; case H14 as [[? ?]|[? ?]]; try discriminate.
          rewrite Zmod.add_0_r.
          rewrite H14. split. { rewrite LittleEndianList.le_combine_1. trivial. }

          cbv [LeakageWeakestPrecondition.store load load_Z coqutil.Map.Memory.load_bytes store store_Z coqutil.Map.Memory.store_bytes coqutil.Map.Memory.unchecked_store_bytes LittleEndianList.le_split]; cbn.
          pose proof map.get_split dst0 _ _ _ H8.
          rewrite (map.get_of_list_word_at width_pos) in H16.
          progress replace (Z.to_nat (Zmod.sub dst0 dst0)) with O in H16 by ZnWords;
            cbn in H16; case H16 as [[? ?]|[? ?]]; try discriminate.
          rewrite Zmod.add_0_r.
          eexists. rewrite H16. split.
          { rewrite bits.unsigned_of_Z, Scalars.wrap_byte_unsigned.
            rewrite byte.of_Z_unsigned; trivial. }

          eapply map.split_remove_put in H6; [|eapply H14].
          eapply map.split_remove_put in H8; [|eapply H16].
          rewrite (map.remove_head_of_list_word_at_cons width_pos) in H6,H8 by (cbn in *; ZnWords).
          assert (map.split (map.put m0 dst0 b) (s0$@(Zmod.add src0 (bits.of_Z width 1))) (map.put (map.put mRs0 src0 b) dst0 b)).
          { eapply map.split_put_None; trivial.
            rewrite (map.get_of_list_word_at width_pos), List.nth_error_None.
            cbn in *; ZnWords. }
          assert (map.split (map.put m0 dst0 b) (d0$@(Zmod.add dst0 (bits.of_Z width 1))) (map.put mRd0 dst0 b)).
          { rewrite <-map.put_put_same with (m:=mRd0) (v1 := B).
            eapply map.split_put_Some; rewrite ?map.get_put_same; eauto. }

          cbv [get literal dlet.dlet].
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn).
          eexists.
          eexists.
          eexists.
          { eauto. }
          eexists.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn).
          eexists.
          eexists.
          { eauto. }
          eexists.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn).
          eexists.
          eexists.
          { eauto. }
          eexists _, _, _, _.
          split.
          { cbv [LeakageLoops.enforce]; cbn.
            repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn); split.
            { exact eq_refl. }
            { eapply map.map_ext; intros kk.
              repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
              repeat (destruct String.eqb; trivial). } }
          eexists _, _, _, _, (length s0); split; ssplit.
          { ZnWords. }
          { rewrite (map.of_list_word_singleton width_pos), <-map.put_putmany_commute, map.putmany_empty_r; eassumption. }
          { rewrite (map.of_list_word_singleton width_pos), <-map.put_putmany_commute, map.putmany_empty_r; eassumption. }
          { ZnWords. }
          { cbn in *; ZnWords. }
          { cbn in *; ZnWords. }
          { cbn in *; ZnWords. }
          split.
          { cbn in *; ZnWords. }
          intuition idtac; repeat straightline_cleanup.
          { eapply map.split_put_r2l in H20; trivial.
            rewrite <-(map.of_list_word_at_cons width_pos) in H20. exact H20. }
          { subst K.
            replace (Z.to_nat n0) with (S (Z.to_nat (Zmod.sub n0 (bits.of_Z width 1))))
              by (rewrite <-Z2Nat.inj_succ by ZnWords; f_equal; cbn in *; ZnWords).
            cbn [memmove_loop_trace List.app]. rewrite <- List.app_assoc. cbn [List.app].
            reflexivity. } }
        { cbn. intuition idtac.
          { eexists _, _; ssplit; eauto. }
          subst k0. cbv [memmove_trace]. subst x.
          rewrite (proj2 (Z.eqb_neq _ _) Hx).
          rewrite (proj2 (Z.ltb_lt _ _)) by ZnWords.
          align_trace. } }

    { assert (n <= x) by ZnWords.

      unfold1_cmd_goal; cbv beta match delta [cmd_body].
      eapply LeakageWeakestPreconditionProperties.dexpr_expr.
      repeat straightline.
      letexists; split.
      { subst l0 l; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
      letexists; split.
      { subst l0 l; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
      repeat straightline.

      eapply LeakageWeakestPreconditionProperties.dexpr_expr.
      repeat straightline.
      letexists; split.
      { subst l1 l0 l; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
      letexists; split.
      { subst l1 l0 l; rewrite ?Properties.map.get_put_dec; exact eq_refl. }
      repeat straightline.

      refine ((LeakageLoops.tailrec
        (HList.polymorphic_list.cons _
        (HList.polymorphic_list.cons _
        (HList.polymorphic_list.cons _
        (HList.polymorphic_list.cons _
        HList.polymorphic_list.nil))))
        ["dst";"src";"n";"x"])
        (fun (v:nat) s mRs d mRd k t m dst src n _x => PrimitivePair.pair.mk (
          n <= x /\ map.split m (s$@(Zmod.sub src (Zmod.sub n (bits.of_Z width 1)))) mRs /\
                    map.split m (d$@(Zmod.sub dst (Zmod.sub n (bits.of_Z width 1)))) mRd /\
          x = Zmod.sub src dst /\ v=n :> Z /\ length s = n :> Z /\ length d = n :> Z
        )
        (fun                     K T M DST SRC N X => t = T   /\  map.split M (s$@(Zmod.sub dst (Zmod.sub n (bits.of_Z width 1)))) mRd /\
          K = memmove_loop_trace (bits.of_Z width (-1)) dst src (Z.to_nat (Zmod.unsigned n)) ++ k))
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
        { cbv [LeakageLoops.enforce]; cbn.
          subst l l0 l1 l2.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn); split.
          { exact eq_refl. }
          { eapply map.map_ext; intros kk.
            repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
            repeat (destruct String.eqb; trivial). } }
        { eapply Wf_nat.lt_wf. }
        { cbn. subst v0 v. rewrite !word.word_sub_add_l_same_r. ssplit; eauto. ZnWords. }
        { intros ?v ?s ?mRs ?d ?mRd ?k ?t ?m ?dst ?src ?n ?x.
          repeat straightline.
          cbn in localsmap.
          eexists n0; exists k0; split; cbv [dexpr expr expr_body localsmap get].
          { rewrite ?Properties.map.get_put_dec. exists n0; cbn. auto. }
          split; cycle 1.
          { intros Ht; rewrite Ht in *.
            intuition idtac; destruct s0, d0; cbn in *; try discriminate; [].
            rewrite map.of_list_word_nil in *; trivial. }
          repeat straightline.
          eapply LeakageWeakestPreconditionProperties.dexpr_expr.
          repeat straightline.
          letexists; split.
          { rewrite ?Properties.map.get_put_dec; exact eq_refl. }
          eapply LeakageWeakestPreconditionProperties.dexpr_expr.
          repeat straightline.
          letexists; split.
          { rewrite ?Properties.map.get_put_dec; cbn. exact eq_refl. }
          repeat straightline.

          cbv [LeakageWeakestPrecondition.load load load_Z]; cbn.
          destruct (@List.exists_last _ s0) as (s0'&b&H's) in *.
          { intro. subst. cbn in *. ZnWords. }
          destruct (@List.exists_last _ d0) as (d0'&B&H'd) in *.
          { intro. subst. cbn in *. ZnWords. }
          subst s0 d0; rename s0' into s0; rename d0' into d0; rewrite List.length_app in *; cbn [List.length] in *.
          exists (bits.of_Z width (byte.unsigned b)).
          pose proof map.get_split src0 _ _ _ H6.
          rewrite !(map.get_of_list_word_at width_pos), !List.nth_error_app2 in H14 by ZnWords.
          match goal with H : context[List.nth_error [_] ?i = None] |- _ =>
              replace i with O in H by ZnWords; cbn [List.nth_error] in H end.
          cbn in H14; case H14 as [[? ?]|[? ?]]; try discriminate.
          rewrite Zmod.add_0_r.
          rewrite H14. split. { rewrite LittleEndianList.le_combine_1. trivial. }

          cbv [LeakageWeakestPrecondition.store load load_Z coqutil.Map.Memory.load_bytes store store_Z coqutil.Map.Memory.store_bytes coqutil.Map.Memory.unchecked_store_bytes LittleEndianList.le_split]; cbn.
          pose proof map.get_split dst0 _ _ _ H8.
          rewrite !(map.get_of_list_word_at width_pos), !List.nth_error_app2 in H16 by ZnWords.
          match goal with H : context[List.nth_error [_] ?i = None] |- _ =>
              replace i with O in H by ZnWords; cbn [List.nth_error] in H end.
          case H16 as [[? ?]|[? ?]]; try discriminate.
          rewrite Zmod.add_0_r.
          eexists. rewrite H16. split.
          { rewrite bits.unsigned_of_Z, Scalars.wrap_byte_unsigned.
            rewrite byte.of_Z_unsigned; trivial. }

          eapply map.split_remove_put in H6; [|eapply H14].
          eapply map.split_remove_put in H8; [|eapply H16].
          rewrite !(map.remove_last_of_list_word_at_snoc width_pos) in H6,H8 by ZnWords.
          assert (map.split (map.put m0 dst0 b) (s0$@(Zmod.sub src0 (Zmod.sub n0 (bits.of_Z width 1)))) (map.put (map.put mRs0 src0 b) dst0 b)).
          { eapply map.split_put_None; trivial.
            rewrite (map.get_of_list_word_at width_pos), List.nth_error_None.
            cbn in *; ZnWords. }
          assert (map.split (map.put m0 dst0 b) (d0$@(Zmod.sub dst0 (Zmod.sub n0 (bits.of_Z width 1)))) (map.put mRd0 dst0 b)).
          { rewrite <-map.put_put_same with (m:=mRd0) (v1 := B).
            eapply map.split_put_Some; rewrite ?map.get_put_same; eauto. }

          cbv [get literal dlet.dlet].
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn).
          eexists.
          eexists.
          eexists.
          { eauto. }
          eexists.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn).
          eexists.
          eexists.
          { eauto. }
          eexists.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn).
          eexists.
          eexists.
          { eauto. }
          eexists _, _, _, _.
          split.
          { cbv [LeakageLoops.enforce]; cbn.
            repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn); split.
            { exact eq_refl. }
            { eapply map.map_ext; intros kk.
              repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
              repeat (destruct String.eqb; trivial). } }
          eexists _, _, _, _, (length s0); split; ssplit.
          { ZnWords. }
          { replace (Zmod.sub (Zmod.sub src0 (bits.of_Z width 1))(Zmod.sub (Zmod.sub n0 (bits.of_Z width 1)) (bits.of_Z width 1)))
              with (Zmod.sub src0 (Zmod.sub n0 (bits.of_Z width 1))) by ZnWords.
            rewrite (map.of_list_word_singleton width_pos), <-map.put_putmany_commute, map.putmany_empty_r; eassumption. }
          { replace (Zmod.sub (Zmod.sub dst0 (bits.of_Z width 1)) (Zmod.sub (Zmod.sub n0 (bits.of_Z width 1)) (bits.of_Z width 1)))
              with (Zmod.sub dst0 (Zmod.sub n0 (bits.of_Z width 1))) by ZnWords.
            rewrite (map.of_list_word_singleton width_pos), <-map.put_putmany_commute, map.putmany_empty_r; eassumption. }
          { ZnWords. }
          { cbn in *; ZnWords. }
          { cbn in *; ZnWords. }
          { cbn in *; ZnWords. }
          split.
          { cbn in *; ZnWords. }
          intuition idtac; repeat straightline_cleanup.
          { eapply map.split_put_r2l in H20; trivial.
            rewrite (map.of_list_word_at_snoc width_pos) by ZnWords.
            progress replace (Zmod.add (Zmod.sub dst0 (Zmod.sub n0 (bits.of_Z width 1))) (bits.of_Z width (length s0))) with dst0 by ZnWords.
            progress replace (Zmod.sub (Zmod.sub dst0 (bits.of_Z width 1)) (Zmod.sub (Zmod.sub n0 (bits.of_Z width 1)) (bits.of_Z width 1))) with (Zmod.sub dst0 (Zmod.sub n0 (bits.of_Z width 1))) in H20 by ZnWords.
            exact H20. }
          { subst K.
            replace (Z.to_nat n0) with (S (Z.to_nat (Zmod.sub n0 (bits.of_Z width 1))))
              by (rewrite <-Z2Nat.inj_succ by ZnWords; f_equal; cbn in *; ZnWords).
            cbn [memmove_loop_trace List.app]. rewrite <- List.app_assoc. cbn [List.app].
            replace (Zmod.add dst0 (bits.of_Z width (-1))) with (Zmod.sub dst0 (bits.of_Z width 1)) by ZnWords.
            replace (Zmod.add src0 (bits.of_Z width (-1))) with (Zmod.sub src0 (bits.of_Z width 1)) by ZnWords.
            reflexivity. } }
        { cbn. intuition idtac.
          { eexists _, _; ssplit; eauto. f_equal. ZnWords. }
          subst k0. cbv [memmove_trace]. subst x.
          rewrite (proj2 (Z.eqb_neq _ _) Hx).
          rewrite (proj2 (Z.ltb_ge _ _)) by ZnWords.
          subst v0 v.
          align_trace. } }
  Qed.

  Local Notation "xs $@ a" := (Array.array ptsto (bits.of_Z width 1) a xs) (at level 10, format "xs $@ a").
  Global Instance spec_of_memmove_array : spec_of "memmove" :=
    fnspec! exists f, "memmove" (dst src n : word) / (d s : list byte) (R Rs : mem -> Prop),
    { requires k t m := m =* s$@src * Rs /\ m =* d$@dst * R /\
        length s = n :> Z /\ length d = n :> Z /\ n <= 2^(width-1);
      ensures k' t' m' := m' =* s$@dst * R /\ t = t' /\ k' = f dst src n ++ k }.

  Lemma memmove_ok_array : program_logic_goal_for_function! memmove.
  Proof.
    cbv [program_logic_goal_for spec_of_memmove_array]; intros.
    pose proof memmove_ok as Hok; cbv [program_logic_goal_for spec_of_memmove] in Hok.
    specialize (Hok functions ltac:(eassumption)); case Hok as [f Hok]; exists f; intros.
    eapply LeakageWeakestPreconditionProperties.Proper_call; cycle 1; [eapply Hok|].
    { intuition idtac.
      - seprewrite_in_by @Array.array1_iff_eq_of_list_word_at H0 ZnWords; eassumption.
      - seprewrite_in_by @Array.array1_iff_eq_of_list_word_at H ZnWords; eassumption.
      - trivial.
      - trivial. }
    { intros ? ? ? ? ?. intuition idtac.
      seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) H2 ZnWords; eassumption. }
  Qed.
End WithParameters.
