Require Import bedrock2.NotationsCustomEntry.

Import Syntax Syntax.Coercions BinInt String List List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition memconst bs := func! (p) {
    i = $0; while i < $(Z.of_nat (length bs)) {
      store1(p, $(expr.inlinetable access_size.one bs "i"));
      p = p + $1;
      i = i + $1
    }
  }.

Require Import bedrock2.WeakestPrecondition bedrock2.Semantics bedrock2.ProgramLogic.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface bedrock2.Map.SeparationLogic.
Require Import bedrock2.ZnWords.
Import Coq.Init.Byte coqutil.Byte.
Local Notation string := String.string.

(*Require Import bedrock2.ptsto_bytes.*)
Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").

Section WithParameters.
  Context {width} {BW: Bitwidth width}.
  Context {word: word.word width} {mem: map.map word byte} {locals: map.map string word}.
  Context {ext_spec: ExtSpec}.
  Import ProgramLogic.Coercions.

  Global Instance spec_of_memconst ident bs : spec_of "memconst" :=
    fnspec! ident (p : word) / (ds : list byte) (R : mem -> Prop),
    { requires t m := m =* ds$@p * R /\ length ds = length bs :>Z /\ length bs < 2^width ;
      ensures t' m := m =* bs$@p * R /\ t=t' }.

  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {locals_ok : map.ok locals}
    {ext_spec_ok : ext_spec.ok ext_spec}.

  Import coqutil.Tactics.letexists coqutil.Tactics.Tactics coqutil.Tactics.autoforward.
  Import coqutil.Word.Properties coqutil.Map.Properties.

  Local Ltac normalize_body_of_function f ::= f.

  Local Ltac ZnWords := destruct width_cases; bedrock2.ZnWords.ZnWords.
  Lemma memconst_ok ident bs functions :
    program_logic_goal_for
      (memconst bs)
      (map.get functions ident = Some (memconst bs) ->
       spec_of_memconst ident bs functions).
  Proof.
    cbv [spec_of_memconst memconst]; repeat straightline.
    refine ((Loops.tailrec
      (HList.polymorphic_list.cons _
      (HList.polymorphic_list.cons _
      HList.polymorphic_list.nil))
      ["p";"i"])
      (fun (n:nat) (ds : list byte) R t m p i => PrimitivePair.pair.mk (
        m =* ds$@p * R /\ i + n = length bs :> Z /\ length ds = n)
      (fun              T M P N => t = T /\ M =* (List.skipn (Z.to_nat i) bs)$@p * R))
      lt
      _ _ _ _ _ _ _);
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
    { ssplit; eauto; ZnWords. }
    { intros ?n ?ds ?R ?t ?m ?p ?i.
      repeat straightline.
      cbn in localsmap.
      eexists; split; cbv [expr expr_body localsmap get].
      { rewrite ?Properties.map.get_put_dec. eexists; cbn; split; reflexivity. }
      rewrite !word.unsigned_ltu.
      destr Z.ltb; split; intros;
        rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1 in H5; try congruence;
        autoforward with typeclass_instances in E; cycle 1.
      { ssplit; trivial. replace n with O in * by ZnWords; cbn.
        destruct ds0 in *; cbn in *; try discriminate.
        rewrite List.skipn_all2; cbn; trivial. ZnWords. }
      repeat straightline.

      eapply WeakestPreconditionProperties.dexpr_expr.
      repeat straightline.
      letexists; split.
      { rewrite ?Properties.map.get_put_dec; exact eq_refl. }

      eapply WeakestPreconditionProperties.dexpr_expr.
      repeat straightline.
      letexists; split.
      { rewrite ?Properties.map.get_put_dec; exact eq_refl. }

      cbv [WeakestPrecondition.load load load_Z load_bytes footprint]; cbn.
      rewrite OfListWord.map.get_of_list_word.
      destruct List.nth_error eqn:?; cycle 1.
      { eapply List.nth_error_None in Heqo. exfalso. ZnWords. }
      rewrite LittleEndianList.le_combine_1.
      eexists; split; eauto.

      destruct ds0 in *; cbn [length Array.array] in *; [exfalso; ZnWords|].
      repeat straightline.

      letexists; split.
      { eexists. rewrite ?Properties.map.get_put_dec; cbn. split; eauto.
        repeat straightline. }

      letexists; split.
      { eexists. rewrite ?Properties.map.get_put_dec; cbn. split; eauto.
        repeat straightline. }

      eexists _, _.
      split.
      { cbv [Loops.enforce]; cbn.
        repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn); split.
        { exact eq_refl. }
        { eapply map.map_ext; intros k.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
          repeat (destruct String.eqb; trivial). } }
      eexists _, _, _; split; ssplit; try ecancel_assumption; try reflexivity.
      { cbn in *. ZnWords. }
      split.
      { ZnWords. }
      intuition idtac.

      pose proof byte.unsigned_range b.
      rewrite word.unsigned_of_Z_nowrap, byte.of_Z_unsigned in H9 by ZnWords.
      replace (Z.to_nat v0) with (1 + (Z.to_nat i0))%nat in H9 by ZnWords.
      rewrite <-List.skipn_skipn in H9.
      rewrite List.nth_error_as_skipn, Properties.word.add_0_r  in Heqo.
      remember (List.skipn (Z.to_nat i0) bs) as ts in *.
      destruct ts in *; cbn [List.skipn List.hd_error Array.array] in *; [discriminate|].
      subst v.
      use_sep_assumption.
      cancel.
      Morphisms.f_equiv.
      congruence. }

    intuition idtac; cbn; ssplit; eauto.
    replace (Z.to_nat i) with O in * by ZnWords; cbn in *; eauto.
  Qed.
End WithParameters.
