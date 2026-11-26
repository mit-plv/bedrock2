Require Import Coq.micromega.Lia.
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

Require Import bedrock2.LeakageWeakestPrecondition bedrock2.LeakageSemantics.
Require Import bedrock2.LeakageLoops bedrock2.LeakageProgramLogic.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface bedrock2.Map.SeparationLogic.
Require Import bedrock2.ZnWords.
Import Coq.Init.Byte coqutil.Byte.
Local Notation string := String.string.

Local Notation "xs $@ a" := (Array.array ptsto (bits.of_Z _ 1) a xs) (at level 10, format "xs $@ a").

Section WithParameters.
  Context {width} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word byte} {locals: map.map string word}.
  Context {ext_spec: ExtSpec} {pick_sp: PickSp}.
  Import LeakageProgramLogic.Coercions.

  Global Instance spec_of_memconst ident bs : spec_of "memconst" :=
    fnspec! exists f, ident (p : word) / (ds : list byte) (R : mem -> Prop),
    { requires k t m := m =* ds$@p * R /\ length ds = length bs :>Z /\ length bs < 2^width ;
      ensures k' t' m := m =* bs$@p * R /\ t=t' /\ k' = f p ++ k }.

  Context {mem_ok: map.ok mem} {locals_ok : map.ok locals}
    {ext_spec_ok : ext_spec.ok ext_spec}.

  Import coqutil.Tactics.letexists coqutil.Tactics.Tactics coqutil.Tactics.autoforward.
  Import coqutil.Word.Properties coqutil.Map.Properties.

  Local Ltac normalize_body_of_function f ::= f.

  (* leakage of one loop iteration, newest event first: the inline table lookup
     leaks the index [i], the store leaks the address [p], and the loop condition
     leaks that it was taken *)
  Local Fixpoint newtrace p i n :=
    match n with
    | S n' => newtrace (Zmod.add p (bits.of_Z width 1)) (Zmod.add i (bits.of_Z width 1)) n' ++
               [leak_word p; leak_word i; leak_bool true]
    | O => []
    end.

  Local Ltac ZnWords := destruct width_cases; bedrock2.ZnWords.ZnWords.
  Lemma memconst_ok ident bs functions :
    program_logic_goal_for
      (memconst bs)
      (map.get functions ident = Some (memconst bs) ->
       spec_of_memconst ident bs functions).
  Proof.
    cbv [spec_of_memconst memconst]; repeat straightline.
    refine ((LeakageLoops.tailrec
      (HList.polymorphic_list.cons _
      (HList.polymorphic_list.cons _
      HList.polymorphic_list.nil))
      ["p";"i"])
      (fun (n:nat) (ds : list byte) R k t m p i => PrimitivePair.pair.mk (
        m =* ds$@p * R /\ i + n = length bs :> Z /\ length ds = n)
      (fun            K T M P N => t = T /\ M =* (List.skipn (Z.to_nat i) bs)$@p * R /\
                                  K = leak_bool false :: newtrace p i n ++ k))
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
    { cbv [LeakageLoops.enforce]; cbn.
      subst l l0.
      repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn); split.
      { exact eq_refl. }
      { eapply map.map_ext; intros kk.
        repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
        repeat (destruct String.eqb; trivial). } }
    { eapply Wf_nat.lt_wf. }
    { ssplit; eauto; ZnWords. }
    { intros ?n ?ds ?R ?k ?t ?m ?p ?i.
      repeat straightline.
      cbn in localsmap.
      eexists; eexists; split; cbv [dexpr expr expr_body localsmap get].
      { rewrite ?Properties.map.get_put_dec. eexists; cbv [literal dlet.dlet]; cbn; split; [reflexivity|split; reflexivity]. }
      destr Z.ltb; split; intros;
        rewrite ?Zmod.unsigned_0, ?bits.unsigned_1 in H5 by (pose proof width_pos; lia); try congruence;
        autoforward with typeclass_instances in E; cycle 1.
      { ssplit; trivial; replace n with O in * by ZnWords; cbn; [|reflexivity].
        destruct ds0 in *; cbn in *; try discriminate.
        rewrite List.skipn_all2; cbn; trivial. ZnWords. }
      repeat straightline.

      eapply LeakageWeakestPreconditionProperties.dexpr_expr.
      repeat straightline.
      letexists; split.
      { rewrite ?Properties.map.get_put_dec; exact eq_refl. }

      eapply LeakageWeakestPreconditionProperties.dexpr_expr.
      repeat straightline.
      letexists; split.
      { rewrite ?Properties.map.get_put_dec; exact eq_refl. }

      cbv [LeakageWeakestPrecondition.load load load_Z load_bytes footprint]; cbn.
      rewrite (OfListWord.map.get_of_list_word width_pos).
      destruct List.nth_error eqn:?; cycle 1.
      { eapply List.nth_error_None in Heqo. exfalso. ZnWords. }
      rewrite LittleEndianList.le_combine_1.
      eexists; split; eauto.

      destruct ds0 in *; cbn [length Array.array] in *; [exfalso; ZnWords|].
      repeat straightline.

      letexists; eexists; split.
      { eexists. rewrite ?Properties.map.get_put_dec; cbn. split; eauto.
        repeat straightline. }

      letexists; eexists; split.
      { eexists. rewrite ?Properties.map.get_put_dec; cbn. split; eauto.
        repeat straightline. }

      eexists _, _.
      split.
      { cbv [LeakageLoops.enforce]; cbn.
        repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn); split.
        { exact eq_refl. }
        { eapply map.map_ext; intros kk.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
          repeat (destruct String.eqb; trivial). } }
      eexists _, _, _; split; ssplit; try ecancel_assumption; try reflexivity.
      { cbn in *. ZnWords. }
      split.
      { ZnWords. }
      intuition idtac.
      2: { subst K. rewrite <-H4. cbn [newtrace]. rewrite <-List.app_assoc. reflexivity. }

      pose proof byte.unsigned_range b.
      rewrite bits.unsigned_of_Z_small, byte.of_Z_unsigned in H7 by ZnWords.
      replace (Z.to_nat v0) with (1 + (Z.to_nat i0))%nat in H7 by ZnWords.
      rewrite <-List.skipn_skipn in H7.
      rewrite <-List.hd_error_skipn, Zmod.add_0_r in Heqo.
      remember (List.skipn (Z.to_nat i0) bs) as ts in *.
      destruct ts in *; cbn [List.skipn List.hd_error Array.array] in *; [discriminate|].
      subst v.
      use_sep_assumption.
      cancel.
      Morphisms.f_equiv.
      congruence. }

    intuition idtac; cbn; ssplit; eauto.
    2: { replace (length ds) with (length bs) in H5 by lia. subst k0.
         instantiate (1 := fun p => leak_bool false :: newtrace p (bits.of_Z width 0) (length bs)).
         reflexivity. }
    replace (Z.to_nat i) with O in * by ZnWords; cbn in *; eauto.
  Qed.
End WithParameters.
