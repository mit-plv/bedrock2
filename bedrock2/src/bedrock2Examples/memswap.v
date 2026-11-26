Require Import bedrock2.NotationsCustomEntry.

Import Syntax Syntax.Coercions BinInt String List List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition memswap := func! (x, y, n) {
  while n {
    vx = load1(x);
    vy = load1(y);
    store1(x, vy);
    store1(y, vx);

    x = x + $1;
    y = y + $1;
    n = n - $1;
    $(cmd.unset "vx");
    $(cmd.unset "vy")
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

  Global Instance spec_of_memswap : spec_of "memswap" :=
    fnspec! exists f, "memswap" (x y n : word) / (xs ys : list byte) (R : mem -> Prop),
    { requires k t m := m =* xs$@x * ys$@y * R /\
                      length xs = n :>Z /\ length ys = n :>Z;
      ensures k' t' m' := m' =* ys$@x * xs$@y * R /\ t=t' /\ k' = f x y n ++ k }.

  Context {mem_ok: map.ok mem} {locals_ok : map.ok locals}
    {ext_spec_ok : ext_spec.ok ext_spec}.

  Import coqutil.Tactics.letexists coqutil.Tactics.Tactics coqutil.Tactics.autoforward.
  Import coqutil.Word.Properties coqutil.Map.Properties.

  (* Leakage of one loop iteration, newest event first: the two stores (to y,
     then x), the two loads (from y, then x), and the loop condition. *)
  Local Fixpoint newtrace x y n :=
    match n with
    | S n' => newtrace (Zmod.add x (bits.of_Z width 1)) (Zmod.add y (bits.of_Z width 1)) n' ++
               [leak_word y; leak_word x; leak_word y; leak_word x; leak_bool true]
    | O => []
    end.

  Local Ltac ZnWords := destruct width_cases; bedrock2.ZnWords.ZnWords.
  Lemma memswap_ok : program_logic_goal_for_function! memswap.
  Proof.
    repeat straightline.
    instantiate (1 := fun x y n => leak_bool false :: newtrace x y (Z.to_nat (Zmod.unsigned n))).

    refine ((LeakageLoops.tailrec
      (HList.polymorphic_list.cons _
      (HList.polymorphic_list.cons _
      (HList.polymorphic_list.cons _
      HList.polymorphic_list.nil)))
      ["x";"y";"n"])
      (fun (v:nat) xs ys R k t m x y n => PrimitivePair.pair.mk (
        m =* xs$@x * ys$@y * R /\ length xs = n :>Z /\ length ys = n :>Z /\ v = n :>Z)
      (fun                 K T M (X Y N : word) =>
        leak_bool false :: newtrace x y (Z.to_nat (Zmod.unsigned n)) ++ k = K /\ t = T /\ M =* ys$@x * xs$@y * R))
      lt
      _ _ _ _ _ _ _ _);
      (* TODO wrap this into a tactic with the previous refine *)
      cbn [HList.hlist.foralls HList.tuple.foralls
           HList.hlist.existss HList.tuple.existss
           HList.hlist.apply  HList.tuple.apply
           HList.hlist
           List.repeat Datatypes.length
           HList.polymorphic_list.repeat HList.polymorphic_list.length
           PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
      { cbv [LeakageLoops.enforce]; cbn.
        subst l.
        repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn); split.
        { exact eq_refl. }
        { eapply map.map_ext; intros kk.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
          repeat (destruct String.eqb; trivial). } }
      { eapply Wf_nat.lt_wf. }
      { cbn; ssplit; try ecancel_assumption; eauto. }
      { intros ?v ?xs ?ys ?R ?k ?t ?m ?x ?y ?n.
        repeat straightline.
        cbn in localsmap.
        eexists n0; exists k0; split; cbv [dexpr expr expr_body localsmap get].
        { rewrite ?Properties.map.get_put_dec. exists n0; cbn. auto. }
        split; cycle 1.
        { intros Ht; rewrite Ht in *.
          intuition idtac; destruct xs0, ys0; cbn in *; try discriminate; try ecancel_assumption; eauto. }

        intros Ht.
        destruct xs0 as [|hxs xs0] in *, ys0 as [|hys ys0] in *;
          cbn [length Array.array] in *; try (cbn in *; congruence); [];

        repeat straightline.
        eapply LeakageWeakestPreconditionProperties.dexpr_expr.

        repeat straightline.
        letexists; split.
        { rewrite ?Properties.map.get_put_dec; exact eq_refl. }
        repeat straightline.

        eapply LeakageWeakestPreconditionProperties.dexpr_expr.
        letexists; split.
        { subst l. rewrite ?Properties.map.get_put_dec; cbn. exact eq_refl. }
        repeat straightline.

        eapply LeakageWeakestPreconditionProperties.dexpr_expr.
        letexists; split.
        { subst l l0. rewrite ?Properties.map.get_put_dec; exact eq_refl. }
        repeat straightline.

        repeat straightline.
        eapply LeakageWeakestPreconditionProperties.dexpr_expr.
        letexists; split.
        { subst l l0. rewrite ?Properties.map.get_put_dec; cbn. exact eq_refl. }

        repeat straightline.
        eapply LeakageWeakestPreconditionProperties.dexpr_expr.
        letexists; split.
        { subst l l0. rewrite ?Properties.map.get_put_dec; cbn. exact eq_refl. }

        repeat straightline.
        eapply LeakageWeakestPreconditionProperties.dexpr_expr.
        letexists; split.
        { subst l l0. rewrite ?Properties.map.get_put_dec; cbn. exact eq_refl. }

        repeat straightline.
        eapply LeakageWeakestPreconditionProperties.dexpr_expr.
        letexists; split.
        { subst l l0. rewrite ?Properties.map.get_put_dec; cbn. exact eq_refl. }

        repeat straightline.
        eapply LeakageWeakestPreconditionProperties.dexpr_expr.
        letexists; split.
        { subst l l0 l1. rewrite ?Properties.map.get_put_dec; cbn. exact eq_refl. }

        repeat straightline.
        eapply LeakageWeakestPreconditionProperties.dexpr_expr.
        letexists; split.
        { subst l l0 l1 l2. rewrite ?Properties.map.get_put_dec; cbn. exact eq_refl. }

        eexists _, _, _.
        split.
        { cbv [LeakageLoops.enforce l l0 l1 l2]; cbn.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn); split.
          { exact eq_refl. }
          { eapply map.map_ext; intros kk.
            repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
            repeat (destruct String.eqb; trivial). } }
        eexists _, _, _, (length xs0); split; ssplit; try ecancel_assumption; try ZnWords.
        split.
        { cbn in *; ZnWords. }
        intuition idtac; repeat straightline_cleanup.
        { replace (Z.to_nat n0) with (S (Z.to_nat (Zmod.sub n0 (bits.of_Z width 1)))) by ZnWords.
          cbn [newtrace List.app]. rewrite <- List.app_assoc. cbn [List.app].
          cbn [leak_binop List.app] in H9. subst v2 v3. exact H9. }
        subst v0 v1 v2 v3.
        pose proof byte.unsigned_range hxs.
        pose proof byte.unsigned_range hys.
        use_sep_assumption.
        rewrite !bits.unsigned_of_Z_small, !byte.of_Z_unsigned by ZnWords.
        cancel. }

      intuition idtac. cbn. eauto.
  Qed.
End WithParameters.
