Require Import bedrock2.NotationsCustomEntry.

Import Syntax Syntax.Coercions BinInt String List List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition memequal := func! (x,y,n) ~> r {
  r = $0;
  while n {
    r = r | (load1(x) ^ load1(y));
    x = x + $1;
    y = y + $1;
    n = n - $1
  };
  r = r == $0
}.

Require Import bedrock2.LeakageWeakestPrecondition bedrock2.LeakageSemantics.
Require Import bedrock2.LeakageLoops bedrock2.LeakageProgramLogic.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface bedrock2.Map.SeparationLogic.
Require Import bedrock2.ZnWords.
Import Coq.Init.Byte coqutil.Byte.
Local Notation string := String.string.

Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").

Section WithParameters.
  Context {width} {BW: Bitwidth width}.
  Context {word: word.word width} {mem: map.map word byte} {locals: map.map string word}.
  Context {ext_spec: ExtSpec} {pick_sp: PickSp}.
  Import LeakageProgramLogic.Coercions.

  Global Instance spec_of_memequal : spec_of "memequal" :=
    fnspec! exists f, "memequal" (x y n : word) / (xs ys : list byte) (Rx Ry : mem -> Prop) ~> r,
    { requires k t m := m =* xs$@x * Rx /\ m =* ys$@y * Ry /\
                      length xs = n :>Z /\ length ys = n :>Z;
      ensures k' t' m' := f x y n ++ k = k' /\ m=m' /\ t=t' /\ (r = 0 :>Z \/ r = 1 :>Z) /\
                       (r  = 1 :>Z <-> xs  = ys) }.

  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {locals_ok : map.ok locals}
    {ext_spec_ok : ext_spec.ok ext_spec}.

  Import coqutil.Tactics.letexists coqutil.Tactics.Tactics coqutil.Tactics.autoforward.
  Import coqutil.Word.Properties coqutil.Map.Properties.

  Local Fixpoint newtrace x y n :=
    match n with
    | S n' => newtrace (word.add x (word.of_Z 1)) (word.add y (word.of_Z 1)) n' ++
               [leak_word y; leak_word x; leak_bool true] 
    | O => []
    end.

  Local Ltac ZnWords := destruct width_cases; bedrock2.ZnWords.ZnWords.
  Lemma memequal_ok : program_logic_goal_for_function! memequal.
  Proof.
    repeat straightline.

    refine ((LeakageLoops.tailrec
      (HList.polymorphic_list.cons _
      (HList.polymorphic_list.cons _
      (HList.polymorphic_list.cons _
      (HList.polymorphic_list.cons _
      HList.polymorphic_list.nil))))
      ["x";"y";"n";"r"])
      (fun (v:nat) xs Rx ys Ry k t m x y n r => PrimitivePair.pair.mk (
        m =* xs$@x * Rx /\  m =* ys$@y * Ry /\
        v=n :> Z /\ length xs = n :> Z /\ length ys = n :> Z
      )
      (fun                   K T M (X Y N R : word) => leak_bool false :: newtrace x y (Z.to_nat (word.unsigned n)) ++ k = K /\ t = T /\ m = M /\
        exists z, R = Z.lor r z :> Z /\ (z  = 0 :>Z <-> xs  = ys)
      ))
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
      { intros ?v ?xs ?Rx ?ys ?Ry ?k ?t ?m ?x ?y ?n ?r.
        repeat straightline.
        cbn in localsmap.
        eexists n0; exists k0; split; cbv [dexpr expr expr_body localsmap get].
        { rewrite ?Properties.map.get_put_dec. exists n0; cbn. auto. }
        split; cycle 1.
        { intros Ht; rewrite Ht in *.
          intuition idtac; destruct xs0, ys0; cbn in *; try discriminate; [].
          exists 0; intuition eauto. rewrite Z.lor_0_r. trivial. }

        intros Ht.
        destruct xs0 as [|hxs xs0] in *, ys0 as [|hys ys0] in *;
          cbn [length Array.array] in *; try (cbn in *; congruence); [];

        repeat straightline.
        eapply LeakageWeakestPreconditionProperties.dexpr_expr.

        repeat straightline.
        letexists; split.
        { rewrite ?Properties.map.get_put_dec; exact eq_refl. }
        repeat straightline.
        letexists; split.
        { rewrite ?Properties.map.get_put_dec; cbn. exact eq_refl. }
        repeat straightline.

        repeat straightline.
        repeat straightline.
        letexists; split.
        { rewrite ?Properties.map.get_put_dec; exact eq_refl. }
        repeat straightline.

        repeat straightline.
        eapply LeakageWeakestPreconditionProperties.dexpr_expr.
        letexists; split.
        { subst l. rewrite ?Properties.map.get_put_dec; cbn. exact eq_refl. }

        repeat straightline.
        eapply LeakageWeakestPreconditionProperties.dexpr_expr.
        letexists; split.
        { subst l l0. rewrite ?Properties.map.get_put_dec; cbn. exact eq_refl. }

        repeat straightline.
        eapply LeakageWeakestPreconditionProperties.dexpr_expr.
        letexists; split.
        { subst l l0 l1. rewrite ?Properties.map.get_put_dec; cbn. exact eq_refl. }

        repeat straightline.

        eexists _, _, _, _.
        split.
        { cbv [LeakageLoops.enforce l l0 l1 l2]; cbn.
          repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec; cbn); split.
          { exact eq_refl. }
          { eapply map.map_ext; intros kk.
            repeat (rewrite ?map.get_put_dec, ?map.get_remove_dec, ?map.get_empty; cbn -[String.eqb]).
            repeat (destruct String.eqb; trivial). } }
        eexists _, _, _, _, (length xs0); split; ssplit.
        { ecancel_assumption. }
        { ecancel_assumption. }
        { ZnWords. }
        { ZnWords. }
        { ZnWords. }
        split.
        { cbn in *; ZnWords. }
        intuition idtac; repeat straightline_cleanup.
        { replace (Z.to_nat n0) with (S (Z.to_nat (word.sub n0 v4))) by ZnWords.
          cbn [newtrace List.app]. rewrite <- List.app_assoc. cbn [List.app].
          subst v3 v4. apply H9. } 
        rewrite H11, word.unsigned_or_nowrap, <-Z.lor_assoc.
        eexists; split; trivial.
        transitivity (hxs = hys /\ xs0 = ys0); [|intuition congruence].
        rewrite <-H12. rewrite Z.lor_eq_0_iff. eapply and_iff_compat_r.
        subst v1 v2. rewrite word.unsigned_xor_nowrap, Z.lxor_eq_0_iff.
        split; [|intros;subst;trivial].
        intro HH.
        pose proof byte.unsigned_range hxs;
        pose proof byte.unsigned_range hys.
        eapply word.unsigned_inj in HH; eapply word.of_Z_inj_small in HH; try ZnWords.
        eapply byte.unsigned_inj in HH; trivial. }

      intuition idtac. case H7 as (?&?&?). subst. subst r.
      eapply LeakageWeakestPreconditionProperties.dexpr_expr.
      letexists; split; cbn.
      { rewrite ?Properties.map.get_put_dec; cbn; exact eq_refl. }
      eexists; split; cbn.
      { rewrite ?Properties.map.get_put_dec; cbn; exact eq_refl. }

      rewrite word.unsigned_of_Z_0, Z.lor_0_l in H6; subst x4 v.
      setoid_rewrite word.unsigned_eqb; setoid_rewrite word.unsigned_of_Z_0.
      repeat straightline. split.
      { instantiate (1 := fun _ _ _ => _ :: _). simpl. reflexivity. }
      repeat straightline. split.
      all: destr Z.eqb; autoforward with typeclass_instances in E;
        rewrite ?word.unsigned_of_Z_1, ?word.unsigned_of_Z_0; eauto.
      all : intuition eauto; discriminate.
  Qed.
End WithParameters.
