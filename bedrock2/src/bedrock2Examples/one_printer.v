Require Import coqutil.sanity coqutil.Byte.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Properties.
Require coqutil.Map.SortedListString.
Require Import coqutil.Z.Lia.
Require Import bedrock2.Syntax coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Export bedrock2.Memory.
Require Import Coq.Lists.List.
Require Import bedrock2.LeakageSemantics.
Require Import bedrock2.MetricLeakageSemantics.

Require Import coqutil.Word.SimplWordExpr.
Require Import bedrock2.FE310CSemantics.
From Coq Require Import ZArith.
From Coq Require Import Lia.

Section WithParams.
  Context {BW: Bitwidth 32} {word: word.word 32} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {word_ok : word.ok word} {mem_ok: map.ok mem}.
  Context {pick_sp: PickSp}.
  Local Instance ext_spec : ExtSpec := FE310CSemantics.leakage_ext_spec.
  Require Import Strings.String.
  Open Scope string_scope.
  
  Definition anMMIOAddr : Z := 131072.

  Definition one_printer :=
    (cmd.while (expr.literal 1) (cmd.interact nil "MMIOWRITE" (cons (expr.literal anMMIOAddr) (cons (expr.literal 1) nil)))).

  Definition countdown :=
    (cmd.while (expr.var "x")
       (cmd.seq
          (cmd.interact nil "MMIOWRITE" (cons (expr.literal anMMIOAddr) (cons (expr.literal 0) nil)))
          (cmd.set "x" (expr.op bopname.sub (expr.var "x") (expr.literal 1))))).
  
  Definition eventual_one_printer :=
    cmd.seq (cmd.stackalloc "x" 0 cmd.skip)
      (cmd.seq countdown one_printer).

  Context {locals_ok: map.ok locals}.

  Lemma countdown_terminates e aep k t m l mc xval :
    map.get l "x" = Some (word.of_Z xval) ->
    Z.le 0 xval ->
    exec e countdown true aep k t m l mc (fun q' aep' _ _ _ _ _=> q' = true /\ aep' = aep).
  Proof.
    intros. replace xval with (Z.of_nat (Z.to_nat xval)) in * by lia. clear H0.
    remember (Z.to_nat xval) as xval'.
    clear Heqxval' xval.
    remember xval' as upper_bound.
    rewrite Hequpper_bound in H.
    assert (xval' <= upper_bound)%nat  by lia. clear Hequpper_bound. revert xval' H0 H.
    revert aep k t m l mc.
    induction upper_bound; intros.
    - eapply exec.while_false.
      + simpl. rewrite H. reflexivity.
      + rewrite word.unsigned_of_Z. replace xval' with 0%nat by lia. reflexivity.
      + auto.
    - assert (word.wrap (Z.of_nat xval') <> 0 \/ word.wrap (Z.of_nat xval') = 0) by lia.
      destruct H1.
      + eapply exec.while_true.
        -- simpl. rewrite H. reflexivity.
        -- rewrite word.unsigned_of_Z. assumption.
        -- eapply exec.seq_cps.
           ++ eapply exec.interact_cps.
              --- apply map.split_empty_r. reflexivity.
              --- reflexivity. 
              --- cbv [ext_spec leakage_ext_spec]. simpl. do 2 eexists. intuition eauto.
                  { cbv [anMMIOAddr isMMIOAddr]. rewrite word.unsigned_of_Z.
                    cbv [word.wrap]. simpl. vm_compute. auto. left. auto.
                    split; congruence. }
                  { rewrite word.unsigned_of_Z. reflexivity. }
                  simpl. intros. fwd. eexists. intuition eauto.
                  econstructor.
                  { simpl. rewrite H. reflexivity. }
                  instantiate (1 := fun q' aep' _ _ _ l' _ => q' = true /\ aep' = aep /\ map.get l' "x" = Some (*(word.of_Z (Z.of_nat xval'))*)_).
                  simpl. intuition. rewrite map.get_put_same. auto.
        -- simpl. intros. fwd. eapply IHupper_bound.
           2: { rewrite H2p2. f_equal.
                instantiate (1 := Z.to_nat (word.unsigned _)). rewrite Z2Nat.id.
                2: { epose proof Properties.word.unsigned_range _ as H2. apply H2. }
                rewrite word.of_Z_unsigned. reflexivity. }
           enough (word.unsigned (word := word) (word.sub (word.of_Z (Z.of_nat xval')) (word.of_Z 1)) <= Z.of_nat upper_bound) by lia.
           pose proof Properties.word.decrement_nonzero_lt as H2.
           specialize (H2 (word.of_Z (Z.of_nat xval'))).
           rewrite word.unsigned_of_Z in H2. specialize (H2 H1).
           remember (word.unsigned _) as blah. clear Heqblah. enough (word.wrap (Z.of_nat xval') <= 1 + (Z.of_nat upper_bound)) by lia.
           clear H2 blah. cbv [word.wrap].
           pose proof Z.mod_le (Z.of_nat xval') (2 ^ 32) as H2.
           specialize (H2 ltac:(lia)). eassert _ as blah. 2: specialize (H2 blah); lia.
           assert (2 ^ 0 <= 2 ^ 32).
           { apply Z.pow_le_mono_r; try lia. (*destruct word_ok; clear - width_pos.
             lia.*) }
           lia.
      + eapply exec.while_false.
        -- simpl. rewrite H. reflexivity.
        -- rewrite word.unsigned_of_Z. assumption.
        -- auto.
  Qed.

  Definition one : Semantics.LogItem := ((map.empty, "MMIOWRITE", (cons (word.of_Z anMMIOAddr) (cons (word.of_Z 1) nil))), (map.empty, nil)).

  Lemma one_not_zero : word.unsigned (word := word) (word.of_Z 1) <> 0.
  Proof.
    rewrite word.unsigned_of_Z. cbv [word.wrap]. 
    destruct word_ok. clear - width_pos.
    assert (2 ^ 1 <= 2 ^ 32).
    { Search (_ ^ _ <= _ ^ _).  apply Z.pow_le_mono_r; lia. }
    replace (2 ^ 1) with 2 in H by reflexivity.
    remember (2 ^ 32) as blah. clear Heqblah.
    Fail Z.div_mod_to_equations; lia. (*?*)
    rewrite Z.mod_small by lia. lia.
  Qed.
  
  Lemma one_printer_prints_ones n e aep k t m l mc :
    exec e one_printer true aep k t m l mc
      (fun q' aep' k' t' m' l' mc' => q' = false /\ aep' = aep /\ t' = repeat one n ++ t)%nat%list.
  Proof.
    revert aep k t m l mc. induction n; intros aep k t m l mc.
    - apply exec.quit. simpl. auto.
    - eapply exec.while_true.
      + reflexivity.
      + apply one_not_zero.
      + eapply exec.interact_cps.
        -- apply map.split_empty_r. reflexivity.
        -- reflexivity.
        -- cbv [ext_spec leakage_ext_spec].
           simpl. do 2 eexists. intuition eauto.
           { cbv [anMMIOAddr isMMIOAddr]. rewrite word.unsigned_of_Z.
             cbv [word.wrap]. simpl. vm_compute. auto. left. auto.
             split; congruence. }
           { rewrite word.unsigned_of_Z. reflexivity. }
           simpl. intros. fwd. eexists. intuition eauto.
           instantiate (1 := fun q' aep' k' t' _ _ _ => q' = true /\ aep' = aep /\ t' = one :: t).
           simpl. auto.
      + simpl. intros. fwd. eapply exec.weaken. 1: apply IHn. simpl. intros.
        fwd. intuition auto.
        replace (repeat one n ++ one :: t)%list with (repeat one (S n) ++ t)%list.
        -- reflexivity.
        -- replace (S n) with (n + 1)%nat by lia. rewrite repeat_app.
           rewrite <- app_assoc. reflexivity.
  Qed.

  Definition eventually_print_ones : AEP :=
    AEP_E (fun n1 => AEP_A (fun n2 => AEP_P (fun _ t _ _ => exists t1, List.length t1 = n1 /\ (t = repeat one n2 ++ t1)%list))).
  
  Lemma eventual_one_printer_eventually_prints_ones e k t m l mc :
    exec e eventual_one_printer true eventually_print_ones k t m l mc
      (fun _ aep k t m l mc =>
         match aep with
         | AEP_P P => P k t m mc
         | _ => False
         end).
  Proof.
    cbv [eventual_one_printer]. eapply exec.seq_cps.
    econstructor.
    { reflexivity. }
    intros. constructor. do 2 eexists. intuition eauto.
    eapply exec.seq. 1: eapply countdown_terminates.
    { rewrite map.get_put_same. instantiate (1 := word.unsigned _).
      rewrite word.of_Z_unsigned. reflexivity. }
    { Search word.unsigned. pose proof (Properties.word.unsigned_range a) as blah.
      destruct blah. assumption. }
    simpl. intros. fwd.
    apply exec.exec_E with (x := List.length t').
    apply exec.exec_A. intros.
    eapply exec.weaken. 1: apply one_printer_prints_ones.
    simpl. intros. fwd. eexists. split; [reflexivity|]. reflexivity.
  Qed.

  Definition one_printer_fun : (list string * list string * cmd) := (nil, nil, eventual_one_printer).
End WithParams.
