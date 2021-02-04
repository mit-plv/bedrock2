Require Import Coq.Arith.Arith.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.ptsto_bytes.
Require Import coqutil.Decidable.
Require Import coqutil.Word.Properties.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import coqutil.Tactics.Simp.
Require Import bedrock2.MetricLogging.
Require Import riscv.Platform.MinimalLogging.
Require Import riscv.Platform.MetricMinimal.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
Require Import coqutil.Map.SortedList.
Require Import compiler.ZNameGen.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.SeparationLogic.
Require Import bedrock2Examples.Demos.
Import Utility.

Section FibCompiled.

  Definition fib_ExprImp nl ns: cmd := Eval cbv in
    snd (snd (Demos.fibonacciServer nl ns)).

  Notation RiscvMachine := MetricRiscvMachine.

  Fixpoint fib (n: nat): Z :=
    match n with
    | O => 0
    | S x =>
      match x with
      | O => 1
      | S y => (fib x + fib y)
      end
    end.

  Definition fib_bounded (n: nat): Z :=
    if (n <? 47)%nat then fib (n + 1) else -1.

  Lemma fib_invert: forall n,
      fib (S (S n)) = fib n + fib (S n).
  Proof.
    induction n.
    - reflexivity.
    - simpl. destruct n.
      + reflexivity.
      + blia.
  Qed.

  Lemma fib_pos: forall n,
      0 <= fib n.
  Proof.
    cut (forall N n, (n < N)%nat -> 0 <= fib n).
    - eauto.
    - induction N.
      + intros. exfalso. apply Nat.nlt_0_r in H. exact H.
      + intros.
        destruct n; [simpl; blia|].
        destruct n; [simpl; blia|].
        rewrite fib_invert.
        generalize (IHN n) (IHN (S n)).
        blia.
  Qed.

  Lemma fib_inc: forall n m,
      (n <= m)%nat ->
      fib n <= fib m.
  Proof.
   induction 1.
   - apply Z.le_refl.
   - apply Z.le_trans with (fib m); [assumption|].
     destruct m.
     + simpl. blia.
     + rewrite fib_invert.
       pose proof (fib_pos m).
       blia.
  Qed.

  Ltac fib_next :=
    match goal with
    | H0: fib ?n0 = ?r0, H1: fib ?n1 = ?r1 |- _ =>
      let Ht := fresh "Ht" in
      let H := fresh "H" in
      assert (n1 = n0 + 1)%nat as Ht by reflexivity; clear Ht;
      assert (fib (S n1) = fib n0 + fib n1) as H by (rewrite fib_invert; reflexivity);
      rewrite H0 in H; rewrite H1 in H;
      match goal with
      | H: fib _ = ?x |- _ =>
        let r := fresh "r" in
        remember x as r;
        match goal with
        | Heqr: ?l = _ + _ |- _ => cbv in Heqr; subst r
        end
      end;
      clear H0
    end.

  Lemma fib_width_limit: forall n,
      (n < 48)%nat ->
      fib n < 2 ^ 32.
  Proof.
    intros.
    assert (fib 0 = 0) by reflexivity.
    assert (fib 1 = 1) by reflexivity.
    do 46 fib_next.
    assert (fib 47 < 2 ^ 32) by (rewrite H2; reflexivity).
    intros.
    induction n.
    - simpl. reflexivity.
    - pose proof (fib_inc (S n) 47%nat) as Hinc.
      apply Nat.lt_le_pred in H.
      simpl in H.
      specialize (Hinc H).
      blia.
  Qed.

  Local Notation instructionsH := (bedrock2.MetricLogging.instructions).

  (*
  Lemma load_word_sep: forall k (m: mem) v R,
      ((ptsto_word k v) * R)%sep m ->
      load access_size.four m k = Some v.
  Proof.
    intros.
    pose proof load_bytes_of_sep as Hload.
    specialize Hload with (1 := H).
    cbv [load load_Z].
    match goal with
    | H: ?y = ?v |- context[?x] =>
      match y with
      | bedrock2.Memory.load_bytes _ _ _ =>
        match x with
        | bedrock2.Memory.load_bytes _ _ _ => change x with y; rewrite H
        end
      end
    end.
    simpl. f_equal.
    rewrite LittleEndian.combine_split.
    change (BinInt.Z.of_nat (Pos.to_nat 4) * 8) with width.
    change width with 32.
    rewrite (Naive._unsigned_in_range v).
    rewrite (Naive.of_Z_unsigned).
    reflexivity.
  Qed.

  Lemma word_add_of_Z: forall width a b c,
      c < 2 ^ width ->
      0 <= a ->
      0 <= b ->
      a + b = c ->
      @word.add width _ (word.of_Z a) (word.of_Z b) = word.of_Z (c).
  Proof.
    intros.
    simpl.
    f_equal.
    repeat (rewrite Z.mod_small; [|blia]).
    assumption.
  Qed.
*)

  Fixpoint get_if s :=
    match s with
    | cmd.seq s1 s2 =>
      match s1 with
      | cmd.cond _ _ _ => s1
      | _ => get_if s2
      end
    | _ => s
    end.

  Definition fib_if ns nl := get_if (fib_ExprImp ns nl).

  Definition fib_while ns nl := Eval cbv in
        match fib_if ns nl with
        | cmd.cond _ w _ => w
        | _ => fib_if ns nl
        end.

  Definition fib_while_body ns nl := Eval cbv in
        match fib_while ns nl with
        | cmd.while _ b => b
        | _ => fib_while ns nl
        end.

  Ltac destruct_hyp :=
    repeat match goal with
           | H : _ /\ _ |- _ => destruct H
           end.

(*
  Ltac eval_fib_var_names :=
    cbv [FibonacciServer.a
           FibonacciServer.b
           Demos.FibonacciServer.c
           Demos.FibonacciServer.i
           Demos.FibonacciServer.n
           Demos.FibonacciServer.ZNames.Inst] in *.

  Ltac known_var :=
    match goal with
    | H: map.get ?l ?a = ?x |- context [?y] =>
      match x with
      | Some ?v =>
        match y with
        | map.get l a =>
          let Hp := fresh "Hp" in
          assert (y = x) as Hp by assumption;
          rewrite Hp; clear Hp
        end
      end
    end.

  Ltac fib_step_precondition :=
    match goal with
    | |- map.get (map.put _ _ _) _ = Some _ =>
      rewrite map.get_put_diff; [assumption|discriminate] || apply map.get_put_same
    | |- _ => assumption || simpl; blia
    end.

  Ltac eval_var_solve :=
    unfold eval_expr;
    eval_fib_var_names;
    repeat known_var;
    reflexivity.

  Ltac exec_set_solve :=
    intros; destruct_hyp;
    eapply @exec.set;
    [
      eval_var_solve |
      try (repeat split; fib_step_precondition)
    ].

  Ltac propogate_eq :=
    repeat match goal with
           | H0: ?x = ?y, H1: ?y = ?z |- _ => rewrite H1 in H0
           end; assumption.

  Lemma fib_correct_body: forall t m (l : locals) mc a b i n (R: mem -> Prop) ns nl,
      R m ->
      map.get l FibonacciServer.a = Some a ->
      map.get l FibonacciServer.b = Some b ->
      map.get l FibonacciServer.i = Some i ->
      map.get l FibonacciServer.n = Some n ->
      exec map.empty (fib_while_body ns nl) t m l mc (fun t' m' l' mc' =>
        t' = t /\
        R m' /\
        map.get l' FibonacciServer.a = Some b /\
        map.get l' FibonacciServer.b = Some (word.add a b) /\
        map.get l' FibonacciServer.i = Some (word.add i (word.of_Z 1)) /\
        map.get l' FibonacciServer.n = Some n /\
        instructionsH mc' - instructionsH mc = 21).
  Proof.
    intros.
    cbv [fib_while_body].
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
      t' = t /\
      R m' /\
      map.get l' FibonacciServer.a = Some a /\
      map.get l' FibonacciServer.b = Some b /\
      map.get l' FibonacciServer.c = Some (word.add a b) /\
      map.get l' FibonacciServer.i = Some i /\
      map.get l' FibonacciServer.n = Some n /\
      instructionsH mc' = instructionsH mc + 5));
      [exec_set_solve|].
    intros.

    eapply @exec.seq with (mid := (fun t' m' (l': locals) mc' =>
      t' = t /\
      R m' /\
      map.get l' (@FibonacciServer.a Basic32Syntax _) = Some b /\
      map.get l' (@FibonacciServer.b Basic32Syntax _)  = Some b /\
      map.get l' (@FibonacciServer.c Basic32Syntax _)  = Some (word.add a b) /\
      map.get l' (@FibonacciServer.i Basic32Syntax _)  = Some i /\
      map.get l' (@FibonacciServer.n Basic32Syntax _)  = Some n /\
      instructionsH mc' = instructionsH mc + 7));
      [exec_set_solve|].
    intros.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
      t' = t /\
      R m' /\
      map.get l' FibonacciServer.a = Some b /\
      map.get l' FibonacciServer.b = Some (word.add a b) /\
      map.get l' FibonacciServer.c = Some (word.add a b) /\
      map.get l' FibonacciServer.i = Some i /\
      map.get l' FibonacciServer.n = Some n /\
      instructionsH mc' = instructionsH mc + 9));
      exec_set_solve.
  Qed.

  Lemma fib_correct_while: forall n (iter : nat) t m (l : locals) mc i (R: mem -> Prop) nl ns,
      Z.of_nat n < 47 ->
      (iter <= n)%nat ->
      (i = n - iter)%nat ->
      R m ->
      map.get l FibonacciServer.a = Some (word.of_Z (fib i)) ->
      map.get l FibonacciServer.b = Some (word.of_Z (fib (S i))) ->
      map.get l FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) ->
      map.get l FibonacciServer.i = Some (word.of_Z (Z.of_nat i) : word) ->
      exec map.empty (fib_while nl ns) t m l mc (fun t' m' l' mc' =>
        t' = t /\
        R m' /\
        instructionsH mc' <= instructionsH mc + (Z.of_nat iter) * 34 + 12 /\
        map.get l' FibonacciServer.b = Some (word.of_Z (fib (n + 1)))).
  Proof.
    induction iter.
    - intros.
      eapply @exec.while_false.
      + eval_var_solve.
      + simpl. destruct_one_match.
        * rewrite H1 in E. rewrite Nat.sub_0_r in E.
          apply Z.lt_irrefl in E.
          exfalso. assumption.
        * reflexivity.
      + repeat split.
        * assumption.
        * simpl. blia.
        * replace n with i by blia.
          rewrite Nat.add_1_r.
          etransitivity; [ eassumption | reflexivity ].
    - intros.
      eapply @exec.while_true.
      + eval_var_solve.
      + simpl. destruct_one_match.
        * simpl. rewrite Zdiv.Zmod_1_l; [discriminate | cbv; reflexivity].
        * repeat match goal with
                 | H: context[_ mod _] |- _ => rewrite Z.mod_small in H; [|blia]
                 end.
          blia.
      + eapply fib_correct_body with (nl := nl) (ns := ns); eauto.
      + intros.
        eval_fib_var_names.
        destruct_hyp.
        eapply weaken_exec.
        * eapply IHiter with (nl := nl) (ns := ns); try (reflexivity || eassumption).
          -- blia.
          -- etransitivity; [eassumption|].
             f_equal. f_equal. f_equal. blia.
          -- etransitivity; [eassumption|].
             f_equal. replace (S i) with (n - iter)%nat by blia. rewrite H1.
             assert (n - iter > 0)%nat by blia.
             pose proof fib_invert as Hfib.
             specialize Hfib with (n := (n - S iter)%nat).
             apply word_add_of_Z; try apply fib_pos.
             ++ change Semantics.width with 32.
                apply fib_width_limit.
                blia.
             ++ replace (S (n - S iter))%nat with (n - iter)%nat in Hfib; [|blia].
                symmetry. apply Hfib.
          -- etransitivity; [eassumption|].
             f_equal. rewrite H1.
             simpl. f_equal.
             rewrite Z.mod_small; [|blia].
             rewrite Z.mod_small; [|blia].
             blia.
        * cbv beta. intros. destruct_hyp.
          repeat split.
          -- propogate_eq.
          -- assumption.
          -- unfold_MetricLog. simpl in *. blia.
          -- assumption.
  Qed.

  Lemma fib_if_true_correct: forall (n: nat) t m (l: locals) mc (R: mem -> Prop) nl ns,
      (n < 47)%nat ->
      R m ->
      map.get l FibonacciServer.a = Some (word.of_Z 0) ->
      map.get l FibonacciServer.b = Some (word.of_Z 1) ->
      map.get l FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) ->
      map.get l FibonacciServer.i = Some (word.of_Z 0)  ->
      exec map.empty (fib_if nl ns) t m l mc (fun t' m' l' mc' =>
        R m' /\
        t' = t /\
        instructionsH mc' <= instructionsH mc + (Z.of_nat n) * 34 + 25 /\
        map.get l' FibonacciServer.b = Some (word.of_Z (fib (n + 1)))).
  Proof.
    intros.
    eapply @exec.if_true.
    - eval_var_solve.
    - simpl.
      destruct_one_match; [discriminate|].
      repeat rewrite Z.mod_small in * by blia.
      exfalso. blia.
    - eapply weaken_exec.
      + destruct_hyp.
        eapply fib_correct_while with (iter := n) (i := 0%nat) (nl := nl) (ns := ns); try eassumption.
        * blia.
        * apply le_n.
        * rewrite Nat.sub_diag. reflexivity.
      + intros. cbv beta in *. destruct_hyp.
        repeat split; try assumption.
        unfold_MetricLog. simpl in *. blia.
  Qed.

  Lemma fib_if_false_correct: forall (n: nat) t m (l: locals) mc (R: mem -> Prop) nl ns,
      Z.of_nat n < 2 ^ 32 ->
      (n >= 47)%nat ->
      R m ->
      map.get l FibonacciServer.a = Some (word.of_Z 0) ->
      map.get l FibonacciServer.b = Some (word.of_Z 1) ->
      map.get l FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) ->
      map.get l FibonacciServer.i = Some (word.of_Z 0)  ->
      exec map.empty (fib_if nl ns) t m l mc (fun t' m' l' mc' =>
        t' = t /\
        R m' /\
        instructionsH mc' <= instructionsH mc + 22 /\
        map.get l' FibonacciServer.b = Some (word.of_Z (-1))).
  Proof.
    intros.
    eapply @exec.if_false.
    + eval_var_solve.
    + simpl.
      destruct_one_match; [|reflexivity].
      repeat rewrite Z.mod_small in * by blia.
      exfalso. blia.
    + exec_set_solve.
  Qed.

  Lemma fib_correct: forall (n: nat) t (m: mem) (l : locals) mc v nl ns,
      (ptsto_word (word.of_Z nl) (word.of_Z (Z.of_nat n)) *
       ptsto_word (word.of_Z ns) (word.of_Z v))%sep m ->
      Z.of_nat n < 2 ^ 32 ->
      exec map.empty (fib_ExprImp nl ns) t m l mc (fun t' m' l' mc' =>
        instructionsH mc' <= instructionsH mc + (Z.of_nat n) * 34 + 72 /\
        (ptsto_word (word.of_Z nl) (word.of_Z (Z.of_nat n)) *
         ptsto_word (word.of_Z ns) (word.of_Z (fib_bounded n)))%sep m').
  Proof.
    intros *. intro Hsep. intros.
    unfold fib_ExprImp.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
      t' = t /\
      (ptsto_word (word.of_Z nl) (word.of_Z (Z.of_nat n)) *
       ptsto_word (word.of_Z ns) (word.of_Z v))%sep m' /\
      map.get l' FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) /\
      instructionsH mc' = instructionsH mc + 10)).
    1: { eapply @exec.set.
         + simpl in *.
           pose proof load_word_sep as Hload.
           specialize Hload with (1 := Hsep).
           match goal with
           | H: ?x = ?r |- context[?y] =>
             match x with
             | load ?a ?m ?v =>
               match y with
               | load a m v => change y with x; rewrite H
               end
             end
           end.
           reflexivity.
         + repeat split; fib_step_precondition. }
    intros. destruct_hyp.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
      t' = t /\
      (ptsto_word (word.of_Z nl) (word.of_Z (Z.of_nat n)) *
       ptsto_word (word.of_Z ns) (word.of_Z v))%sep m' /\
      map.get l' FibonacciServer.a = Some (word.of_Z 0) /\
      map.get l' FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) /\
      instructionsH mc' = instructionsH mc + 19));
      [exec_set_solve|].
    intros. destruct_hyp.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
      t' = t /\
      (ptsto_word (word.of_Z nl) (word.of_Z (Z.of_nat n)) *
       ptsto_word (word.of_Z ns) (word.of_Z v))%sep m' /\
      map.get l' FibonacciServer.a = Some (word.of_Z 0) /\
      map.get l' FibonacciServer.b = Some (word.of_Z 1) /\
      map.get l' FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) /\
      instructionsH mc' = instructionsH mc + 28));
      [exec_set_solve|].
    intros. destruct_hyp.
    eapply @exec.seq with (mid := (fun t' m' l' mc' =>
      t' = t /\
      (ptsto_word (word.of_Z nl) (word.of_Z (Z.of_nat n)) *
       ptsto_word (word.of_Z ns) (word.of_Z v))%sep m' /\
      map.get l' FibonacciServer.a = Some (word.of_Z 0) /\
      map.get l' FibonacciServer.b = Some (word.of_Z 1) /\
      map.get l' FibonacciServer.i = Some (word.of_Z 0) /\
      map.get l' FibonacciServer.n = Some (word.of_Z (Z.of_nat n)) /\
      instructionsH mc' = instructionsH mc + 37));
      [exec_set_solve|].
    intros.
    destruct_hyp.
    unfold fib_bounded.
    destruct (n <? 47)%nat eqn:Hlt.
    - rewrite Nat.ltb_lt in *.
      eapply @exec.seq with (mid := (fun t' m' l' mc' =>
        t' = t /\
        (ptsto_word (word.of_Z nl) (word.of_Z (Z.of_nat n)) *
         ptsto_word (word.of_Z ns) (word.of_Z v))%sep m' /\
        instructionsH mc' <= instructionsH mc + (Z.of_nat n) * 34 + 62 /\
        map.get l' FibonacciServer.b = Some (word.of_Z (fib (n + 1))))).
        * eapply weaken_exec; [eapply fib_if_true_correct with (nl := nl) (ns := ns); eassumption|].
          cbv beta. intros. destruct_hyp.
          repeat split; try assumption.
          -- propogate_eq.
          -- blia.
        * intros. destruct_hyp.
          eapply @exec.store.
          -- reflexivity.
          -- eval_var_solve.
          -- pose proof load_word_sep as Hsepload.
             apply sep_comm in H23.
             specialize Hsepload with (1 := H23).
             cbv [store store_Z bedrock2.Memory.store_bytes].
             cbv [load load_Z] in Hsepload.
             destruct_one_match; [reflexivity|].
             match goal with
             | H0: ?x = ?v, H1: context[?y] |- _ =>
               match x with
               | bedrock2.Memory.load_bytes _ _ _ =>
                 match y with
                 | bedrock2.Memory.load_bytes _ _ _ => change y with x in H1; rewrite H0 in H1
                 end
               end
             end.
             discriminate.
          -- repeat split.
             ++ unfold_MetricLog. simpl in *. blia.
             ++ apply sep_comm in H23.
                pose proof unchecked_store_bytes_of_sep as HStore.
                specialize HStore with (1 := H23).
                match goal with
                | |- context[?x] =>
                  match x with
                  | LittleEndian.split _ _ => specialize HStore with (bs := x)
                  end
                end.
                wcancel_assumption.
    - rewrite Nat.ltb_ge in *.
      eapply @exec.seq with (mid := (fun t' m' l' mc' =>
        t' = t /\
        (ptsto_word (word.of_Z nl) (word.of_Z (Z.of_nat n)) *
         ptsto_word (word.of_Z ns) (word.of_Z v))%sep m' /\
        instructionsH mc' <= instructionsH mc + (Z.of_nat n) * 34 + 62 /\
        map.get l' FibonacciServer.b = Some (word.of_Z (-1)))).
      * eapply weaken_exec; [eapply fib_if_false_correct with (nl := nl) (ns := ns); eassumption|].
          cbv beta. intros. destruct_hyp.
          repeat split; try assumption.
          -- propogate_eq.
          -- blia.
        * intros. destruct_hyp.
          eapply @exec.store.
          -- reflexivity.
          -- eval_var_solve.
          -- pose proof load_word_sep as Hsepload.
             apply sep_comm in H23.
             specialize Hsepload with (1 := H23).
             cbv [store store_Z bedrock2.Memory.store_bytes].
             cbv [load load_Z] in Hsepload.
             destruct_one_match; [reflexivity|].
             match goal with
             | H0: ?x = ?v, H1: context[?y] |- _ =>
               match x with
               | bedrock2.Memory.load_bytes _ _ _ =>
                 match y with
                 | bedrock2.Memory.load_bytes _ _ _ => change y with x in H1; rewrite H0 in H1
                 end
               end
             end.
             discriminate.
          -- repeat split.
             ++ unfold_MetricLog. simpl in *. blia.
             ++ apply sep_comm in H23.
                pose proof unchecked_store_bytes_of_sep as HStore.
                specialize HStore with (1 := H23).
                match goal with
                | |- context[?x] =>
                  match x with
                  | LittleEndian.split _ _ => specialize HStore with (bs := x)
                  end
                end.
                wcancel_assumption.
  Qed.

  Definition run1 : Pipeline.M unit := @run1 _ _ _ _ Pipeline.RVM _ iset.
  Definition mcomp_sat := GoFlatToRiscv.mcomp_sat.

  Lemma fib_compiled: forall n (initialMachine: RiscvMachine) insts v nl ns R,
      0 <= n < 2 ^ 32 ->
      word.unsigned (getPc initialMachine) mod 4 = 0 ->
      getNextPc initialMachine = word.add (getPc initialMachine) (word.of_Z 4) ->
      insts = (ExprImp2Riscv (fib_ExprImp nl ns)) ->
      subset (footpr (program (getPc initialMachine) insts))
             (of_list initialMachine.(getXAddrs)) ->
      (program (getPc initialMachine) insts * R *
       (ptsto_word (word.of_Z ns) (word.of_Z v) *
        ptsto_word (word.of_Z nl) (word.of_Z n)))%sep initialMachine.(getMem) ->
      runsToNonDet.runsTo (mcomp_sat run1) initialMachine
        (fun (finalL: RiscvMachine) =>
           (program (getPc initialMachine) insts * R *
            (ptsto_word (word.of_Z ns) (word.of_Z (fib_bounded (Z.to_nat n))) *
             ptsto_word (word.of_Z nl) (word.of_Z n)))%sep finalL.(getMem) /\
           getPc finalL = add (getPc initialMachine) (mul (ZToReg 4) (ZToReg (Zlength insts))) /\
           getNextPc finalL = add (getPc finalL) (ZToReg 4) /\
           finalL.(getMetrics).(instructions) - initialMachine.(getMetrics).(instructions) <= n * 34 + 72).
  Proof.
    intros. subst.
    destruct H.

    rewrite <- sep_inline_eq in H4.
    destruct H4 as [initialMem Hsep]. destruct Hsep.

    eapply runsToNonDet.runsTo_weaken.
    - pose proof Pipeline.exprImp2Riscv_correct as Hp.
      specialize Hp with (sH := fib_ExprImp nl ns)
                         (mcH := bedrock2.MetricLogging.EmptyMetricLog).
      eapply Hp.
      + clear. intros. exact H.
      + simpl. blia.
      + cbv. intuition congruence.
      + reflexivity.
      + assumption.
      + assumption.
      + reflexivity.
      + assumption.
      + instantiate (2 := initialMem). instantiate (1 := R). seplog.
      + constructor.
      + eapply ExprImp.weaken_exec.
        * eapply fib_correct with (n := Z.to_nat n).
          -- rewrite Z2Nat.id; [|assumption]. instantiate (1 := v). wcancel_assumption.
          -- rewrite Z2Nat.id; assumption.
        * intros. eassumption.
    - intros.
      do 3 destruct H6.
      destruct_hyp.
      rewrite Z2Nat.id in *; try assumption.
      repeat split.
      + apply sep_inline_eq.
        eexists.
        split.
        * seplog.
        * wcancel_assumption.
      + assumption.
      + assumption.
      + repeat unfold_MetricLog. repeat simpl_MetricLog. simpl in *.
        destruct_hyp.
        eapply Z.le_trans.
        * eassumption.
        * blia.
  Qed.
  (*
  Print Assumptions fib_compiled.
  *)
*)

End FibCompiled.
