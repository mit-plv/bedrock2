Require Import lib.LibTacticsMin.
Require Import compiler.Common.
Require Import compiler.Tactics.
Require Import compiler.Op.
Require Import compiler.StateCalculus.
Require Import compiler.Memory.
Require Import riscv.NameWithEq.

Section FlatImp.

  Context {w: nat}. (* bit width *)

  Context {Name: NameWithEq}.
  Notation var := (@name Name).
  Existing Instance eq_name_dec.

  Context {state: Type}.
  Context {stateMap: Map state var (word w)}.
  Context {vars: Type}.
  Context {varset: set vars var}.

  Ltac state_calc := state_calc_generic (@name Name) (word w).

  Inductive stmt: Set :=
    | SLoad(x: var)(a: var): stmt
    | SStore(a: var)(v: var): stmt
    | SLit(x: var)(v: word w): stmt
    | SOp(x: var)(op: binop)(y z: var): stmt
    | SSet(x y: var): stmt
    | SIf(cond: var)(bThen bElse: stmt): stmt
    | SLoop(body1: stmt)(cond: var)(body2: stmt): stmt
    | SSeq(s1 s2: stmt): stmt
    | SSkip: stmt.

  Fixpoint stmt_size(s: stmt): nat :=
    match s with
    | SLoad x a => 1
    | SStore a v => 1
    | SLit x v => 1
    | SOp x op y z => 1
    | SSet x y => 1
    | SIf cond bThen bElse => 1 + (stmt_size bThen) + (stmt_size bElse)
    | SLoop body1 cond body2 => 1 + (stmt_size body1) + (stmt_size body2)
    | SSeq s1 s2 => 1 + (stmt_size s1) + (stmt_size s2)
    | SSkip => 1
    end.

  (* If we want a bigstep evaluation relation, we either need to put
     fuel into the SLoop constructor, or give it as argument to eval *)
  Fixpoint eval_stmt(f: nat)(st: state)(m: mem w)(s: stmt): option (state * mem w) :=
    match f with
    | 0 => None (* out of fuel *)
    | S f => match s with
      | SLoad x a =>
          a <- get st a;
          v <- read_mem a m;
          Return (put st x v, m)
      | SStore a v =>
          a <- get st a;
          v <- get st v;
          m <- write_mem a v m;
          Return (st, m)
      | SLit x v =>
          Return (put st x v, m)
      | SOp x op y z =>
          y <- get st y;
          z <- get st z;
          Return (put st x (eval_binop op y z), m)
      | SSet x y =>
          v <- get st y;
          Return (put st x v, m)
      | SIf cond bThen bElse =>
          vcond <- get st cond;
          eval_stmt f st m (if dec (vcond = $0) then bElse else bThen)
      | SLoop body1 cond body2 =>
          p <- eval_stmt f st m body1;
          let '(st, m) := p in
          vcond <- get st cond;
          if dec (vcond = $0) then Return (st, m) else
            q <- eval_stmt f st m body2;
            let '(st, m) := q in
            eval_stmt f st m (SLoop body1 cond body2)
      | SSeq s1 s2 =>
          p <- eval_stmt f st m s1;
          let '(st, m) := p in
          eval_stmt f st m s2
      | SSkip => Return (st, m)
      end
    end.

  Local Ltac inversion_lemma :=
    intros;
    simpl in *;
    repeat (destruct_one_match_hyp; try discriminate);
    inversionss;
    eauto 15.

  Lemma invert_eval_SLoad: forall fuel initialSt initialM x y final,
    eval_stmt (S fuel) initialSt initialM (SLoad x y) = Some final ->
    exists a v, get initialSt y = Some a /\
                read_mem a initialM = Some v /\
                final = (put initialSt x v, initialM).
  Proof. inversion_lemma. Qed.

  Lemma invert_eval_SStore: forall fuel initialSt initialM x y final,
    eval_stmt (S fuel) initialSt initialM (SStore x y) = Some final ->
    exists a v finalM, get initialSt x = Some a /\
                       get initialSt y = Some v /\
                       write_mem a v initialM = Some finalM /\
                       final = (initialSt, finalM).
  Proof. inversion_lemma. Qed.

  Lemma invert_eval_SLit: forall fuel initialSt initialM x v final,
    eval_stmt (S fuel) initialSt initialM (SLit x v) = Some final ->
    final = (put initialSt x v, initialM).
  Proof. inversion_lemma. Qed.

  Lemma invert_eval_SOp: forall fuel x y z op initialSt initialM final,
    eval_stmt (S fuel) initialSt initialM (SOp x op y z) = Some final ->
    exists v1 v2,
      get initialSt y = Some v1 /\
      get initialSt z = Some v2 /\
      final = (put initialSt x (eval_binop op v1 v2), initialM).
  Proof. inversion_lemma. Qed.

  Lemma invert_eval_SSet: forall fuel x y initialSt initialM final,
    eval_stmt (S fuel) initialSt initialM (SSet x y) = Some final ->
    exists v,
      get initialSt y = Some v /\ final = (put initialSt x v, initialM).
  Proof. inversion_lemma. Qed.

  Lemma invert_eval_SIf: forall fuel cond bThen bElse initialSt initialM final,
    eval_stmt (S fuel) initialSt initialM (SIf cond bThen bElse) = Some final ->
    exists vcond,
      get initialSt cond = Some vcond /\
      (vcond <> $0 /\ eval_stmt fuel initialSt initialM bThen = Some final \/
       vcond =  $0 /\ eval_stmt fuel initialSt initialM bElse = Some final).
  Proof. inversion_lemma. Qed.

  Lemma invert_eval_SLoop: forall fuel st1 m1 body1 cond body2 p4,
    eval_stmt (S fuel) st1 m1 (SLoop body1 cond body2) = Some p4 ->
    eval_stmt fuel st1 m1 body1 = Some p4 /\ get (fst p4) cond = Some $0 \/
    exists st2 m2 st3 m3 cv, eval_stmt fuel st1 m1 body1 = Some (st2, m2) /\
                             get st2 cond = Some cv /\ cv <> $0 /\
                             eval_stmt fuel st2 m2 body2 = Some (st3, m3) /\
                             eval_stmt fuel st3 m3 (SLoop body1 cond body2) = Some p4.
  Proof. inversion_lemma. Qed.

  Lemma invert_eval_SSeq: forall fuel initialSt initialM s1 s2 final,
    eval_stmt (S fuel) initialSt initialM (SSeq s1 s2) = Some final ->
    exists midSt midM, eval_stmt fuel initialSt initialM s1 = Some (midSt, midM) /\
                       eval_stmt fuel midSt midM s2 = Some final.
  Proof. inversion_lemma. Qed.

  Lemma invert_eval_SSkip: forall fuel initialSt initialM final,
    eval_stmt (S fuel) initialSt initialM SSkip = Some final ->
    final = (initialSt, initialM).
  Proof. inversion_lemma. Qed.

(*
Ltac invert_eval_stmt :=
  match goal with
  | E: eval_stmt (Datatypes.S ?fuel) _ ?s = Success _ |- _ =>
    destruct s;
    [ apply invert_eval_SLit in E
    | apply invert_eval_SOp in E; destruct E as [? [? [? [? ?]]]]
    | apply invert_eval_SSet in E; destruct E as [? [? ?]]
    | apply invert_eval_SIf in E; destruct E as [? [? [[? ?]|[? ?]]]]
    | apply invert_eval_SLoop in E; destruct E as [[? ?] | [? [? [? [? [? [? [? ?]]]]]]]]
    | apply invert_eval_SSeq in E; destruct E as [? [? ?]]
    | apply invert_eval_SSkip in E ]
  end.
*)

  Ltac invert_eval_stmt :=
    lazymatch goal with
    | E: eval_stmt (S ?fuel) _ _ ?s = Some _ |- _ =>
      destruct s;
      [ apply invert_eval_SLoad in E
      | apply invert_eval_SStore in E
      | apply invert_eval_SLit in E
      | apply invert_eval_SOp in E
      | apply invert_eval_SSet in E
      | apply invert_eval_SIf in E
      | apply invert_eval_SLoop in E
      | apply invert_eval_SSeq in E
      | apply invert_eval_SSkip in E ];
      deep_destruct E;
      [ let x := fresh "Case_SLoad" in pose proof tt as x; move x at top
      | let x := fresh "Case_SStore" in pose proof tt as x; move x at top
      | let x := fresh "Case_SLit" in pose proof tt as x; move x at top
      | let x := fresh "Case_SOp" in pose proof tt as x; move x at top
      | let x := fresh "Case_SSet" in pose proof tt as x; move x at top
      | let x := fresh "Case_SIf_Then" in pose proof tt as x; move x at top
      | let x := fresh "Case_SIf_Else" in pose proof tt as x; move x at top
      | let x := fresh "Case_SLoop_Done" in pose proof tt as x; move x at top
      | let x := fresh "Case_SLoop_NotDone" in pose proof tt as x; move x at top
      | let x := fresh "Case_SSeq" in pose proof tt as x; move x at top
      | let x := fresh "Case_SSkip" in pose proof tt as x; move x at top ]
    end.

  Lemma increase_fuel_still_Success: forall fuel1 fuel2 initialSt initialM s final,
    fuel1 <= fuel2 ->
    eval_stmt fuel1 initialSt initialM s = Some final ->
    eval_stmt fuel2 initialSt initialM s = Some final.
  Proof.
    induction fuel1; introv L Ev.
    - inversions Ev.
    - destruct fuel2; [omega|].
      assert (fuel1 <= fuel2) as F by omega. specialize IHfuel1 with (1 := F).
      destruct final as [finalSt finalM].
      invert_eval_stmt; simpl in *;
      repeat match goal with
      | IH: _, H: _ |- _ =>
          let IH' := fresh IH in pose proof IH as IH';
          specialize IH' with (1 := H);
          ensure_new IH'
      end;
      repeat match goal with
      | H: _ = Some _ |- _ => rewrite H
      end;
      try congruence;
      try simpl_if;
      eauto.
  Qed.

  (* returns the set of modified vars *)
  Fixpoint modVars(s: stmt): vars :=
    match s with
    | SLoad x y => singleton_set x
    | SStore x y => empty_set
    | SLit x v => singleton_set x
    | SOp x op y z => singleton_set x
    | SSet x y => singleton_set x
    | SIf cond bThen bElse =>
        union (modVars bThen) (modVars bElse)
    | SLoop body1 cond body2 =>
        union (modVars body1) (modVars body2)
    | SSeq s1 s2 =>
        union (modVars s1) (modVars s2)
    | SSkip => empty_set
    end.

  Lemma modVarsSound: forall fuel s initialSt initialM finalSt finalM,
    eval_stmt fuel initialSt initialM s = Some (finalSt, finalM) ->
    only_differ initialSt (modVars s) finalSt.
  Proof.
    induction fuel; introv Ev.
    - discriminate.
    - invert_eval_stmt; simpl in *; inversionss;
      repeat match goal with
      | IH: _, H: _ |- _ =>
          let IH' := fresh IH in pose proof IH as IH';
          specialize IH' with (1 := H);
          simpl in IH';
          ensure_new IH'
      end;
      state_calc.
  Qed.

  Fixpoint accessedVars(s: stmt): vars :=
    match s with
    | SLoad x y => union (singleton_set x) (singleton_set y)
    | SStore x y => union (singleton_set x) (singleton_set y)
    | SLit x v => singleton_set x
    | SOp x op y z => union (singleton_set x) (union (singleton_set y) (singleton_set z))
    | SSet x y => union (singleton_set x) (singleton_set y)
    | SIf cond bThen bElse =>
        union (singleton_set cond) (union (accessedVars bThen) (accessedVars bElse))
    | SLoop body1 cond body2 =>
        union (singleton_set cond) (union (accessedVars body1) (accessedVars body2))
    | SSeq s1 s2 =>
        union (accessedVars s1) (accessedVars s2)
    | SSkip => empty_set
    end.

  Lemma modVars_subset_accessedVars: forall s,
    subset (modVars s) (accessedVars s).
  Proof.
    intro s. induction s; simpl; unfold singleton_set; state_calc.
  Qed.

(* not needed at the moment
  Lemma eval_stmt_swap_state: forall fuel initial1 initial2 final1 s,
    eval_stmt fuel initial1 s = Success final1 ->
    agree_on initial1 (accessedVars s) initial2 ->
    exists final2,
      eval_stmt fuel initial2 s = Success final2 /\
      agree_on final1 (accessedVars s) final2.
  Proof.
    intro fuel. induction fuel; [intros; discriminate|].
    introv E A.
    invert_eval_stmt.
    - subst. eexists. apply (conj eq_refl). state_calc.
    - Opaque singleton_set.
      simpl in *. unfold option2res in *.
      assert (get initial2 y = Some x0) as Y2. {
        unfold agree_on in *.
        specialize (A y).
        (* TODO make sure state_calc does these rewritings and succeeds *)
        rewrite? union_spec in A.
        rewrite? singleton_set_spec in A.
        intuition congruence.
      }
      rewrite Y2. clear Y2.
      assert (get initial2 z = Some x1) as Z2. {
        unfold agree_on in *.
        specialize (A z).
        (* TODO make sure state_calc does these rewritings and succeeds *)
        rewrite? union_spec in A.
        rewrite? singleton_set_spec in A.
        intuition congruence.
      }
      rewrite Z2. clear Z2.
      subst.
      eexists. apply (conj eq_refl). state_calc.
    - simpl in *. unfold option2res in *.
      assert (get initial2 y = Some x0) as Y2. {
        unfold agree_on in *.
        specialize (A y).
        (* TODO make sure state_calc does these rewritings and succeeds *)
        rewrite? union_spec in A.
        rewrite? singleton_set_spec in A.
        intuition congruence.
      }
      rewrite Y2.
      subst.
      eexists. apply (conj eq_refl). state_calc.
    - simpl in *. unfold option2res in *.
      assert (get initial2 cond = Some x) as Y2. {
        unfold agree_on in *.
        specialize (A cond).
        (* TODO make sure state_calc does these rewritings and succeeds *)
        rewrite? union_spec in A.
        rewrite? singleton_set_spec in A.
        intuition congruence.
      }
      rewrite Y2.
      subst.
      destruct_one_match; [contradiction|].
      specialize (IHfuel initial1 initial2).
      specializes IHfuel.
      + eassumption.
      + unfold agree_on in *. intros.
        specialize (A x0).
        (* TODO make sure state_calc does these rewritings and succeeds *)
        rewrite? union_spec in A.
        rewrite? singleton_set_spec in A.
        intuition congruence.
      + destruct IHfuel as [final2 [IH1 IH2]].
        eexists. split; [eassumption|].
        pose proof (modVarsSound _ _ _ _ H1) as M1.
        pose proof (modVarsSound _ _ _ _ IH1) as M2.
        pose proof (modVars_subset_accessedVars s1) as Ss.
        (* In A, replace initial1 by final1, which reduces the agreement set by (modVars s1).
           Then replace in A initial2 by final2, which leaves the already reduced agreement set
           unchanged.
           Then take the union of A and IH2.
           Since (modVars s1) is a subset of (accessedVars s1), the goal follows. *)
        Time state_calc. (* 14.835 secs *)
    - simpl in *. unfold option2res in *.
      assert (get initial2 cond = Some x) as Y2. {
        unfold agree_on in *.
        specialize (A cond).
        (* TODO make sure state_calc does these rewritings and succeeds *)
        rewrite? union_spec in A.
        rewrite? singleton_set_spec in A.
        intuition congruence.
      }
      rewrite Y2.
      subst.
      destruct_one_match; [|contradiction].
      specialize (IHfuel initial1 initial2).
      specializes IHfuel.
      + eassumption.
      + unfold agree_on in *. intros.
        specialize (A x).
        (* TODO make sure state_calc does these rewritings and succeeds *)
        rewrite? union_spec in A.
        rewrite? singleton_set_spec in A.
        intuition congruence.
      + destruct IHfuel as [final2 [IH1 IH2]].
        eexists. split; [eassumption|].
        pose proof (modVarsSound _ _ _ _ H1) as M1.
        pose proof (modVarsSound _ _ _ _ IH1) as M2.
        pose proof (modVars_subset_accessedVars s2) as Ss.
        (* In A, replace initial1 by final1, which reduces the agreement set by (modVars s1).
           Then replace in A initial2 by final2, which leaves the already reduced agreement set
           unchanged.
           Then take the union of A and IH2.
           Since (modVars s1) is a subset of (accessedVars s1), the goal follows. *)
        Time state_calc. (* 14.835 secs *)
    - simpl in *. unfold option2res in *. rename final1 into middle1.
      specialize (IHfuel initial1 initial2 middle1).
      specializes IHfuel.
      + eassumption.
      + unfold agree_on in *. intros.
        specialize (A x).
        (* TODO make sure state_calc does these rewritings and succeeds *)
        rewrite? union_spec in A.
        rewrite? singleton_set_spec in A.
        intuition congruence.
      + destruct IHfuel as [middle2 [IH1 IH2]].
        rewrite IH1.
        assert (get middle2 cond = Some $ (0)) as G2. {
        pose proof (modVarsSound _ _ _ _ H) as M1.
        pose proof (modVarsSound _ _ _ _ IH1) as M2.
        pose proof (modVars_subset_accessedVars s1) as Ss.
        assert (agree_on middle1
      (union (singleton_set cond) (union (accessedVars s1) (accessedVars s2)))
      middle2) by 
        state_calc. rewrite <- H0. symmetry. unfold agree_on in H1. apply H1.
        state_calc. (* TODO make this work with just one invocation of state_calc. *)
        }
        rewrite G2. destruct_one_match; [|contradiction].
        eexists. apply (conj eq_refl).
        pose proof (modVarsSound _ _ _ _ H) as M1.
        pose proof (modVarsSound _ _ _ _ IH1) as M2.
        pose proof (modVars_subset_accessedVars s1) as Ss.
        state_calc.
    - simpl in *. unfold option2res in *. rename x into middle1.
      pose proof IHfuel as IHfuel2.
      specialize (IHfuel initial1 initial2 middle1).
      specializes IHfuel.
      + eassumption.
      + unfold agree_on in *. intros.
        specialize (A x).
        (* TODO make sure state_calc does these rewritings and succeeds *)
        rewrite? union_spec in A.
        rewrite? singleton_set_spec in A.
        intuition congruence.
      + destruct IHfuel as [middle2 [IH1 IH2]].
        rewrite IH1.
        assert (get middle2 cond = Some x1) as G2. {
        pose proof (modVarsSound _ _ _ _ H) as M1.
        pose proof (modVarsSound _ _ _ _ IH1) as M2.
        pose proof (modVars_subset_accessedVars s1) as Ss.
        clear IHfuel2.
        assert (agree_on middle1
      (union (singleton_set cond) (union (accessedVars s1) (accessedVars s2)))
      middle2) by 
        state_calc. rewrite <- H0. symmetry. unfold agree_on in H4. apply H4.
        state_calc. (* TODO make this work with just one invocation of state_calc. *)
        }
        rewrite G2. destruct_one_match; [contradiction|].
        rename IHfuel2 into IHfuel.
        pose proof IHfuel as IHfuel3.
        specialize (IHfuel middle1 middle2).
        specializes IHfuel.
        * eassumption.
        * pose proof (modVarsSound _ _ _ _ H) as M1.
          pose proof (modVarsSound _ _ _ _ IH1) as M2.
          pose proof (modVars_subset_accessedVars s1) as Ss.
          clear IHfuel3.
          assert (agree_on middle1
          (union (singleton_set cond) (union (accessedVars s1) (accessedVars s2)))
          middle2) by 
            state_calc.
          unfold agree_on in *.
          intros. specialize (H4 x).
          rewrite? union_spec in H4.
          rewrite? singleton_set_spec in H4.
          intuition congruence. (* TODO make this work with just one invocation of state_calc. *)
        * rename x0 into prefinal1.
          destruct IHfuel as [prefinal2 [IH3 IH4]].
          rewrite IH3.
          rename IHfuel3 into IHfuel.
          specialize (IHfuel prefinal1 prefinal2).
          specializes IHfuel.
          ** eassumption.
          ** pose proof (modVarsSound _ _ _ _ H2) as M1.
             pose proof (modVarsSound _ _ _ _ IH3) as M2.
             pose proof (modVars_subset_accessedVars s2) as Ss.
             assert (agree_on prefinal1
             (union (singleton_set cond) (union (accessedVars s1) (accessedVars s2)))
             prefinal2) by 
               state_calc.
             unfold agree_on in *.
             intros. specialize (H4 x).
             rewrite? union_spec in H4.
             rewrite? singleton_set_spec in H4.
             intuition congruence. (* TODO make this work with just one invocation of state_calc. *)
          ** exact IHfuel.
    - simpl in *. rename x into middle1.
      pose proof IHfuel as IHfuel2.
      specialize (IHfuel initial1 initial2 middle1).
      specializes IHfuel.
      + eassumption.
      + unfold agree_on in *. intros.
        specialize (A x).
        (* TODO make sure state_calc does these rewritings and succeeds *)
        rewrite? union_spec in A.
        rewrite? singleton_set_spec in A.
        intuition congruence.
      + destruct IHfuel as [middle2 [IH1 IH2]].
        rewrite IH1.
        rename IHfuel2 into IHfuel.
        specialize (IHfuel middle1 middle2).
        specializes IHfuel.
        * eassumption.
        * pose proof (modVarsSound _ _ _ _ H) as M1.
          pose proof (modVarsSound _ _ _ _ IH1) as M2.
          pose proof (modVars_subset_accessedVars s1) as Ss.
          assert (agree_on middle1
          (union (accessedVars s1) (accessedVars s2))
          middle2) by 
            state_calc.
          unfold agree_on in *.
          intros. specialize (H1 x).
          rewrite? union_spec in H1.
          rewrite? singleton_set_spec in H1.
          intuition congruence. (* TODO make this work with just one invocation of state_calc. *)
        * destruct IHfuel as [final2 [IH3 IH4]].
          eexists. apply (conj IH3).
          pose proof (modVarsSound _ _ _ _ H0) as M1.
          pose proof (modVarsSound _ _ _ _ IH3) as M2.
          pose proof (modVars_subset_accessedVars s2) as Ss.
          state_calc.
    - subst. eexists. simpl. apply (conj eq_refl). assumption.
  Time Qed. (* 1.433 secs *)
*)

End FlatImp.

Module TestFlatImp.

Instance ZName: NameWithEq := {| name := Z |}.

Definition var: Set := (@name ZName). (* only inside this test module *)

Definition _n := 0%Z.
Definition _a := 1%Z.
Definition _b := 2%Z.
Definition _s := 3%Z.
Definition _one := 4%Z.
(*
one = 1
n = input()
a = 0
b = 1
loop:
  stay in loop only if n nonzero
  s = a+b
  a = b
  b = s
  n = n - one
*)
Example fib(n: word 8) :=
  SSeq (SLit _one $1) (
  SSeq (SLit _n n) (
  SSeq (SLit _a $0) (
  SSeq (SLit _b $1) (
  SLoop SSkip
        _n
        (SSeq (SOp _s OPlus _a _b) (
         SSeq (SSet _a _b) (
         SSeq (SSet _b _s) (
              (SOp _n OMinus _n _one)))))
  )))).

Definition eval_stmt_test fuel initialSt := @eval_stmt 8 ZName _ _ fuel initialSt (no_mem 8).

Example finalFibState(n: nat) := (eval_stmt_test 100 empty (fib $n)).
Example finalFibVal(n: nat): option (word 8) := match finalFibState n with
| Some (s, _) => get s _b
| _ => None
end.

Goal finalFibVal 0 = Some $1. reflexivity. Qed.
Goal finalFibVal 1 = Some $1. reflexivity. Qed.
Goal finalFibVal 2 = Some $2. reflexivity. Qed.
Goal finalFibVal 3 = Some $3. reflexivity. Qed.
Goal finalFibVal 4 = Some $5. reflexivity. Qed.
Goal finalFibVal 5 = Some $8. reflexivity. Qed.
Goal finalFibVal 6 = Some $13. reflexivity. Qed.

End TestFlatImp.
