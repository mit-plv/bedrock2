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
    | S f' => match s with
      | SLoad x a =>
          a' <- get st a;
          v <- read_mem a' m;
          Return (put st x v, m)
      | SStore a v =>
          a' <- get st a;
          v' <- get st v;
          m' <- write_mem a' v' m;
          Return (st, m')
      | SLit x v =>
          Return (put st x v, m)
      | SOp x op y z =>
          v1 <- get st y;
          v2 <- get st z;
          Return (put st x (eval_binop op v1 v2), m)
      | SSet x y =>
          v <- get st y;
          Return (put st x v, m)
      | SIf cond bThen bElse =>
          vcond <- get st cond;
          eval_stmt f' st m (if dec (vcond = $0) then bElse else bThen)
      | SLoop body1 cond body2 =>
          p <- eval_stmt f' st m body1;
          let '(st', m') := p in
          vcond <- get st' cond;
          if dec (vcond = $0) then Return (st', m') else
            q <- eval_stmt f' st' m' body2;
            let '(st'', m'') := q in
            eval_stmt f' st'' m'' (SLoop body1 cond body2)
      | SSeq s1 s2 =>
          p <- eval_stmt f' st m s1;
          let '(st', m') := p in
          eval_stmt f' st' m' s2
      | SSkip => Return (st, m)
      end
    end.

  Lemma invert_eval_SLit: forall fuel initial x v final,
    eval_stmt fuel initial (SLit x v) = Success final ->
    final = put initial x v.
  Proof.
    intros. destruct fuel; [discriminate|]. inversion H. auto.
  Qed.

  Lemma invert_eval_SOp: forall fuel x y z op initial final,
    eval_stmt fuel initial (SOp x op y z) = Success final ->
    exists v1 v2,
      get initial y = Some v1 /\
      get initial z = Some v2 /\
      final = put initial x (eval_binop op v1 v2).
  Proof.
    introv Ev. destruct fuel; simpl in Ev; [discriminate|].
    unfold option2res in *.
    repeat (destruct_one_match_hyp; try discriminate); inversionss; eauto 10.
  Qed.

  Lemma invert_eval_SSet: forall fuel x y initial final,
    eval_stmt fuel initial (SSet x y) = Success final ->
    exists v,
      get initial y = Some v /\ final = put initial x v.
  Proof.
    intros. destruct fuel; [discriminate|].
    simpl in *.
    unfold option2res in *.
    repeat (destruct_one_match_hyp; try discriminate); inversionss; eauto 10.
  Qed.

  Lemma invert_eval_SIf: forall fuel cond bThen bElse initial final,
    eval_stmt (Coq.Init.Datatypes.S fuel) initial (SIf cond bThen bElse) = Success final ->
    exists vcond,
      get initial cond = Some vcond /\
      (vcond <> $0 /\ eval_stmt fuel initial bThen = Success final \/
       vcond =  $0 /\ eval_stmt fuel initial bElse = Success final).
  Proof.
    introv Ev. simpl in Ev. unfold option2res in *.
    repeat (destruct_one_match_hyp; try discriminate); inversionss; eauto 10.
  Qed.

  Lemma invert_eval_SLoop: forall fuel st1 body1 cond body2 st4,
    eval_stmt (Coq.Init.Datatypes.S fuel) st1 (SLoop body1 cond body2) = Success st4 ->
    eval_stmt fuel st1 body1 = Success st4 /\ get st4 cond = Some $0 \/
    exists st2 st3 cv, eval_stmt fuel st1 body1 = Success st2 /\
                       get st2 cond = Some cv /\ cv <> $0 /\
                       eval_stmt fuel st2 body2 = Success st3 /\
                       eval_stmt fuel st3 (SLoop body1 cond body2) = Success st4.
  Proof.
    introv Ev. simpl in Ev. unfold option2res in *.
    repeat (destruct_one_match_hyp; try discriminate); inversionss; eauto 10.
  Qed.

  Lemma invert_eval_SSeq: forall fuel initial s1 s2 final,
    eval_stmt (Coq.Init.Datatypes.S fuel) initial (SSeq s1 s2) = Success final ->
    exists mid, eval_stmt fuel initial s1 = Success mid /\
                eval_stmt fuel mid s2 = Success final.
  Proof.
    introv Ev. simpl in Ev. destruct_one_match_hyp; try discriminate. eauto.
  Qed.

  Lemma invert_eval_SSkip: forall fuel initial final,
    eval_stmt fuel initial SSkip = Success final ->
    initial = final.
  Proof. intros. destruct fuel; [discriminate|]. inversion H. auto. Qed.

  Lemma increase_fuel_still_Success: forall fuel1 fuel2 initial s final,
    fuel1 <= fuel2 ->
    eval_stmt fuel1 initial s = Success final ->
    eval_stmt fuel2 initial s = Success final.
  Proof.
    induction fuel1; introv L Ev.
    - inversions Ev.
    - destruct fuel2; [omega|]. destruct s.
      + exact Ev.
      + exact Ev.
      + exact Ev.
      + simpl in *. destruct_one_match; try discriminate.
        erewrite IHfuel1; [reflexivity | omega | exact Ev].
      + apply invert_eval_SLoop in Ev.
        destruct Ev as [Ev | Ev]. 
        * destruct Ev as [Ev C]. 
          simpl. erewrite IHfuel1; [|omega|eassumption].
          rewrite C. simpl. destruct_one_match; [reflexivity | contradiction].
        * destruct Ev as [mid2 [mid3 [cv [Ev1 [C1 [C2 [Ev2 Ev3]]]]]]].
          simpl.
          erewrite IHfuel1; [|omega|eassumption].
          erewrite IHfuel1; [|omega|eassumption].
          erewrite IHfuel1; [|omega|eassumption].
          rewrite C1. simpl.
          destruct_one_match; [ contradiction | reflexivity ].
     + apply invert_eval_SSeq in Ev.
       destruct Ev as [mid [Ev1 Ev2]].
       simpl.
       erewrite IHfuel1; [|omega|eassumption].
       erewrite IHfuel1; [|omega|eassumption].
       reflexivity.
     + simpl. inversionss. reflexivity.
  Qed.

  (* returns the set of modified vars *)
  Fixpoint modVars(s: stmt): vars :=
    match s with
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

(*
Ltac TAC_D :=
  match goal with
  (* we use an explicit type T because otherwise the inferred type might differ *)
  | |- context[dec (@eq ?T ?t1 ?t2)] => idtac "TAC_D"; destruct (dec (@eq T t1 t2)); [subst|]
  end.


Ltac state_calc00 :=
  idtac "state_calc";
  unf; intros; autorewrite with rewrite_set_op_specs in *; rewrite_get_put;
  repeat match goal with
  | x: ?T, H: forall (y: ?T), _ |- _ => unique pose proof (H x)
  end. 
  
Ltac go1 :=
  repeat (intuition (auto || congruence) || TAC_D).


Definition get_DecidableEq(T: Type){e: DecidableEq T}: DecidableEq T := e.

Ltac do_rewr :=       rewrite get_put in *. 

*)

  Lemma modVarsSound: forall fuel s initial final,
    eval_stmt fuel initial s = Success final ->
    only_differ initial (modVars s) final.
  Proof.
    induction fuel; introv Ev.
    - discriminate.
    - destruct s.
      + simpl in *. inversionss. state_calc.

(*
If we forget to put a DecidableEq for var (currently var=Z) into scope, weird things happen,
because erewrite leaves the implicit DecidableEq as an existential var

      unf; intros; autorewrite with rewrite_set_op_specs in *.

rewrite_get_put.
      do_rewr.
      
      
      let r := eval unfold get_DecidableEq in (get_DecidableEq var) in idtac r.
      
      let e := constr:(fun (x: var) => dec (x = x)) in
      match e with
      | (fun x => @dec _ (?d x x)) => idtac d
      end.
      
      Check (dec (x = x)).
      assert (DecidableEq var). change var with Z. eauto.
      { state_calc00. go1. (* solves the goal *) }

      { state_calc00; go1.  (* does not solve the goal *)


      { state_calc00; go1.  (* does not solve the goal *)




      
 (* unf; intros; autorewrite with rewrite_set_op_specs in *; rewrite_get_put. 
  repeat match goal with
  | x: ?T, H: forall (y: ?T), _ |- _ => unique pose proof (H x)
  end.*)
  go1.
  
  repeat (intuition (auto || congruence) || destruct_one_dec_eq).
(*copy/pasting body of state_calc has different effect than state_calc?? *)
      
       state_calc.
*)
      + simpl in Ev. unfold option2res in *.
        repeat (destruct_one_match_hyp_of_type (option (word w)); try discriminate).
        inversionss. simpl. state_calc.
      + simpl in Ev. unfold option2res in *.
        repeat (destruct_one_match_hyp_of_type (option (word w)); try discriminate).
        inversionss. simpl. state_calc.
      + Opaque union. simpl in *. unfold option2res in *.
        repeat (destruct_one_match_hyp_of_type (option (word w)); try discriminate).
        destruct fuel; [ inversion Ev | ].
        specializes IHfuel; [ eassumption |].
        destruct_one_match_hyp; state_calc.
      + apply invert_eval_SLoop in Ev. destruct Ev as [Ev | Ev]. 
        * destruct Ev as [Ev C]. 
          simpl. specializes IHfuel; [eassumption|]. state_calc.
        * destruct Ev as [mid2 [mid3 [cv [Ev1 [C1 [C2 [Ev2 Ev3]]]]]]].
          simpl.
          pose proof (IHfuel _ _ _ Ev1) as IH1.
          pose proof (IHfuel _ _ _ Ev2) as IH2.
          pose proof (IHfuel _ _ _ Ev3) as IH3.
          clear - IH1 IH2 IH3. simpl in IH3.
          state_calc.
      + apply invert_eval_SSeq in Ev.
        destruct Ev as [mid [Ev1 Ev2]]. simpl.
        pose proof (IHfuel _ _ _ Ev1) as IH1.
        pose proof (IHfuel _ _ _ Ev2) as IH2.
        clear - IH1 IH2. state_calc.
      + simpl. inversionss. state_calc.
  Qed.

  Fixpoint accessedVars(s: stmt): vars :=
    match s with
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

Definition eval_stmt_test := @eval_stmt 8 ZName _ _.

Example finalFibState(n: nat): Res (var -> option (word 8)) := (eval_stmt_test 100 empty (fib $n)).
Example finalFibVal(n: nat): option (word 8) := match finalFibState n with
| Success s => get s _b
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
