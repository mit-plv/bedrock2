Require Import compiler.FlatImp.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.fwd.
Require Import String.
Require Import coqutil.Map.MapEauto.
Open Scope Z_scope.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Datatypes.ListSet.
Local Notation var := String.string (only parsing).
Require Import compiler.util.Common.
Require Import bedrock2.MetricLogging.
Require Import coqutil.Tactics.fwd.
(*  below only for of_list_list_diff *)
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.

Section WithArguments1.
  Context {width: Z}.
  Context {BW: Bitwidth.Bitwidth width }.
  Context {word : word width } { word_ok : word.ok word }.
  Context {env: map.map string (list var * list var * stmt var) } { env_ok : map.ok env }.
  Context {mem: map.map word (Init.Byte.byte : Type) } {mem_ok : map.ok mem } .
  Context {locals: map.map string word } {locals_ok : map.ok locals }.
  Context {ext_spec : LeakageSemantics.ExtSpec } {ext_spec_ok: LeakageSemantics.ext_spec.ok ext_spec } .
  Context {pick_sp : LeakageSemantics.PickSp}.
  Ltac subset_union_solve :=
    match goal  with
    | |- subset (union _ _) _  => eapply subset_union_l; subset_union_solve
    | |- subset _ (union _ _)  =>
        try solve [ eapply subset_union_rl; subset_union_solve ]; try solve [ eapply subset_union_rr; subset_union_solve ]; idtac
    | |- subset ?x ?x => solve [ eapply subset_refl ]
    | |- _ => fail
    end.

  Ltac listset_to_set :=
    match goal with
    | H: context[of_list (ListSet.list_union _ _ _)] |- _ => rewrite ListSet.of_list_list_union in H
    | H: context[of_list (ListSet.list_diff _ _ _)] |- _ =>
        rewrite of_list_list_diff in H;
        try match goal with
          | |- EqDecider String.eqb => eapply String.eqb_spec
          end
    | H: context[of_list (List.removeb _ _ _)] |- _ =>
        rewrite ListSet.of_list_removeb in H
    end.

  Local Notation bcond := (@FlatImp.bcond var).

  Definition accessed_vars_bcond(c: bcond): list var :=
    match c with
    | CondBinary _ x y => list_union String.eqb [x] [y]
    | CondNez x => [x]
    end.

  Fixpoint accessed_vars_stmt(s: stmt var) : list var :=
    match s with
    | SInteract _ _ argvars => argvars
    | SCall _ _ args => args
    | SLoad _ _ a _ => [a]
    | SStore _ a v _ => list_union String.eqb [a] [v]
    | SInlinetable _ _ _ i => [i]
    | SStackalloc x _ body => list_union String.eqb [x] (accessed_vars_stmt body)
    | SLit _ _ => []
    | SOp _ _ y oz =>
        match oz with
        | Const _ => [y]
        | Var z => list_union String.eqb [y] [z]
        end
    | SSet _ y => [y]
    | SIf cond bThen bElse => list_union String.eqb
                                (accessed_vars_bcond cond)
                                (list_union String.eqb
                                   (accessed_vars_stmt bThen)
                                   (accessed_vars_stmt bElse))
    | SLoop body1 cond body2 =>
        list_union String.eqb
          (accessed_vars_bcond cond)
          (list_union String.eqb
             (accessed_vars_stmt body1)
             (accessed_vars_stmt body2))
    | SSeq s1 s2 =>
        list_union String.eqb
          (accessed_vars_stmt s1)
          (accessed_vars_stmt s2)
    | SSkip => []
    end.

  Definition is_list_subset (x: list var) (x': list var)
    := forallb (fun v => (existsb (eqb v) x')) x.

  Lemma is_list_subset_refl :
    forall l, is_list_subset l l = true.
  Proof.
    induction l.
    - simpl. reflexivity.
    - unfold is_list_subset.
      simpl.
      rewrite eqb_refl.
      simpl.
      eapply forallb_forall.
      intros.
      replace (existsb (eqb x) l) with true%bool.
      2: { symmetry. rewrite existsb_exists.
           exists x; auto.
           propositional idtac.
           eapply eqb_refl.
      }
      eapply Bool.orb_true_r.
  Qed.

  Lemma is_list_subset_of_list:
    forall l1 l2,
      PropSet.subset (PropSet.of_list l1) (PropSet.of_list l2) <->
      is_list_subset l1 l2 = true.
  Proof.
    unfold iff.
    split.
    - induction l1.
      + simpl. intros. reflexivity.
      + intros. eapply subset_of_list_cons in H.
        simpl.
        destr H. eapply IHl1 in H0.
        rewrite H, H0 in *.
        simpl.
        reflexivity.
    - induction l1.
      + simpl. intros.
        unfold subset, of_list.
        intros.
        unfold PropSet.elem_of in *.
        inversion H0.
      + intros. simpl in H.
        eapply andb_prop in H.
        destr H.
        eapply subset_of_list_cons.
        rewrite H.
        propositional idtac.
        reflexivity.
  Qed.
  
  Fixpoint fixpoint_inc'
    (fuel: nat)
    (x: list var)
    (default: list var)
    (F: list var -> list var) :=
    match fuel with
    | O => default
    | S fuel' => let x' := F x
             in if is_list_subset x' x then x else
                  fixpoint_inc' fuel' x' default F
    end.

  Lemma fixpoint_inc'_convergence:
    forall fuel x default F,
      let retval := fixpoint_inc' fuel x default F
      in is_list_subset (F retval) retval = true \/
           retval = default.
  Proof.
    induction fuel.
    - simpl. intros. auto.
    - simpl. intros.
      destr (is_list_subset (F x) x).
      + rewrite E in *. auto.
      + eapply IHfuel.
  Qed.

  Definition fix_fuel := 8%nat.
  Definition fixpoint_inc := fixpoint_inc' fix_fuel [].

  Lemma fixpoint_inc'_bounded':
    forall fuel default F,
      (forall x', is_list_subset x' default = true
                  -> is_list_subset (F x') default = true)
      -> forall x,
        is_list_subset x default = true ->
        let retval := fixpoint_inc' fuel x default F in
        is_list_subset retval default = true.
  Proof.
    induction fuel.
    - intros. simpl in *.
      eapply is_list_subset_refl.
    - intros. simpl in *.
      destr (is_list_subset (F x) x).
      + eapply H0.
      + assert (is_list_subset (F retval) retval = true \/
                  retval = default).  {
          eapply fixpoint_inc'_convergence.
        }
        destr H1.
        * eapply IHfuel in H.
          2: { eapply H. }
          2: { eapply H0. }
          eapply H.
        * rewrite H1. eapply is_list_subset_refl.
  Qed.


  Lemma fixpoint_inc'_bounded:
    forall fuel default F,
      (forall x', is_list_subset x' default = true
                  -> is_list_subset (F x') default = true)
      ->
        let retval := fixpoint_inc' fuel [] default F in
        is_list_subset retval default = true.
  Proof.
    intros.
    eapply fixpoint_inc'_bounded'.
    2: { simpl. reflexivity. }
    eapply H.
  Qed.

    
  Lemma subset_of_list_find_removeb:
    forall a x l,
      subset
        (of_list
           (if find (eqb a) (List.removeb eqb x l)
            then List.removeb eqb x l
            else a :: List.removeb eqb x l))
        (of_list (if find (eqb a) l then l else a :: l)).
  Proof.
    unfold subset, of_list, elem_of in *; simpl; intros.
    destr (find (eqb a) (List.removeb eqb x l)).
    - destr (find (eqb a) l ).
      + eapply List.In_removeb_weaken. eassumption.
      + eapply in_cons. eapply List.In_removeb_weaken.
        eassumption.
    - eapply in_inv in H.
      destr H.
      + rewrite H in *.
        destr (find (eqb x0)).
        * inversion E.
        * destr (find (eqb x0) l).
          -- pose proof E1 as E1'.
             eapply List.find_eqb in E1.
             rewrite <- E1 in E1'.
             eapply find_some.
             eapply E1'.
          -- eapply in_eq.
      + destr (find (eqb a) l ).
        * eapply List.In_removeb_weaken. eassumption.
        * eapply in_cons. eapply List.In_removeb_weaken.
          eassumption.
  Qed.
  
  Fixpoint live(s: stmt var)(l: list var): list var :=
    match s with
    | SInteract resvars _ argvars  =>
          list_union String.eqb
            (argvars) (list_diff String.eqb l resvars)
    | SCall binds _ args =>
        list_union String.eqb args (list_diff String.eqb l binds)
    | SLoad _ x a _ =>
        list_union String.eqb [a] (list_diff String.eqb l [x])
    | SStore _ a v _ =>
        list_union String.eqb (list_union String.eqb [a] [v]) l
    | SInlinetable _ x _ i =>
        list_union String.eqb [i] (list_diff String.eqb l [x])
    | SStackalloc x _ body =>
        list_diff String.eqb (live body l) [x]
    | SLit x v =>
        list_diff String.eqb l [x]
    | SOp x _ y oz =>
        match oz with
        | Const _ => list_union String.eqb [y] (list_diff String.eqb l [x])
        | Var z => list_union String.eqb (list_union String.eqb [y] [z]) (list_diff String.eqb l [x])
        end
    | SSet x y =>
        list_union String.eqb [y] (list_diff String.eqb l [x])
    | SIf c s1 s2 =>
        list_union String.eqb
          (list_union String.eqb (live s1 l) (live s2 l))
          (accessed_vars_bcond c)
    | SSeq s1 s2 => live s1 (live s2 l)
    | SSkip => l
    | SLoop s1 c s2 =>
        let default := list_union String.eqb (accessed_vars_stmt (SLoop s1 c s2)) l in
        fixpoint_inc default
          (fun x => (live s1 (list_union String.eqb
                                (live s2 x)
                                (list_union String.eqb
                                  (accessed_vars_bcond c)
                                  l))))
    end.

  Lemma live_upper_bound':
    forall s l,
      subset (of_list (live s l)) (of_list (list_union String.eqb (accessed_vars_stmt s) l)).
  Proof.
    intro.
    induction s.
    - simpl. eapply subset_of_list_find_removeb.
    - simpl. intros.  eapply sameset_ref.
    - simpl. eapply subset_of_list_find_removeb.
    - simpl. intros.
      unfold subset, elem_of. intros.
      destr (eqb x x0).
      * destr (find (eqb x0) (accessed_vars_stmt s)).
        -- rewrite of_list_list_union.
           eapply in_union_l.
           eapply find_some in E.
           fwd. eauto using Ep0.
        -- repeat (rewrite of_list_list_union;
                   eapply in_union_l).
           unfold elem_of.
           unfold of_list.
           eapply in_eq.
      * assert (of_list (live s l) x0).
        { rewrite of_list_removeb in H. unfold diff in *.
          fwd. eapply Hp0.
        }
        eapply IHs in H0.
        repeat rewrite of_list_list_union.
        unfold elem_of in *.
        rewrite of_list_list_union in *.
        destr (find (eqb x) (accessed_vars_stmt s)).
        { eassumption. }
        { unfold union, elem_of, of_list in *.
          propositional idtac.
          left. eauto using in_cons.
        }
    - simpl. intro.
      eapply subset_of_list_removeb.
    - simpl.
      destr z.
      + destr ((y =? v)%string); intro.
        * eapply subset_of_list_split_union.
          -- eapply subset_refl.
          -- eapply subset_of_list_removeb.
        * eapply subset_of_list_split_union.
          -- eapply subset_refl.
          -- eapply subset_of_list_removeb.
      + simpl. eapply subset_of_list_find_removeb.
    - simpl. eapply subset_of_list_find_removeb.
    - simpl; intro. eapply subset_of_list_union.
      + eapply subset_of_list_union.
        * eapply subset_trans.
          -- eapply IHs1.
          -- repeat rewrite of_list_list_union.
             subset_union_solve.
        * eapply subset_trans.
          -- eapply IHs2.
          -- repeat rewrite of_list_list_union.
             subset_union_solve.
      + repeat rewrite of_list_list_union.
        subset_union_solve.
    - simpl.
      intros.
      eapply subset_trans.
      + unfold fixpoint_inc.
        eapply is_list_subset_of_list.
        eapply fixpoint_inc'_bounded.
        intros.
        eapply is_list_subset_of_list in H.
        eapply is_list_subset_of_list.
        repeat listset_to_set.
        repeat rewrite of_list_list_union.
        * eapply subset_trans; [ eapply IHs1 | ].
          repeat rewrite of_list_list_union.
          eapply subset_union_l; [ subset_union_solve | ].
          eapply subset_union_l; [ eapply subset_trans; [ eapply IHs2 | ] | ].
          -- repeat rewrite of_list_list_union.
             eapply subset_union_l; [ subset_union_solve | ].
             eassumption.
          -- subset_union_solve.
      + eapply subset_refl.
    - simpl.
      intros.
      eapply subset_trans.
      + eapply IHs1.
      + eapply subset_of_list_union.
        * repeat rewrite of_list_list_union.
          subset_union_solve.
        * eapply subset_trans.
          -- eapply IHs2.
          -- repeat rewrite of_list_list_union.
             subset_union_solve.
    - simpl. intros. eapply subset_refl.
    - simpl.
      intros.
      eapply subset_of_list_split_union.
      + eapply subset_refl.
      + eapply subset_of_list_diff.
    - simpl. intros. eapply subset_refl.
      eapply subset_of_list_split_union.
      + eapply subset_refl.
      + eapply subset_of_list_diff.
  Qed.

  Lemma live_while:
    forall s1 c s2 l,
      let l' := live (SLoop s1 c s2) l in
      subset (of_list (live s1
                         (list_union eqb
                            (live s2 l')
                            (list_union eqb (accessed_vars_bcond c) l)))) (of_list l').
  Proof.
    intros.
    cbn -[fixpoint_inc' list_union]   in l'.
    unfold fixpoint_inc in l'.

    let Heq := fresh in
    specialize
      (fixpoint_inc'_convergence
         fix_fuel []
          (list_union eqb
             (list_union eqb (accessed_vars_bcond c)
                (list_union eqb (accessed_vars_stmt s1)
                   (accessed_vars_stmt s2))) l)
          (fun x : list string =>
           live s1
             (list_union eqb
                (live s2 x)
                (list_union eqb (accessed_vars_bcond c) l)))) as Heq.
    cbn zeta in H; destr H.
    - eapply is_list_subset_of_list in H.
      replace (fixpoint_inc' fix_fuel []
              (list_union eqb
                 (list_union eqb (accessed_vars_bcond c)
                    (list_union eqb (accessed_vars_stmt s1)
                       (accessed_vars_stmt s2))) l)
              (fun x : list string =>
               live s1
                 (list_union eqb
                    (live s2 x)
                    (list_union eqb (accessed_vars_bcond c) l)
                    ))) with l' in *.
      2: { auto. }
      assumption.
    -  replace (fixpoint_inc' fix_fuel []
              (list_union eqb
                 (list_union eqb (accessed_vars_bcond c)
                    (list_union eqb (accessed_vars_stmt s1)
                       (accessed_vars_stmt s2))) l)
              (fun x : list string =>
               live s1
                 (list_union eqb
                     (live s2 x)(list_union eqb (accessed_vars_bcond c) l)
                   ))) with l' in *.
       2: { auto. }
       eapply subset_trans; [ eapply live_upper_bound' | ].
       rewrite H.
       repeat rewrite of_list_list_union.
       eapply subset_union_l; [ subset_union_solve | ].
       eapply subset_union_l; [  | subset_union_solve ].
       eapply subset_trans; [ eapply live_upper_bound' | ].
       repeat rewrite of_list_list_union.
       subset_union_solve.
  Qed.
  
  Fixpoint dce(s: stmt var)(u: list var)  : stmt var :=
    match s with
    | SInteract _ _ _ => s
    | SCall _ _ _ => s
    | SLoad _ x _ _ =>
        if (existsb (eqb x) u) then
          s
        else
          SSkip
    | SStore _ _ _ _ => s
    | SInlinetable _ x _ _ =>
        if (existsb (eqb x) u) then
          s
        else
          SSkip
    | SStackalloc x n body =>
        SStackalloc x n (dce body u)
        (* The below optimization probably can be made to work;
           on past attempt, got stuck at goals about `Memory.anybytes n a map.empty` *)
        (* if (existsb (eqb x) (live body u)) then
          SStackalloc x n (dce body u)
        else
          (dce body u) *)
    | SLit x _ =>
        if (existsb (eqb x) u) then
          s
        else
          SSkip
    | SOp x _ _ _ =>
        if (existsb (eqb x) u) then
          s
        else
          SSkip
    | SSet x _ =>
         if (existsb (eqb x) u) then
          s
        else
          SSkip
    | SIf c s1 s2 => SIf c (dce s1 u) (dce s2 u)
    | SLoop s1 c s2 =>
        let live_before :=  (live (SLoop s1 c s2) u) in
        SLoop
          (dce s1 (list_union String.eqb
                     (live s2 live_before)
                      (list_union
                         eqb
                         (accessed_vars_bcond c)
                         u)))
          c
          (dce s2 (live_before))
    | SSeq s1 s2 => SSeq (dce s1 (live s2 u)) (dce s2 u)
    | SSkip => SSkip
    end.

  Require Import compiler.CustomFix.
  Require Import bedrock2.LeakageSemantics.
  Require Import Coq.Init.Wf Wellfounded.
  Definition tuple : Type := leakage * stmt var * list var.
  Definition project_tuple (tup : tuple) :=
    let '(kH, s, u) := tup in (length kH, s).
  Definition lt_tuple (x y : tuple) :=
    lt_tuple' (project_tuple x) (project_tuple y).
  
  Lemma lt_tuple_wf : well_founded lt_tuple.
  Proof.
    cbv [lt_tuple]. apply wf_inverse_image. apply lt_tuple'_wf.
  Defined.

  Definition dtransform_stmt_trace_body
    (e: env)
    (tup : leakage * stmt var * list var)
    (dtransform_stmt_trace : forall othertup, lt_tuple othertup tup -> leakage * leakage)
    : leakage * leakage. (*skipH * kL*)
    refine (
        match tup as x return tup = x -> _ with
        | (kH, s, u) =>
            fun _ =>
              match s as x return s = x -> _ with
              | SInteract _ _ _ =>
                  fun _ =>
                    match kH with
                    | leak_list l :: kH' => ([leak_list l], [leak_list l])
                    | _ => (nil, nil)
                    end
              | SCall _ fname _ =>
                  fun _ =>
                    match kH as x return kH = x -> _ with
                    | leak_unit :: kH' =>
                        fun _ =>
                          match @map.get _ _ env e fname with
                          | Some (params, rets, fbody) =>
                              let '(skip, kL) := dtransform_stmt_trace (kH', fbody, rets) _ in
                              (leak_unit :: skip, leak_unit :: kL)
                          | None => (nil, nil)
                          end
                    | _ => fun _ => (nil, nil)
                    end eq_refl
              | SLoad _ x _ _ =>
                  fun _ =>
                    match kH with
                    | leak_word addr :: kH' =>
                        if (existsb (eqb x) u) then
                          ([leak_word addr], [leak_word addr])
                        else
                          ([leak_word addr], nil)
                    | _ => (nil, nil)
                    end
              | SStore _ _ _ _ =>
                  fun _ =>
                    match kH with
                    | leak_word addr :: kH' => ([leak_word addr], [leak_word addr])
                    | _ => (nil, nil)
                    end
              | SInlinetable _ x _ _ =>
                  fun _ =>
                    match kH with
                    | leak_word i :: kH' =>
                        if (existsb (eqb x) u) then
                          ([leak_word i], [leak_word i])
                        else
                          ([leak_word i], nil)
                    | _ => (nil, nil)
                    end
              | SStackalloc x n body =>
                  fun _ => dtransform_stmt_trace (kH, body, u) _
              | SLit x _ =>
                  fun _ => (nil, nil)
              | SOp x op _ _ =>
                  fun _ =>
                    (*copied from spilling.
                      I should do a leak_list for ops (or just make every op leak two words)
                      so I don't have to deal with this nonsense*)
                    let skip :=
                      match op with
                      | Syntax.bopname.divu
                      | Syntax.bopname.remu =>
                          match kH with
                          | leak_word x1 :: leak_word x2 :: k' => [leak_word x1; leak_word x2]
                          | _ => nil
                          end
                      | Syntax.bopname.slu
                      | Syntax.bopname.sru
                      | Syntax.bopname.srs =>
                          match kH with
                          | leak_word x2 :: kH' => [leak_word x2]
                          | _ => nil
                          end
                      | _ => nil
                      end
                    in
                    if (existsb (eqb x) u) then
                      (skip, skip)
                    else
                      (skip, nil)
              | SSet _ _ => fun _ => (nil, nil)
              | SIf _ thn els =>
                  fun _ =>
                    match kH as x return kH = x -> _ with
                    | leak_bool b :: kH' =>
                        fun _ =>
                          let '(skip, kL) := dtransform_stmt_trace (kH', if b then thn else els, u) _ in
                          (leak_bool b :: skip, leak_bool b :: kL)
                    | _ => fun _ => (nil, nil)
                    end eq_refl
              | SLoop s1 c s2 =>
                  fun _ =>
                    let live_before := live (SLoop s1 c s2) u in
                    let (skip1, kL1) := dtransform_stmt_trace (kH, s1, (list_union String.eqb
                                                                          (live s2 live_before)
                                                                          (list_union eqb (accessed_vars_bcond c) u))) _ in
                    Let_In_pf_nd (List.skipn (length skip1) kH)
                      (fun kH' _ =>
                         match kH' as x return kH' = x -> _ with
                         | leak_bool true :: kH'' =>
                             fun _ =>
                               let '(skip2, kL2) := dtransform_stmt_trace (kH'', s2, live_before) _ in
                               let kH''' := List.skipn (length skip2) kH'' in
                               let (skip3, kL3) := dtransform_stmt_trace (kH''', s, u) _ in
                               (skip1 ++ [leak_bool true] ++ skip2 ++ skip3, kL1 ++ [leak_bool true] ++ kL2 ++ kL3)
                         | leak_bool false :: kH'' =>
                             fun _ => (skip1 ++ [leak_bool false], kL1 ++ [leak_bool false])
                         | _ => fun _ => (nil, nil)
                         end eq_refl)
              | SSeq s1 s2 =>
                  fun _ =>
                    let '(skip1, kL1) := dtransform_stmt_trace (kH, s1, live s2 u) _ in
                    let kH' := List.skipn (length skip1) kH in
                    let '(skip2, kL2) := dtransform_stmt_trace (kH', s2, u) _ in
                    (skip1 ++ skip2, kL1 ++ kL2)
              | SSkip => fun _ => (nil, nil)
              end eq_refl
        end eq_refl).
    Proof.
      all: cbv [lt_tuple project_tuple].
      all: subst.
      all: repeat match goal with
             | t := List.skipn ?n ?k |- _ =>
                      let H := fresh "H" in
                      assert (H := List.skipn_length n k); subst t end.
      all: try (right; constructor; constructor).
      all: try (left; simpl; blia).
    - assert (H' := skipn_length (length skip1) kH).
      rewrite e3 in *. simpl in *. left. blia.
    - assert (H' := skipn_length (length skip1) kH).
      rewrite e3 in *. simpl in *. left. blia.
    - destruct (length (List.skipn (length skip1) kH) =? length kH)%nat eqn:E.
      + apply Nat.eqb_eq in E. rewrite E. right. constructor. constructor.
      + apply Nat.eqb_neq in E. left. blia.
    Defined.
    Check Fix.
    Definition dtransform_stmt_trace e :=
      Fix lt_tuple_wf _ (dtransform_stmt_trace_body e).

    Lemma fix_step e tup : dtransform_stmt_trace e tup = dtransform_stmt_trace_body e tup (fun y _ => dtransform_stmt_trace e y).
    Proof.
      cbv [dtransform_stmt_trace].
      apply (@Fix_eq' _ _ lt_tuple_wf _ (dtransform_stmt_trace_body e)).
      { intros. clear tup. rename f into f1. rename g into f2.
        cbv [dtransform_stmt_trace_body]. cbv beta.
        destruct x as [ [k s] u].
        (*cbv [Equiv] in H. destruct H as [H1 H2]. injection H1. intros. subst. clear H1.*)
        Tactics.destruct_one_match. all: try reflexivity.
        { apply H. }
        { Tactics.destruct_one_match; try reflexivity. Tactics.destruct_one_match; try reflexivity.
          repeat (Tactics.destruct_one_match; try reflexivity).
          erewrite H in E. rewrite E in E0. inversion E0. subst. reflexivity. }
        { Tactics.destruct_one_match; try reflexivity. Tactics.destruct_one_match; try reflexivity.
          erewrite H in E. rewrite E in E0. inversion E0. subst.
          apply Let_In_pf_nd_ext. intros. Tactics.destruct_one_match; try reflexivity.
          Tactics.destruct_one_match; try reflexivity. Tactics.destruct_one_match; try reflexivity.
          repeat Tactics.destruct_one_match; try reflexivity.
          all: (erewrite H in E1; rewrite E1 in E3; inversion E3; subst) ||
                 (erewrite H in E1; rewrite E1 in E2; inversion E2; subst).
          erewrite H in E2. rewrite E2 in E4. inversion E4. subst. reflexivity. }
        { repeat Tactics.destruct_one_match.
          all: (erewrite H in E; rewrite E in E1; inversion E1; subst) ||
                 (erewrite H in E; rewrite E in E0; inversion E0; subst; reflexivity). 
          erewrite H in E0. rewrite E0 in E2.
          inversion E2. subst. reflexivity. }
        { Tactics.destruct_one_match; try reflexivity. Tactics.destruct_one_match; try reflexivity.
          Tactics.destruct_one_match; try reflexivity. Tactics.destruct_one_match.
          Tactics.destruct_one_match. erewrite H. reflexivity. } }
    Qed.

  Definition dce_function: (list string *
                              list string *
                              stmt string ) ->
                           result (list string
                                   * list string
                                   * stmt string
                             ) :=
    fun '(argnames, retnames, body) =>
      let body' := dce body retnames in
      Success (argnames, retnames, body').

  Definition dce_functions : env -> result env :=
    map.try_map_values dce_function.


  Definition compile_post
    mcH mcL used_after
    (postH: Semantics.trace -> mem -> locals -> MetricLog -> Prop)
    :
    Semantics.trace -> mem -> locals -> MetricLog -> Prop
    :=
    (fun t' m' lL' mcL' =>
       exists lH' mcH',
         map.agree_on (PropSet.of_list used_after) lH' lL'
         /\ metricsLeq (mcL' - mcL) (mcH' - mcH)
         /\ postH t' m' lH' mcH').

  Lemma agree_on_eval_bcond:
    forall cond (m1 m2: locals),
      map.agree_on (of_list (accessed_vars_bcond cond)) m1 m2 ->
      eval_bcond m1 cond = eval_bcond m2 cond.
  Proof.
    intros.
    induction cond.
    - simpl in *.
      destr ((x =? y)%string).
      + unfold map.agree_on, of_list in H.
        assert (map.get m1 y = map.get m2 y).
        { eapply H. unfold elem_of. eapply in_eq. }
        repeat rewrite H0. reflexivity.
      + unfold map.agree_on in H.
        assert (map.get m1 y = map.get m2 y).
        { eapply H. unfold elem_of. eapply in_cons, in_eq. }
        assert (map.get m1 x = map.get m2 x).
        { eapply H. unfold elem_of. eapply in_eq.  }
        repeat rewrite H0, H1.
        reflexivity.
    - simpl in *.
      assert (map.get m1 x = map.get m2 x).
      { eapply H. unfold elem_of. eapply in_eq. }
      rewrite H0. reflexivity.
  Qed.
End WithArguments1.
