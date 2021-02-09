Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.
Require Export Rupicola.Lib.Gensym.
Require Import Rupicola.Lib.Tactics.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok _}.

  Lemma compile_skip {tr mem locals functions} {pred0: predicate} :
    pred0 tr mem locals ->
    (<{ Trace := tr;
        Memory := mem;
        Locals := locals;
        Functions := functions }>
     cmd.skip
     <{ pred0 }>).
  Proof. repeat straightline; assumption. Qed.

  Lemma compile_word_of_Z_constant
        {tr mem locals functions} {T} {pred: T -> predicate} :
    forall (z: Z) k k_impl,
    forall var,
      let v := word.of_Z z in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal z)) k_impl
      <{ pred (nlet [var] v k) }>.
  Proof. repeat straightline; eassumption. Qed.

  Lemma compile_Z_constant
        {tr mem locals functions} {T} {pred: T -> predicate} :
    forall z k k_impl,
    forall var,
      let v := z in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (word.of_Z v);
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal z)) k_impl
      <{ pred (nlet [var] v k) }>.
  Proof. repeat straightline; eassumption. Qed.

  Lemma compile_nat_constant
        {tr mem locals functions} {T} {pred: T -> predicate} :
    forall n k k_impl,
    forall var,
      let v := n in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (word.of_Z (Z.of_nat v));
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal (Z.of_nat n))) k_impl
      <{ pred (nlet [var] v k) }>.
  Proof. repeat straightline; eassumption. Qed.

  Notation b2w b :=
    (word.of_Z (Z.b2z b)).

  Lemma compile_bool_constant
        {tr mem locals functions} {T} {pred: T -> predicate} :
    forall b k k_impl,
    forall var,
      let v := b in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (b2w v);
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal (Z.b2z v))) k_impl
      <{ pred (nlet [var] v k) }>.
  Proof. repeat straightline; eassumption. Qed.

  (* FIXME generalize *)
  Lemma compile_xorb
        {tr mem locals functions} {T} {pred: T -> predicate} :
    forall x x_var y y_var k k_impl,
    forall var,
      map.get locals x_var = Some (b2w x) ->
      map.get locals y_var = Some (b2w y) ->
      let v := xorb x y in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (b2w v);
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.op bopname.xor (expr.var x_var) (expr.var y_var)))
              k_impl
      <{ pred (k v) }>.
  Proof.
    intros.
    repeat straightline.
    eexists; split.
    { repeat straightline.
      eexists; split; [ eassumption | ].
      repeat straightline.
      eexists; split; [ eassumption | ].
      reflexivity. }
    red.
    rewrite <-(word.of_Z_unsigned (word.xor _ _)).
    rewrite word.unsigned_xor_nowrap.
    rewrite !word.unsigned_of_Z_b2z, Z.lxor_xorb.
    assumption.
  Qed.

  Lemma compile_add
        {tr mem locals functions} {T} {pred: T -> predicate} :
    forall x x_var y y_var k k_impl,
    forall var,
      map.get locals x_var = Some x ->
      map.get locals y_var = Some y ->
      let v := word.add x y in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.op bopname.add (expr.var x_var) (expr.var y_var)))
              k_impl
      <{ pred (nlet [var] v k) }>.
  Proof.
    repeat straightline.
    eexists; split; eauto.
    repeat straightline.
    eexists; split; eauto.
    repeat straightline.
    eexists; split; eauto.
  Qed.

  Lemma compile_eqb
        {tr mem locals functions} {T} {pred: T -> predicate} :
    forall x x_var y y_var k k_impl,
    forall var,
      map.get locals x_var = Some x ->
      map.get locals y_var = Some y ->
      let v := word.eqb x y in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (b2w v);
          Functions := functions }>
       k_impl
       <{ pred (nlet [var] v k) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.op bopname.eq (expr.var x_var) (expr.var y_var)))
              k_impl
      <{ pred (nlet [var] v k) }>.
  Proof.
    intros. repeat straightline'.
    subst_lets_in_goal.
    rewrite word.unsigned_eqb in *. cbv [Z.b2z] in *.
    destruct_one_match; eauto.
  Qed.

  (* TODO: make more types *)
  Lemma compile_copy_local
        {tr mem locals functions} {T} {pred: T -> predicate} :
    forall v0 k k_impl
      src_var dst_var,
      map.get locals src_var = Some v0 ->
      let v := v0 in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals dst_var v;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set dst_var (expr.var src_var)) k_impl
      <{ pred (nlet [dst_var] v k) }>.
  Proof.
    repeat straightline'; eauto.
  Qed.

  (* FIXME check out what happens when running straightline on a triple with a cmd.seq; could we get rid of the continuation arguments?  Would it require more rewrites? *)

  (* N.B. this should *not* be added to any compilation tactics, since it will
     always apply; it needs to be applied manually *)
  Lemma compile_unset
        {tr mem locals functions} {pred0: predicate} :
    forall var cmd,
      <{ Trace := tr;
         Memory := mem;
         Locals := map.remove locals var;
         Functions := functions }>
      cmd
      <{ pred0 }> ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.unset var) cmd
      <{ pred0 }>.
  Proof.
    repeat straightline'; eauto.
  Qed.

  Definition map_remove_many {K V} {M: map.map K V} m (ks: list K) :=
    List.fold_left map.remove ks m.

  Definition DefaultValue (T: Type) (t: T) := T.

  Lemma compile_unsets
        {tr mem locals functions} {pred0: predicate} :
    forall (vars: let x := DefaultValue (list string) [] in list string) cmd,
      (<{ Trace := tr;
          Memory := mem;
          Locals := map_remove_many locals vars;
          Functions := functions }>
       cmd
       <{ pred0 }>) ->
      (<{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       fold_right (fun v c => cmd.seq (cmd.unset v) c) cmd vars
       <{ pred0 }>).
  Proof.
    induction vars in locals |- *; cbn [fold_right]; intros.
    - assumption.
    - apply compile_unset.
      apply IHvars.
      assumption.
  Qed.

  (* N.B. should only be added to compilation tactics that solve their subgoals,
     since this applies to any shape of goal *)
  Lemma compile_copy_pointer
        {tr mem locals functions} {T} {pred: T -> predicate} :
    forall {data} (Data : Semantics.word -> data -> Semantics.mem -> Prop)
      x_var x_ptr (x : data) k k_impl var R,

      (* This assumption is used to drive the compiler, but it's not used by the proof *)
      (Data x_ptr x * R)%sep mem ->
      map.get locals x_var = Some x_ptr ->

      let v := x in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var x_ptr;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.var x_var)) k_impl
      <{ pred (nlet [var] v k) }>.
  Proof.
    unfold postcondition_cmd.
    intros.
    repeat straightline'.
    eassumption.
  Qed.

  Lemma compile_if_word (* FIXME generalize to arbitrary ifs *)
        {tr mem locals functions} {T} {pred: T -> predicate} :
    forall t_var f_var (t f : word) (c : bool) c_var
      k k_impl var,

      map.get locals c_var = Some (b2w c) ->
      map.get locals t_var = Some t ->
      map.get locals f_var = Some f ->

      let v := if c then t else f in

      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.cond (expr.var c_var)
                  (cmd.set var (expr.var t_var))
                  (cmd.set var (expr.var f_var)))
        k_impl
      <{ pred (let/n x as var := v in
               k x) }>.
  Proof.
    intros.
    repeat straightline'.
    split_if ltac:(repeat straightline').
    { subst_lets_in_goal. rewrite word.unsigned_of_Z_b2z.
      cbv [Z.b2z]; destruct_one_match; try congruence; [ ].
      intros. repeat straightline'. eauto. }
    { subst_lets_in_goal. rewrite word.unsigned_of_Z_b2z.
      cbv [Z.b2z]; destruct_one_match; try congruence; [ ].
      intros. repeat straightline'. eauto. }
  Qed.

  Lemma compile_if_pointer
        {tr mem locals functions} {T} {pred: T -> predicate} :
    forall {data} (Data : Semantics.word -> data -> Semantics.mem -> Prop) Rt Rf
      t_var f_var t_ptr f_ptr (t f : data) (c : bool) c_var
      k k_impl var,

      (Data t_ptr t * Rt)%sep mem ->
      (Data f_ptr f * Rf)%sep mem ->

      map.get locals c_var = Some (b2w c) ->
      map.get locals t_var = Some t_ptr ->
      map.get locals f_var = Some f_ptr ->

      let v := if c then t else f in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (if c then t_ptr else f_ptr);
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.cond (expr.var c_var)
                  (cmd.set var (expr.var t_var))
                  (cmd.set var (expr.var f_var)))
        k_impl
      <{ pred (let/n x as var := v in k x) }>.
  Proof.
    intros.
    unfold postcondition_cmd.

    intros.
    repeat straightline'.
    split_if ltac:(repeat straightline').
    { subst_lets_in_goal. rewrite word.unsigned_of_Z_b2z.
      cbv [Z.b2z]; destruct_one_match; try congruence; [ ].
      intros. repeat straightline'. eauto. }
    { subst_lets_in_goal. rewrite word.unsigned_of_Z_b2z.
      cbv [Z.b2z]; destruct_one_match; try congruence; [ ].
      intros. repeat straightline'. eauto. }
  Qed.

  Section NoSkips.
    Definition is_skip cmd :=
      match cmd with
      | cmd.skip => true
      | _ => false
      end.

    Lemma is_skip_sound cmd :
      is_skip cmd = true -> cmd = cmd.skip.
    Proof. destruct cmd; inversion 1; congruence. Qed.

    Lemma is_skip_complete cmd :
      is_skip cmd = false -> cmd <> cmd.skip.
    Proof. destruct cmd; inversion 1; congruence. Qed.

    Fixpoint noskips (c: cmd.cmd) :=
      match c with
      | cmd.stackalloc lhs nbytes body =>
        cmd.stackalloc lhs nbytes (noskips body)
      | cmd.cond condition nonzero_branch zero_branch =>
        cmd.cond condition (noskips nonzero_branch) (noskips zero_branch)
      | cmd.seq s1 s2 =>
        let s1 := noskips s1 in
        let s2 := noskips s2 in
        match is_skip s1, is_skip s2 with
        | true, _ => s2
        | _, true => s1
        | _, _ => cmd.seq s1 s2
        end
      | cmd.while test body => cmd.while test (noskips body)
      | _ => c
      end.

    Lemma WeakestPrecondition_weaken :
      forall cmd {functions} (p1 p2: _ -> _ -> _ -> Prop),
        (forall tr mem locals, p1 tr mem locals -> p2 tr mem locals) ->
        forall tr mem locals,
          WeakestPrecondition.program
            functions cmd tr mem locals p1 ->
          WeakestPrecondition.program
            functions cmd tr mem locals p2.
    Proof.
    Admitted.

    Lemma noskips_sound:
      forall cmd {tr mem locals functions} post,
        WeakestPrecondition.cmd
          (WeakestPrecondition.call functions)
          (noskips cmd) tr mem locals post ->
        WeakestPrecondition.cmd
          (WeakestPrecondition.call functions)
          cmd tr mem locals post.
    Proof.
      induction cmd;
        repeat match goal with
               | _ => eassumption
               | _ => apply IHcmd
               | [ H: _ /\ _ |- _ ] => destruct H
               | [  |- _ /\ _ ] => split
               | [ H: forall v t m l, ?P v t m l -> _ |- ?P _ _ _ _ -> _ ] =>
                 let h := fresh in intros h; specialize (H _ _ _ _ h)
               | [ H: exists _, _ |- _ ] => destruct H
               | [  |- exists _, _ ] => eexists
               | [ H: context[WeakestPrecondition.cmd] |- context[WeakestPrecondition.cmd] ] => solve [eapply H; eauto]
               | _ => cbn || intros ? || eauto
               end.
      { destruct (is_skip (noskips cmd1)) eqn:H1;
          [ apply is_skip_sound in H1; rewrite H1 in * |
            apply is_skip_complete in H1 ].
        - apply IHcmd1, IHcmd2; eassumption.
        - destruct (is_skip (noskips cmd2)) eqn:H2;
            [ apply is_skip_sound in H2; rewrite H2 in * |
              apply is_skip_complete in H2 ].
          + eapply WeakestPrecondition_weaken, IHcmd1; eauto.
          + eapply WeakestPrecondition_weaken.
            * intros * H0. eapply IHcmd2. exact H0.
            * eapply IHcmd1. eassumption.  }
    Qed.

    Lemma noskips_complete:
      forall cmd {tr mem locals functions} post,
        WeakestPrecondition.cmd
          (WeakestPrecondition.call functions)
          cmd tr mem locals post ->
        WeakestPrecondition.cmd
          (WeakestPrecondition.call functions)
          (noskips cmd) tr mem locals post.
    Proof.
      induction cmd;
        repeat match goal with
               | _ => eassumption
               | _ => apply IHcmd
               | [ H: _ /\ _ |- _ ] => destruct H
               | [  |- _ /\ _ ] => split
               | [ H: forall v t m l, ?P v t m l -> _ |- ?P _ _ _ _ -> _ ] =>
                 let h := fresh in intros h; specialize (H _ _ _ _ h)
               | [ H: exists _, _ |- _ ] => destruct H
               | [  |- exists _, _ ] => eexists
               | [ H: context[WeakestPrecondition.cmd] |- context[WeakestPrecondition.cmd] ] => solve [eapply H; eauto]
               | _ => cbn || intros ? || eauto
               end.
      { apply IHcmd1 in H.
        destruct (is_skip (noskips cmd1)) eqn:H1;
          [ apply is_skip_sound in H1; rewrite H1 in * |
            apply is_skip_complete in H1 ].
        - apply IHcmd2; eassumption.
        - destruct (is_skip (noskips cmd2)) eqn:H2;
            [ apply is_skip_sound in H2; rewrite H2 in * |
              apply is_skip_complete in H2 ].
          + eapply WeakestPrecondition_weaken in H; [ apply H | ].
            intros; eapply IHcmd2; eauto.
          + eapply WeakestPrecondition_weaken in H; [ apply H | ].
            intros * H0. apply IHcmd2 in H0. apply H0. }
    Qed.

  End NoSkips.

  Lemma postcondition_func_norets_postcondition_cmd
        {T} spec (x: T) cmd R tr mem locals functions :
    (let pred a := postcondition_cmd (fun _ : Semantics.locals => True) (spec a) [] R tr in
     <{ Trace := tr;
        Memory := mem;
        Locals := locals;
        Functions := functions }>
     cmd
     <{ pred x }>) ->
    <{ Trace := tr;
       Memory := mem;
       Locals := locals;
       Functions := functions }>
    cmd
    <{ fun (tr' : Semantics.trace) (m' : Semantics.mem) (_ : Semantics.locals) =>
         postcondition_func_norets (spec x) R tr tr' m' [] }>.
  Proof.
    cbv [postcondition_func_norets
           postcondition_func postcondition_cmd]; intros.
    eapply Proper_cmd;
      [ solve [apply Proper_call] | repeat intro
        | eassumption ].
    sepsimpl; cleanup; eauto; [ ].
    match goal with H : map.getmany_of_list _ [] = Some _ |- _ =>
                    inversion H; clear H; subst
    end.
    eauto.
  Qed.

  Lemma getmany_list_map l :
    forall a vs (P :_ -> Prop),
      map.getmany_of_list l a = Some vs ->
      P vs ->
      WeakestPrecondition.list_map (WeakestPrecondition.get l) a P.
  Proof.
    induction a; cbn [WeakestPrecondition.list_map
                        WeakestPrecondition.list_map_body]; intros;
      match goal with
      | H : map.getmany_of_list _ [] = _ |- _ => cbn in H; congruence
      | H : map.getmany_of_list _ (_ :: _) = _ |- _ =>
        pose proof (map.getmany_of_list_exists_elem
                      _ _ _ _ ltac:(eauto using in_eq) H);
          cbn in H
      end.
      cleanup; eexists; ssplit; [ eassumption | ].
      repeat destruct_one_match_hyp; try congruence; [ ].
      repeat match goal with
             | H : Some _ = Some _ |- _ =>
               inversion H; clear H; subst
             end.
      eapply IHa; eauto.
  Qed.

  Lemma postcondition_func_postcondition_cmd
        {T} spec (x: T) cmd R tr mem locals retvars functions :
    (let pred a := postcondition_cmd (fun _ : Semantics.locals => True) (spec a) retvars R tr in
     <{ Trace := tr;
        Memory := mem;
        Locals := locals;
        Functions := functions }>
     cmd
     <{ pred x }>) ->
    <{ Trace := tr;
       Memory := mem;
       Locals := locals;
       Functions := functions }>
    cmd
    <{ fun tr' m' l =>
         WeakestPrecondition.list_map
           (WeakestPrecondition.get l) retvars
           (fun rets => postcondition_func (spec x) R tr tr' m' rets) }>.
  Proof.
    cbv [postcondition_func postcondition_cmd]; intros.
    cleanup.
    use_hyp_with_matching_cmd; cleanup; subst.
    eapply getmany_list_map; sepsimpl; eauto.
  Qed.
End with_parameters.

(* FIXME move *)
Ltac term_head x :=
  match x with
  | ?f _ => term_head f
  | _ => x
  end.

Ltac compile_setup_unfold_spec :=
  match goal with
  | [  |- context[?spec] ] =>
    match type of spec with
    | spec_of _ => cbv [spec]
    end
  | _ => idtac (* Spec inlined *)
  end.

Ltac compile_setup :=
  cbv [program_logic_goal_for];
  compile_setup_unfold_spec;
  (* modified version of a clause in straightline *)
  (intros; WeakestPrecondition.unfold1_call_goal;
   (cbv beta match delta [WeakestPrecondition.call_body]);
   lazymatch goal with
   | |- if ?test then ?T else _ =>
     replace test with true by reflexivity; change_no_check T
   end; cbv beta match delta [WeakestPrecondition.func]);
  repeat straightline; subst_lets_in_goal; cbn [length];
  first [ apply postcondition_func_norets_postcondition_cmd
        | apply postcondition_func_postcondition_cmd ];
  intros;
  lazymatch goal with
  | |- context [ WeakestPrecondition.cmd _ _ _ _ _ (?pred ?spec) ] =>
    let hd := term_head spec in unfold hd
  | |- context [ postcondition_cmd _ (fun r => ?pred ?spec r) ] => (* FIXME *)
    let hd := term_head spec in unfold hd
  | _ => fail "Postcondition not in expected shape (?pred gallina_spec)"
  end;
  apply noskips_complete.

Ltac lookup_variable m val :=
  lazymatch m with
  | map.put _ ?k val => constr:(k)
  | map.put ?m' _ _ => lookup_variable m' val
  end.

Ltac solve_map_get_goal_step :=
  lazymatch goal with
  | [ H: map.extends ?m2 ?m1 |- map.get ?m2 ?k = Some ?v ] =>
    simple apply (fun p => @map.extends_get _ _ _ m1 m2 k v p H)
  | [  |- map.get ?m _ = Some ?val ] =>
    tryif has_evar val then fail 1 val "has evars" else
      first [ simple apply map.get_put_same |
              rewrite map.get_put_diff ]
  | [  |- map.get ?m _ = None ] =>
    first [ simple apply map.get_empty |
            rewrite map.get_put_diff ]
  | [  |- _ <> _ ] => congruence
  end.

Ltac solve_map_get_goal :=
  progress repeat solve_map_get_goal_step.

Create HintDb compiler.
Hint Unfold postcondition_cmd : compiler.

Ltac compile_find_post :=
  lazymatch goal with
  | |- context [ WeakestPrecondition.cmd _ _ _ _ _ (?pred ?term) ] => constr:((pred, term))
  end.

Ltac compile_get_binding :=
  lazymatch compile_find_post with
  | (_, nlet _ ?v _) => v
  | (_, dlet ?v _) => v
  end.

(* Using [simple apply] ensures that Coq doesn't unfold [nlet]s *)
Ltac compile_basics :=
  gen_sym_inc;                  (* FIXME remove? *)
  let name := gen_sym_fetch "v" in
  let hd := compile_get_binding in
  first [simple eapply compile_word_of_Z_constant |
         simple eapply compile_Z_constant |
         simple eapply compile_nat_constant |
         simple eapply compile_bool_constant |
         simple eapply compile_xorb |
         simple eapply compile_add |
         simple eapply compile_eqb |
         simple eapply compile_if_word |
         simple eapply compile_if_pointer ].

Ltac compile_custom := fail.

Ltac compile_cleanup :=
  match goal with
  | [  |- let _ := _ in _ ] => intros
  | [  |- forall _, _ ] => intros
  end.

Ltac compile_cleanup_post :=
  match goal with
  | [  |- True ] => exact I
  | [  |- _ /\ _ ] => split
  | [  |- _ = _ ] => reflexivity
  | [  |- exists _, _ ] => eexists
  | _ =>
    first [ progress subst_lets_in_goal
          | progress autounfold with compiler ]
  end.

Ltac compile_unify_post :=
  (* [unshelve] captures the list of variables to unset as a separate goal; if
     it is not resolved by unification, compile_done will take care of it. *)
  unshelve refine (compile_unsets _ _ _);  (* coq#13839 *)
  [ shelve (* cmd *) | intros (* vars *) | ]; cycle 1;
  [ (* triple *)
    simple apply compile_skip;
    repeat compile_cleanup_post | ].

Ltac compile_solve_side_conditions :=
  match goal with
  | [  |- sep _ _ _ ] =>
    autounfold with compiler in *;
      cbn [fst snd] in *;       (* FIXME generalize this? *)
      ecancel_assumption
  | [  |- map.get _ _ = _ ] =>
    solve [subst_lets_in_goal; solve_map_get_goal]
  | [  |- map.getmany_of_list _ [] = Some _ ] =>
    reflexivity (* CPC remove? *)
  | _ =>
    first [ compile_cleanup
          | solve [eauto with compiler] ]
  end.

Ltac compile_binding :=
  let _ := compile_get_binding in
  first [ compile_custom | compile_basics ].

Ltac compile_triple :=
  lazymatch goal with
  | [  |- WeakestPrecondition.cmd _ _ _ _ _ _ ] =>
    try clear_old_seps;
    (* Look for a binding: if there is none, finish compiling *)
    first [ compile_binding | compile_unify_post ]
  end.

Ltac compile_step :=
  first [ compile_cleanup |
          compile_triple |
          compile_unify_post |
          compile_solve_side_conditions ].

Ltac compile_done :=
  match goal with
  | [ _ := DefaultValue ?T ?t |- ?T ] => exact t
  | _ => idtac
  end.

(* only apply compile_step when repeat_compile_step solves all the side
     conditions but one *)
Ltac safe_compile_step :=        (* TODO try to change compile_step so that it's always safe? *)
  compile_step; [ solve [repeat compile_step] .. | ].

(* TODO: Use unshelve + eauto with compile_custom + shelve instead of compile_custom *)
(* TODO find the way to preserve the name of the binder in ‘k’ instead of renaming everything to ‘v’ *)

Ltac compile :=
  compile_setup; repeat compile_step; compile_done.
