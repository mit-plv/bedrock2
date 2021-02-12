Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.
Require Export Rupicola.Lib.Gensym.
Require Import Rupicola.Lib.Tactics.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok _}.

  Lemma compile_nlet_as_nlet_eq {tr mem locals functions} {A} (v: A):
    forall {T} {pred: T -> predicate} {k: A -> T}
      vars cmd,
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd
      <{ pred (nlet_eq (P := fun _ => T) vars v (fun x _ => k x)) }> ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd
      <{ pred (nlet vars v k) }>.
  Proof. intros; assumption. Qed.

  Lemma compile_skip {tr mem locals functions} {pred0: predicate} :
    pred0 tr mem locals ->
    (<{ Trace := tr;
        Memory := mem;
        Locals := locals;
        Functions := functions }>
     cmd.skip
     <{ pred0 }>).
  Proof. repeat straightline; assumption. Qed.

  Lemma compile_seq {tr mem locals functions} :
    forall {pred0 pred1: predicate} {c0 c1},
      (<{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       c0
       <{ pred0 }>) ->
      (forall tr mem locals,
         pred0 tr mem locals ->
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       c1
       <{ pred1 }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq c0 c1
      <{ pred1 }>.
  Proof. intros; eapply WeakestPrecondition_weaken; eauto. Qed.

  Lemma compile_word_of_Z_constant {tr mem locals functions} (z: Z) :
    let v := word.of_Z z in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      var,
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal z)) k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof. repeat straightline; eassumption. Qed.

  Lemma compile_Z_constant {tr mem locals functions} z :
    let v := z in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      var,
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (word.of_Z v);
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal z)) k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof. repeat straightline; eassumption. Qed.

  Lemma compile_nat_constant {tr mem locals functions} n :
    let v := n in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      var,
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (word.of_Z (Z.of_nat v));
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal (Z.of_nat n))) k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof. repeat straightline; eassumption. Qed.

  Notation b2w b :=
    (word.of_Z (Z.b2z b)).

  Lemma compile_bool_constant {tr mem locals functions} b :
    let v := b in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      var,
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (b2w v);
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.literal (Z.b2z v))) k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof. repeat straightline; eassumption. Qed.

  (* FIXME generalize *)
  Lemma compile_xorb {tr mem locals functions} x y :
    let v := xorb x y in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      x_var y_var var,
      map.get locals x_var = Some (b2w x) ->
      map.get locals y_var = Some (b2w y) ->
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (b2w v);
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.op bopname.xor (expr.var x_var) (expr.var y_var)))
              k_impl
      <{ pred (k v eq_refl) }>.
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

  Lemma compile_add {tr mem locals functions} x y :
    let v := word.add x y in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} k_impl
      x_var y_var var,
      map.get locals x_var = Some x ->
      map.get locals y_var = Some y ->
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.op bopname.add (expr.var x_var) (expr.var y_var)))
              k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof.
    repeat straightline.
    eexists; split; eauto.
    repeat straightline.
    eexists; split; eauto.
    repeat straightline.
    eexists; split; eauto.
  Qed.

  Lemma compile_eqb {tr mem locals functions} x y :
    let v := word.eqb x y in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} k_impl
      x_var y_var var,
      map.get locals x_var = Some x ->
      map.get locals y_var = Some y ->
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (b2w v);
          Functions := functions }>
       k_impl
       <{ pred (nlet_eq [var] v k) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.op bopname.eq (expr.var x_var) (expr.var y_var)))
              k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof.
    intros. repeat straightline'.
    subst_lets_in_goal.
    remember (word.eqb x y) as b in *.
    rewrite word.unsigned_eqb in Heqb; subst b.
    cbv [Z.b2z] in *; destruct_one_match; eauto.
  Qed.

  (* TODO: make more types *)
  Lemma compile_copy_local {tr mem locals functions} v0 :
    let v := v0 in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      src_var dst_var,
      map.get locals src_var = Some v0 ->
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals dst_var v;
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set dst_var (expr.var src_var)) k_impl
      <{ pred (nlet_eq [dst_var] v k) }>.
  Proof.
    repeat straightline'; eauto.
  Qed.

  Lemma compile_sig_as_nlet_eq {tr mem locals functions} {A} P0 (x0: A) Px0:
    let v := exist P0 x0 Px0 in
    forall {T} {pred: T -> predicate} {k: {x: A | P0 x} -> T}
      vars cmd,
      (let Px := Px0 in
       let cast {x0'} Heq := eq_rect_r (fun x => P0 x) Px Heq in
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       cmd
       <{ pred (nlet_eq (P := fun _ => T) vars x0
                        (fun x0' Heq => k (exist P0 x0' (cast Heq)))) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd
      <{ pred (nlet vars v k) }>.
  Proof. eauto. Qed.

  (* FIXME check out what happens when running straightline on a triple with a cmd.seq; could we get rid of the continuation arguments?  Would it require more rewrites? *)

  (* N.B. this should *not* be added to any compilation tactics, since it will
     always apply; it needs to be applied manually *)
  Lemma compile_unset {tr mem locals functions} :
    forall {pred0: predicate}
      var cmd,
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

  Definition DefaultValue (T: Type) (t: T) := T.

  Lemma compile_unsets {tr mem locals functions}
        {pred0: predicate} :
    forall (vars: DefaultValue (list string) []) cmd,
      (<{ Trace := tr;
          Memory := mem;
          Locals := map.remove_many locals vars;
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

  (* FIXME find a way to automate the application of these two lemmas *)
  (* N.B. should only be added to compilation tactics that solve their subgoals,
     since this applies to any shape of goal *)
  Lemma compile_copy_pointer {tr mem locals functions} {data} (x: data) :
    let v := x in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      (Data : Semantics.word -> data -> Semantics.mem -> Prop) R
      x_var x_ptr var,

      (* This assumption is used to drive the compiler, but it's not used by the proof *)
      (Data x_ptr x * R)%sep mem ->
      map.get locals x_var = Some x_ptr ->

      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var x_ptr;
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.var x_var)) k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof.
    intros.
    repeat straightline'.
    eassumption.
  Qed.

  Lemma compile_if {tr mem locals functions} (c: bool) {A} (t f: A) :
    let v := if c then t else f in
    forall {P} {pred: P v -> predicate} {val_pred: A -> predicate}
      {k: nlet_eq_k P v} {k_impl t_impl f_impl}
      c_var vars,

      map.get locals c_var = Some (b2w c) ->

      (let v := v in
       c = true ->
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       t_impl
       <{ val_pred t }>) ->
      (let v := v in
       c = false ->
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       f_impl
       <{ val_pred f }>) ->
      (let v := v in
       forall tr mem locals,
         val_pred v tr mem locals ->
       <{ Trace := tr;
          Memory := mem;
          Locals := locals;
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.cond (expr.var c_var) t_impl f_impl)
        k_impl
      <{ pred (nlet_eq vars v k) }>.
  Proof.
    intros * Hc Ht Hf Hk.
    repeat straightline'.
    split_if ltac:(repeat straightline'); subst_lets_in_goal.
    all: rewrite word.unsigned_of_Z_b2z; cbv [Z.b2z].
    all: destruct_one_match; try congruence; [ ]; intros.
    all: eapply compile_seq; eauto.
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

    Lemma noskips_correct:
      forall cmd {tr mem locals functions} post,
        WeakestPrecondition.program functions
          (noskips cmd) tr mem locals post <->
        WeakestPrecondition.program functions
          cmd tr mem locals post.
    Proof.
      split; revert tr mem locals post.
      all: induction cmd;
        repeat match goal with
               | _ => eassumption
               | _ => apply IHcmd
               | [ H: _ /\ _ |- _ ] => destruct H
               | [  |- _ /\ _ ] => split
               | [ H: forall v t m l, ?P v t m l -> exists _, _ |- ?P _ _ _ _ -> _ ] =>
                 let h := fresh in intros h; specialize (H _ _ _ _ h)
               | [ H: exists _, _ |- _ ] => destruct H
               | [  |- exists _, _ ] => eexists
               | [ H: context[WeakestPrecondition.cmd] |- context[WeakestPrecondition.cmd] ] => solve [eapply H; eauto]
               | _ => unfold WeakestPrecondition.program in * || cbn || intros ? || eauto
               end.

      all: destruct (is_skip (noskips cmd1)) eqn:H1;
        [ apply is_skip_sound in H1; rewrite H1 in * |
          apply is_skip_complete in H1;
           (destruct (is_skip (noskips cmd2)) eqn:H2;
            [ apply is_skip_sound in H2; rewrite H2 in * |
              apply is_skip_complete in H2 ]) ].

      - apply IHcmd1, IHcmd2; eassumption.
      - eapply WeakestPrecondition_weaken, IHcmd1; eauto.
      - eapply WeakestPrecondition_weaken.
        * intros * H0. eapply IHcmd2. apply H0.
        * eapply IHcmd1. eassumption.

      - eapply IHcmd1 in H. eapply IHcmd2. eassumption.
      - eapply IHcmd1 in H. eapply WeakestPrecondition_weaken in H; [ apply H |].
        intros; eapply IHcmd2; eauto.
      - apply IHcmd1 in H. eapply WeakestPrecondition_weaken in H; [ apply H |].
        intros * H0%IHcmd2. apply H0.
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
  apply noskips_correct;
  unfold WeakestPrecondition.program.

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

Ltac map_to_list m :=
  let rec loop m acc :=
      match m with
      | map.put ?m ?k ?v =>
        loop m uconstr:((k, v) :: acc)
      | map.empty =>
        (* Reverse for compatibility with map.of_list *)
        uconstr:(List.rev acc)
      end in
  loop m uconstr:([]).

Ltac solve_map_remove_many_reify  :=
  lazymatch goal with
  | [  |- map.remove_many ?m0 _ = ?m1 ] =>
    let b0 := map_to_list m0 in
    let b1 := map_to_list m1 in
    change m0 with (map.of_list b0);
    change m1 with (map.of_list b1)
  end.

Ltac solve_map_remove_many :=
  solve_map_remove_many_reify;
  apply map.remove_many_diff;
  [ try (vm_compute; reflexivity) | try reflexivity ].

Create HintDb compiler.
Hint Unfold postcondition_cmd : compiler.

Ltac compile_find_post :=
  lazymatch goal with
  | |- WeakestPrecondition.cmd _ _ _ _ _ (?pred ?term) =>
    constr:((pred, term))
  end.

Class IsRupicolaBinding {T} (t: T) := is_rupicola_binding: bool.
Hint Extern 2 (IsRupicolaBinding (nlet _ _ _)) => exact true : typeclass_instances.
Hint Extern 2 (IsRupicolaBinding (nlet_eq _ _ _)) => exact true : typeclass_instances.
Hint Extern 2 (IsRupicolaBinding (dlet _ _)) => exact true : typeclass_instances.
Hint Extern 5 (IsRupicolaBinding _) => exact false : typeclass_instances.

Ltac is_rupicola_binding term :=
  constr:(match tt return IsRupicolaBinding term with _ => _ end).

Ltac compile_unfold_head_binder' hd :=
  (** Use `compile_unfold_head_binding` for debugging **)
  lazymatch compile_find_post with
  | (?pred, ?x0) => (* FIXME should just unfold x in all cases that report isunifiable, but that does too much *)
    lazymatch goal with
    | [  |- context C [pred x0] ] =>
      match is_rupicola_binding x0 with
      | true =>
        let x0 := unfold_head x0 in
        let C' := context C [pred x0] in
        change C'
      | false => fail 0 x0 "does not look like a let-binding"
      end
    end
  end.

(* Useful for debugging *)
Ltac compile_unfold_head_binder :=
  let p := compile_find_post in
  compile_unfold_head_binder' p.

(* Using [simple apply] ensures that Coq doesn't peek past the first binding [nlet]s *)
Ltac compile_basics :=
  gen_sym_inc;                  (* FIXME remove? *)
  let name := gen_sym_fetch "v" in
  try simple apply compile_nlet_as_nlet_eq;
  first [simple eapply compile_word_of_Z_constant |
         simple eapply compile_Z_constant |
         simple eapply compile_nat_constant |
         simple eapply compile_bool_constant |
         simple eapply compile_xorb |
         simple eapply compile_add |
         simple eapply compile_eqb |
         simple eapply compile_if ].

Ltac compile_custom := fail.

Ltac compile_cleanup :=
  match goal with
  | [ H: _ /\ _ |- _ ] => destruct H
  | [ H: ?x = _ |- _ ] => is_var x; subst x
  | [ H: match ?x with _ => _ end |- _ ] => destruct x; [ idtac ]
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
  | [  |- map.getmany_of_list _ _ = _ ] =>
    apply map.getmany_of_list_cons
  | [  |- map.remove_many _ _ = _ ] =>
    solve_map_remove_many
  | [  |- _ <> _ ] => congruence
  | _ =>
    first [ compile_cleanup
          | solve [eauto with compiler] ]
  end.

Ltac compile_binding :=
  first [ compile_custom | compile_basics ].

Ltac compile_triple :=
  lazymatch compile_find_post with
  | (_, ?hd) =>
    try clear_old_seps;
    (* Look for a binding: if there is none, finish compiling *)
    match is_rupicola_binding hd with
    | true => compile_binding
    | false => compile_unify_post
    end
  end.

Ltac compile_step :=
  first [ compile_cleanup |
          compile_triple |
          compile_solve_side_conditions ].

Ltac compile_done :=
  match goal with
  | [ |- DefaultValue ?T ?t ] => exact t
  | _ =>
    idtac "Compilation incomplete.";
    idtac "You may need to add new compilation lemmas to `compile_custom` or new `Hint Extern`s for `IsRupicolaBinding` to `typeclass_instances`."
  end.

(* only apply compile_step when repeat_compile_step solves all the side
     conditions but one *)
Ltac safe_compile_step :=        (* TODO try to change compile_step so that it's always safe? *)
  compile_step; [ solve [repeat compile_step] .. | ].

(* TODO: Use unshelve + eauto with compile_custom + shelve instead of compile_custom *)
(* TODO find the way to preserve the name of the binder in ‘k’ instead of renaming everything to ‘v’ *)

Ltac compile :=
  compile_setup; repeat compile_step; compile_done.
