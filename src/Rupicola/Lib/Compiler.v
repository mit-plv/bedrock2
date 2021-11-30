Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.
Require Import Rupicola.Lib.Tactics.

Section CompilerBasics.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {memT: map.map word Byte.byte}.
  Context {localsT: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok memT}.
  Context {locals_ok : map.ok localsT}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Lemma compile_dlet_as_nlet_eq {tr mem locals functions} {A} {vars: list string} (v: A):
    forall {T} {pred: T -> predicate} {k: A -> T} {cmd},
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
      <{ pred (dlet v k) }>.
  Proof. intros; assumption. Qed.

  Lemma compile_nlet_as_nlet_eq {tr mem locals functions} {A} (v: A):
    forall {T} {pred: T -> predicate} {k: A -> T} {cmd}
      vars,
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

  Lemma compile_nested_nlet {tr mem locals functions} {A T1} vs1 (v0: A) (k1: A -> T1):
    let v := nlet vs1 v0 k1 in
    forall {T2} {pred: T2 -> predicate}
      {k2: T1 -> T2} {cmd}
      vs2,
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd
      <{ pred (nlet vs1 v0 (fun v => nlet vs2 (k1 v) k2)) }> ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd
      <{ pred (nlet vs2 v k2) }>.
  Proof. intros; assumption. Qed.

  Lemma compile_nlet_push_continuation {tr mem locals functions} {A B B'} vs1 (f: B -> B') (v1: A) (k1: A -> B):
    let v := f (nlet vs1 v1 k1) in
    forall {pred: B' -> predicate} {cmd},
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd
      <{ pred (nlet vs1 v1 (fun v1 => f (k1 v1))) }> ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd
      <{ pred (f (nlet vs1 v1 k1)) }>.
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

  (* FIXME find a way to automate the application of these copy lemmas *)
  (* N.B. should only be added to compilation tactics that solve their subgoals,
     since this applies to any shape of goal *)
  Lemma compile_copy_pointer {tr mem locals functions} {data} (x: data) :
    let v := x in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      (Data : word -> data -> memT -> Prop) R
      x_expr x_ptr var,

      (* This assumption is used to drive the compiler, but it's not used by the proof *)
      (Data x_ptr x * R)%sep mem ->
      WeakestPrecondition.dexpr mem locals x_expr x_ptr ->

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
      cmd.seq (cmd.set var x_expr) k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof.
    intros.
    repeat straightline'.
    eauto.
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
End CompilerBasics.

Section with_parameters.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {memT: map.map word Byte.byte}.
  Context {localsT: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok memT}.
  Context {locals_ok : map.ok localsT}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

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

    Definition compile_setup_remove_skips := noskips_correct.

    (*Important for Qed performance on certain derivations,
      since it stops noskips from being unfolded.
      Originally added for fiat-crypto/src/Bedrock/Group/ScalarMult/Ladderstep.v.
     *)
    Strategy 1 [noskips is_skip].
  End NoSkips.

  Section NoReassign.
    Definition is_var_expr e v : bool:=
      match e with
      | expr.var v' => String.eqb v v'
      | _ => false
      end.

    Lemma is_var_expr_spec e v:
      BoolSpec (e = expr.var v) (e <> expr.var v) (is_var_expr e v).
    Proof.
      destruct e; simpl; try (constructor; congruence); [].
      destruct (String.eqb_spec v x); constructor; congruence.
    Qed.

    Fixpoint noreassign (c: cmd.cmd) :=
      match c with
      | cmd.stackalloc lhs nbytes body =>
        cmd.stackalloc lhs nbytes (noreassign body)
      | cmd.cond condition nonzero_branch zero_branch =>
        cmd.cond condition (noreassign nonzero_branch) (noreassign zero_branch)
      | cmd.seq s1 s2 =>
        cmd.seq (noreassign s1) (noreassign s2)
      | cmd.while test body =>
        cmd.while test (noreassign body)
      | cmd.set v e =>
        if is_var_expr e v then cmd.skip else c
      | _ => c
      end.

    Lemma noreassign_correct:
      forall cmd {tr mem locals functions} post,
        WeakestPrecondition.program functions
          cmd tr mem locals post ->
        WeakestPrecondition.program functions
          (noreassign cmd) tr mem locals post.
    Proof.
      all: induction cmd;
        repeat match goal with
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

      - destruct (is_var_expr_spec rhs lhs); simpl in *; subst; eauto; [].
        destruct H as (xx & Hxx & ->).
        rewrite map.put_idemp in H0; assumption.
      - eapply WeakestPrecondition_weaken, IHcmd1; eauto;
          intros; eapply WeakestPrecondition_weaken, IHcmd2; eauto.
    Qed.

    Definition compile_setup_remove_reassigns := noreassign_correct.
    Strategy 1 [noreassign is_var_expr].
  End NoReassign.
End with_parameters.

Section with_parameters.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {memT: map.map word Byte.byte}.
  Context {localsT: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok memT}.
  Context {locals_ok : map.ok localsT}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Section Setup.
    Lemma compile_setup_getmany_list_map {tr mem locals functions} :
      forall P {cmd} retvars,
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd
        <{ wp_bind_retvars retvars P }> ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd
        <{ fun tr' mem' locals' =>
             WeakestPrecondition.list_map
               (WeakestPrecondition.get locals') retvars
               (fun ws => P ws tr' mem' locals') }>.
    Proof.
      intros; eapply WeakestPrecondition_weaken; try eassumption.
      clear; firstorder eauto using getmany_list_map.
    Qed.

    Lemma compile_setup_WeakestPrecondition_call_first {tr mem locals}
          name argnames retvars body args functions post:
      map.of_list_zip argnames args = Some locals ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      body
      <{ wp_bind_retvars
           retvars
           (fun rets tr' mem' local' => post tr' mem' rets)  }> ->
      WeakestPrecondition.call
        ((name, (argnames, retvars, body)) :: functions)
        name tr mem args post.
    Proof.
      intros; WeakestPrecondition.unfold1_call_goal.
      red. rewrite String.eqb_refl.
      red. eexists; split; eauto.
      eapply WeakestPrecondition_weaken; try eassumption.
      clear; firstorder eauto using getmany_list_map.
    Qed.

    Lemma compile_setup_postcondition_func_noret
          {T} spec (x: T) cmd R tr mem locals functions :
      (let pred a := postcondition_cmd (fun _ : localsT => True) (spec a) [] R tr in
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
      <{ wp_bind_retvars
           []
           (fun rets tr' m' _ =>
              postcondition_func_norets (spec x) R tr tr' m' rets) }>.
    Proof.
      cbv [postcondition_func_norets
             postcondition_func postcondition_cmd]; intros.
      use_hyp_with_matching_cmd;
        cbn in *; intros; exists []; sepsimpl; subst; eauto.
    Qed.

    Lemma compile_setup_postcondition_func
          {T} spec (x: T) cmd R tr mem locals retvars functions :
      (let pred a := postcondition_cmd (fun _ : localsT => True) (spec a) retvars R tr in
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
      <{ wp_bind_retvars
           retvars
           (fun rets tr' m' _ => postcondition_func (spec x) R tr tr' m' rets) }>.
    Proof.
      cbv [postcondition_func postcondition_cmd]; intros.
      use_hyp_with_matching_cmd; red; sepsimpl; subst; eauto.
    Qed.
  End Setup.
End with_parameters.

Ltac compile_find_post :=
  lazymatch goal with
  | |- WeakestPrecondition.cmd _ _ _ _ _ (?pred ?term) =>
    constr:((pred, term))
  end.

Ltac compile_setup_unfold_spec_of :=
  intros;
  match goal with
  | [  |- ?g ] =>
    let hd := term_head g in
    lazymatch type of hd with
    | spec_of _ => cbv [hd]; intros
    end
  | _ => idtac (* Spec inlined *)
  end.

Ltac compile_setup_find_app term head :=
  match constr:(Set) with
  | _ => find_app term head
  | _ => fail "Gallina program" head "not found in postcondition" term
  end.

Ltac compile_setup_isolate_gallina_program :=
  lazymatch goal with
  | [ _: __rupicola_program_marker ?prog |-
      WeakestPrecondition.cmd ?fns ?cmd ?tr ?mem ?locals ?post ] =>
    let gallina := compile_setup_find_app post prog in
    lazymatch (eval pattern gallina in post) with
    | ?pred ?gallina =>
      let nm := fresh "pred" in
      set pred as nm;
      change (WeakestPrecondition.cmd fns cmd tr mem locals (nm gallina))
    end
  | |- WeakestPrecondition.cmd _ _ _ _ _ (?pred ?spec) => idtac
  | _ => fail "Not sure which program is being compiled.  Expecting a WeakestPrecondition goal with a postcondition in the form (?pred gallina_spec)."
  end.

Ltac compile_setup_unfold_gallina_spec :=
  lazymatch compile_find_post with
  | (_, ?spec) => let hd := term_head spec in unfold hd
  end.

Create HintDb compiler_setup.
Create HintDb compiler_setup_post.
#[export] Hint Resolve compile_setup_postcondition_func : compiler_setup_post.
#[export] Hint Resolve compile_setup_postcondition_func_noret : compiler_setup_post.
#[export] Hint Extern 20 (WeakestPrecondition.cmd _ _ _ _ _ _) => shelve : compiler_setup_post.

Tactic Notation "step_with_db" ident(db) :=
  progress unshelve (typeclasses eauto 10 with db); shelve_unifiable.

Ltac compile_setup :=
  cbv [program_logic_goal_for];
  compile_setup_unfold_spec_of;
  eapply compile_setup_WeakestPrecondition_call_first;
  [ try reflexivity (* Arity check *)
  | repeat step_with_db compiler_setup;
    (step_with_db compiler_setup_post ||
     compile_setup_isolate_gallina_program); intros;
    compile_setup_unfold_gallina_spec;
    apply compile_setup_remove_reassigns;
    apply compile_setup_remove_skips;
    unfold WeakestPrecondition.program ].

Ltac lookup_variable m val :=
  lazymatch m with
  | map.put _ ?k val => constr:(k)
  | map.put ?m' _ _ => lookup_variable m' val
  end.

Ltac solve_map_get_goal_refl m :=
  reify_map m;
  apply map.get_of_str_list_assoc_impl;
  reflexivity.

Ltac solve_map_get_goal_step :=
  lazymatch goal with
  | [ H: map.extends ?m2 ?m1 |- map.get ?m2 ?k = Some ?v ] =>
    simple apply (fun p => @map.extends_get _ _ _ m1 m2 k v p H)
  | [  |- context[map.remove_many _ []] ] =>
    (* This comes from compile_unset with an empty list *)
    change (map.remove_many ?m []) with m
  | [  |- map.get ?m ?k = ?v ] =>
    tryif first [ has_evar k | has_evar m ] then
      lazymatch v with
      | Some ?val =>
        tryif has_evar val then fail 1 val "has evars" else
          first [ simple apply map.get_put_same | rewrite map.get_put_diff ]
      | None =>
        first [ simple apply map.get_empty | rewrite map.get_put_diff ]
      end
    else
      solve_map_get_goal_refl m
  | [  |- _ <> _ ] => congruence
  end.

Ltac solve_map_get_goal :=
  progress repeat solve_map_get_goal_step.

Ltac solve_map_remove_many_reify :=
  lazymatch goal with
  | [  |- map.remove_many ?m0 _ = ?m1 ] =>
    reify_map m0; reify_map m1
  end.

Ltac solve_map_remove_many :=
  solve_map_remove_many_reify;
  apply map.remove_many_diff_of_str_list;
  (* FIXME should this really run vm_compute? *)
  [ try (vm_compute; reflexivity) | try reflexivity ].

Ltac solve_map_eq_reify :=
  lazymatch goal with
  | [  |- ?m0 = ?m1 ] =>
    reify_map m0; reify_map m1
  end.

Ltac solve_map_eq :=
  solve_map_eq_reify;
  apply map.eq_of_str_list;
  reflexivity.

Create HintDb compiler_cleanup.
Hint Rewrite @word.of_Z_unsigned : compiler_cleanup.
Hint Rewrite @word.of_nat_to_nat_unsigned : compiler_cleanup.
Hint Rewrite @word.of_Z_of_nat_to_nat_unsigned : compiler_cleanup.
#[export] Hint Unfold cast : compiler_cleanup.
#[export] Hint Unfold Convertible_Z_nat : compiler_cleanup.
#[export] Hint Unfold Convertible_byte_nat : compiler_cleanup.
#[export] Hint Unfold Convertible_Fin_nat : compiler_cleanup.
#[export] Hint Unfold Convertible_word_nat : compiler_cleanup.

Inductive __DummyRelation : False -> False -> Prop :=
  __DummyConstructor : forall f: False, __DummyRelation f f.

Create HintDb compiler_cleanup_post. (* https://github.com/coq/coq/issues/14874 *)
Hint Rewrite __DummyConstructor : compiler_cleanup_post. (* Create the DB *)
#[export] Hint Unfold wp_bind_retvars : compiler_cleanup_post.
#[export] Hint Unfold wp_pure_bind_retvars : compiler_cleanup_post.
#[export] Hint Unfold postcondition_cmd : compiler_cleanup_post.

#[export] Hint Extern 2 (IsRupicolaBinding (nlet (A := ?A) ?vars _ _)) => exact (RupicolaBinding A vars) : typeclass_instances.
#[export] Hint Extern 2 (IsRupicolaBinding (nlet_eq (A := ?A) ?vars _ _)) => exact (RupicolaBinding A vars) : typeclass_instances.
#[export] Hint Extern 2 (IsRupicolaBinding (dlet (A := ?A) _ _)) => exact (RupicolaBinding A []) : typeclass_instances.
#[export] Hint Extern 5 (IsRupicolaBinding _) => exact NotARupicolaBinding : typeclass_instances.

Ltac is_rupicola_binding term :=
  constr:(match tt return IsRupicolaBinding term with _ => _ end).

Ltac compile_unfold_head_binder' hd :=
  (** Use `compile_unfold_head_binding` for debugging **)
  lazymatch compile_find_post with
  | (?pred, ?x0) => (* FIXME should just unfold x in all cases that report isunifiable, but that does too much *)
    lazymatch goal with
    | [  |- context C [pred x0] ] =>
      lazymatch is_rupicola_binding x0 with
      | RupicolaBinding _ _ =>
        let x0 := unfold_head x0 in
        let C' := context C [pred x0] in
        change C'
      | NotARupicolaBinding => fail 0 x0 "does not look like a let-binding"
      end
    end
  end.

(* Useful for debugging *)
Ltac compile_unfold_head_binder :=
  let p := compile_find_post in
  compile_unfold_head_binder' p.

Create HintDb compiler.
Create HintDb compiler_pull_binding.
#[export] Hint Extern 1 =>
  simple eapply compile_nested_nlet; shelve : compiler_pull_binding.
#[export] Hint Extern 1 =>
  simple eapply compile_nlet_push_continuation; shelve : compiler_pull_binding.

Ltac compile_binding :=
  (* We don't want to show users goals with nlet_eq, so compile_nlet_as_nlet_eq
     isn't in the ‘compiler’ hint db. *)
  try simple apply compile_nlet_as_nlet_eq;
  step_with_db compiler.

(* Use [simple eapply] (not eapply) if you add anything here, to ensure that Coq
   doesn't peek past the first [nlet]. *)
Ltac compile_custom := fail.

Tactic Notation "compile_autocleanup" "with" ident(db) :=
  progress (autorewrite with db in *;
            repeat autounfold with db in * ).

Ltac compile_cleanup :=
  match goal with
  | [ H: _ /\ _ |- _ ] => decompose [and] H; clear H
  | [ H: ?x = _ |- _ ] => is_var x; subst x
  | [ H: match ?x with _ => _ end |- _ ] => destruct x; [ idtac ]
  | [  |- let _ := _ in _ ] => intros
  | [  |- forall _, _ ] => intros
  end.

Ltac compile_cleanup_post :=
  match goal with
  | _ => compile_cleanup
  | _ => compile_autocleanup with compiler_cleanup_post
  | _ => step_with_db compiler_cleanup_post
  | _ => progress subst_lets_in_goal
  | [  |- True ] => exact I
  | [  |- _ /\ _ ] => split
  | [  |- _ = _ ] => reflexivity
  | [  |- exists _, _ ] => eexists
  end.

Ltac compile_unset_and_skip :=
  (* [unshelve] captures the list of variables to unset as a separate goal; it
     is resolved by unification or by compile_use_default_value. *)
  unshelve refine (compile_unsets _ _ _);  (* coq#13839 *)
  [ shelve (* cmd *) | intros (* vars *) | ]; cycle 1;
  [ (* triple *)
    simple apply compile_skip;
    repeat compile_cleanup_post | ].

Ltac compile_use_default_value :=
  lazymatch goal with
  | [ |- DefaultValue ?T ?t ] => exact t
  end.

Create HintDb compiler_side_conditions.
Hint Rewrite __DummyConstructor : compiler_side_conditions. (* Create the DB *)
Hint Rewrite Nat2Z.id Z2Nat.id
  using solve[typeclasses eauto with compiler_side_conditions lia]
  : compiler_cleanup.
#[export] Hint Resolve Nat2Z.is_nonneg : compiler_side_conditions.
#[export] Hint Resolve eq_refl : compiler_side_conditions. (* For typeclasses eauto *)

Create HintDb solve_map_get_goal.

(* FIXME most cases below could be folded into the database above *)
Ltac compile_solve_side_conditions :=
  match goal with
  | [  |- sep _ _ _ ] =>
      cbn [fst snd P2.car P2.cdr] in *;       (* FIXME generalize this? *)
      ecancel_assumption
  | [  |- map.get _ _ = _ ] =>
    solve [subst_lets_in_goal;
           autounfold with solve_map_get_goal;
           solve_map_get_goal]
  | [  |- map.getmany_of_list _ _ = _ ] =>
    apply map.getmany_of_list_cons
  | [  |- map.remove_many _ _ = _ ] =>
    solve_map_remove_many
  | [  |- eq (A := map.rep) _ _ ] =>
    solve_map_eq (* FIXME can this be unified with the previous case? *)
  | [  |- _ = _ ] => reflexivity
  | [  |- _ <> _ ] => congruence
  | [  |- _ /\ _ ] => split
  | _ =>
    first [ compile_use_default_value
          | compile_autocleanup with compiler_side_conditions
          | step_with_db compiler_side_conditions
          | typeclasses eauto (* for TC instances *)
          | solve [ eauto 2 with nocore ] ]
  end.

Ltac compile_triple :=
  let _ := compile_find_post in
  try clear_old_seps;
  (* Reorder `nlet`s before introducing `nlet_eq` and checking for bindings. *)
  repeat step_with_db compiler_pull_binding;
  lazymatch compile_find_post with
  | (_, ?hd) => (* Look for a binding: if there is none, finish compiling *)
    lazymatch is_rupicola_binding hd with
    | RupicolaBinding _ _ => first [compile_custom | compile_binding]
    | NotARupicolaBinding => compile_unset_and_skip
    end
  end.

Ltac compile_step :=
  first [ compile_cleanup |
          compile_autocleanup with compiler_cleanup |
          step_with_db compiler_cleanup |
          compile_triple |
          compile_solve_side_conditions ].

Ltac compile_done :=
  match goal with
  | _ =>
    idtac "Compilation incomplete.";
    idtac "You may need to add new compilation lemmas using `Hint Extern 1 => simple eapply … : compiler` or to tell Rupicola about your custom bindings using `Hint Extern 2 (IsRupicolaBinding (xlet (A := ?A) ?vars _ _)) => exact (RupicolaBinding A vars) : typeclass_instances`."
  end.

(* only apply compile_step when repeat_compile_step solves all the side
     conditions but one *)
Ltac safe_compile_step :=        (* TODO try to change compile_step so that it's always safe? *)
  compile_step; [ solve [repeat compile_step] .. | ].

(* TODO find the way to preserve the name of the binder in ‘k’ instead of renaming everything to ‘v’ *)

Ltac compile :=
  (* There are two repeats here because after compile_unsets we might try to
     solve some goals, fail, decide to unify the list of variables to unset with
     [], and at that point we want to try again. *)
  compile_setup; repeat repeat compile_step; compile_done.
