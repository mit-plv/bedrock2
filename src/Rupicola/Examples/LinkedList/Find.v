Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.SepLocals.
Require Import Rupicola.Lib.ControlFlow.DownTo.
Require Import Rupicola.Examples.LinkedList.LinkedList.

Section Gallina.
  (* returns the portion of the linked list headed by the first element x for
     which [f x = true]; if there is no such element, returns an empty list *)
  (* N.B. n should be the length of the list *)
  Definition ll_find
             {A} (d : A) (f : A -> bool) (ls : linkedlist A) (n : nat)
  : linkedlist A :=
    let/n p := ls in
    let/n x := downto p n
                      (fun p _ =>
                         let/n x := ll_hd d p in
                         let/n c := f x in
                         let/n p' := ll_next p in
                         let/n p := if c then p else p' in
                         p) in
  x.
End Gallina.

Section Compile.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  (* TODO: generalize *)
  Local Notation LinkedList :=
    (@LinkedList semantics word access_size.word scalar) (only parsing).
  Local Notation word_size_in_bytes :=
    (@Memory.bytes_per Semantics.width access_size.word).
  Local Notation next_word :=
    (fun p : address =>
       word.add p (word.of_Z (Z.of_nat word_size_in_bytes))).

  Lemma compile_if_pointer {tr mem locals functions} {data} (c: bool) (t f: data) :
    let v := if c then t else f in
    forall {P} {pred: P v -> predicate}
      {k: nlet_eq_k P v} {k_impl}
      (Data : Semantics.word -> data -> Semantics.mem -> Prop) Rt Rf
      t_var f_var t_ptr f_ptr c_var var,

      (Data t_ptr t * Rt)%sep mem ->
      (Data f_ptr f * Rf)%sep mem ->

      map.get locals c_var = Some (b2w c) ->
      map.get locals t_var = Some t_ptr ->
      map.get locals f_var = Some f_ptr ->

      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var (if c then t_ptr else f_ptr);
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.cond (expr.var c_var)
                  (cmd.set var (expr.var t_var))
                  (cmd.set var (expr.var f_var)))
        k_impl
      <{ pred (nlet_eq [var] v k) }>.
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

  Open Scope list_scope.
  Program Instance spec_of_ll_find : spec_of "ll_find" :=
    fnspec! "ll_find" (pll n: address) (k: word) /
          (end_ptr dummy : address) (ll : linkedlist word) R
          ~> px,
       { requires fns tr mem :=
           word.unsigned n = Z.of_nat (length ll) /\
           (0 < length ll)%nat /\ (* FIXME 0 < length is redundant *)
           (LinkedList end_ptr pll ll ⋆ R) mem;
         ensures tr' mem' :=
           let result := ll_find dummy (word.eqb k) ll (length ll) in
           exists ll1, tr = tr' /\ ll = (ll1 ++ result) /\
                  (LinkedList px pll ll1 * LinkedList end_ptr px result * R)%sep mem' }.

  Definition downto_inv
             R
             tr0
             (ll : linkedlist word)
             (x end_ptr pll : address)
             (x_var p_var : string)
             (i : nat)
             (gst : linkedlist word)
             (st : linkedlist word)
    : predicate :=
    fun tr mem locals =>
      let ll1 := gst in
      exists p,
        tr = tr0
        /\ i <= length st
        /\ ll = (gst ++ st)%list
        /\ map.get locals x_var = Some x
        /\ map.get locals p_var = Some p
        /\ (LinkedList p pll ll1 * LinkedList end_ptr p st * R)%sep mem.

  Derive ll_find_body SuchThat
         (defn! "ll_find"("pll", "n", "k") ~> "p" { ll_find_body },
          implements @ll_find)
         As ll_find_body_correct.
  Proof.
    compile_setup.
    cleanup.

    simple eapply compile_nlet_as_nlet_eq.
    simple eapply compile_copy_pointer;
      repeat compile_step.

    simple eapply compile_nlet_as_nlet_eq.
    simple eapply compile_downto
      with
        (ginit := [])
        (i_var := "n")
        (ghost_step :=
           fun st gst _ =>
             if (word.eqb k (ll_hd dummy st))
             then gst else (gst ++ [ll_hd dummy st])%list)
        (Inv := downto_inv R tr ll k end_ptr pll "k" "p").

    all:lazymatch goal with
        | |- context [WeakestPrecondition.cmd] => idtac
        | |- context[@downto_inv] =>
          eexists;
            cbn [LinkedList.LinkedList]; sepsimpl;
              repeat apply conj; subst_lets_in_goal
        | _ => idtac
        end.
    all:lazymatch goal with
        | |- context [WeakestPrecondition.cmd] => idtac
        | |- sep _ _ _ => ecancel_assumption
        | |- map.get _ _ = Some _ =>
          subst_lets_in_goal; try push_map_remove;
            autorewrite with mapsimpl; try reflexivity
        | _ => solve [eauto]
        end.

    { (* compile loop body *)
      intros. clear_old_seps.
      cbv [downto_inv] in H3.
      sepsimpl_hyps. cleanup; subst.

      repeat match goal with
             | H : map.get (map.remove _ _) _ = _ |- _ =>
               rewrite map.get_remove_diff in H
                 by (subst_lets_in_goal; congruence)
             end.
      assert (st = ll_hd dummy st :: ll_next st)
        as Hcons by
            (apply (ll_hd_next_eq st dummy);
             destruct st; cbn [length] in *; congruence || lia).
      rewrite Hcons in *.
      cbn [LinkedList] in *|-.

      match goal with
      | H : sep (sep ?p ?q) _ _ |- _ =>
        (* reverse order and try simplifying again *)
        eapply (sep_assoc p q) in H
      end.
      sepsimpl_hyps. (* FIXME this should not need the explicit sep_assoc above  *)
      cbn beta iota delta [ll_hd hd ll_next tl].

      (* FIXME use an explicit map in the invariant *)
      Ltac map_t :=
        repeat first [ rewrite map.get_put_same; reflexivity |
                       rewrite map.get_put_diff  |
                       rewrite map.get_remove_diff]; (eassumption || congruence).

      simple apply compile_nlet_as_nlet_eq.
      simple eapply compile_ll_hd with (ll_var := "p").
      all:lazymatch goal with
          | |- sep _ _ _ =>
            cbn [ll_hd hd ll_next tl]; ecancel_assumption
          | _ => idtac
          end.
      1: map_t.

      intros. clear_old_seps.
      compile_step.

      1,2: map_t.

      gen_sym_inc.
      eapply compile_nlet_as_nlet_eq;
      eapply compile_ll_next;
        [ repeat compile_step .. | ];
        [ try solve [repeat compile_step] .. | ].
      map_t.

      eapply compile_nlet_as_nlet_eq.
      eapply compile_if_pointer;
        try ecancel_assumption.
      { cbn [LinkedList].
        cbn [ll_hd hd ll_next tl] in *.
        sepsimpl. lift_eexists.
        ecancel_assumption. }
      all: try map_t.

      compile_step.
      (* unset loop-local variables *)
      (* FIXME remove_unused_vars does not work here. *)
      (* repeat remove_unused_var. *)

      compile_unset_and_skip;
        [ instantiate (1 := []); simpl | .. ].

      all: try (simpl; map_t).

      { red; repeat compile_cleanup_post.
        lift_eexists; sepsimpl; subst_lets_in_goal.
        { destruct_one_match; cbn [length] in *; lia. }
        { rewrite Hcons;
          destruct_one_match;
            try rewrite <-app_assoc; reflexivity. }
        { simpl;
          repeat first [ rewrite map.get_remove_diff by congruence
                       | autorewrite with mapsimpl ].
          eauto. }
        { simpl.
          repeat first [ rewrite map.get_remove_diff by congruence
                       | autorewrite with mapsimpl ].
          reflexivity. }
        { destruct_one_match.
          all:cbn [LinkedList]; sepsimpl.
          { eapply sep_assoc.
            eapply sep_comm.
            eapply sep_assoc.
            eapply sep_ex1_l.
            lift_eexists.
            ecancel_assumption. }
          { seprewrite @LinkedList_snoc_iff1.
            sepsimpl. lift_eexists; sepsimpl.
            ecancel_assumption. } } } }

    { intros.
      cbv [downto_inv] in *. sepsimpl_hyps.
      repeat match goal with H : map.get (map.remove _ _) _ = _ |- _ =>
                             rewrite map.get_remove_diff in H
                               by (subst_lets_in_goal; congruence)
             end.

      (* TODO: make compile_done try to solve the map.getmany_of_list goal *)
      eapply compile_skip.
      red; repeat compile_cleanup_post.

      { cbn; rewrite H8. reflexivity. }
      all: eauto. }
  Qed.
End Compile.
