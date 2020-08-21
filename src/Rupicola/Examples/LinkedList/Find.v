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
    let/d p := ls in
    let/d x := downto p n
                      (fun st _ =>
                         let/d x := ll_hd d st in
                         let/d c := f x in
                         let/d p := ll_next st in
                         let/d st' := if c then st else p in
                         st') in
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

  Definition LLFindResult
             (end_ptr pll : address)
             (ll : linkedlist word) (x : word)
             (result : linkedlist word)
             (rets : list word)
    : Semantics.mem -> Prop :=
    liftexists px ll1,
    (emp (rets = [px]
          /\ ll = (ll1 ++ result)%list)
     * LinkedList px pll ll1
     * LinkedList end_ptr px result)%sep.

  Instance spec_of_ll_find : spec_of "ll_find" :=
    (forall! (end_ptr pll : address) (ll : linkedlist word)
           (n x dummy : word),
        (sep (emp (word.unsigned n = Z.of_nat (length ll)
                   /\ 0 < length ll)
              * LinkedList end_ptr pll ll)%sep)
          ===>
          "ll_find" @ [pll; n; x] returns rets
          ===>
          LLFindResult
            end_ptr pll ll x
            (ll_find dummy (word.eqb x) ll (length ll)) rets).

  Definition downto_inv
             (ll : linkedlist word)
             (x end_ptr pll : address)
             (x_var p_var : string)
             (locals : Semantics.locals)
             (i : nat)
             (gst : linkedlist word)
             (st : linkedlist word)
             (_ : list word) (* TODO: use this? *)
    : Semantics.mem -> Prop :=
    let ll1 := gst in
    liftexists p,
    (emp (i <= length st
          /\ ll = (gst ++ st)%list
          /\ map.get locals x_var = Some x
          /\ map.get locals p_var = Some p)
     * LinkedList p pll ll1 * LinkedList end_ptr p st)%sep.

  Derive ll_find_body SuchThat
         (let args := ["pll"; "n"; "x"] in
          let rets := ["p"] in
          let ll_find := ("ll_find", (args, rets, ll_find_body)) in
          program_logic_goal_for
            ll_find
            (ltac:(let x := program_logic_goal_for_function
                              ll_find (@nil string) in
                   exact x)))
         As ll_find_body_correct.
  Proof.
    cbv [spec_of_ll_find].
    setup. sepsimpl.
    pose (p_var := "p").
    pose (n_var := "n").
    pose (x_var := "x").
    simple eapply compile_pointer with (var:=p_var);
      [ solve [compile_step] .. | ].
    compile_step.

    let x_var := (eval hnf in x_var) in
    let x := match goal with |- context [map.put _ x_var ?x] => x end in
    simple eapply compile_downto
      with
        (ginit := [])
        (i_var := n_var)
        (ghost_step :=
           fun st gst _ =>
             if (word.eqb x (ll_hd dummy st))
             then gst else (gst ++ [ll_hd dummy st])%list)
        (Inv := downto_inv ll x end_ptr pll x_var p_var).
    all:lazymatch goal with
        | |- word.unsigned _ = Z.of_nat _ => solve [eauto]
        | |- context [WeakestPrecondition.cmd] => idtac
        | |- sep _ _ _ =>
          cbv [downto_inv];
            cbn [fst snd List.app LinkedList];
            lift_eexists; sepsimpl
        | _ => idtac
        end.
    all:lazymatch goal with
        | |- sep _ _ _ => ecancel_assumption
        | _ => idtac
        end.
    all:lazymatch goal with
        | |- context [WeakestPrecondition.cmd] => idtac
        | |- _ <> [] =>
          subst_lets_in_goal; rewrite <-length_zero_iff_nil; lia
        | |- ?x = ?x => reflexivity
        | |- map.get _ _ = Some _ =>
          subst_lets_in_goal; try push_map_remove;
            autorewrite with mapsimpl; try reflexivity
        | _ => solve [eauto]
        end.

    { (* compile loop body *)
      intros. clear_old_seps.
      cbv [downto_inv] in *|-.
      sepsimpl_hyps. cleanup; subst.

      repeat match goal with H : map.get (map.remove _ _) _ = _ |- _ =>
                             rewrite map.get_remove_diff in H
                               by (subst_lets_in_goal; congruence)
             end.
      match goal with
      | H : _ <= length ?st,
            Hll : context [LinkedList.LinkedList _ _ ?st] |- _ =>
        rewrite (ll_hd_next_eq st dummy) in *
          by (destruct st; cbn [length] in H; congruence || lia)
      end.
      cbn [LinkedList] in *|-.
      sepsimpl_hyps.
      cbn beta iota delta [ll_hd hd ll_next tl].

      eexists; intros.

      gen_sym_inc.
      let v := gen_sym_fetch "v" in
      simple eapply compile_ll_hd with (var:=v).
      all:lazymatch goal with
          | |- sep _ _ _ =>
            cbn [ll_hd hd ll_next tl]; ecancel_assumption
          | _ => idtac
          end.
      all:lazymatch goal with
          | |- context [WeakestPrecondition.cmd] => idtac
          | _ => solve [compile_step]
          end.

      intros. clear_old_seps.

      repeat safe_compile_step.

      gen_sym_inc.
      let v := gen_sym_fetch "v" in
      simple eapply compile_ll_next with (var:=v);
        [ repeat compile_step .. | ];
        [ try solve [repeat compile_step] .. | ].
      repeat safe_compile_step.

      simple eapply compile_if_pointer with (var:="p");
        try ecancel_assumption.
      { cbn [LinkedList].
        cbn [ll_hd hd ll_next tl] in *.
        sepsimpl. lift_eexists.
        ecancel_assumption. }
      all:lazymatch goal with
          | |- context [WeakestPrecondition.cmd] => idtac
          | _ => solve [compile_step]
          end.

      repeat safe_compile_step.

      (* unset loop-local variables *)
      repeat remove_unused_var.

      compile_done.
      { subst_lets_in_goal.
        autorewrite with mapsimpl.
        ssplit; reflexivity. }
      { cbv [downto_inv].
        lift_eexists; sepsimpl; subst_lets_in_goal.
        { destruct_one_match; cbn [length] in *; lia. }
        { destruct_one_match;
            try rewrite <-app_assoc; reflexivity. }
        { rewrite map.get_remove_diff by congruence.
          autorewrite with mapsimpl. eauto. }
        { rewrite map.get_remove_diff by congruence.
          autorewrite with mapsimpl. eauto. }
        { destruct_one_match.
          all:cbn [LinkedList]; sepsimpl.
          { lift_eexists; ecancel_assumption. }
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
      compile_done;
        [ subst p_var; eapply map.getmany_of_list_cons;
          eauto; reflexivity | ].
      cbv [LLFindResult].
      lift_eexists; sepsimpl;
        lazymatch goal with
        | |- sep _ _ _ => ecancel_assumption
        | _ => idtac
        end.
      all:eauto. }
  Qed.
End Compile.
