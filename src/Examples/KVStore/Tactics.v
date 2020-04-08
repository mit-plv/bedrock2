Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.letexists.
Require Import Rupicola.Examples.KVStore.KVStore.
Require Import Rupicola.Examples.KVStore.Properties.
Require bedrock2.ProgramLogic.

Ltac borrow_reserved :=
  match goal with
  | H : context [Reserved] |- _ =>
    seprewrite_in reserved_borrowed_iff1 H
  end.

Ltac unborrow_step Value :=
  match goal with
  | H : sep ?L ?R ?mem |- context [?mem] =>
    match type of H with
      context [?P (map.put ?m ?k (Borrowed ?px, ?x))] =>
      let F1 :=
          match (eval pattern
                      (P (map.put m k (Borrowed px, x))) in
                    (sep L R)) with ?f _ => f end in
      let F2 :=
          match (eval pattern (Value px x) in F1) with
            ?f _ => f end in
      let H' := fresh in
      assert (F2 (P (map.put m k (Reserved px, x))) (emp True) mem)
        as H' by (seprewrite reserved_borrowed_iff1;
                  ecancel_assumption);
      clear H; cbv beta in H'
    end
  | H : context [map.put (map.put _ _ (Borrowed ?px, ?x))
                         _ (Reserved ?py, ?y)] |- _ =>
    rewrite (map.put_put_diff_comm _ _ (Borrowed px, x)
                                   (Reserved py, y))
      in H by congruence
  end.
Ltac unborrow Value := progress (repeat unborrow_step Value).

Ltac unreserve_step :=
  match goal with
  | H : sep ?L ?R ?mem |- context [?mem] =>
    match type of H with
      context [?P (map.put ?m ?k (Reserved ?px, ?x))] =>
      let F1 :=
          match (eval pattern
                      (P (map.put m k (Reserved px, x))) in
                    (sep L R)) with ?f _ => f end in
      let H' := fresh in
      (* hacky because seprewrite doesn't do impl1 *)
      assert (F1 (P (map.put m k (Owned, x))) mem) as H'
          by (eapply Proper_sep_impl1;
              [ repeat
                  rewrite (sep_assoc (_ (map.put _ _ (Owned, _))));
                eapply Proper_sep_impl1;
                [ eapply reserved_owned_impl1 | reflexivity ]
              | reflexivity | ]; ecancel_assumption);
      clear H; cbv beta in H'
    end
  | H : context [map.put (map.put _ _ (Reserved ?px, ?x))
                         _ (Owned, ?y)] |- _ =>
    rewrite (map.put_put_diff_comm _ _ (Reserved px, x)
                                   (Owned, y))
      in H by congruence
  end.
Ltac unreserve := progress (repeat unreserve_step).

Ltac destruct_lists_of_known_length :=
  repeat match goal with
         | H : S _ = S _ |- _ => apply Nat.succ_inj in H
         | H : length ?x = S _ |- _ =>
           destruct x; cbn [length] in H; [ congruence | ]
         | H : length ?x = 0 |- _ =>
           destruct x; cbn [length] in H; [ clear H | congruence]
         end;
  cbn [hd tl] in *.

Ltac boolean_cleanup :=
  repeat match goal with
         | H : _ |- _ =>
           rewrite word.unsigned_of_Z_0 in H
         | H : _ |- _ =>
           rewrite word.unsigned_of_Z_1 in H
         | H : ?x = word.of_Z 0%Z |- _ => subst x
         | H : ?x = word.of_Z 1%Z |- _ => subst x
         | x := word.of_Z 0%Z |- _ => subst x
         | x := word.of_Z 1%Z |- _ => subst x
         | _ => congruence
         end.

Ltac clear_owned :=
  repeat match goal with
         | H : _ |- _ => rewrite put_owned_annotate in H
         | H : _ |- _ =>
           rewrite map.put_noop in H
             by (rewrite ?map.get_put_dec;
                 repeat match goal with
                          |- context [key_eqb ?a ?b] =>
                          destr.destr (key_eqb a b) end;
                 subst; congruence)
         end.

(* just a wrapper that calls straightline_call + straightline, and also
   destructs output lists *)
Ltac handle_call :=
  ProgramLogic.straightline_call; [ ecancel_assumption | ];
  repeat ProgramLogic.straightline;
  destruct_lists_of_known_length;
  repeat ProgramLogic.straightline.

(* stolen from a bedrock2 example file (LAN9250.v) *)
Ltac split_if :=
  lazymatch goal with
    |- WeakestPrecondition.cmd _ ?c _ _ _ ?post =>
    let c := eval hnf in c in
        lazymatch c with
        | Syntax.cmd.cond _ _ _ =>
          letexists; split;
          [solve[repeat ProgramLogic.straightline]|split]
        end
  end.

Ltac add_map_annotations :=
  match goal with
  | H : context [Map _ _] |- _ =>
    seprewrite_in annotate_iff1 H
  end.

Ltac remove_map_annotations :=
  clear_owned;
  repeat match goal with
         | H : ?P ?mem |- context [?mem] =>
           seprewrite_in unannotate_iff1 H
         end.
