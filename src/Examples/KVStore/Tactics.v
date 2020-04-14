Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.letexists.
Require Import Rupicola.Examples.KVStore.KVStore.
Require Import Rupicola.Examples.KVStore.Properties.
Require bedrock2.ProgramLogic.

Ltac borrow_reserved_step filter :=
  match goal with
  | H : sep ?L ?R ?mem |- context [?mem] =>
    match type of H with
      context [?P ?pm (map.put ?m ?k (Reserved ?px, ?x))] =>
      filter px;
      seprewrite_in (reserved_borrowed_iff1 pm m k px x) H
    end
  | H : context [map.put (map.put _ _ (Reserved ?px, ?x)) _ ?y] |- _ =>
    filter px;
    rewrite (map.put_put_diff_comm _ _ (Reserved px, x) y)
      in H by congruence
  end.
Ltac borrow_all_reserved :=
  progress (repeat borrow_reserved_step ltac:(fun _ => idtac)).
Ltac borrow_reserved p :=
  progress (repeat borrow_reserved_step ltac:(fun p' => unify p p')).

Ltac unborrow_step filter :=
  match goal with
  | H : sep ?L ?R ?mem |- context [?mem] =>
    match type of H with
      context [?P (map.put ?m ?k (Borrowed ?px, ?x))] =>
      filter px;
      match type of H with
        context [?Q ?px ?x] =>
        let F1 :=
            match (eval pattern
                        (P (map.put m k (Borrowed px, x))) in
                      (sep L R)) with ?f _ => f end in
        let F2 :=
            match (eval pattern (Q px x) in F1) with
              ?f _ => f end in
        let H' := fresh in
        assert (F2 (P (map.put m k (Reserved px, x))) (emp True) mem)
          as H' by (seprewrite reserved_borrowed_iff1;
                    ecancel_assumption);
        clear H; cbv beta in H'
      end
    end
  | H : context [map.put (map.put _ _ (Borrowed ?px, ?x))
                         _ ?y] |- _ =>
    filter px;
    rewrite (map.put_put_diff_comm _ _ (Borrowed px, x) y)
      in H by congruence
  end.
Ltac unborrow_all :=
  progress (repeat unborrow_step ltac:(fun _ => idtac)).
Ltac unborrow p :=
  progress (repeat unborrow_step ltac:(fun p' => unify p p')).

Ltac unreserve_step filter :=
  match goal with
  | H : sep ?L ?R ?mem |- context [?mem] =>
    match type of H with
      context [?P (map.put ?m ?k (Reserved ?px, ?x))] =>
      filter px;
      let F1 :=
          match (eval pattern
                      (P (map.put m k (Reserved px, x))) in
                    (sep L R)) with ?f _ => f end in
      let H' := fresh in
      (* hacky because seprewrite doesn't do impl1 *)
      assert (F1 (P (map.put m k (Owned, x))) mem) as H'
          by (seprewrite (sep_assoc (P (map.put m k (Owned, x))));
              eapply Proper_sep_impl1;
              [ repeat
                  rewrite (sep_assoc (_ (map.put _ _ (Owned, _))));
                eapply Proper_sep_impl1;
                [ eapply reserved_owned_impl1 | reflexivity ]
              | reflexivity | ]; ecancel_assumption);
      clear H; cbv beta in H'
    end
  | H : context [map.put (map.put _ _ (Reserved ?px, ?x)) _ ?y] |- _ =>
    filter px;
    rewrite (map.put_put_diff_comm _ _ (Reserved px, x) y)
      in H by congruence
  end.
Ltac unreserve_all :=
  progress (repeat unreserve_step ltac:(fun _ => idtac)).
Ltac unreserve p :=
  progress (repeat unreserve_step ltac:(fun p' => unify p p')).

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
  repeat match goal with
         | _ => progress subst
         | _ => progress unborrow_all
         | _ => progress unreserve_all
         | _ => progress clear_owned
         | H : sep _ _ _ |- _ =>
           (* TODO: why doesn't mapsimpl do this? *)
           erewrite @map.put_put_same in H by (typeclasses eauto)
         end;
  match goal with
  | H : context [annotate] |- _ =>
    seprewrite_in unannotate_iff1 H
  end.

Ltac clear_old_seps :=
  match goal with
  | H : sep _ _ ?mem |- context [?mem] =>
    repeat match goal with
           | H' : sep _ _ ?m |- _ =>
             assert_fails (unify m mem); clear H'
           end
  end.
