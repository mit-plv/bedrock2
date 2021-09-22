Require Import Rupicola.Lib.Api.

Require Import Rupicola.Examples.KVStore.KVStore.
Require Import Rupicola.Examples.KVStore.Properties.

Ltac borrow_step filter :=
  match goal with
  | H : sep ?L ?R ?mem |- context [?mem] =>
    match type of H with
      context [?P ?pm (map.put ?m ?k (Reserved ?px, ?x))] =>
      filter px;
      seprewrite_in (reserved_borrowed_iff1 pm m k px x x) H
    end
  | H : context [map.put (map.put _ _ (Reserved ?px, ?x)) _ ?y] |- _ =>
    filter px;
    rewrite (map.put_put_diff_comm _ _ (Reserved px, x) y)
      in H by congruence
  end.
Ltac borrow_all :=
  progress (repeat borrow_step ltac:(fun _ => idtac)).
Ltac borrow p :=
  progress (repeat borrow_step ltac:(fun p' => unify p p')).

Ltac unborrow_step filter :=
  match goal with
  | H : sep ?L ?R ?mem |- context [?mem] =>
    match type of H with
      context [?P ?pm (map.put ?m ?k (Borrowed ?px, ?x))] =>
      filter px;
      match type of H with
        context [?Q ?px ?y] =>
        let F1 :=
            match (eval pattern
                        (P pm (map.put m k (Borrowed px, x))) in
                      (sep L R)) with ?f _ => f end in
        let F2 :=
            match (eval pattern (Q px y) in F1) with
              ?f _ => f end in
        let H' := fresh in
        assert (F2 (P pm (map.put m k (Reserved px, y))) (emp True) mem)
          as H' by (seprewrite (reserved_borrowed_iff1 pm m k px y x);
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

Ltac kv_hammer :=
  repeat match goal with
         | _ => progress subst
         | _ => straightline'
         | _ => progress destruct_products
         | _ => progress clear_old_seps
         | H : map.get _ _ = Some _ |- _ => rewrite H in *
         | H : context [key_eqb ?k1 ?k2] |- _ =>
           destr (key_eqb k1 k2)
         | kvp : @kv_parameters _ _ _ _ _ _ ?value _ |- _ =>
           (* handles (require !err):
              destruct map get and only allow one remaining subgoal *)
           destruct_one_match_hyp_of_type (option value);
           destruct_products; try clear_old_seps; try congruence;
           split_if ltac:(solve[repeat straightline']);
           intros; boolean_cleanup; [ ]
         | kvp : @kv_parameters _ _ _ _ _ _ ?value _ |- _ =>
           (* handles case analysis of map-get other than require !err:
              destruct map get and allow two remaining subgoals *)
           destruct_one_match_hyp_of_type (option value);
           destruct_products; try clear_old_seps;
           (* make sure this doesn't work on require !err *)
           (* TODO: why doesn't assert_fails work? *)
           tryif split_if ltac:(solve[repeat straightline'])
           then fail else idtac;
           boolean_cleanup
         | H : _ |- _ =>
           (* TODO: why doesn't mapsimpl do this? *)
           erewrite @map.put_put_same in H by typeclasses eauto
         | H : _ |- _ => rewrite map.get_put_dec in H
         | |- WeakestPrecondition.call _ ?f _ _ _ _ =>
           (* call get *)
           unify f (fst get);
           handle_call; autorewrite with mapsimpl in *
         | |- WeakestPrecondition.call _ ?f _ ?m ?args _ =>
           (* call put -- unborrow everything except value being placed *)
           unify f (fst put);
           let pv :=
               (eval hnf in (hd (word.of_Z 0) (tl (tl args)))) in
           try unborrow_all; try borrow pv;
           handle_call; autorewrite with mapsimpl in *
         | _ => progress autorewrite with mapsimpl in *
         end.
