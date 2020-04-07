Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Array.
Require Import bedrock2.BasicCSyntax.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.NotationsCustomEntry.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Map.SortedList.
Require Import coqutil.Tactics.destr.
Local Open Scope string_scope.
Import ListNotations.

Local Declare Scope sep_scope.
Local Delimit Scope sep_scope with sep.
Local Infix "*" := (sep) : sep_scope.

(* TODO: add fiat-crypto's break_match to coqutil? *)
Ltac break_match :=
  match goal with
  | |- context [match ?x with _ => _ end] =>
    let H := fresh "Heq" in
    destruct x eqn:H;
    rewrite ?H in *
  end.
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
         | x := word.of_Z 0 |- _ => subst x
         | x := word.of_Z 1 |- _ => subst x
         | _ => congruence
         end.

(* TODO: should move upstream to coqutil *)
Module map.
  Section __.
    Context {key value} {map : map.map key value}
            {map_ok : map.ok map}
            {key_eqb}
            {key_eq_dec :
               forall x y : key, BoolSpec (x = y) (x <> y) (key_eqb x y)}.

    Lemma put_put_diff_comm k1 k2 v1 v2 m :
      k1 <> k2 ->
      map.put (map.put m k1 v1) k2 v2 = map.put (map.put m k2 v2) k1 v1.
    Proof.
      intros. apply map.map_ext. intros.
      rewrite !map.get_put_dec;
        repeat match goal with |- context [key_eqb ?x ?y] =>
                               destr (key_eqb x y) end;
        congruence.
    Qed.

    Lemma put_noop k v m :
      map.get m k = Some v -> map.put m k v = m.
    Proof.
      intros. apply map.map_ext. intros.
      rewrite !map.get_put_dec;
        repeat match goal with |- context [key_eqb ?x ?y] =>
                               destr (key_eqb x y) end;
        congruence.
    Qed.
  End __.
End map.

Section KVStore.
  (* TODO: once bedrock2 version is updated, these can be replaced by the
     commented-out generalized version below. *)
  Local Existing Instance BasicCSyntax.StringNames_params.
  Local Existing Instance BasicC64Semantics.parameters.
  Local Existing Instance BasicC64Semantics.parameters_ok.
  (*
  Context {p : Semantics.parameters} {word_size_in_bytes : Z}.
  Context {p_ok : Semantics.parameters_ok p}.
   *)
  Local Notation address := Semantics.word (only parsing).
  Local Definition bedrock_func : Type :=
    funname * (list string * list string * cmd).
  Local Coercion name_of_func (f : bedrock_func) := fst f.
  Local Coercion literal (z : Z) : Syntax.expr := expr.literal z.
  Local Coercion var (x : string) : Syntax.expr := expr.var x.

  Inductive annotation : Type :=
  | Reserved : address -> annotation
  | Borrowed : address -> annotation
  | Owned : annotation
  .

  Definition AnnotatedValue_gen {value}
             (Value : Semantics.word -> value -> Semantics.mem -> Prop)
             (addr : Semantics.word) (av : annotation * value)
    : Semantics.mem -> Prop :=
    match (fst av) with
    | Reserved pv => (emp (addr = pv) * Value pv (snd av))%sep
    | Borrowed pv => emp (addr = pv)
    | Owned => Value addr (snd av)
    end.

  Class kv_parameters {key value}
        {Value : Semantics.word -> value -> Semantics.mem -> Prop} :=
    { map_gen : forall value, map.map key value;
      map := map_gen value;
      annotated_map := map_gen (annotation * value);
      init_map_size_in_bytes : nat;
      key_eqb : key -> key -> bool;
      Key : Semantics.word -> key -> Semantics.mem -> Prop;
      Map_gen :
        forall value (Value : Semantics.word -> value ->
                              Semantics.mem -> Prop),
          Semantics.word -> map.rep (map:=map_gen value) ->
          Semantics.mem -> Prop;
      Map : _ -> map -> _ -> _ := Map_gen value Value;
      AnnotatedMap : _ -> annotated_map -> _ -> _ :=
        Map_gen (annotation * value)
                (AnnotatedValue_gen Value);
    }.

  Class kv_parameters_ok {key value Value}
        {p : @kv_parameters key value Value} :=
    { map_ok_gen : forall value, map.ok (map_gen value);
      map_ok : map.ok map := map_ok_gen value;
      annotated_map_ok : map.ok annotated_map :=
        map_ok_gen (annotation * value);
      key_eq_dec :
        forall x y : key, BoolSpec (x = y) (x <> y) (key_eqb x y);
      Map_put_impl1 :
        forall value Value pm
               (m : map.rep (map:=map_gen value))
               k v1 v2 R1 R2,
          (forall pv,
              Lift1Prop.impl1
                (sep (Value pv v1) R1)
                (sep (Value pv v2) R2)) ->
          Lift1Prop.impl1
            (sep (Map_gen value Value pm (map.put m k v1)) R1)
            (sep (Map_gen value Value pm (map.put m k v2)) R2);
      Map_fold_iff1 :
        forall value1 value2 Value1 Value2 (f : value1 -> value2),
          (forall pv v,
              Lift1Prop.iff1 (Value1 pv v) (Value2 pv (f v))) ->
          forall pm m,
            Lift1Prop.iff1
              (Map_gen value1 Value1 pm m)
              (Map_gen value2 Value2 pm
                       (map.fold
                          (fun m' k v => map.put m' k (f v))
                          map.empty m)); }.

  Section with_params.
    Context {key value : Type} {Value}
            {kvp : kv_parameters}
            {ok : @kv_parameters_ok key value Value kvp}.
    Existing Instance map_ok.
    Existing Instance annotated_map_ok.
    Existing Instance key_eq_dec.

    Lemma Map_put_iff1 :
      forall value Value pm (m : map.rep (map:=map_gen value))
             k v1 v2 R1 R2,
        (forall pv,
            Lift1Prop.iff1
              (sep (Value pv v1) R1)
              (sep (Value pv v2) R2)) ->
        Lift1Prop.iff1
          (sep (Map_gen value Value pm (map.put m k v1)) R1)
          (sep (Map_gen value Value pm (map.put m k v2)) R2).
    Proof.
      intros *.
      intro Hiff; split; intros;
        eapply Map_put_impl1; intros; eauto;
          rewrite Hiff; reflexivity.
    Qed.

      Axiom get put map_init : bedrock_func.

      Definition annotate (m : map) : annotated_map :=
        map.fold (fun m' k v => map.put m' k (Owned, v)) map.empty m.

      Lemma annotate_get_None m k :
        map.get m k = None -> map.get (annotate m) k = None.
      Proof.
        cbv [annotate]; eapply map.fold_spec; intros;
          try eapply map.get_empty; [ ].
        rewrite map.get_put_dec.
        match goal with H : map.get (map.put _ ?k1 _) ?k2 = None |- _ =>
                        rewrite map.get_put_dec in H;
                          destruct (key_eqb k1 k2); try congruence; [ ]
        end.
        eauto.
      Qed.

      Lemma annotate_get_Some m k v :
        map.get m k = Some v ->
        map.get (annotate m) k = Some (Owned, v).
      Proof.
        cbv [annotate]; eapply map.fold_spec;
          rewrite ?map.get_empty; intros; [ congruence | ].
        rewrite map.get_put_dec.
        match goal with H : map.get (map.put _ ?k1 _) ?k2 = Some _ |- _ =>
                        rewrite map.get_put_dec in H;
                          destruct (key_eqb k1 k2); try congruence; [ ]
        end.
        eauto.
      Qed.

      Lemma annotate_get_full m k :
        map.get (annotate m) k = match map.get m k with
                                 | Some v => Some (Owned, v)
                                 | None => None
                                 end.
      Proof.
        break_match; eauto using annotate_get_None, annotate_get_Some.
      Qed.

      Lemma annotate_iff1 pm m :
        Lift1Prop.iff1
          (Map pm m) (AnnotatedMap pm (annotate m)).
      Proof.
        apply Map_fold_iff1; intros; reflexivity.
      Qed.

      Lemma unannotate_iff1 pm m :
        Lift1Prop.iff1
          (AnnotatedMap pm (annotate m)) (Map pm m).
      Proof. symmetry; apply annotate_iff1. Qed.

      Lemma reserved_borrowed_iff1 pm m k pv v :
        Lift1Prop.iff1
          (AnnotatedMap pm (map.put m k (Reserved pv, v)))
          (sep (AnnotatedMap pm (map.put m k (Borrowed pv, v)))
               (Value pv v)).
      Proof.
        cbv [AnnotatedMap].
        rewrite <-sep_emp_True_r.
        apply Map_put_iff1. intros.
        rewrite sep_emp_True_r.
        reflexivity.
      Qed.

      Lemma reserved_owned_impl1 pm m k pv v :
        Lift1Prop.impl1
          (AnnotatedMap pm (map.put m k (Reserved pv, v)))
          (AnnotatedMap pm (map.put m k (Owned, v))).
      Proof.
        rewrite <-(sep_emp_True_r (_ (map.put _ _ (Reserved _, _)))).
        rewrite <-(sep_emp_True_r (_ (map.put _ _ (Owned, _)))).
        cbv [AnnotatedMap]. repeat intro.
        eapply Map_put_impl1; intros; [ | eassumption ].
        cbn [AnnotatedValue_gen fst snd].
        rewrite !sep_emp_True_r.
        intro; rewrite sep_emp_l; intros;
          repeat match goal with
                 | H : _ /\ _ |- _ => destruct H
                 end;
          subst; eauto.
      Qed.

      Instance spec_of_map_init : spec_of map_init :=
        fun functions =>
          forall p start R tr mem,
            (* { p -> start } *)
            (* space must already be allocated at start *)
            (truncated_scalar
               access_size.word p (word.unsigned start)
             * Lift1Prop.ex1
                 (fun xs =>
                    sep (emp (length xs = init_map_size_in_bytes))
                        (array ptsto (word.of_Z 1) start xs))
            * R)%sep mem ->
            WeakestPrecondition.call
              functions map_init tr mem [p]
              (fun tr' mem' rets =>
                 tr = tr'
                 /\ rets = []
                 /\ (truncated_scalar
                       access_size.word p (word.unsigned start)
                      * Map p map.empty * R)%sep mem').

      (* get returns a pair; a boolean (true if there was an error) and a value,
       which is meaningless if there was an error. *)
      Instance spec_of_map_get : spec_of get :=
        fun functions =>
          forall pm m pk k R tr mem,
            sep (sep (AnnotatedMap pm m) (Key pk k)) R mem ->
            WeakestPrecondition.call
              functions get tr mem [pm; pk]
              (fun tr' mem' rets =>
                 tr = tr'
                 /\ length rets = 2%nat
                 /\ let err := hd (word.of_Z 0) rets in
                    let pv := hd (word.of_Z 0) (tl rets) in
                    match map.get m k with
                    | Some (a, v) =>
                      match a with
                      | Borrowed _ => True (* no guarantees *)
                      | Reserved pv' =>
                        err = word.of_Z 0
                        /\ pv = pv'
                        /\ (AnnotatedMap
                              pm (map.put m k (Reserved pv, v))
                            * Key pk k * R)%sep mem'
                      | Owned =>
                        err = word.of_Z 0
                        /\ (AnnotatedMap
                              pm (map.put m k (Reserved pv, v))
                            * Key pk k * R)%sep mem'
                      end
                    | None =>
                      (* if k not \in m, err = true and no change *)
                      err = word.of_Z 1
                      /\ (AnnotatedMap pm m * Key pk k * R)%sep mem'
                    end).

      (* put returns a boolean indicating whether the key was already
         present. If true, the original value pointer now points to the old
         value. *)
      Instance spec_of_map_put : spec_of put :=
        fun functions =>
          forall pm m pk k pv v R tr mem,
            (Map pm m * Key pk k * Value pv v * R)%sep mem ->
            WeakestPrecondition.call
              functions put tr mem [pm; pk; pv]
              (fun tr' mem' rets =>
                 tr = tr'
                 /\ length rets = 1%nat
                 /\ let was_overwrite := hd (word.of_Z 0) rets in
                    match map.get m k with
                    | Some old_v =>
                      was_overwrite = word.of_Z 1
                      /\ (Map pm (map.put m k v) * Key pk k
                          * Value pv old_v * R)%sep mem'
                    | None =>
                      (* if there was no previous value, the map consumes both
                         the key and value memory *)
                      was_overwrite = word.of_Z 0
                      /\ (Map pm (map.put m k v) * R)%sep mem' 
                    end).
  End with_params.

  Section example.
    Context {add : bedrock_func}.
    Definition Int (addr : Semantics.word) (x : Z) : Semantics.mem -> Prop :=
      sep (emp (0 <= x < 2^Semantics.width)%Z)
          (truncated_scalar access_size.word addr x).

    Context {key : Type}
            {kvp : kv_parameters}
            {ok : @kv_parameters_ok key Z Int kvp}.

    Existing Instances map_ok annotated_map_ok key_eq_dec.
    Existing Instances spec_of_map_get spec_of_map_put.

      Instance spec_of_add : spec_of add :=
        fun functions =>
          forall px x py y pout old_out R tr mem,
            (Int px x * Int py y * Int pout old_out * R)%sep mem ->
            WeakestPrecondition.call
              functions add tr mem [px; py; pout]
              (fun tr' mem' rets =>
                 tr = tr'
                 /\ rets = [] 
                 /\ let out := word.wrap (x + y) in
                    (Int px x * Int py y * Int pout out * R)%sep mem').

      (* look up k1 and k2, add their values and store in k3 *)
      Definition put_sum_gallina (m : map.rep (map:=map))
                 (k1 k2 k3 : key) : map.rep (map:=map) :=
        match map.get m k1, map.get m k2 with
        | Some v1, Some v2 => map.put m k3 (word.wrap (v1 + v2)%Z)
        | _, _ => m
        end.

      (* like put, returns a boolean indicating whether the put was an
         overwrite, and stores the old value in v if the boolean is true *)
      Definition put_sum : bedrock_func :=
        let m := "m" in
        let k1 := "k1" in
        let k2 := "k2" in
        let k3 := "k3" in
        let v := "v" in (* pre-allocated memory for a value *)
        let v1 := "v1" in
        let v2 := "v2" in
        let err := "err" in
        let ret := "ret" in
        ("get_add_put",
         ([m; k1; k2; k3; v], [ret],
          bedrock_func_body:(
              unpack! err, v1 = get (m, k1) ;
                require !err ;
                unpack! err, v2 = get (m, k2) ;
                require !err ;
                add (v1, v2, v); 
                unpack! ret = put (m, k3, v)
        ))).

      Instance spec_of_put_sum : spec_of put_sum :=
        fun functions =>
          forall pm m pk1 k1 pk2 k2 pk3 k3 pv v R tr mem,
            map.get m k1 <> None ->
            map.get m k2 <> None ->
            k1 <> k2 -> (* TODO: try not requiring this *)
            (Map pm m * Key pk1 k1 * Key pk2 k2 * Key pk3 k3
             * Int pv v * R)%sep mem ->
            WeakestPrecondition.call
              functions put_sum tr mem [pm; pk1; pk2; pk3; pv]
              (fun tr' mem' rets =>
                 tr = tr'
                 /\ length rets = 1
                 /\ hd (word.of_Z 0) rets =
                    match map.get m k3 with
                    | Some _ => word.of_Z 1
                    | None => word.of_Z 0
                    end
                 /\ (Map pm (put_sum_gallina m k1 k2 k3)
                     * Key pk1 k1 * Key pk2 k2 *
                     (match map.get m k3 with
                      | Some v3 =>
                        Key pk3 k3 * Int pv v3 * R
                      | None => R
                      end))%sep mem').


      Local Ltac unborrow_step :=
        match goal with
        | H : sep ?L ?R ?mem |- context [?mem] =>
          match type of H with
            context [?P (map.put ?m ?k (Borrowed ?px, ?x))] =>
            let F1 :=
                match (eval pattern
                            (P (map.put m k (Borrowed px, x))) in
                          (sep L R)) with ?f _ => f end in
            let F2 :=
                match (eval pattern (Int px x) in F1) with
                  ?f _ => f end in
            let H' := fresh in
            assert (F2 (P (map.put m k (Reserved px, x))) (emp True) mem)
              as H' by (seprewrite (reserved_borrowed_iff1 (Value:=Int));
                        ecancel_assumption);
            clear H; cbv beta in H'
          end
        | H : context [map.put (map.put _ _ (Borrowed ?px, ?x))
                               _ (Reserved ?py, ?y)] |- _ =>
          rewrite (map.put_put_diff_comm _ _ (Borrowed px, x)
                                         (Reserved py, y))
            in H by congruence
        end.
      Local Ltac unborrow := progress (repeat unborrow_step).

      Local Ltac unreserve_step :=
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
      Local Ltac unreserve := progress (repeat unreserve_step).

      (* Entire chain of separation-logic reasoning for put_sum
         (omitting keys for readability):

         { pm -> m; pv -> v}
         // annotate_iff1
         { pm -> annotate m; pv -> v}
         // get k1
         { pm -> map.put (annotate m) k1 (Reserved pv1, v1); pv -> v}
         // reserved_borrowed_iff1
         { pm -> map.put (annotate m) k1 (Borrowed pv1, v1);
                 pv1 -> v1; pv -> v}
         // get k2
         { pm -> map.put (map.put (annotate m) k1 (Borrowed pv1, v1))
                         k2 (Reserved pv2, v2); pv1 -> v1; pv -> v}
         // reserved_borrowed_iff1
         { pm -> map.put (map.put (annotate m) k1 (Borrowed pv1, v1))
                         k2 (Borrowed pv2, v2);
                 pv2 -> v2; pv1 -> v1; pv -> v}
         // add
         { pm -> map.put (map.put (annotate m) k1 (Borrowed pv1, v1))
                         k2 (Borrowed pv2, v2);
                 pv2 -> v2; pv1 -> v1; pv -> (v1 + v2)}
         // reserved_borrowed_iff1
         { pm -> map.put (map.put (annotate m) k1 (Borrowed pv1, v1))
                         k2 (Reserved pv2, v2); pv1 -> v1; pv -> (v1 + v2)}
         // commutativity of put (requires k1 <> k2)
         { pm -> map.put (map.put (annotate m) k2 (Reserved pv2, v2))
                         k1 (Borrowed pv1, v1); pv1 -> v1; pv -> (v1 + v2)}
         // reserved_borrowed_iff1
         { pm -> map.put (map.put (annotate m) k2 (Reserved pv2, v2))
                         k1 (Reserved pv1, v1); pv -> (v1 + v2)}
         // reserved_impl1
         { pm -> map.put (map.put (annotate m) k2 (Reserved pv2, v2))
                         k1 (Owned, v1); pv -> (v1 + v2)}
         // commutativity of put (requires k1 <> k2)
         { pm -> map.put (map.put (annotate m) k1 (Owned, v1))
                         k2 (Reserved pv2, v2); pv -> (v1 + v2)}
         // reserved_impl1
         { pm -> map.put (map.put (annotate m) k1 (Owned, v1))
                         k2 (Owned, v2); pv -> (v1 + v2)}
         // puts are noops 
         { pm -> annotate m; pv -> (v1 + v2)}
         // annotate_iff1
         { pm -> m; pv -> (v1 + v2)}
         // put k3 (v1 + v2)
         { pm -> map.put m k3 (v1 + v2); match map.get m k3 with
                                         | Some v3 => { pv -> v3 }
                                         | None => emp True
                                         end }
       *)
      Lemma put_sum_ok : program_logic_goal_for_function! put_sum. 
      Proof.
        repeat straightline.

        (* annotate map *)
        match goal with
        | H : context [Map _ _] |- _ =>
          seprewrite_in (annotate_iff1 (Value:=Int)) H
        end.

        (* first get *)
        straightline_call; [ ecancel_assumption | ].
        repeat straightline.
        destruct_lists_of_known_length.
        repeat straightline.

        (* require !err *)
        WeakestPrecondition.unfold1_cmd_goal;
          (cbv beta match delta [WeakestPrecondition.cmd_body]).
        repeat straightline.
        cbv [put_sum_gallina].
        fold map annotated_map in *.
        match goal with
          H : _ |- _ =>
          rewrite ?map.get_put_diff, annotate_get_full in H
            by congruence
        end.
        match goal with
        | |- context [match map.get ?m k1 with _ => _ end] =>
          destruct (map.get m k1) eqn:?
        end; repeat straightline; split; intros;
          boolean_cleanup; [ ].
        WeakestPrecondition.unfold1_cmd_goal;
          (cbv beta delta [WeakestPrecondition.cmd_body]).
        repeat straightline.

        (* borrow the result of the first get *)
        match goal with
        | H : context [Reserved] |- _ =>
          seprewrite_in (reserved_borrowed_iff1) H
        end.

        (* second get *)
        straightline_call; [ ecancel_assumption | ].
        repeat straightline.
        destruct_lists_of_known_length.
        repeat straightline.

        (* require !err *)
        WeakestPrecondition.unfold1_cmd_goal;
          (cbv beta match delta [WeakestPrecondition.cmd_body]).
        repeat straightline.
        cbv [put_sum_gallina map].
        match goal with
          H : _ |- _ =>
          rewrite ?map.get_put_diff, annotate_get_full in H
            by congruence
        end.
        match goal with
        | |- context [match map.get ?m k2 with _ => _ end] =>
          destruct (map.get m k2) eqn:?
        end; repeat straightline; split; intros;
          boolean_cleanup; [ ].
        WeakestPrecondition.unfold1_cmd_goal;
          (cbv beta delta [WeakestPrecondition.cmd_body]).
        repeat straightline.

        (* borrow the result of the second get *)
        match goal with
        | H : context [Reserved] |- _ =>
          seprewrite_in (reserved_borrowed_iff1 (Value:=Int)) H
        end.
                
        (* add *)
        straightline_call; [ ecancel_assumption | ].
        repeat straightline.
        destruct_lists_of_known_length.
        repeat straightline.

        (* remove all the annotations in preparation for put *)
        unborrow. unreserve.
        repeat match goal with
               | H : context [map.put _ _ (Owned, ?x)] |- _ =>
                 rewrite (map.put_noop _ (Owned, x)) in H
                   by (rewrite ?map.get_put_diff by congruence;
                       eauto using annotate_get_Some)
               | H : context [annotate _] |- _ =>
                 seprewrite_in (unannotate_iff1 (Value:=Int)) H
               end.

        (* put *)
        straightline_call; [ ecancel_assumption | ].
        repeat straightline.
        destruct_lists_of_known_length.
        repeat straightline.

        (* final proof *)
        fold map annotated_map in *.
        repeat match goal with
               | _ => progress (subst; cbn [hd tl])
               | H : _ /\ _ |- _ => destruct H
               | H : Some _ = Some _ |- _ => inversion H; clear H
               | |- _ /\ _ => split
               | _ => reflexivity
               | _ => congruence
               | _ => break_match
               | _ => ecancel_assumption
               end.
      Qed.
  End example.
End KVStore.
