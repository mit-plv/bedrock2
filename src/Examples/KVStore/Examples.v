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
Require Import Rupicola.Examples.KVStore.KVStore.
Require Import Rupicola.Examples.KVStore.Properties.
Require Import Rupicola.Examples.KVStore.Tactics.
Local Open Scope string_scope.
Import ListNotations.

Local Declare Scope sep_scope.
Local Delimit Scope sep_scope with sep.
Local Infix "*" := (sep) : sep_scope.

(* TODO: is there a better way to do this? *)
Local Notation bedrock_func := KVStore.bedrock_func.

Section examples.
  (*
  Context {p : Semantics.parameters} {word_size_in_bytes : Z}.
  Context {p_ok : Semantics.parameters_ok p}.
   *)
  Local Coercion name_of_func (f : bedrock_func) := fst f.
  Local Coercion literal (z : Z) : Syntax.expr := expr.literal z.
  Local Coercion var (x : string) : Syntax.expr := expr.var x.

  Section put_sum.
    Context {add : bedrock_func}.
    Definition Int (addr : Semantics.word) (x : Z) : Semantics.mem -> Prop :=
      sep (emp (0 <= x < 2^Semantics.width)%Z)
          (truncated_scalar access_size.word addr x).

    Context {ops} {key : Type}
            {kvp : kv_parameters}
            {ok : @kv_parameters_ok ops key Z Int kvp}.

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
        seprewrite_in annotate_iff1 H
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
        seprewrite_in reserved_borrowed_iff1 H
      end.

      (* add *)
      straightline_call; [ ecancel_assumption | ].
      repeat straightline.
      destruct_lists_of_known_length.
      repeat straightline.

      (* remove all the annotations in preparation for put *)
      unborrow Int. unreserve.
      repeat match goal with
             | H : context [map.put _ _ (Owned, ?x)] |- _ =>
               rewrite (map.put_noop _ (Owned, x)) in H
                 by (rewrite ?map.get_put_diff by congruence;
                     eauto using annotate_get_Some)
             | H : context [annotate _] |- _ =>
               seprewrite_in unannotate_iff1 H
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
  End put_sum.
End examples.
