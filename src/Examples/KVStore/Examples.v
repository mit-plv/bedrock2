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
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.destr.
Require Import coqutil.Tactics.Tactics.
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
          k1 <> k2 -> (* required because add needs arguments separate *)
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
         // commutativity of put (when k1 <> k2)
         { pm -> map.put (map.put (annotate m) k2 (Reserved pv2, v2))
                         k1 (Borrowed pv1, v1); pv1 -> v1; pv -> (v1 + v2)}
         // reserved_borrowed_iff1
         { pm -> map.put (map.put (annotate m) k2 (Reserved pv2, v2))
                         k1 (Reserved pv1, v1); pv -> (v1 + v2)}
         // reserved_impl1
         { pm -> map.put (map.put (annotate m) k2 (Reserved pv2, v2))
                         k1 (Owned, v1); pv -> (v1 + v2)}
         // commutativity of put (when k1 <> k2)
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
      repeat straightline. cbv [put_sum_gallina].
      add_map_annotations.

      repeat match goal with
             | _ => progress kv_hammer
             | |- WeakestPrecondition.call _ ?f _ ?m ?args _ =>
               (* call add -- need to borrow all args first *)
               unify f (name_of_func add);
                 let in0 := (eval hnf in (hd (word.of_Z 0) args)) in
                 let in1 := (eval hnf in (hd (word.of_Z 0) (tl args))) in
                 let in2 :=
                     (eval hnf in (hd (word.of_Z 0) (tl (tl args)))) in
                 try borrow in0; try borrow in1; try borrow in2;
                   handle_call; autorewrite with mapsimpl in *
             end.

      all: remove_map_annotations.

      all: subst; ssplit; try reflexivity.
      all: ecancel_assumption.
    Qed.
  End put_sum.

  Section swap.
    Context {ops} {key value : Type} {Value}
            {kvp : kv_parameters}
            {ok : @kv_parameters_ok ops key value Value kvp}.

    Existing Instances map_ok annotated_map_ok key_eq_dec.
    Existing Instances spec_of_map_get spec_of_map_put.

    (* look up k1 and k2, add their values and store in k3 *)
    Definition swap_gallina (m : map.rep (map:=map))
               (k1 k2 : key) : map.rep (map:=map) :=
      match map.get m k1, map.get m k2 with
      | Some v1, Some v2 =>
        map.put (map.put m k2 v1) k1 v2
      | _, _ => m
      end.

    Definition swap : bedrock_func :=
      let m := "m" in
      let k1 := "k1" in
      let k2 := "k2" in
      let v1 := "v1" in
      let v2 := "v2" in
      let err := "err" in
      ("swap",
       ([m; k1; k2], [],
        bedrock_func_body:(
          unpack! err, v1 = get (m, k1) ;
            require !err ;
            unpack! err, v2 = get (m, k2) ;
            require !err ;
            unpack! err = put (m, k2, v1)
            (* now v2 is stored in v1 -- no need for second put *)
      ))).

    Instance spec_of_swap : spec_of swap :=
      fun functions =>
        forall pm m pk1 k1 pk2 k2 R tr mem,
          map.get m k1 <> None ->
          map.get m k2 <> None ->
          k1 <> k2 -> (* TODO: try removing *)
          (Map pm m * Key pk1 k1 * Key pk2 k2 * R)%sep mem ->
          WeakestPrecondition.call
            functions swap tr mem [pm; pk1; pk2]
            (fun tr' mem' rets =>
               tr = tr'
               /\ rets = []
               /\ (Map pm (swap_gallina m k1 k2)
                   * Key pk1 k1 * Key pk2 k2 * R)%sep mem').

    (* Entire chain of separation-logic reasoning for swap:

         { pm -> m; pk1 -> k1; pk2 -> k2 }
         // annotate
         { pm -> annotate m; pk1 -> k1; pk2 -> k2 }
         // get k1
         { pm -> map.put (annotate m) k1 (Reserved pv1, v1);
              pk1 -> k1; pk2 -> k2 }
         // get k2
         { pm -> map.put (map.put (annotate m) k1 (Reserved pv1, v1))
                         k2 (Reserved pv2, v2); pk1 -> k1; pk2 -> k2 }
         // borrow pv1
         { pm -> map.put (map.put (annotate m) k2 (Reserved pv2, v2))
                         k1 (Borrowed pv1, v1); pv1 -> v1;
                         pk1 -> k1; pk2 -> k2 }
         // put k2
         { pm -> map.put
                   (map.put (map.put (annotate m) k2 (Reserved pv2, v2))
                         k1 (Borrowed pv1, v1)) k2 (Reserved pv2, v1);
             pv1 -> v2; pk1 -> k1; pk2 -> k2 }
         // put_put
         { pm -> map.put (map.put (annotate m) k1 (Borrowed pv1, v1))
                         k2 (Reserved pv2, v1);
             pv1 -> v2; pk1 -> k1; pk2 -> k2 }
        // unborrow pv1
         { pm -> map.put (map.put (annotate m) k2 (Reserved pv2, v1))
                         k1 (Reserved pv1, v2);
             pk1 -> k1; pk2 -> k2 }
     *)
    Lemma swap_ok : program_logic_goal_for_function! swap.
    Proof.
      repeat straightline. cbv [swap_gallina].
      add_map_annotations.

      kv_hammer.

      remove_map_annotations.
      rewrite map.put_put_diff_comm by congruence.
      subst; ssplit; try reflexivity.
      ecancel_assumption.
    Qed.
  End swap.
End examples.
