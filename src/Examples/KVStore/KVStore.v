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

  Class kv_ops :=
    { map_init : bedrock_func;
      get : bedrock_func;
      put : bedrock_func; }.

  Class kv_parameters
        {ops : kv_ops} {key value : Type}
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

  Class kv_parameters_ok
        {ops : kv_ops} {key value Value}
        {p : @kv_parameters ops key value Value} :=
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

  Section specs.
    Context {ops key value Value}
            {kvp : @kv_parameters ops key value Value}.

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
               /\ (Map p map.empty * R)%sep mem').

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
                    err = word.of_Z 0
                    /\ (match a with
                        | Borrowed pv' => pv = pv'
                        | Reserved pv' => pv = pv'
                        | Owned => True
                        end)
                    /\ (AnnotatedMap
                          pm (match a with
                              | Borrowed _ => m
                              | Reserved _ => m
                              | Owned => map.put m k (Reserved pv, v)
                              end) * Key pk k * R)%sep mem'
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
          (AnnotatedMap pm m
           * Key pk k * Value pv v * R)%sep mem ->
          WeakestPrecondition.call
            functions put tr mem [pm; pk; pv]
            (fun tr' mem' rets =>
               tr = tr'
               /\ length rets = 1%nat
               /\ let was_overwrite := hd (word.of_Z 0) rets in
                  match map.get m k with
                  | Some (a, old_v) =>
                    match a with
                    | Borrowed _ => True (* no guarantees *)
                    | Reserved pv' =>
                      was_overwrite = word.of_Z 1
                      /\ (AnnotatedMap pm (map.put m k (Reserved pv', v))
                          * Key pk k * Value pv old_v * R)%sep mem'
                    | Owned =>
                      was_overwrite = word.of_Z 1
                      /\ (AnnotatedMap pm (map.put m k (Owned, v))
                          * Key pk k * Value pv old_v * R)%sep mem'
                    end
                  | None =>
                    (* if there was no previous value, the map consumes both
                       the key and value memory *)
                    was_overwrite = word.of_Z 0
                    /\ (AnnotatedMap pm (map.put m k (Owned, v))
                        * R)%sep mem'
                  end).
  End specs.
End KVStore.
