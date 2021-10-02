Require Import Rupicola.Lib.Api.


Inductive annotation {width: Z} {BW: Bitwidth width} {word: word.word width} : Type :=
| Reserved : word -> annotation
| Borrowed : word -> annotation
| Owned : annotation
.

Section KVStore.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Local Notation annotation := (@annotation _ BW word).

  Definition AnnotatedValue_gen {value}
             (Value : word -> value -> mem -> Prop)
             (addr : word) (av : annotation * value)
    : mem -> Prop :=
    match (fst av) with
    | Reserved pv => (emp (addr = pv) * Value pv (snd av))%sep
    | Borrowed pv => emp (addr = pv)
    | Owned => Value addr (snd av)
    end.

  Class kv_ops :=
    { map_init : func;
      get : func;
      put : func; }.

  Class kv_parameters
        {ops : kv_ops} {key value : Type}
        {Value : word -> value -> mem -> Prop} :=
    { map_gen : forall value, map.map key value;
      map := map_gen value;
      annotated_map := map_gen (annotation * value);
      init_map_size_in_bytes : nat;
      key_eqb : key -> key -> bool;
      Key : word -> key -> mem -> Prop;
      Map_gen :
        forall value (Value : word -> value ->
                              mem -> Prop),
          word -> map.rep (map:=map_gen value) ->
          mem -> Prop;
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
               (fun xs: list _ =>
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
