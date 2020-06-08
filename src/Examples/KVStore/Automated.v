Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.KVStore.KVStore.
Require Import Rupicola.Examples.KVStore.Properties.
Require Import Rupicola.Examples.KVStore.Tactics.

Section KVSwap.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {ops} {key value : Type} {Value}
          {dummy_value : value}
          {kvp : kv_parameters}
          {ok : @kv_parameters_ok semantics ops key value Value kvp}.

  Existing Instances ops kvp ok.
  Existing Instances map_ok annotated_map_ok key_eq_dec.
  Existing Instances spec_of_map_get.

  (* MAP LAYOUTS


  pk | key
  pk+1 | pointer (pv)

  pv | value

  get v returns pk+1


  Keys = words, inline
  Values = ?? (pointers stored inline)

  map = linked list of (key, value pointer) pairs

  entry:

  pk   | key1
  pk+1 | value1
  pk+2 | pk'
  ...
  pk'   | key2
  pk'+1 | value2
  pk'+2 | NULL

  Value value1 tt
  Value := fun (value : word) (x : unit) => emp True
  get key1 --> value1 (and you now "own" value1, which means nothing)

  put key1 value3 --> (1, value1) (and you now "own" value1, which means nothing)

  pk   | key1
  pk+1 | value3
  pk+2 | pk'
  ...
  pk'   | key2
  pk'+1 | value2
  pk'+2 | NULL
  ...
  pk3 | key3

  put key3 value4 --> (0, NULL)

  pk   | key1
  pk+1 | value3
  pk+2 | pk'
  ...
  pk'   | key2
  pk'+1 | value2
  pk'+2 | pk3
  ...
  pk3 | key3



  entry:

  pk   | key1
  pk+1 | pv1
  pk+2 | pk'
  ...
  pv1 | value1
  ...
  pk'   | key2
  pk'+1 | pv2
  pk'+2 | NULL
  ...
  pv2 | value2

  Value pv1 value1 * Value pv2 value2
  Value := fun (addr x : word) => mem[addr] = x
  Key := fun (addr : word) (x : unit) => emp True
  get key1 --> pv1
  get key2 --> pv2
  borrow pv1
  borrow pv2

  pk   | key1
  pk+1 | (pv1)
  pk+2 | pk'
  ...
  pv1 | value1
  ...
  pk'   | key2
  pk'+1 | (pv2)
  pk'+2 | NULL
  ...
  pv2 | value2

  put key1 pv2 (you own pv1 and pv2) --> 1 (map now owns pv2)

  pk   | key1
  pk+1 | pv2
  pk+2 | pk'
  ...
  pv1 | value1
  ...
  pk'   | key2
  pk'+1 | (pv2)
  pk'+2 | NULL
  ...
  pv2 | value2

  put key2 pv1 (you own pv1) --> 1 (map now owns pv1)

  pk   | key1
  pk+1 | pv2
  pk+2 | pk'
  ...
  pv1 | value1
  ...
  pk'   | key2
  pk'+1 | pv1
  pk'+2 | NULL
  ...
  pv2 | value2

   *)
  Import KVStore.

  Instance spec_of_map_put : spec_of put :=
    fun functions =>
      forall pm m pk k pv v R tr mem,
        (AnnotatedMap pm m
         * Key pk k * Value pv v * R)%sep mem ->
        WeakestPrecondition.call
          functions put tr mem [pm; pk; pv]
          (fun tr' mem' rets =>
             tr = tr'
             /\ length rets = 0%nat
             /\ match map.get m k with
                | Some (Borrowed _, old_v) =>
                  (AnnotatedMap pm (map.put m k (Owned, v))
                   * Key pk k * R)%sep mem'
                | _ =>
                  (* not allowed! no guarantees for you *)
                  True
                end).


  Definition do_or_default {A B}
             (a : option A) (f : A -> B) (default : B) : B :=
    match a with
    | Some a => f a
    | None => default
    end.

  Notation "'let/o'  x  :=  val  'goto_fail' default 'in'  body" :=
    (do_or_default val (fun x => body) default) (at level 4).

  (* look up k1 and k2, add their values and store in k3 *)
  Definition kvswap_gallina (m : map.rep (map:=map))
             (k1 k2 : key) : map.rep (map:=map) * key * key :=
    let/o v1 := map.get m k1 goto_fail (m, k1, k2) in
    let/o v2 := map.get m k2 goto_fail (m, k1, k2) in
    let/d m := map.put m k2 v1 in
    let/d m := map.put m k1 v2 in
    (m, k1, k2).

  (*
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
   *)

  Definition MapAndTwoKeys pm pk1 pk2 v :=
    let m := fst (fst v) in
    let k1 := snd (fst v) in
    let k2 := snd v in
    (Map pm m * Key pk1 k1 * Key pk2 k2)%sep.

  Definition deannotate (m : annotated_map) : map.rep (map:=map) :=
    map.fold
      (fun (m' : map.rep) (k : key) (v : annotation * value) =>
         map.put m' k (snd v)) map.empty m.

  Lemma get_deannotate_Some m k a v :
    map.get m k = Some (a, v) ->
    map.get (deannotate m) k = Some v.
  Admitted.
  Lemma get_deannotate_None m k :
    map.get m k = None ->
    map.get (deannotate m) k = None.
  Admitted.

  Definition is_owned {A} (an: annotation * A) :=
    match an with
    | (Owned, _) => True
    | _ => False
    end.
  (* Arguments is_owned {A} / !an. *)

  Definition is_borrowed {A} (an: annotation * A) :=
    match an with
    | (Borrowed _, _) => True
    | _ => False
    end.
  (* Arguments is_borrowed {A} / !an. *)

  Lemma get_annotate_is_Owned:
    forall (m : map) (k1 : key) (a : annotation * value),
      map.get (annotate m) k1 = Some a -> is_owned a.
  Proof.
    intros m k1 a H.
    autorewrite with mapsimpl in H.
    destruct_one_match_hyp.
    - match goal with
      | [ H: Some _ = Some _ |- _ ] => inversion H
      end.
      reflexivity.
    - discriminate.
  Qed.

  Lemma compile_map_get :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr R R' functions T (pred: T -> _ -> Prop)
           m m_ptr m_var M
           k k_ptr k_var
           default default_impl
           K K_impl,
      spec_of_map_get functions ->
      m = deannotate M ->
    forall err var,
      var <> err ->
      (AnnotatedMap m_ptr M * Key k_ptr k * R')%sep mem ->
      map.get locals m_var = Some m_ptr ->
      map.get locals k_var = Some k_ptr ->
      (forall a, map.get M k = Some a -> is_owned a) ->
      let v := (map.get m k) in
      (forall garbage mem',
          v = None ->
          (AnnotatedMap m_ptr M * Key k_ptr k * R')%sep mem' ->
          find default_impl
          implementing (pred default)
          and-locals-post locals_ok
          with-locals (map.put (map.put locals err (word.of_Z 1))
                            var garbage)
          and-memory mem' and-trace tr and-rest R
          and-functions functions) ->
      (forall head hd_ptr mem',
          v = Some head ->
          (AnnotatedMap m_ptr
                        (map.put M k
                                 (Reserved hd_ptr, head))
           * Key k_ptr k * R')%sep mem' ->
          find K_impl
          implementing (pred (K head))
          and-locals-post locals_ok
          with-locals (map.put (map.put locals err (word.of_Z 0))
                            var hd_ptr)
          and-memory mem' and-trace tr and-rest R
          and-functions functions) ->
      (let head := v in
       find (cmd.seq
               (cmd.call [err; var] (fst (@KVStore.get ops)) [expr.var m_var; expr.var k_var])
               (cmd.cond (expr.op bopname.eq (expr.var err) (expr.literal 0))
                         K_impl
                         default_impl))
       implementing (pred (do_or_default head K default))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    exists [m_ptr; k_ptr].
    split.
    { cbn.
      eexists; split; [ eassumption | ].
      eexists; split; [ eassumption | ].
      reflexivity. }
    kv_hammer.
    destruct_one_match_hyp_of_type (option (annotation * value)).
    { destruct_products.
      destruct_one_match_hyp_of_type annotation;
        match goal with
        | [ H: forall a, Some _ = Some a -> _ |- _ ] => specialize (H _ eq_refl); cbn in H
        end; try contradiction.
      subst. subst m. subst v.
      match goal with
      | l := context [map.put _ err] |- _ => subst l
      end.
      erewrite get_deannotate_Some by eassumption.
      cbn [do_or_default].
      exists (word.of_Z 1).
      split.
      { eexists.
        split.
        { rewrite ?map.get_put_diff, map.get_put_same by congruence.
          reflexivity. }
        { cbv [WeakestPrecondition.expr
                 WeakestPrecondition.expr_body
                 WeakestPrecondition.literal
                 Semantics.interp_binop dlet.dlet].
          rewrite word.eqb_eq; reflexivity. } }
      { rewrite word.unsigned_of_Z_1.
        split; try congruence; [ ]. intros.
        cbn [fst snd].
        match goal with
        | H : _ |- _ => apply H
        end.
        { erewrite get_deannotate_Some by eassumption.
          reflexivity. }
        { ecancel_assumption. } } }
    { destruct_products.
      subst. subst m. subst v.
      match goal with
      | l := context [map.put _ err] |- _ => subst l
      end.
      erewrite get_deannotate_None by eassumption.
      cbn [do_or_default].
      exists (word.of_Z 0).
      split.
      { eexists.
        split.
        { rewrite ?map.get_put_diff, map.get_put_same by congruence.
          reflexivity. }
        { cbv [WeakestPrecondition.expr
                 WeakestPrecondition.expr_body
                 WeakestPrecondition.literal
                 Semantics.interp_binop dlet.dlet].
          destr (word.eqb (word.of_Z 1) (word.of_Z 0)); congruence. } }
      { rewrite word.unsigned_of_Z_0.
        split; try congruence; [ ]. intros.
        cbn [fst snd].
        match goal with
        | H : _ |- _ => apply H
        end.
        { eapply get_deannotate_None. eassumption. }
        { ecancel_assumption. } } }
  Qed.

  (*
  Instance spec_of_map_put : spec_of put :=
    fun functions =>
      forall pm m pk k pv v R tr mem,
        (AnnotatedMap pm m
         * Key pk k * Value pv v * R)%sep mem ->
        WeakestPrecondition.call
          functions put tr mem [pm; pk; pv]
          (fun tr' mem' rets =>
             tr = tr'
             /\ length rets = 2%nat
             /\ let was_overwrite := hd (word.of_Z 0) rets in
               let old_ptr := hd (word.of_Z 0) (tl rets) in
               match map.get m k with
               | Some (a, old_v) =>
                 match a with
                 | Borrowed _ => True (* no guarantees *)
                 | Reserved pv' =>
                   was_overwrite = word.of_Z 1
                   /\ old_ptr = pv'
                   /\ (AnnotatedMap pm (map.put m k (Reserved pv, v))
                      * Key pk k * Value old_ptr old_v * R)%sep mem'
                 | Owned =>
                   was_overwrite = word.of_Z 1
                   /\ (AnnotatedMap pm (map.put m k (Owned, v))
                      * Key pk k * Value old_ptr old_v * R)%sep mem'
                 end
               | None =>
                 (* if there was no previous value, the map consumes both
                     the key and value memory *)
                 was_overwrite = word.of_Z 0
                 /\ (AnnotatedMap pm (map.put m k (Owned, v))
                    * R)%sep mem'
               end).
   *)

  Lemma compile_map_put_replace :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
           tr R R' functions T (pred: T -> _ -> Prop)
           m m_ptr m_var M
           k k_ptr k_var
           v v_ptr v_var
           K K_impl,
      spec_of_map_put functions ->
      m = deannotate M ->
      (AnnotatedMap m_ptr M * Key k_ptr k * Value v_ptr v * R')%sep mem ->
      map.get locals m_var = Some m_ptr ->
      map.get locals k_var = Some k_ptr ->
      map.get locals v_var = Some v_ptr ->
      (exists a, map.get M k = Some a /\ is_borrowed a) ->
      let m := (map.put m k v) in (* FIXME this should say put_replace *)
      (forall mem',
         let head := m in
         (AnnotatedMap m_ptr (map.put M k (Owned, v))
          * Key k_ptr k * R')%sep mem' ->
         find K_impl
         implementing (pred (K head))
         and-locals-post locals_ok
         with-locals locals
         and-memory mem' and-trace tr and-rest R
         and-functions functions) ->
      (let head := m in
       find (cmd.seq
               (cmd.call []
                         (fst (@KVStore.put ops))
                         [expr.var m_var; expr.var k_var; expr.var v_var])
               K_impl)
       implementing (pred (dlet head K))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    repeat straightline.
    exists [m_ptr; k_ptr; v_ptr].
    split.
    { cbn.
      eexists; split; eauto.
      eexists; split; eauto.
      eexists; split; eauto. }
    { kv_hammer.
      match goal with
      | [ H: forall mem, _ mem -> _ |- _ ] => apply H
      end.
      destruct_one_match_hyp_of_type annotation; try contradiction.
      eassumption. }
  Qed.

  Hint Resolve get_annotate_is_Owned : compiler.

  Lemma deannotate_annotate:
    forall m : map, m = deannotate (annotate m).
  Proof.
  Admitted.

  Hint Extern 1 (?m = deannotate (annotate ?m)) => simple apply deannotate_annotate : compiler.

  Lemma get_deannotate_annotate:
    forall k v (m : map),
      map.get m k = v ->
      map.get (deannotate (annotate m)) k = v.
  Proof.
    intros. rewrite <- deannotate_annotate; eauto.
  Qed.

  Hint Resolve get_deannotate_annotate : compiler.
  Hint Unfold MapAndTwoKeys : compiler.

  Lemma deannotate_put:
    forall (m : map) M (k : key) (p : annotation * value),
      m = map.put (deannotate M) k (snd p) ->
      m = deannotate (map.put M k p).
  Proof.
  Admitted.

  Hint Resolve deannotate_put : compiler.

  Hint Extern 1 => simple eapply put_noop' : compiler.


  Axiom __magic__ : forall {A}, A.
  Ltac admitt := exfalso; clear; apply __magic__.

  Derive kvswap_body SuchThat
         (let kvswap := ("kvswap", (["m"; "k1"; "k2"], [],
                                    kvswap_body)) in
          program_logic_goal_for kvswap
          (forall functions,
              spec_of_map_get functions ->
              spec_of_map_put functions ->
              forall pm m pk1 k1 pk2 k2 R tr mem,
                k1 <> k2 -> (* TODO: try removing *)
                (Map pm m * Key pk1 k1 * Key pk2 k2 * R)%sep mem ->
                WeakestPrecondition.call
                  (kvswap :: functions)
                  "kvswap"
                  tr mem [pm; pk1; pk2]
                  (postcondition_for
                     (MapAndTwoKeys
                        pm pk1 pk2
                        (kvswap_gallina m k1 k2)) R tr)))
      As kvswap_body_correct.
  Proof.
    setup.
    (* Is there a systematic way to move from unannotated to annotated? The
    annotated spec is better for composing definitions, but the unannotated
    one is better for reading specs. *)
    add_map_annotations.
    eapply compile_map_get with (var:="v1") (err:="err") (M:=annotate m).
    all: repeat compile_step; eauto with compiler.
    { match goal with
      | [  |- _ <> _ ] => congruence
      end. }
    { intros.               (* FIXME compile_step *)
      clear_old_seps.
      compile_done.
      autounfold with compiler.
      cbn [fst snd].
      remove_map_annotations. (* FIXME *)
      compile_step. }
    { intros.
      clear_old_seps.
      eapply compile_map_get with (var:="v2") (err:="err"); repeat compile_step.
      { eauto with compiler. }
      { match goal with
        | [  |- _ <> _ ] => congruence
        end. }
      { intros.
        Hint Rewrite @map.get_put_diff @map.get_put_same @map.put_put_same
             @annotate_get_Some @annotate_get_None
             using (typeclasses eauto || congruence) : mapsimpl_not_too_much.

        autorewrite with mapsimpl_not_too_much in *. (* FIXME is that enough for the other cases? *)
        eauto with compiler. }
      { intros.
        clear_old_seps.
        repeat compile_step.
        remove_map_annotations. (* Should be done only in the skip case *)
        compile_done. }
      { intros; clear_old_seps.
        eapply compile_map_put_replace;
          lazymatch goal with
          | [  |- sep _ _ _ ] => borrow_all
          | _ => idtac
          end.
        3: ecancel_assumption.
        all: repeat compile_step; eauto with compiler.
        { simple apply deannotate_put.
          cbn.
          eapply put_noop';
            eauto 10 with compiler.
          autorewrite with mapsimpl_not_too_much.
          admitt.
        }
        all: eauto.
        { repeat match goal with
                 | [  |- exists _, _ ] => eexists
                 | [  |- _ /\ _ ] => split
                 | _ => progress autorewrite with mapsimpl_not_too_much
                 | _ => reflexivity
                 end. }
        intros.
        clear_old_seps.

        (* autorewrite with mapsimpl. *)
        (* rewrite map.put_put_same in H3. *)

        eapply compile_map_put_replace;
          lazymatch goal with
          | [  |- sep _ _ _ ] => try borrow_all
          | _ => idtac
          end.

        all: repeat compile_step; eauto with compiler.

        all: subst head1.
        { apply map.map_ext.
          intros; autorewrite with mapsimpl.
          admitt. }
          { repeat match goal with
                 | [  |- exists _, _ ] => eexists
                 | [  |- _ /\ _ ] => split
                 | _ => progress autorewrite with mapsimpl_not_too_much
                 | _ => reflexivity
                      end. }
        { intros.
          clear_old_seps.
          repeat compile_step.
          remove_map_annotations. (* Should be done only in the skip case *)
          compile_done. }
  Abort.
End KVSwap.
