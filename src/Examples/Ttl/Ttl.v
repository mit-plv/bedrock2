Require Import Rupicola.Lib.Api.

(* Definition packet := *)
(*   hlist.t ["field1"; …; "ttl"] [Byte.byte; …; Byte.byte]. (* field1, ttl *) *)

Section with_semantics.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {width_gt_1 : (1 < Semantics.width)%Z}. (* without this, we have no guarantee that index 2 fits in the allowed integer size *)

  Definition packet :=
    Vector.t Semantics.word 2. (* field1, ttl *)

  Notation field1_index := Fin.F1.
  Notation ttl_index := (Fin.FS Fin.F1).
  Notation field1 p := (Vector.nth p field1_index).
  Notation ttl p := (Vector.nth p ttl_index).

  Definition WordVector {n} (addr: address) (v: Vector.t Semantics.word n) : Semantics.mem -> Prop :=
    array scalar (word.of_Z 8) addr (Vector.to_list v).

  Definition Packet (addr: address) (p: packet) : Semantics.mem -> Prop :=
    WordVector addr p.

  Definition decr_gallina (p: packet) :=
    let/d ttl := (ttl p) in
    let/d m1 := word.of_Z (-1) in
    let/d ttl := word.add ttl m1 in
    let/d p := Vector.replace p ttl_index ttl in
    p.

  Lemma vector_uncons {A n} (v: Vector.t A n) :
    match n return Vector.t A n -> Prop with
    | 0 => fun v => v = Vector.nil _
    | S n =>fun v => v = Vector.cons _ (Vector.hd v) _ (Vector.tl v)
    end v.
  Proof.
    destruct v; reflexivity.
  Qed.

  Lemma Vector_to_list_length {A n} (v: Vector.t A n):
    Datatypes.length (Vector.to_list v) = n.
  Proof. Admitted.

  Lemma compile_nth :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr R R' functions T (pred: T -> _ -> Prop)
      {n} (vector: Vector.t Semantics.word n) vector_ptr vector_var
      offset var k k_impl,
      (Z.of_nat n < 2 ^ Semantics.width)%Z ->
      sep (WordVector vector_ptr vector) R' mem ->
      map.get locals vector_var = Some vector_ptr ->
      let v := Vector.nth vector offset in
      let noffset := proj1_sig (Fin.to_nat offset) in
      (let head := v in
       forall m,
         sep (WordVector vector_ptr vector) R' m ->
         (find k_impl
          implementing (pred (k head))
          and-locals-post locals_ok
          with-locals (map.put locals var head)
          and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq (cmd.set
                        var
                        (expr.load
                           access_size.word
                           (expr.op bopname.add
                                    (expr.var vector_var)
                                    (expr.literal ((word.unsigned (word.of_Z 8) * Z.of_nat noffset))))))
                     k_impl)
       implementing (pred (dlet head k))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    unfold WordVector in *.
    repeat straightline.
    exists (word.of_Z (word.unsigned v)).
    split.
    { repeat straightline; eauto.
      exists vector_ptr; intuition.
      seprewrite_in @array_index_nat_inbounds H0;
        cycle 1.
      { eexists.
        split.
        { eapply load_word_of_sep.
          ecancel_assumption. }
      { subst v.
        (* FIXME: vector/list lemmas *)
        admit. } }
      { rewrite Vector_to_list_length.
        apply (proj2_sig (Fin.to_nat offset)). } }
    { repeat straightline.
      cbv [dlet.dlet].
      subst l.
      rewrite word.of_Z_unsigned.
      eauto. }
    Unshelve.
    apply (word.of_Z 0).
    Admitted.

  Lemma compile_replace :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr R R' functions T (pred: T -> _ -> Prop)
      {n} (vector: Vector.t Semantics.word n) vector_ptr vector_var
      value value_var offset
      k k_impl,
      (Z.of_nat n < 2 ^ Semantics.width)%Z ->
      sep (WordVector vector_ptr vector) R' mem ->
      map.get locals vector_var = Some vector_ptr ->
      map.get locals value_var = Some value ->
      let v := (Vector.replace vector offset value) in
      let noffset := proj1_sig (Fin.to_nat offset) in
      (let head := v in
       forall m,
         sep (WordVector vector_ptr head) R' m ->
         (find k_impl
          implementing (pred (k head))
          and-locals-post locals_ok
          with-locals locals
          and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq (cmd.store access_size.word
                                (expr.op bopname.add
                                         (expr.var vector_var)
                                         (expr.literal ((word.unsigned (word.of_Z 8) * Z.of_nat noffset))))
                                (expr.var value_var))
                     k_impl)
       implementing (pred (dlet head k))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    unfold WordVector in *.
    repeat straightline.
    exists (word.add vector_ptr
                     (word.of_Z (word.unsigned (word.of_Z 8) * Z.of_nat noffset))).
    split.
    { repeat straightline; eauto.
      exists vector_ptr; intuition.
      reflexivity. }
    { exists value.
      split.
      { straightline.
        eexists; eauto. }
      { repeat straightline.
        eapply store_word_of_sep.
        { seprewrite_in @array_index_nat_inbounds H0;
            cycle 1.
          { ecancel_assumption. }
          { subst noffset.
            rewrite Vector_to_list_length.
            apply (proj2_sig (Fin.to_nat offset)). } }
        { intros.
          apply H3.
          seprewrite (array_index_nat_inbounds (default:=word.of_Z 0) scalar (word.of_Z 8) (Vector.to_list v) vector_ptr (proj1_sig (Fin.to_nat offset))); cycle 1.
          { admit.                (* Lemmas on Vector.to_list and replace *)
          }
          { subst noffset.
            rewrite Vector_to_list_length.
            apply (proj2_sig (Fin.to_nat offset)). } }
  Admitted.

  Hint Unfold Packet : compiler.
  Opaque dlet.

  Instance spec_of_decr : spec_of "decr" :=
    forall! pp p,
      (sep (Packet pp p)) ===> "decr" @ [pp] ===> Packet pp (decr_gallina p).

  (* TODO: something like program_logic_goal_for_function! *)
  Derive decr_body SuchThat
         (let decr := ("decr", (["p"], [], decr_body)) in
          program_logic_goal_for
            decr
            (ltac:(let x := program_logic_goal_for_function decr (@nil string) in
                   exact x)))
    As decr_body_correct.
  Proof.
    cbv [program_logic_goal_for spec_of_decr].
    setup.
    assert (Z.of_nat 2 < 2 ^ Semantics.width)%Z
      by (change (Z.of_nat 2) with (2 ^ 1)%Z;
          apply Z.pow_lt_mono_r; lia).
    eapply compile_nth with (var := "ttl").
    all:repeat compile_step.
    eapply compile_replace.
    all:repeat compile_step.
    compile_done.
  Qed.

End with_semantics.
