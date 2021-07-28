Require Import Rupicola.Lib.Api.

(* Definition packet := *)
(*   hlist.t ["field1"; …; "ttl"] [Byte.byte; …; Byte.byte]. (* field1, ttl *) *)
(* FIXME move to VectorArray.t *)

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Context {width_sufficient : (2 < 2 ^ Semantics.width)%Z}. (* without this, we have no guarantee that index 2 fits in the allowed integer size *)

  Definition packet :=
    Vector.t Semantics.word 2. (* field1, ttl *)

  Notation field1_index := Fin.F1.
  Notation ttl_index := (Fin.FS Fin.F1).
  Notation field1 p := (Vector.nth p field1_index).
  Notation ttl p := (Vector.nth p ttl_index).

  Definition WordVector {n} (addr: address) (v: Vector.t Semantics.word n) : Semantics.mem -> Prop :=
    array scalar (word.of_Z 8) addr (Vector.to_list v).

  Definition Packet (addr: address) (p: packet)
    : Semantics.mem -> Prop :=
    WordVector addr p.

  Definition decr_gallina (p: packet) :=
    let/n ttl := (ttl p) in
    let/n m1 := word.of_Z (-1) in
    let/n ttl := word.add ttl m1 in
    let/n p := Vector.replace p ttl_index ttl in
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

  Lemma compile_nth {n} {tr mem locals functions}
        (vector: Vector.t Semantics.word n) offset:
    let v := Vector.nth vector offset in
    let noffset := proj1_sig (Fin.to_nat offset) in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      R vector_ptr vector_var var,

      (Z.of_nat n < 2 ^ Semantics.width)%Z ->

      sep (WordVector vector_ptr vector) R mem ->
      map.get locals vector_var = Some vector_ptr ->

      (let v := v in
       forall m,
         sep (WordVector vector_ptr vector) R m ->
         <{ Trace := tr;
            Memory := m;
            Locals := map.put locals var v;
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      (cmd.seq (cmd.set
                  var
                  (expr.load
                     access_size.word
                     (expr.op bopname.add
                              (expr.var vector_var)
                              (expr.literal ((@word.unsigned _ Semantics.word (word.of_Z 8) * Z.of_nat noffset))))))
               k_impl)
      <{ pred (nlet_eq [var] v k) }>.
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

  Lemma compile_replace {n} {tr mem locals functions}
        (vector: Vector.t Semantics.word n) offset value:
    let v := (Vector.replace vector offset value) in
    let noffset := proj1_sig (Fin.to_nat offset) in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      R vector_ptr vector_var value_var,

      (Z.of_nat n < 2 ^ Semantics.width)%Z ->
      sep (WordVector vector_ptr vector) R mem ->

      map.get locals vector_var = Some vector_ptr ->
      map.get locals value_var = Some value ->

      (let v := v in
       forall m,
         sep (WordVector vector_ptr v) R m ->
         <{ Trace := tr;
            Memory := m;
            Locals := locals;
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.store access_size.word
                         (expr.op bopname.add
                                  (expr.var vector_var)
                                  (expr.literal ((@word.unsigned _ Semantics.word (word.of_Z 8) *
                                                  Z.of_nat noffset))))
                         (expr.var value_var))
              k_impl
      <{ pred (nlet_eq [vector_var] v k) }>.
  Proof.
    intros.
    unfold WordVector in *.
    repeat straightline.
    exists (word.add vector_ptr
                     (word.of_Z (@word.unsigned _ Semantics.word (word.of_Z 8) * Z.of_nat noffset))).
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

  Hint Unfold Packet : compiler_cleanup.

  Instance spec_of_decr : spec_of "decr" :=
    fnspec! "decr" ptr / p R,
    { requires fns tr mem := (Packet ptr p ⋆ R) mem;
      ensures tr' mem' := tr' = tr /\ (Packet ptr (decr_gallina p) ⋆ R) mem' }.

  Hint Extern 1 => simple eapply compile_nth; shelve : compiler.
  Hint Extern 1 => simple eapply compile_replace; shelve : compiler.

  Derive decr_body SuchThat
         (defn! "decr"("p") { decr_body },
          implements decr_gallina)
    As decr_body_correct.
  Proof.
    compile.
  Qed.
End with_parameters.

Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.
Arguments decr_body /.
Eval simpl in decr_body.
