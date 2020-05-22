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
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Map.SortedList.
Require Import coqutil.Tactics.destr.
Require Import coqutil.Tactics.Tactics.
Require Import Coq.Numbers.DecimalString.

Local Open Scope string_scope.
Import ListNotations.

Require Import Incr.
Import GallinaIncr.
Import dlet.

Module Ttl.
  Local Existing Instance bedrock2.BasicCSyntax.StringNames_params.
  Local Existing Instance BasicC64Semantics.parameters.
  Local Existing Instance BasicC64Semantics.parameters_ok.

  (* FIXME update bedrock2 to get rid of Semantics.byte *)
  (* Definition packet := *)
  (*   hlist.t ["field1"; …; "ttl"] [Semantics.byte; …; Semantics.byte]. (* field1, ttl *) *)

  Definition packet :=
    Vector.t Semantics.byte 2. (* field1, ttl *)

  Local Declare Scope sep_scope.
  Local Delimit Scope sep_scope with sep.
  Local Infix "*" := (sep) : sep_scope.

  Notation address := Semantics.word.

  Notation field1_index := Fin.F1.
  Notation ttl_index := (Fin.FS Fin.F1).
  Notation field1 p := (Vector.nth p field1_index).
  Notation ttl p := (Vector.nth p ttl_index).

  Definition ByteVector {n} (addr: address) (v: Vector.t Semantics.byte n) : Semantics.mem -> Prop :=
    array ptsto (word.of_Z 1) addr (Vector.to_list v).

  Definition Packet (addr: address) (p: packet) : Semantics.mem -> Prop :=
    ByteVector addr p.

  Definition decr_gallina (p: packet) :=
    let/d ttl := (ttl p) in
    let/d ttl := word.sub ttl (word.of_Z 1) in
    let/d p := Vector.replace p ttl_index ttl in
    p.

  Import GallinaIncr.

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

  Lemma compile_replace :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr R R' functions T (pred: T -> _ -> Prop)
      {n} (vector: Vector.t Semantics.byte n) vector_ptr vector_var
      value value_var offset
      k k_impl,
      (Z.of_nat n < 2 ^ Semantics.width)%Z ->
      sep (ByteVector vector_ptr vector) R' mem ->
      map.get locals vector_var = Some vector_ptr ->
      map.get locals value_var = Some value ->
      let v := (Vector.replace vector offset (word.of_Z (word.unsigned value))) in
      let zoffset := Z.of_nat (proj1_sig (Fin.to_nat offset)) in
      (let head := v in
       forall m,
         sep (ByteVector vector_ptr head) R' m ->
         (find k_impl
          implementing (pred (k head))
          with-locals locals
          and-memory m and-trace tr and-rest R
          and-functions functions)) ->
      (let head := v in
       find (cmd.seq (cmd.store access_size.one
                                (expr.op bopname.add
                                         (expr.var vector_var)
                                         (expr.literal zoffset))
                                (expr.var value_var))
                     k_impl)
       implementing (pred (dlet head k))
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    intros.
    unfold ByteVector in *.
    repeat straightline.
    exists (word.add vector_ptr (word.of_Z zoffset)).
    split.
    { repeat straightline; eauto.
      exists vector_ptr; intuition.
      reflexivity. }
    { exists value.
      split.
      { straightline.
        eexists; eauto. }
      { repeat straightline.
        eapply store_one_of_sep.
        { pose proof (vector_uncons vector).
          (let lemma0 := open_constr:(bytearray_index_inbounds
                                       (Vector.to_list vector)
                                       vector_ptr
                                       (word.of_Z zoffset) _) in
           let t := type of lemma0 in
           let t := (eval cbv zeta in t) in
           let lemma1 := open_constr:(lemma0 : t) in
           seprewrite0_in lemma1 H0).
          ecancel_assumption.
          Unshelve.
          subst zoffset.
          rewrite word.unsigned_of_Z.
          pose proof (proj2_sig (Fin.to_nat offset)) as Hlt.
          simpl in Hlt.
          rewrite Vector_to_list_length.
          unfold word.wrap.     (* FIXME lemmify *)
          rewrite Z.mod_small.
          { apply Nat2Z.inj_lt; eauto. }
          { split.
            { apply Zle_0_nat. }
            { etransitivity.
              { apply Nat2Z.inj_lt.
                eassumption. }
              { eassumption. } } } }
        { intros.
          apply H3.
          (let lemma0 := open_constr:(bytearray_index_inbounds
                                       (Vector.to_list v)
                                       vector_ptr
                                       (word.of_Z zoffset) _) in
           let t := type of lemma0 in
           let t := (eval cbv zeta in t) in
           let lemma1 := open_constr:(lemma0 : t) in
           seprewrite0 lemma1).
          admit.                (* Lemmas on Vector.to_list and replace *)
          Unshelve.
          subst zoffset.
          rewrite word.unsigned_of_Z.
          pose proof (proj2_sig (Fin.to_nat offset)) as Hlt.
          simpl in Hlt.
          rewrite Vector_to_list_length.
          unfold word.wrap.     (* FIXME lemmify *)
          rewrite Z.mod_small.
          { apply Nat2Z.inj_lt; eauto. }
          { split.
            { apply Zle_0_nat. }
            { etransitivity.
              { apply Nat2Z.inj_lt.
                eassumption. }
              { eassumption. } } } }
  Admitted.


  Derive decr_body SuchThat
       (let decr := ("decr", (["p"], [], decr_body)) in
        program_logic_goal_for decr
        (forall functions,
            forall pp p R tr mem,
              (Packet pp p * R)%sep mem ->
              WeakestPrecondition.call
                (decr :: functions)
                "decr"
                tr mem [pp]
                (postcondition_for
                   (Packet pp (decr_gallina p)) R tr)))
    As decr_body_correct.
  Proof.
    setup.
    repeat t.
