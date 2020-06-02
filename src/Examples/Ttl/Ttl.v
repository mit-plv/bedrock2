Require Import Rupicola.Lib.Api.

Local Notation function_t :=
  ((String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type).
Local Notation functions_t :=
  (list function_t).

(* modified version of program_logic_goal_for_function, in which callee names
  are manually inserted *)
Ltac program_logic_goal_for_function proc callees :=
  let __ := constr:(proc : function_t) in
  let fname := (eval cbv in (fst proc)) in
  let callees := (eval cbv in callees) in
  let spec := lazymatch constr:(_:spec_of fname) with ?s => s end in
  constr:(forall functions : functions_t,
             ltac:(let s := assuming_correctness_of_in
                              callees functions
                              (spec (cons proc functions)) in
                   exact s)).

(* Definition packet := *)
(*   hlist.t ["field1"; …; "ttl"] [Byte.byte; …; Byte.byte]. (* field1, ttl *) *)

Definition packet :=
  Vector.t Semantics.word 2. (* field1, ttl *)

Local Declare Scope sep_scope.
Local Delimit Scope sep_scope with sep.
Local Infix "*" := (sep) : sep_scope.

Notation address := Semantics.word.

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

Notation "'forall!' x .. y ',' pre '===>' fname '@' args '==>' post" :=
  (fun functions =>
     (forall x,
         .. (forall y,
                forall R tr mem,
                  (pre * R)%sep mem ->
                  WeakestPrecondition.call
                    functions fname tr mem args
                    (postcondition_for post R tr)) ..))
       (x binder, y binder, only parsing, at level 199).
Instance spec_of_decr : spec_of "decr" :=
  forall! pp p,
    Packet pp p ===> "decr" @ [pp] ==> Packet pp (decr_gallina p).

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
  assert (Z.of_nat 2 < 2 ^ Semantics.width)%Z by (cbn; lia).
  eapply compile_nth with (var := "ttl").
  1-3:repeat compile_step; eauto.
  do 6 compile_step.
  1-2:repeat compile_step.
  intros.
  eapply compile_replace.
  1-4:repeat compile_step; eauto.
  repeat compile_step.
Qed.
