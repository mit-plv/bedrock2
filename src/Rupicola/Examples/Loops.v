Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Lib.Loops.
Require Import Rupicola.Examples.Cells.Cells.

Section Ex.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Ltac compile_loopy :=
    compile_setup;
    repeat compile_step || (apply compile_nlet_as_nlet_eq; compile_ranged_for);
    compile_done.

  Open Scope Z_scope.

  Notation "∅" := map.empty.
  Notation "m [[ k ← v ]]" :=
    (map.put m k v)
      (left associativity, at level 1,
       format "m [[ k  ←  v ]]").

  Lemma signed_lt_unsigned (w : Semantics.word):
    word.signed w <= word.unsigned w.
  Proof.
    pose proof word.unsigned_range w.
    rewrite word.signed_unsigned_dec.
    destruct Z_lt_le_dec; lia.
  Qed.

  Instance HasDefault_word : HasDefault word :=
    word.of_Z 0.

  Program Definition vect_memcpy {n1 n2} (len: word)
          (a1: VectorArray.t word n1)
          (a2: VectorArray.t word n2)
          (pr1: word.unsigned len < Z.of_nat n1)
          (pr2: word.unsigned len < Z.of_nat n2) :=
    let/n from := word.of_Z 0 in
    let/n a2 := ranged_for_u
                 from len
                 (fun a2 tok idx Hlt =>
                    let/n v := VectorArray.get a1 idx _ in
                    let/n a2 := VectorArray.put a2 idx _ v in
                    (tok, a2)) a2 in
    (a1, a2).
  Next Obligation.
    pose proof word.unsigned_range idx.
    pose proof word.unsigned_range len.
    unfold cast, Convertible_word_nat.
    lia.
  Qed.
  Next Obligation.
    pose proof word.unsigned_range idx.
    pose proof word.unsigned_range len.
    unfold cast, Convertible_word_nat.
    lia.
  Qed.

  Instance spec_of_vect_memcpy : spec_of "vect_memcpy" :=
    fnspec! "vect_memcpy" (len: word) (a1_ptr a2_ptr : address) /
          {n1} (a1: VectorArray.t word n1)
          {n2} (a2: VectorArray.t word n2)
          (pr1: word.unsigned len < Z.of_nat n1)
          (pr2: word.unsigned len < Z.of_nat n2)
          R,
    { requires fns tr mem :=
        (vectorarray_value AccessWord a1_ptr a1 ⋆
                           vectorarray_value AccessWord a2_ptr a2 ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        let res := vect_memcpy len a1 a2 pr1 pr2 in
        (vectorarray_value AccessWord a1_ptr (fst res) ⋆
                           vectorarray_value AccessWord a2_ptr (snd res) ⋆ R) mem' }.

  Derive vect_memcpy_body SuchThat
         (defn! "vect_memcpy"("len", "a1", "a2") { vect_memcpy_body },
          implements @vect_memcpy)
         As vect_memcpy_correct.
  Proof.
    compile_loopy.
  Qed.

  Program Definition vect_memcpy_s {n1 n2} (len: word)
          (a1: VectorArray.t word n1)
          (a2: VectorArray.t word n2)
          (pr1: word.signed len < Z.of_nat n1)
          (pr2: word.signed len < Z.of_nat n2) :=
    let/n from eq:_ := word.of_Z 0 in
    let/n a2 := ranged_for_s
                 from len
                 (fun a2 tok idx Hlt =>
                    let/n v := VectorArray.get a1 idx _ in
                    let/n a2 := VectorArray.put a2 idx _ v in
                    (tok, a2)) a2 in
    (a1, a2).
  Next Obligation.
    pose proof word.half_modulus_pos (word:=word).
    unfold cast, Convertible_word_nat.
    rewrite word.signed_of_Z, word.swrap_inrange in H0 by lia.
    rewrite word.signed_gz_eq_unsigned; lia.
  Qed.
  Next Obligation.
    pose proof word.half_modulus_pos (word:=word).
    unfold cast, Convertible_word_nat.
    rewrite word.signed_of_Z, word.swrap_inrange in H0 by lia.
    rewrite word.signed_gz_eq_unsigned; lia.
  Qed.

  Instance spec_of_vect_memcpy_s : spec_of "vect_memcpy_s" :=
    fnspec! "vect_memcpy_s" (len: word) (a1_ptr a2_ptr : address) /
          {n1} (a1: VectorArray.t word n1)
          {n2} (a2: VectorArray.t word n2)
          (pr1: word.signed len < Z.of_nat n1)
          (pr2: word.signed len < Z.of_nat n2)
          R,
    { requires fns tr mem :=
        (vectorarray_value AccessWord a1_ptr a1 ⋆
                           vectorarray_value AccessWord a2_ptr a2 ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        let res := vect_memcpy_s len a1 a2 pr1 pr2 in
        (vectorarray_value AccessWord a1_ptr (fst res) ⋆
                           vectorarray_value AccessWord a2_ptr (snd res) ⋆ R) mem' }.

  Derive vect_memcpy_s_body SuchThat
         (defn! "vect_memcpy_s"("len", "a1", "a2") { vect_memcpy_s_body },
          implements @vect_memcpy_s)
         As vect_memcpy_s_correct.
  Proof.
    compile_loopy.
  Qed.

  Definition list_memcpy (len: word)
             (a1: ListArray.t word)
             (a2: ListArray.t word) :=
    let/n from := word.of_Z 0 in
    let/n a2 := ranged_for_u
                 from len
                 (fun a2 tok idx Hlt =>
                    let/n v := ListArray.get a1 idx in
                    let/n a2 := ListArray.put a2 idx v in
                    (tok, a2)) a2 in
    (a1, a2).

  Instance spec_of_sizedlist_memcpy : spec_of "sizedlist_memcpy" :=
    fnspec! "sizedlist_memcpy" (len: word) (a1_ptr a2_ptr : address) /
          {n1} (a1: ListArray.t word)
          {n2} (a2: ListArray.t word)
          (pr1: word.unsigned len < Z.of_nat n1)
          (pr2: word.unsigned len < Z.of_nat n2)
          R,
    { requires fns tr mem :=
        (sizedlistarray_value AccessWord a1_ptr n1 a1 ⋆
                              sizedlistarray_value AccessWord a2_ptr n2 a2 ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        let res := list_memcpy len a1 a2 in
        (sizedlistarray_value AccessWord a1_ptr n1 (fst res) ⋆
                              sizedlistarray_value AccessWord a2_ptr n2 (snd res) ⋆ R) mem' }.

  Section Sz.
    Import SizedListArrayCompiler.
    Derive sizedlist_memcpy_body SuchThat
           (defn! "sizedlist_memcpy"("len", "a1", "a2") { sizedlist_memcpy_body },
            implements list_memcpy)
           As sizedlist_memcpy_correct.
    Proof.
      Hint Extern 1 => lia : compiler_cleanup.
      Time compile_loopy.
    Qed.
  End Sz.

  Instance spec_of_unsizedlist_memcpy : spec_of "unsizedlist_memcpy" :=
    fnspec! "unsizedlist_memcpy" (len: word) (a1_ptr a2_ptr : address) /
          (a1: ListArray.t word) (a2: ListArray.t word)
          (pr1: word.unsigned len < Z.of_nat (List.length a1))
          (pr2: word.unsigned len < Z.of_nat (List.length a2))
          R,
    { requires fns tr mem :=
        (listarray_value AccessWord a1_ptr a1 ⋆
                         listarray_value AccessWord a2_ptr a2 ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        let res := list_memcpy len a1 a2 in
        (listarray_value AccessWord a1_ptr (fst res) ⋆
                         listarray_value AccessWord a2_ptr (snd res) ⋆ R) mem' }.

  Section Unsz.
    Import UnsizedListArrayCompiler.

    Derive unsizedlist_memcpy_body SuchThat
           (defn! "unsizedlist_memcpy"("len", "a1", "a2") {
                  unsizedlist_memcpy_body },
            implements list_memcpy)
           As unsizedlist_memcpy_correct.
    Proof.
      compile_loopy.

      { lia. (* loop index in bounds + function precondition *) }
      { (* Note the call to induction.
           Without vectors or the sizedlist predicate, we need to check that the index is in bounds but we modified the array.
           Using a vector type instead keeps the inranged_for in the type and the statement of put specifies that the length is preserved.
           Putting that info in the representation predicates has a similar effect.
           Without this, we need to perform induction explicitly. *)
        subst a.
        unfold ranged_for'.
        apply ranged_for_break_ind.
        - simpl. lia.
        - intros; unfold nlet; cbn.
          rewrite ListArray.put_length.
          assumption. }
    Qed.
  End Unsz.

  Program Definition incr_gallina (c: cell) : cell :=
    let/n one := word.of_Z 1 in
    let/n from := word.of_Z 3 in
    let/n to := word.of_Z 5 in
    let/n tick := word.of_Z 0 in
    let/n (tick, c) :=
       ranged_for_u (A := P2.prod word cell)
                    from to
                    (fun '\< tick, c \> tok idx bounded =>
                       let/n v := get c in
                       let/n v := word.add v idx in
                       let/n c := put v c in
                       let/n tick := word.add tick one in
                       (tok, \< tick, c \>))
                    \< tick, c \> : P2.prod word cell in
    (let/n v := get c in
     let/n v := word.add v tick in
     let/n c := put v c in
     c).

  Instance spec_of_incr : spec_of "incr" :=
    fnspec! "incr" c_ptr / (c: cell) R,
    { requires fns tr mem :=
        (cell_value c_ptr c ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        (cell_value c_ptr (incr_gallina c) ⋆ R) mem' }.

  Derive incr_body SuchThat
         (defn! "incr"("c") { incr_body },
          implements incr_gallina)
         As body_correct.
  Proof.
    compile_loopy.
  Qed.
End Ex.

(* Require Import bedrock2.NotationsCustomEntry. *)
(* Require Import bedrock2.NotationsInConstr. *)
(* Eval cbv [sizedlist_memcpy_body unsizedlist_memcpy_body vect_memcpy_s_body fold_right noskips is_skip] in sizedlist_memcpy_body. *)
