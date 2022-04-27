Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Lib.Loops.
Require Import Rupicola.Examples.Cells.Cells.
Import LoopCompiler.

Section Ex.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Program Definition vect_memcpy {n1 n2} (len: word)
          (a1: VectorArray.t word n1)
          (a2: VectorArray.t word n2)
          (pr1: word.unsigned len < Z.of_nat n1)
          (pr2: word.unsigned len < Z.of_nat n2) :=
    let/n a2 := ranged_for_u
                 (word.of_Z 0) len
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
    fnspec! "vect_memcpy" (len: word) (a1_ptr a2_ptr : word) /
          {n1} (a1: VectorArray.t word n1)
          {n2} (a2: VectorArray.t word n2)
          (pr1: word.unsigned len < Z.of_nat n1)
          (pr2: word.unsigned len < Z.of_nat n2)
          R,
    { requires tr mem :=
        (vectorarray_value AccessWord a1_ptr a1 ⋆
                           vectorarray_value AccessWord a2_ptr a2 ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        let res := vect_memcpy len a1 a2 pr1 pr2 in
        (vectorarray_value AccessWord a1_ptr (fst res) ⋆
                           vectorarray_value AccessWord a2_ptr (snd res) ⋆ R) mem' }.

  Derive vect_memcpy_br2fn SuchThat
         (defn! "vect_memcpy"("len", "a1", "a2") { vect_memcpy_br2fn },
          implements @vect_memcpy)
         As vect_memcpy_correct.
  Proof.
    compile.
  Qed.

  Program Definition vect_memcpy_s {n1 n2} (len: word)
          (a1: VectorArray.t word n1)
          (a2: VectorArray.t word n2)
          (pr1: word.signed len < Z.of_nat n1)
          (pr2: word.signed len < Z.of_nat n2) :=
    let/n a2 := ranged_for_s
                 (word.of_Z 0) len
                 (fun a2 tok idx Hlt =>
                    let/n v := VectorArray.get a1 idx _ in
                    let/n a2 := VectorArray.put a2 idx _ v in
                    (tok, a2)) a2 in
    (a1, a2).
  Next Obligation.
    pose proof word.half_modulus_pos (word:=word).
    unfold cast, Convertible_word_nat.
    rewrite word.signed_of_Z, word.swrap_inrange in H by lia.
    rewrite word.signed_gz_eq_unsigned; lia.
  Qed.
  Next Obligation.
    pose proof word.half_modulus_pos (word:=word).
    unfold cast, Convertible_word_nat.
    rewrite word.signed_of_Z, word.swrap_inrange in H by lia.
    rewrite word.signed_gz_eq_unsigned; lia.
  Qed.

  Instance spec_of_vect_memcpy_s : spec_of "vect_memcpy_s" :=
    fnspec! "vect_memcpy_s" (len: word) (a1_ptr a2_ptr : word) /
          {n1} (a1: VectorArray.t word n1)
          {n2} (a2: VectorArray.t word n2)
          (pr1: word.signed len < Z.of_nat n1)
          (pr2: word.signed len < Z.of_nat n2)
          R,
    { requires tr mem :=
        (vectorarray_value AccessWord a1_ptr a1 ⋆
                           vectorarray_value AccessWord a2_ptr a2 ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        let res := vect_memcpy_s len a1 a2 pr1 pr2 in
        (vectorarray_value AccessWord a1_ptr (fst res) ⋆
                           vectorarray_value AccessWord a2_ptr (snd res) ⋆ R) mem' }.

  Derive vect_memcpy_s_br2fn SuchThat
         (defn! "vect_memcpy_s"("len", "a1", "a2") { vect_memcpy_s_br2fn },
          implements @vect_memcpy_s)
         As vect_memcpy_s_correct.
  Proof.
    compile.
  Qed.

  Definition list_memcpy (len: word)
             (a1: ListArray.t word)
             (a2: ListArray.t word) :=
    let/n a2 := ranged_for_u
                 (word.of_Z 0) len
                 (fun a2 tok idx Hlt =>
                    let/n v := ListArray.get a1 idx in
                    let/n a2 := ListArray.put a2 idx v in
                    (tok, a2)) a2 in
    (a1, a2).

  Instance spec_of_sizedlist_memcpy : spec_of "sizedlist_memcpy" :=
    fnspec! "sizedlist_memcpy" (len: word) (a1_ptr a2_ptr : word) /
          {n1} (a1: ListArray.t word)
          {n2} (a2: ListArray.t word)
          (pr1: word.unsigned len < Z.of_nat n1)
          (pr2: word.unsigned len < Z.of_nat n2)
          R,
    { requires tr mem :=
        (sizedlistarray_value AccessWord n1 a1_ptr a1 ⋆
         sizedlistarray_value AccessWord n2 a2_ptr a2 ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        let res := list_memcpy len a1 a2 in
        (sizedlistarray_value AccessWord n1 a1_ptr (fst res) ⋆
         sizedlistarray_value AccessWord n2 a2_ptr (snd res) ⋆ R) mem' }.

  Section Sz.
    Import SizedListArrayCompiler.
    Derive sizedlist_memcpy_br2fn SuchThat
           (defn! "sizedlist_memcpy"("len", "a1", "a2") { sizedlist_memcpy_br2fn },
            implements list_memcpy)
           As sizedlist_memcpy_correct.
    Proof.
      Hint Extern 1 => lia : compiler_side_conditions.
      Time compile.
    Qed.
  End Sz.

  Instance spec_of_unsizedlist_memcpy : spec_of "unsizedlist_memcpy" :=
    fnspec! "unsizedlist_memcpy" (len: word) (a1_ptr a2_ptr : word) /
          (a1: ListArray.t word) (a2: ListArray.t word)
          (pr1: word.unsigned len <= Z.of_nat (List.length a1))
          (pr2: word.unsigned len <= Z.of_nat (List.length a2))
          R,
    { requires tr mem :=
        (listarray_value AccessWord a1_ptr a1 ⋆
                         listarray_value AccessWord a2_ptr a2 ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        let res := list_memcpy len a1 a2 in
        (listarray_value AccessWord a1_ptr (fst res) ⋆
                         listarray_value AccessWord a2_ptr (snd res) ⋆ R) mem' }.

  Section Unsz.
    Import UnsizedListArrayCompiler.

    Derive unsizedlist_memcpy_br2fn SuchThat
           (defn! "unsizedlist_memcpy"("len", "a1", "a2") {
                  unsizedlist_memcpy_br2fn },
            implements list_memcpy)
           As unsizedlist_memcpy_correct.
    Proof.
      compile_setup; repeat compile_step.

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
    let/n tick := word.of_Z 0 in
    let/n (tick, c) :=
       ranged_for_u
         (word.of_Z 3) (word.of_Z 5)
         (fun '\< tick, c \> tok idx bounded =>
            let/n v := get c in
            let/n v := word.add v idx in
            let/n c := put v in
            let/n tick := word.add tick (word.of_Z 1) in
            (tok, \< tick, c \>))
         \< tick, c \> in
    (let/n v := get c in
     let/n v := word.add v tick in
     let/n c := put v in
     c).

  Instance spec_of_incr : spec_of "incr" :=
    fnspec! "incr" c_ptr / (c: cell) R,
    { requires tr mem :=
        (cell_value c_ptr c ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        (cell_value c_ptr (incr_gallina c) ⋆ R) mem' }.

  Derive incr_br2fn SuchThat
         (defn! "incr"("c") { incr_br2fn },
          implements incr_gallina)
         As incr_br2fn_ok.
  Proof.
    compile.
  Qed.
End Ex.

Require bedrock2.BasicC64Semantics.

Module RangedForTests.
  (* This module lives here instead of in Lib/Arrays because the instances in
     BasicC64Semantics are global, so simply `Require`-ing that module is enough
     to pollute the context. *)
  Import BasicC64Semantics.

  Time Compute (ranged_for 0 15
                        (fun acc t idx _ =>
                           if Z.ltb 11 idx then
                             let t' := ExitToken.break t in
                             (t', acc)
                           else
                             let acc := idx :: acc in
                             (t, acc)) []).

  Time Compute (ranged_for_u (word.of_Z 0) (word.of_Z 15)
                          (fun acc t idx _ =>
                             if word.ltu (word.of_Z 11) idx then
                               let t' := ExitToken.break t in
                               (t', acc)
                             else
                               let acc := idx :: acc in
                               (t, acc)) []).
End RangedForTests.

From bedrock2 Require Import BasicC64Semantics NotationsCustomEntry.
Compute sizedlist_memcpy_br2fn (word := word).
Compute unsizedlist_memcpy_br2fn (word := word).
Compute vect_memcpy_s_br2fn (word := word).
