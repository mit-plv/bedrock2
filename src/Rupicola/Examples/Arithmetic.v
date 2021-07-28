Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Lib.Loops.
From bedrock2 Require BasicC32Semantics BasicC64Semantics.

Module Type FNV1A_params.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Parameter prime : word.
  Parameter offset : word.
End FNV1A_params.

Module FNV1A (P: FNV1A_params).
  Existing Instances P.semantics P.semantics_ok.
  Import SizedListArrayCompiler.

  Notation "∅" := map.empty.
  Notation "m [[ k ← v ]]" :=
    (map.put m k v)
      (left associativity, at level 1,
       format "m [[ k  ←  v ]]").

  Definition update (hash data : word) :=
    let/n p := P.prime in
    let/n hash := word.xor hash data in
    let/n hash := word.mul hash p in
    hash.

  Implicit Type R : Semantics.mem -> Prop.
  Instance spec_of_update : spec_of "update" :=
    fnspec! "update" (hash: word) (data: word) ~> hash',
    { requires fns tr mem := True;
      ensures tr' mem' := tr = tr' /\ mem = mem' /\ hash' = update hash data }.

  Derive update_body SuchThat
         (defn! "update"("hash", "data") ~> "hash" { update_body },
          implements update)
         As update_body_correct.
  Proof.
    compile.
  Qed.

  Definition fnv1a (data: ListArray.t byte) len :=
    let/n p := P.prime in
    let/n hash := P.offset in
    let/n from := word.of_Z 0 in
    let/n hash := ranged_for_u
                   from len
                   (fun hash tok idx Hlt =>
                      let/n b := ListArray.get data idx in
                      let/n hash := word.mul (word.xor hash (word_of_byte b)) p in
                      (tok, hash)) hash in
    hash.

  Instance spec_of_fnv1a : spec_of "fnv1a" :=
    fnspec! "fnv1a" data_ptr len /
           (data: ListArray.t byte) n R
           (pr: word.unsigned len < Z.of_nat n)
           ~> hash,
    { requires fns tr mem :=
        (sizedlistarray_value AccessByte data_ptr n data ⋆ R) mem;
      ensures tr' mem' :=
        tr = tr' /\
        (sizedlistarray_value AccessByte data_ptr n data ⋆ R) mem' /\
        hash = fnv1a data len }.

  Derive fnv1a_body SuchThat
         (defn! "fnv1a"("data", "len") ~> "hash" { fnv1a_body },
          implements fnv1a)
         As fnv1a_body_correct.
  Proof.
    compile_setup; repeat compile_step.

     simple apply compile_nlet_as_nlet_eq.
     eapply compile_ranged_for_u with (loop_pred := (fun idx hash tr' mem' locals' =>
         tr' = tr /\
         locals' = ∅[["data" ← data_ptr]][["len" ← len]][["p" ← P.prime]]
                    [["hash" ← hash]][["from" ← idx]] /\
         (sizedlistarray_value AccessByte data_ptr n data ⋆ R) mem')).

     all: repeat repeat compile_step; try lia; compile_done.
  Qed.
End FNV1A.

Module FNV1A32_params <: FNV1A_params.
  Definition semantics : Semantics.parameters := BasicC32Semantics.parameters.
  Definition semantics_ok : Semantics.parameters_ok semantics := _.
  Definition prime : Naive.word32 := Eval compute in word.of_Z 16777619.
  Definition offset : Naive.word32 := Eval compute in word.of_Z 2166136261.
End FNV1A32_params.

Module FNV1A32 := FNV1A FNV1A32_params.

Module FNV1A64_params <: FNV1A_params.
  Definition semantics : Semantics.parameters := BasicC64Semantics.parameters.
  Definition semantics_ok : Semantics.parameters_ok semantics := _.
  Definition prime : Naive.word64 := Eval compute in word.of_Z 1099511628211.
  Definition offset : Naive.word64 := Eval compute in word.of_Z 14695981039346656037.
End FNV1A64_params.

Module FNV1A64 := FNV1A FNV1A64_params.

Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.

Eval cbv in FNV1A32.fnv1a_body.
Eval cbv in FNV1A64.fnv1a_body.

Module Murmur3.
  Import BasicC32Semantics.

  Definition scramble (k : word) :=
    let/n k := word.mul k (word.of_Z 513432918353) in
    let/n k := word.or (word.slu k (word.of_Z 15)) (word.sru k (word.of_Z 17)) in
    let/n k := word.mul k (word.of_Z 461845907) in
    k.

  Implicit Type R : Semantics.mem -> Prop.
  Instance spec_of_scramble : spec_of "scramble" :=
    fnspec! "scramble" (k: word) ~> k',
    { requires fns tr mem := True;
      ensures tr' mem' := tr = tr' /\ mem = mem' /\ k' = scramble k }.

  Derive scramble_body SuchThat
         (defn! "scramble"("k") ~> "k" { scramble_body },
          implements scramble)
         As scramble_body_correct.
  Proof.
    Time compile.                  (* 1.9s, 1.16 on compressed example; 2.02 s previously; but 4s to fail on compressed example *)
  Time Qed.                          (* 2.3, 0.35 on compressed example; instantaneous previously *)
End Murmur3.

Eval cbv in Murmur3.scramble_body.
