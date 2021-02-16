Require Import Rupicola.Lib.Api.
From bedrock2 Require BasicC32Semantics BasicC64Semantics.

Module Type FNV1A_params.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Parameter prime : word.
  Parameter offset : word.
End FNV1A_params.

Module FNV1A (P: FNV1A_params).
  Existing Instances P.semantics P.semantics_ok.

  Definition fnv1a_update (hash data : word) :=
    let/n p := P.prime in
    let/n hash := word.xor hash data in
    let/n hash := word.mul hash p in
    hash.

  Implicit Type R : Semantics.mem -> Prop.
  Instance spec_of_fnv1a_update : spec_of "fnv1a_update" :=
    fnspec "fnv1a_update" (hash: word) (data: word) / R ~> hash',
    { requires tr mem := R mem;
      ensures tr' mem' := R mem' /\ hash' = fnv1a_update hash data }.

  Derive fnv1a_update_body SuchThat
         (defn! "fnv1a_update"("hash", "data") ~> "hash" { fnv1a_update_body },
          implements fnv1a_update)
         As fnv1a_update_body_correct.
  Proof.
    compile.
  Qed.
End FNV1A.

Module FNV1A32_params <: FNV1A_params.
  Import BasicC32Semantics.
  Definition semantics : Semantics.parameters := _.
  Definition semantics_ok : Semantics.parameters_ok semantics := _.
  Definition prime := Eval compute in word.of_Z 16777619.
  Definition offset := Eval compute in word.of_Z 2166136261%Z.
End FNV1A32_params.

Module FNV1A32 := FNV1A FNV1A32_params.

Module FNV1A64_params <: FNV1A_params.
  Import BasicC64Semantics.
  Definition semantics : Semantics.parameters := _.
  Definition semantics_ok : Semantics.parameters_ok semantics := _.
  Definition prime := Eval compute in word.of_Z 16777619.
  Definition offset := Eval compute in word.of_Z 2166136261%Z.
End FNV1A64_params.

Module FNV1A64 := FNV1A FNV1A64_params.

Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.
Eval cbv in FNV1A32.fnv1a_update_body.
