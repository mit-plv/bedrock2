Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Arrays.

Section with_parameters.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Definition packet :=
    Vector.t word 2. (* field1, ttl *)

  Definition __lt {a b: nat} : if lt_dec a b return Prop then Nat.lt a b else True :=
    match lt_dec a b as c return (if c return Prop then Nat.lt a b else True) with
    | left pr => pr
    | _ => I
    end.

  Notation _lt :=
    ltac:(lazymatch goal with
          | [  |- (?a < ?b)%nat ] => exact (@__lt a b)
          end) (only parsing).

  Notation ttl_idx := 1%nat.
  Definition field1 (p: packet) := (VectorArray.get p 0%nat _lt).
  Definition ttl (p: packet) := (VectorArray.get p ttl_idx _lt).

  Definition Packet (addr: word) (p: packet) : mem -> Prop :=
    vectorarray_value AccessWord addr p.

  Definition decr_gallina (p: packet) :=
    let/n ttl := (ttl p) in
    let/n ttl := word.add ttl (word.of_Z (-1)) in
    let/n p := VectorArray.put p ttl_idx _lt ttl in
    p.

  Hint Unfold Packet : compiler_cleanup.

  Instance spec_of_decr : spec_of "decr" :=
    fnspec! "decr" ptr / p R,
    { requires tr mem :=
        (Packet ptr p ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\ (Packet ptr (decr_gallina p) ⋆ R) mem' }.

  Import VectorArrayCompiler.
  Hint Unfold ttl : compiler_cleanup.

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
