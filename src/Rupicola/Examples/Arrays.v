Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Lib.Loops.

Section with_parameters.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Section GetPut.
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

    Derive decr_br2fn SuchThat
           (defn! "decr"("p") { decr_br2fn },
            implements decr_gallina)
      As decr_br2fn_ok.
    Proof.
      compile.
    Qed.
  End GetPut.

  Section Loops.
    Definition mask_bytes (bs: ListArray.t byte) mask :=
      let/n bs := ListArray.map (byte.and mask) bs in bs.

    Definition xor_bytes (bs: ListArray.t byte) :=
      let/n r := Byte.x00 in
      let/n r := ListArray.fold_left byte.xor bs Byte.x00 in
      r.

    Definition incr_words (ws: ListArray.t word) :=
      let/n ws := ListArray.map (word.add (word.of_Z 1)) ws in ws.

    Definition sum_words (ws: ListArray.t word) :=
      let/n r := word.of_Z 0 in
      let/n r := ListArray.fold_left word.add ws r in
      r.

    Import LoopCompiler.
    Import SizedListArrayCompiler.
    Hint Extern 10 => lia : compiler_side_conditions.

    Notation bytes := (sizedlistarray_value access_size.one).
    Notation words := (sizedlistarray_value access_size.word).

    Instance spec_of_mask_bytes : spec_of "mask_bytes" :=
      fnspec! "mask_bytes" ptr wlen wmask / (bs : ListArray.t byte) mask R,
        { requires tr mem :=
            wmask = word.of_Z (byte.unsigned mask) /\
            wlen = word.of_Z (Z.of_nat (length bs)) /\
            Z.of_nat (length bs) < 2 ^ width /\
            (bytes (length bs) ptr bs ⋆ R) mem;
          ensures tr' mem' :=
            tr' = tr /\
            (bytes (length bs) ptr (mask_bytes bs mask) ⋆ R) mem' }.

    Derive mask_bytes_br2fn SuchThat
           (defn! "mask_bytes" ("bs", "len", "mask") { mask_bytes_br2fn },
            implements mask_bytes)
           As mask_bytes_br2fn_ok.
    Proof.
      Time compile.
    Qed.

    Instance spec_of_xor_bytes : spec_of "xor_bytes" :=
      fnspec! "xor_bytes" ptr wlen / (bs : ListArray.t byte) R ~> r,
        { requires tr mem :=
            wlen = word.of_Z (Z.of_nat (length bs)) /\
            Z.of_nat (length bs) < 2 ^ width /\
            (bytes (length bs) ptr bs ⋆ R) mem;
          ensures tr' mem' :=
            tr' = tr /\ r = word.of_Z (byte.unsigned (xor_bytes bs)) /\
            (bytes (length bs) ptr bs ⋆ R) mem' }.

    Derive xor_bytes_br2fn SuchThat
           (defn! "xor_bytes" ("bs", "len") ~> "r" { xor_bytes_br2fn },
            implements xor_bytes)
           As xor_bytes_br2fn_ok.
    Proof.
      Time compile.
    Qed.

    Instance spec_of_incr_words : spec_of "incr_words" :=
      fnspec! "incr_words" ptr wlen / (ws : ListArray.t word) R,
        { requires tr mem :=
            wlen = word.of_Z (Z.of_nat (length ws)) /\
            Z.of_nat (length ws) < 2 ^ width /\
            (words (length ws) ptr ws ⋆ R) mem;
          ensures tr' mem' :=
            tr' = tr /\
            (words (length ws) ptr (incr_words ws) ⋆ R) mem' }.

    Derive incr_words_br2fn SuchThat
           (defn! "incr_words" ("ws", "len") { incr_words_br2fn },
            implements incr_words)
           As incr_words_br2fn_ok.
    Proof.
      Time compile.
    Qed.

    Instance spec_of_sum_words : spec_of "sum_words" :=
      fnspec! "sum_words" ptr wlen / (ws : ListArray.t word) R ~> r,
        { requires tr mem :=
            wlen = word.of_Z (Z.of_nat (length ws)) /\
            Z.of_nat (length ws) < 2 ^ width /\
            (words (length ws) ptr ws ⋆ R) mem;
          ensures tr' mem' :=
            tr' = tr /\ r = word.of_Z (word.unsigned (sum_words ws)) /\
            (words (length ws) ptr ws ⋆ R) mem' }.

    Derive sum_words_br2fn SuchThat
           (defn! "sum_words" ("ws", "len") ~> "r" { sum_words_br2fn },
            implements sum_words)
           As sum_words_br2fn_ok.
    Proof.
      Time compile.
    Qed.
  End Loops.
End with_parameters.

From bedrock2 Require Import BasicC64Semantics NotationsInConstr.
Compute decr_br2fn (word := word).
Compute mask_bytes_br2fn (width := 64).
Compute xor_bytes_br2fn (word := word).
Compute incr_words_br2fn (word := word).
Compute sum_words_br2fn (word := word).
