Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Lib.Loops.
Require Import Rupicola.Lib.WordNotations.
Require Import coqutil.Word.LittleEndianList.

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

  Section Casts.
    Notation bytes := (listarray_value (memT := mem) (word := word) access_size.one).
    Notation words := (listarray_value (memT := mem) (word := word) access_size.word).

    Notation of_nat n := (word.of_Z (Z.of_nat n)).
    Notation of_Z := word.of_Z.
    Notation unsigned := word.unsigned.

    Notation bs2ws := (bs2ws (word := word) (Memory.bytes_per (width := width) access_size.word)).
    Notation ws2bs := (ws2bs (word := word) (Memory.bytes_per (width := width) access_size.word)).
    Notation bytes_per_word := (Memory.bytes_per (width := width) access_size.word).

(*|
A simple program that takes as input an array of bytes, reinterprets it as an array of little-endian machine words, and counts the number of matches for a given search term in the resulting array.
|*)

    Definition count_ws (data: ListArray.t byte) (needle: word) :=
      let/n r := 0 in
      let/n data := bs2ws data in
      let/n r := ListArray.fold_left (fun r w64 =>
           let/n hit := word.eqb w64 needle in
           let/n r := r + Z.b2z hit in
           r)
        data 0 in
      let/n data := ws2bs data in
      r.

(*|
Instead of applying the mask byte by byte, the program starts by casting its input into a list of 64-bit words, processes these words, and finally casts the result back to a lists of bytes.  Without loading appropriate libraries, Rupicola will not recognize these patterns:
|*)

    Instance spec_of_count_ws : spec_of "count_ws" :=
      fnspec! "count_ws" ptr wlen needle / (bs: list byte) R ~> r, {
        requires tr mem :=
          wlen = of_nat (length bs) /\
          Z.of_nat (length bs) < 2 ^ width /\
          (Datatypes.length bs mod bytes_per_word = 0)%nat /\
          (bytes ptr bs ⋆ R) mem;
        ensures tr' mem' :=
          tr' = tr /\ r = of_Z (count_ws bs needle) /\
          (bytes ptr bs ⋆ R) mem'
      }.

    Lemma bytes_as_words ptr bs:
      (length bs mod bytes_per_word = 0)%nat ->
      Lift1Prop.iff1 (bytes ptr bs) (words ptr (bs2ws bs)).
    Proof. apply words_of_bytes. Qed.

    Lemma words_as_bytes ptr bs:
      (length bs mod bytes_per_word = 0)%nat ->
      Lift1Prop.iff1 (words ptr (bs2ws bs)) (bytes ptr bs).
    Proof. symmetry; apply words_of_bytes; assumption. Qed.

    Lemma compile_bs2ws [t m l σ] (bs: list byte):
      let v := bs2ws bs in
      forall {P} {pred: P v -> _} {k: nlet_eq_k P v} K r bs_var ptr,
        (bytes ptr bs ⋆ r) m ->
        (length bs mod bytes_per_word = 0)%nat ->
        (forall m' : mem,
          (words ptr v ⋆ r) m' ->
          <{ Trace := t; Memory := m'; Locals := l; Functions := σ }> K <{ pred (k v eq_refl) }>) ->
        <{ Trace := t; Memory := m; Locals := l; Functions := σ }>
          K
        <{ pred (let/n x as bs_var eq:Heq := v in k x Heq) }>.
    Proof. intros; seprewrite_in bytes_as_words H; eauto. Qed.

    Lemma compile_bs2ws_rev [t m l σ] (bs: list byte):
      let v := ws2bs (bs2ws bs) in
      forall {P} {pred: P v -> _} {k: nlet_eq_k P v} K r bs_var ptr,

        (words ptr (bs2ws bs) ⋆ r) m ->
        (length bs mod bytes_per_word = 0)%nat ->

        (forall m' : mem,
            (bytes ptr bs ⋆ r) m' ->
            <{ Trace := t; Memory := m'; Locals := l; Functions := σ }>
              K
            <{ pred (k v eq_refl) }>) ->

        <{ Trace := t; Memory := m; Locals := l; Functions := σ }>
          K
        <{ pred (let/n x as bs_var eq:Heq := v in k x Heq) }>.
    Proof. intros; seprewrite_in (words_as_bytes) H; eauto. Qed.

    Import UnsizedListArrayCompiler.

    Hint Extern 1 => simple eapply compile_bs2ws; shelve : compiler.
    Hint Extern 1 => simple eapply compile_bs2ws_rev; shelve : compiler.
    Hint Extern 1 => (pose proof bytes_per_range access_size.word) : nia.
    Hint Rewrite @bs2ws_length using solve[eauto with nia] : compiler_side_conditions.
    Hint Rewrite Nat2Z_inj_div : compiler_side_conditions.
    Hint Extern 10 => eauto with nia : compiler_side_conditions.

    Derive count_ws_br2fn SuchThat
      (defn! "count_ws"("data", "len", "needle") ~> "r" { count_ws_br2fn },
       implements count_ws) As count_ws_br2fn_ok.
    Proof.
      compile.
    Qed.
  End Casts.
End with_parameters.

From bedrock2 Require Import BasicC64Semantics NotationsCustomEntry.
Compute decr_br2fn (word := word).
Compute mask_bytes_br2fn (width := 64).
Compute xor_bytes_br2fn (word := word).
Compute incr_words_br2fn (word := word).
Compute sum_words_br2fn (word := word).
Compute count_ws_br2fn (word := word).
