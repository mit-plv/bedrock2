Require Import
        Rupicola.Lib.Api
        Rupicola.Lib.Loops
        Rupicola.Lib.Arrays
        Rupicola.Lib.InlineTables.
Require Import
        Rupicola.Examples.CRC32.Table.

(* Require Import bedrock2.Semantics. *)
(* Require Import coqutil.Word.Interface coqutil.Byte. *)

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Definition crc_table : list word :=
    List.map word.of_Z crc_table_Z.

  Program Definition crc32 (data : list byte) (*32bit or larger*) :=
    let/n crc32 := word.of_Z 0xFFFFFFFF in
    let/n crc32 :=
      ranged_for_u (word_ok := word_ok)
        (word.of_Z 0)
        (word.of_Z (Z.of_nat (length data)))
        (fun crc32 tok idx _ =>
           let/n b := (ListArray.get (data : ListArray.t byte) idx) in
           let/n nLookupIndex :=
             word.and (word.xor crc32 (word_of_byte b))
                      (word.of_Z 0xFF) in
           let/n nLookupRes := InlineTable.get crc_table nLookupIndex in
           let/n crc32 := word.sru crc32 (word.of_Z 8) in
           let/n crc32 := word.xor crc32 nLookupRes in
           (tok, crc32))
        crc32 in
    let/n crc32 := word.xor crc32 (word.of_Z 0xFFFFFFFF) in
    crc32.

  Lemma idx_in_bounds (w: word) :
    (Z.to_nat (word.unsigned (word.and w (word.of_Z 255))) < 256)%nat.
  Proof.
    pose proof word.unsigned_range (word.and w (word.of_Z 255)).
    apply (Z2Nat.inj_lt _ 256); [lia..|].
    eapply Z.le_lt_trans; [apply word.and_leq_right|].
    eapply Z.le_lt_trans; [apply word.unsigned_of_Z_le|].
    all: lia.
  Qed.

  Lemma length_representable :
    Z.of_nat (Datatypes.length (to_byte_table crc_table)) <= 2 ^ width.
  Proof.
    rewrite length_to_byte_table; simpl List.length.
    destruct width_cases as [-> | ->]; vm_compute; inversion 1.
  Qed.

  Instance spec_of_crc32 : spec_of "crc32" :=
    fnspec! "crc32" data_ptr len / (data : list byte) R ~> r,
    { requires tr mem :=
        (len = word.of_Z (Z.of_nat (length data)) /\
        (listarray_value AccessByte data_ptr data * R)%sep mem);
      ensures tr' mem' :=
        tr' = tr /\
        r = crc32 data /\
        (listarray_value AccessByte data_ptr data * R)%sep mem' }.

  Import LoopCompiler.
  Import UnsizedListArrayCompiler.

  Hint Resolve idx_in_bounds length_representable : compiler_side_conditions.

  Hint Rewrite word.unsigned_of_Z : compiler_side_conditions.
  Hint Extern 1 (_ < Z.of_nat ?n) => (pose proof word.wrap_of_nat_le n; lia)
         : compiler_side_conditions.

  Derive crc32_br2fn SuchThat
         (defn! "crc32" ("data", "len") ~> "crc32" { crc32_br2fn },
          implements crc32)
         As crc32_br2fn_ok.
  Proof.
    compile.
  Qed.
End __.

Require Import coqutil.Word.Naive.
Definition crc32_cbytes := Eval vm_compute in
  list_byte_of_string (ToCString.c_module [crc32_br2fn (word:=word64)]).
