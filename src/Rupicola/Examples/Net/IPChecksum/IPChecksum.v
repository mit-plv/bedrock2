From Rupicola.Examples Require Import IPChecksum.Impl IPChecksum.Compiler.

Instance spec_of_ip_checksum : spec_of "ip_checksum" :=
  fnspec! "ip_checksum" data_ptr wlen / (data : list byte) R ~> chk,
    { requires tr mem :=
        wlen = word.of_Z (Z.of_nat (length data)) /\
        Z.of_nat (Datatypes.length data) < 2 ^ 32 /\ (* FIXME implied by sep *)
        (listarray_value AccessByte data_ptr data * R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        chk = ip_checksum_impl data /\
        (listarray_value AccessByte data_ptr data * R)%sep mem' }.

Import LoopCompiler.
Import UnsizedListArrayCompiler.

Hint Rewrite Nat2Z.id : compiler_cleanup.

#[local] Hint Unfold ip_checksum_upd : compiler_cleanup.
#[local] Hint Unfold co_word_of_Z co_word_of_byte : compiler_cleanup.
#[local] Hint Extern 10 => cbn; Z.div_mod_to_equations; nia : compiler_side_conditions.

#[local] Hint Extern 1 => simple apply dexpr_compile_odd; shelve: compiler_side_conditions.
#[local] Hint Extern 1 => simple apply dexpr_compile_div_2; shelve: compiler_side_conditions.

#[local] Hint Extern 1 => lia : arith.
#[local] Hint Resolve odd_sub_pos : arith.
Hint Rewrite word_not_xor : compiler_cleanup.
Hint Rewrite Z2Nat.id using eauto with arith : compiler_side_conditions.

Derive ip_checksum_body SuchThat
       (defn! "ip_checksum" ("data", "len") ~> "chk16"
         { ip_checksum_body },
         implements ip_checksum_impl)
       As body_correct.
Proof.
  Time compile.
Time Qed.

Require Import bedrock2.ToCString.
Compute c_func ("ip_checksum", (["data"; "len"], ["chk16"], ip_checksum_body)).
