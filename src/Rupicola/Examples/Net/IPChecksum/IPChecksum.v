From Rupicola.Examples Require Import IPChecksum.Impl.

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

#[local] Hint Unfold ip_checksum_upd : compiler_cleanup.
#[local] Hint Extern 10 => cbn; nia : compiler_side_conditions.

Lemma odd_sub_pos z:
  0 <= z -> Z.odd z = true -> 0 <= z - 1.
Proof. destruct (Z.eq_dec z 0) as [-> | ]; simpl; lia. Qed.

#[local] Hint Resolve odd_sub_pos : lia.
Hint Rewrite Z2Nat.id using eauto with lia : compiler_side_conditions.

Derive ip_checksum_br2fn SuchThat
       (defn! "ip_checksum" ("data", "len") ~> "chk16"
         { ip_checksum_br2fn },
         implements ip_checksum_impl)
       As ip_checksum_br2fn_ok.
Proof.
  Time compile.
Time Qed.

Definition ip_checksum_cbytes := Eval vm_compute in
  list_byte_of_string (ToCString.c_module [ip_checksum_br2fn]).
