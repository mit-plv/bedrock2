Require Import Rupicola.Lib.Api.
Require Import bedrock2.Semantics.
Require Import coqutil.Word.Interface coqutil.Byte.
Local Open Scope Z_scope.

Section __.
  
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Section Gallina.
    (*
      hand-translated from:
      void make_crc_table(void)
   {
     unsigned long c;
     int n, k;
   
     for (n = 0; n < 256; n++) {
       c = (unsigned long) n;
       for (k = 0; k < 8; k++) {
         if (c & 1)
           c = 0xedb88320L ^ (c >> 1);
         else
           c = c >> 1;
       }
       crc_table[n] = c;
     }
     crc_table_computed = 1;
   }
     *)
    (*The inner loop, executed 8 times*)
    Fixpoint gen_crc_table' (c : Z) (k : nat) : Z :=
      match k with
      | O => c
      | S k =>
        let c := gen_crc_table' c k in
        if negb (Z.land c 1 =? 0)
        then Z.lxor 0xedb88320 (Z.shiftr c 1)
        else Z.shiftr c 1
      end.

    Definition gen_crc_table_entry (n : nat) : Z :=
      let c := Z.of_nat n in
      gen_crc_table' c 8.

    Definition crc_table' : list Z :=
      Eval compute in
        List.map gen_crc_table_entry (seq 0 256).
    
    Definition crc_table : list Z :=
         [0x00000000; 0x77073096; 0xee0e612c; 0x990951ba;
    0x076dc419; 0x706af48f; 0xe963a535; 0x9e6495a3;
    0x0edb8832; 0x79dcb8a4; 0xe0d5e91e; 0x97d2d988;
    0x09b64c2b; 0x7eb17cbd; 0xe7b82d07; 0x90bf1d91;
    0x1db71064; 0x6ab020f2; 0xf3b97148; 0x84be41de;
    0x1adad47d; 0x6ddde4eb; 0xf4d4b551; 0x83d385c7;
    0x136c9856; 0x646ba8c0; 0xfd62f97a; 0x8a65c9ec;
    0x14015c4f; 0x63066cd9; 0xfa0f3d63; 0x8d080df5;
    0x3b6e20c8; 0x4c69105e; 0xd56041e4; 0xa2677172;
    0x3c03e4d1; 0x4b04d447; 0xd20d85fd; 0xa50ab56b;
    0x35b5a8fa; 0x42b2986c; 0xdbbbc9d6; 0xacbcf940;
    0x32d86ce3; 0x45df5c75; 0xdcd60dcf; 0xabd13d59;
    0x26d930ac; 0x51de003a; 0xc8d75180; 0xbfd06116;
    0x21b4f4b5; 0x56b3c423; 0xcfba9599; 0xb8bda50f;
    0x2802b89e; 0x5f058808; 0xc60cd9b2; 0xb10be924;
    0x2f6f7c87; 0x58684c11; 0xc1611dab; 0xb6662d3d;
    0x76dc4190; 0x01db7106; 0x98d220bc; 0xefd5102a;
    0x71b18589; 0x06b6b51f; 0x9fbfe4a5; 0xe8b8d433;
    0x7807c9a2; 0x0f00f934; 0x9609a88e; 0xe10e9818;
    0x7f6a0dbb; 0x086d3d2d; 0x91646c97; 0xe6635c01;
    0x6b6b51f4; 0x1c6c6162; 0x856530d8; 0xf262004e;
    0x6c0695ed; 0x1b01a57b; 0x8208f4c1; 0xf50fc457;
    0x65b0d9c6; 0x12b7e950; 0x8bbeb8ea; 0xfcb9887c;
    0x62dd1ddf; 0x15da2d49; 0x8cd37cf3; 0xfbd44c65;
    0x4db26158; 0x3ab551ce; 0xa3bc0074; 0xd4bb30e2;
    0x4adfa541; 0x3dd895d7; 0xa4d1c46d; 0xd3d6f4fb;
    0x4369e96a; 0x346ed9fc; 0xad678846; 0xda60b8d0;
    0x44042d73; 0x33031de5; 0xaa0a4c5f; 0xdd0d7cc9;
    0x5005713c; 0x270241aa; 0xbe0b1010; 0xc90c2086;
    0x5768b525; 0x206f85b3; 0xb966d409; 0xce61e49f;
    0x5edef90e; 0x29d9c998; 0xb0d09822; 0xc7d7a8b4;
    0x59b33d17; 0x2eb40d81; 0xb7bd5c3b; 0xc0ba6cad;
    0xedb88320; 0x9abfb3b6; 0x03b6e20c; 0x74b1d29a;
    0xead54739; 0x9dd277af; 0x04db2615; 0x73dc1683;
    0xe3630b12; 0x94643b84; 0x0d6d6a3e; 0x7a6a5aa8;
    0xe40ecf0b; 0x9309ff9d; 0x0a00ae27; 0x7d079eb1;
    0xf00f9344; 0x8708a3d2; 0x1e01f268; 0x6906c2fe;
    0xf762575d; 0x806567cb; 0x196c3671; 0x6e6b06e7;
    0xfed41b76; 0x89d32be0; 0x10da7a5a; 0x67dd4acc;
    0xf9b9df6f; 0x8ebeeff9; 0x17b7be43; 0x60b08ed5;
    0xd6d6a3e8; 0xa1d1937e; 0x38d8c2c4; 0x4fdff252;
    0xd1bb67f1; 0xa6bc5767; 0x3fb506dd; 0x48b2364b;
    0xd80d2bda; 0xaf0a1b4c; 0x36034af6; 0x41047a60;
    0xdf60efc3; 0xa867df55; 0x316e8eef; 0x4669be79;
    0xcb61b38c; 0xbc66831a; 0x256fd2a0; 0x5268e236;
    0xcc0c7795; 0xbb0b4703; 0x220216b9; 0x5505262f;
    0xc5ba3bbe; 0xb2bd0b28; 0x2bb45a92; 0x5cb36a04;
    0xc2d7ffa7; 0xb5d0cf31; 0x2cd99e8b; 0x5bdeae1d;
    0x9b64c2b0; 0xec63f226; 0x756aa39c; 0x026d930a;
    0x9c0906a9; 0xeb0e363f; 0x72076785; 0x05005713;
    0x95bf4a82; 0xe2b87a14; 0x7bb12bae; 0x0cb61b38;
    0x92d28e9b; 0xe5d5be0d; 0x7cdcefb7; 0x0bdbdf21;
    0x86d3d2d4; 0xf1d4e242; 0x68ddb3f8; 0x1fda836e;
    0x81be16cd; 0xf6b9265b; 0x6fb077e1; 0x18b74777;
    0x88085ae6; 0xff0f6a70; 0x66063bca; 0x11010b5c;
    0x8f659eff; 0xf862ae69; 0x616bffd3; 0x166ccf45;
    0xa00ae278; 0xd70dd2ee; 0x4e048354; 0x3903b3c2;
    0xa7672661; 0xd06016f7; 0x4969474d; 0x3e6e77db;
    0xaed16a4a; 0xd9d65adc; 0x40df0b66; 0x37d83bf0;
    0xa9bcae53; 0xdebb9ec5; 0x47b2cf7f; 0x30b5ffe9;
    0xbdbdf21c; 0xcabac28a; 0x53b39330; 0x24b4a3a6;
    0xbad03605; 0xcdd70693; 0x54de5729; 0x23d967bf;
    0xb3667a2e; 0xc4614ab8; 0x5d681b02; 0x2a6f2b94;
         0xb40bbe37; 0xc30c8ea1; 0x5a05df1b; 0x2d02ef8d].

    Goal crc_table = crc_table'.
      reflexivity.
    Qed.
    Definition crc32 (data : list byte) : Z (*32bit*) :=
      let/n crc32 := 0xFFFFFFFF in
      let/n crc32 :=
         List.fold_right (fun b crc32 =>
                 let/n nLookupIndex :=
                    Z.land (Z.lxor crc32 (byte.unsigned b)) (byte.unsigned Byte.xff) in
                 Z.lxor (Z.shiftr crc32 8)
                          (nth (Z.to_nat nLookupIndex) crc_table 0)
               )
               crc32 data in
      let/n crc32 := Z.lxor crc32 0xFFFFFFFF in
      crc32.
  End Gallina.

  (*Properties about width; could be moved somewhere more general*)
  Lemma width_at_least_32 : 32 <= width.
  Proof using semantics_ok.
    destruct width_cases; lia.
  Qed.

   Lemma width_mod_8 : width mod 8 = 0.
  Proof using semantics_ok.
    destruct width_cases as [H | H]; rewrite H;
      reflexivity.
  Qed.
  
  (* TODO: check endianness *)
  Definition Z_to_bytes (z : Z) : list byte:=
    HList.tuple.to_list (LittleEndian.split (Z.to_nat (width / 8)) z).
             
  (* Turns a table of 32-bit words stored in Zs into
     a table of bytes
   *)
  Definition to_byte_table : list Z -> list byte :=
    flat_map Z_to_bytes.
  
  Lemma map_fold_empty_id (f : mem -> Core.word -> Init.Byte.byte -> mem) m
    : (forall m k v, f m k v = map.put m k v) ->
      map.fold f map.empty m = m.
  Proof.
    intro f_put.
    apply map.fold_spec; auto.
    intros; subst; eauto.
  Qed.

  Lemma of_list_word_at_0 xs
    : OfListWord.map.of_list_word xs
      = OfListWord.map.of_list_word_at (word.of_Z 0) xs.
  Proof.
    unfold OfListWord.map.of_list_word_at.
    unfold MapKeys.map.map_keys.
    unfold OfListWord.map.of_list_word.
    induction xs; simpl.
    { rewrite map.fold_empty; auto. }
    {
      rewrite <- seq_shift.
      rewrite map_map.
      
      rewrite word.unsigned_of_Z_0.
      cbn.
      rewrite map_fold_empty_id; [ reflexivity | ..].
      {
        intros.
        rewrite word.ring_theory.(Radd_0_l).
        reflexivity.
      }
    }
  Qed.

 

  (*
  Lemma eq_rect_r_over_pair (f : nat -> Type) A B a b m n (eqn : m = n)
    : (f m = A * (B n))%type ->
       (f n = A * (B n))%type ->
        eq_rect_r f (a,b) eqn = (a, eq_rect_r f b eqn). *)

  
  Lemma eq_rect_r_S n m f e eqn
    : forall eqn',
      @eq_rect_r nat (S n) f e (S m) eqn
      = eq_rect_r (fun x => f (S x)) e eqn'.
  Proof.
    inversion eqn.
    subst.
    intros.
    rewrite (Eqdep_dec.UIP_refl_nat _ eqn).
    rewrite (Eqdep_dec.UIP_refl_nat _ eqn').
    reflexivity.
  Qed.

    
  Lemma Htuple_of_list_to_list:
    forall {A : Type} n (xs : HList.tuple A n) eqn,
      HList.tuple.of_list (HList.tuple.to_list xs)
      = eq_rect_r (fun n0 : nat => HList.tuple A n0) xs eqn.
  Proof.
    induction n; intro xs; cbn in *.
    {
      intro eqn;
      match goal with
        [|- tt = ?e] => destruct e; reflexivity
      end.
    }
    {
      intro eqn;
      destruct xs.
      Import PrimitivePair.pair.
      inversion eqn.
      rewrite IHn with _2 H0.
      clear IHn.
      rewrite (eq_rect_r_S _ _ _ _ _ H0).
      clear eqn.

      
      unfold HList.tuple.
      simpl.
      generalize H0.
      generalize (Datatypes.length (HList.tuple.to_list _2)).
      destruct H1.
      reflexivity.
    }
  Qed.

  
  Lemma load_of_list_word a b b1 b2 b3 n
    : Z.of_nat (Datatypes.length (a ++ b)) <= 2 ^ width ->
      b = (b1 ++ b2 ++ b3)%list ->
      n = Z.of_nat (length b1) ->
      width = 8* Z.of_nat (Datatypes.length b2) ->
      load access_size.word (OfListWord.map.of_list_word (a ++ b)) (word.of_Z (Z.of_nat (length a) + n))
      = load access_size.word (OfListWord.map.of_list_word b) (word.of_Z n).
  Proof.
    intros; subst.
    assert (Z.of_nat (Datatypes.length (b1 ++ b2 ++ b3)) <= 2 ^ width).
    {
      rewrite app_length in H.
      rewrite Nat2Z.inj_add in H.
      lia.
    }
    rewrite !of_list_word_at_0.
    erewrite !load_word_of_sep;
      try reflexivity;
      match goal with
        [|- ?P (OfListWord.map.of_list_word_at ?p ?xs)] =>
         assert (array ptsto (word.of_Z 1) p xs
                       (OfListWord.map.of_list_word_at p xs)) as H1;
           [apply ptsto_bytes.array1_iff_eq_of_list_word_at; eauto using mem_ok|
           generalize dependent (OfListWord.map.of_list_word_at p xs); intros]
      end.
    {      
      pose proof scalar_of_bytes as H4.
      symmetry in H4.
      seprewrite H4; eauto using width_at_least_32.
      clear H4.
      repeat seprewrite_in (array_append ptsto) H1.
      rewrite !word.ring_theory.(Radd_0_l) in H1.
      rewrite !word.ring_morph_mul in H1.
      rewrite !word.of_Z_unsigned in H1.
      rewrite !word.ring_theory.(Rmul_1_l) in H1.
      ecancel_assumption.
    }    
    {      
      pose proof scalar_of_bytes as H4.
      symmetry in H4.
      seprewrite H4; eauto using width_at_least_32.
      clear H4.
      repeat seprewrite_in (array_append ptsto) H1.
      rewrite !word.ring_theory.(Radd_0_l) in H1.
      rewrite !word.ring_morph_mul in H1.
      rewrite !word.of_Z_unsigned in H1.
      rewrite !word.ring_theory.(Rmul_1_l) in H1.
      rewrite word.ring_morph_add.
      ecancel_assumption.
    }
  Qed.

  
  Lemma length_to_byte_table t
    : Datatypes.length (to_byte_table t) = (Z.to_nat (width / 8) * Datatypes.length t)%nat.
  Proof.
    induction t; simpl; try lia.
    rewrite app_length.
    rewrite IHt.
    unfold Z_to_bytes.
    rewrite HList.tuple.length_to_list.
    lia.
  Qed.

  Lemma length_of_to_bytes a
    : width = 8 * Z.of_nat (Datatypes.length (Z_to_bytes a)).
  Proof.
    unfold Z_to_bytes.
    rewrite HList.tuple.length_to_list.
    rewrite Z2Nat.id;
      destruct width_cases as [H' | H']; rewrite H';
        cbn; lia.
  Qed.
  
  (*TODO: might want to generalize w/ an offset?
   *)
  Lemma load_from_word_table t n
    : List.Forall (fun z => 0 <= z < 2^width) t ->
      Z.of_nat (length (to_byte_table t)) <= 2 ^ width ->
      (n < length t)%nat ->
      load access_size.word
           (OfListWord.map.of_list_word (to_byte_table t))
           (word.of_Z (width/8 * Z.of_nat n))
      = Some (word.of_Z (nth n t 0)).
  Proof.
    intros cell_bounds table_bounds.
    revert n; induction t; intro n; destruct n; intros; try (simpl in *; lia).
    {
      rewrite Z.mul_0_r.
      rewrite of_list_word_at_0.
      assert (array ptsto (word.of_Z 1) (word.of_Z 0)
                    (Z_to_bytes a ++ to_byte_table t)
                    (OfListWord.map.of_list_word_at
                       (word.of_Z 0)
                       (Z_to_bytes a ++ to_byte_table t))).
      {
        seprewrite ptsto_bytes.array1_iff_eq_of_list_word_at; auto;
          sepsimpl; reflexivity.
      }
      seprewrite_in @array_append H0.
      seprewrite_in @scalar_of_bytes H0; auto.
      apply width_at_least_32.
      {
         apply length_of_to_bytes.
      }
      eapply load_word_of_sep.
      assert ((LittleEndian.combine
                (Datatypes.length (Z_to_bytes a))
                (HList.tuple.of_list (Z_to_bytes a))) = a).
      {
        unfold Z_to_bytes.
        rewrite (Htuple_of_list_to_list _ _(HList.tuple.length_to_list _)).
        destruct (HList.tuple.length_to_list _).
        cbn.
        rewrite LittleEndian.combine_split.
        rewrite HList.tuple.length_to_list.
        rewrite Z2Nat.id.
        inversion cell_bounds; subst.
        assert (width mod 8 = width - width / 8 * 8) by (apply Zmod_eq; lia).
        rewrite width_mod_8 in H1.
        assert (width/8*8 = width) by lia.
        apply Zmod_small.
        rewrite H2.
        assumption.
        destruct width_cases as [H' | H']; rewrite H';
          intro cmp; inversion cmp.
      }
      {
        simpl in *.
        rewrite <- H1 at 1.
        ecancel_assumption.
      }
    }
    {
      cbn [nth].
      replace (width/8 * Z.of_nat (S n)) with (width/8 + (width/8* Z.of_nat n)) by lia.
      unfold to_byte_table; simpl; fold to_byte_table.
      match goal with
        [|- load _ _ (word.of_Z (?w + _)) = _ ] =>
        assert (w = Z.of_nat (Datatypes.length (Z_to_bytes a)))
      end.
      {
        unfold Z_to_bytes.
        rewrite HList.tuple.length_to_list.
        rewrite Z2Nat.id; try lia.
        destruct width_cases as [H' | H']; rewrite H';
          intro cmp; inversion cmp.
      }
      rewrite H0 at 1.
      erewrite load_of_list_word.
      apply IHt.
      { inversion cell_bounds; assumption. }
      {
        unfold Z_to_bytes in table_bounds;
        simpl in table_bounds;
        fold Z_to_bytes in table_bounds.
        rewrite app_length in table_bounds.
        lia.
      }
      { simpl in H; lia. }
      { simpl in table_bounds; lia. }
      { rewrite <- (List.firstn_skipn (Z.to_nat (width/8 * Z.of_nat n)) (to_byte_table t)).
        f_equal.
        match goal with
          [|- ?l = _] =>
          rewrite <- (List.firstn_skipn (Z.to_nat (width / 8)) l)
        end.
        f_equal.
      }
      {
        rewrite firstn_length_le.
        rewrite Z2Nat.id; try lia.
        rewrite Z2Nat.inj_mul; try lia.
        rewrite Nat2Z.id.
        rewrite length_to_byte_table.
        simpl in H.
        nia.
      }
      {
        rewrite firstn_length_le; try lia.
        {
          rewrite Z2Nat.id; try lia.
          pose proof width_mod_8.
          apply Z_div_exact_2; auto; lia.
        }
        {
          rewrite skipn_length.
          rewrite Z2Nat.inj_mul; try lia.
          rewrite Nat2Z.id.
          rewrite length_to_byte_table.
          simpl in H.
          nia.
        }
      }
    }
Qed.
  
  (* Want a lemma to compile the call to nth as a static lookup *)
  Lemma compile_table_nth {n t} {tr mem locals functions}:
    let v := nth n t 0 in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      (R : _ -> Prop) var,
      32 <= width (*for a lemma*) ->
      Forall (fun z : Z => 0 <= z < 2 ^ width) t ->
      (n < Datatypes.length t)%nat ->
      (Z.of_nat (Datatypes.length (to_byte_table t)) <= 2 ^ width) ->
      R mem ->
      
      (let v := v in
       forall m,
         R m ->
         <{ Trace := tr;
            Memory := m;
            Locals := map.put locals var (word.of_Z v);
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      (cmd.seq (cmd.set
                  var
                  (expr.inlinetable access_size.word (to_byte_table t)
                                    (expr.literal (width/8 * Z.of_nat n))))
               k_impl)
      <{ pred (nlet_eq [var] v k) }>.
  Proof.
    intros; repeat straightline.
    exists (word.of_Z v).
    split.
    {
      repeat straightline.
      exists (word.of_Z v).
      split; auto.
      apply load_from_word_table; auto.
    }
    {
      repeat straightline.
      apply H4.
      assumption.
    }
  Qed.
      
End __.
