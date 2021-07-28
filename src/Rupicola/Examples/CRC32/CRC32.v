Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Loops.
Require Import bedrock2.Semantics.
Require Import coqutil.Word.Interface coqutil.Byte.
Local Open Scope Z_scope.
Require Import Rupicola.Lib.Arrays.

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

    Definition crc_table_Z' : list Z :=
      Eval compute in
        List.map gen_crc_table_entry (seq 0 256).
    
    Definition crc_table_Z : list Z :=
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

    Definition crc_table : list Semantics.word := (List.map word.of_Z crc_table_Z).
    Definition crc_table' : list Semantics.word := (List.map word.of_Z crc_table_Z').
      
    Goal crc_table = crc_table'.
      reflexivity.
    Qed.
    (*TODO: use word instead of Z*)
    (*
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
     *)

    
    Definition crc32' (data : list byte) (*32bit or larger*) :=
      let/n crc32 := word.of_Z 0xFFFFFFFF in
      let/n idx := (word.of_Z 0) in
      let/n crc32 :=
         ranged_for_u idx
                      (word.of_Z (Z.of_nat (length data)))
                      (fun crc32 tok idx _ => let/n b := (ListArray.get (data : ListArray.t byte) idx) in
                                              let/n nLookupIndex :=
                                                 (*TODO: idiomatic way to get byte to word*)
                                                 word.and (word.xor crc32 (word.of_Z (byte.unsigned b)))
                                                          (word.of_Z 0xFF) in
                                              let/n nLookupRes := nth (Z.to_nat (word.unsigned nLookupIndex))
                                                                      crc_table (word.of_Z 0) in
                                            let/n crc32 := word.sru crc32 (word.of_Z 8) in
                                            let/n crc32 := word.xor crc32 nLookupRes in 
                                            (tok, crc32))
                      crc32 in
      let/n crc32 := word.xor crc32 (word.of_Z 0xFFFFFFFF) in
      crc32.
           
  End Gallina.

  (*TODO: better idea than never-used default?
    could probably use idx bounds proof to exclude that case
   *)
  Lemma fold_right_to_ranged A B (f : A -> B -> B) base lst default
    : List.fold_right f base lst = ranged_for_all 0 (Z.of_nat (length lst)) (fun acc idx _ => f (nth (Z.to_nat idx) lst default) acc) base.
  Proof.
    (*induction lst; cbn; auto.*)
  Abort.

  (*
  Lemma crc32_to_ranged : crc32 = crc32'.
  Proof.
  Admitted.
   *)

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

  (*TODO: is there a batter way to write this?*)
  Definition word_to_bytes (z : Semantics.word) : list byte:=
    HList.tuple.to_list (LittleEndian.split (Z.to_nat (width / 8)) (word.unsigned z)).
             
  (* Turns a table of 32-bit words stored in Zs into
     a table of bytes
   *)
  Definition to_byte_table : list Semantics.word -> list byte :=
    flat_map word_to_bytes.
  
  Lemma map_fold_empty_id (f : mem -> Semantics.word -> Init.Byte.byte -> mem) m
    : (forall m k v, f m k v = map.put m k v) ->
      map.fold f map.empty m = m.
  Proof.
    intro f_put.
    apply map.fold_spec; auto.
    intros; subst; eauto.
  Qed.

  Lemma of_list_word_at_0 (xs : list byte)
    : OfListWord.map.of_list_word xs
      = OfListWord.map.of_list_word_at (word.of_Z 0 : Semantics.word) xs.
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
      = load access_size.word (OfListWord.map.of_list_word b) (word.of_Z n : Semantics.word).
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
      repeat seprewrite_in (@array_append (@width semantics) (@Semantics.word semantics)) H1.
      rewrite !word.ring_morph_mul in H1.
      rewrite !word.of_Z_unsigned in H1.
      rewrite !word.ring_theory.(Rmul_1_l) in H1.
      rewrite <-!word.ring_morph_add in H1.
      simpl in H1.      

      seprewrite_in (scalar_of_bytes width_at_least_32 (word.of_Z (Z.of_nat (length b1))) b2 H2) H1.
      ecancel_assumption.
    }
    {
      repeat seprewrite_in (@array_append (@width semantics) (@Semantics.word semantics)) H1.
      rewrite !word.ring_morph_mul in H1.
      rewrite !word.of_Z_unsigned in H1.
      rewrite !word.ring_theory.(Rmul_1_l) in H1.
      rewrite <-!word.ring_morph_add in H1.
      simpl in H1.      

      seprewrite_in (scalar_of_bytes width_at_least_32) H1; auto.
      ecancel_assumption.
    }
  Qed.
  
  Lemma length_to_byte_table t
    : Datatypes.length (to_byte_table t) = (Z.to_nat (width / 8) * Datatypes.length t)%nat.
  Proof.
    induction t; simpl; try lia.
    rewrite app_length.
    rewrite IHt.
    unfold word_to_bytes.
    rewrite HList.tuple.length_to_list.
    lia.
  Qed.

  Lemma length_of_to_bytes a
    : width = 8 * Z.of_nat (Datatypes.length (word_to_bytes a)).
  Proof.
    unfold word_to_bytes.
    rewrite HList.tuple.length_to_list.
    rewrite Z2Nat.id;
      destruct width_cases as [H' | H']; rewrite H';
        cbn; lia.
  Qed.
  
  Lemma load_from_word_table t n
    : Z.of_nat (length (to_byte_table t)) <= 2 ^ width ->
      (n < length t)%nat ->
      load access_size.word
           (OfListWord.map.of_list_word (to_byte_table t))
           (word.of_Z (width/8 * Z.of_nat n))
      = Some (nth n t (word.of_Z 0)).
  Proof.
    intros table_bounds.
    revert n; induction t; intro n; destruct n; intros; try (simpl in *; lia).
    {
      rewrite Z.mul_0_r.
      rewrite of_list_word_at_0.
      assert (array ptsto (word.of_Z 1) (word.of_Z 0)
                    (word_to_bytes a ++ to_byte_table t)
                    (OfListWord.map.of_list_word_at
                       (word.of_Z 0 : Semantics.word)
                       (word_to_bytes a ++ to_byte_table t))).
      {
        eapply ptsto_bytes.array1_iff_eq_of_list_word_at; auto using mem_ok.
      }
      seprewrite_in @array_append H0.
      seprewrite_in @scalar_of_bytes H0; auto.
      apply width_at_least_32.
      {
         apply length_of_to_bytes.
      }
      eapply load_word_of_sep.
      assert ((LittleEndian.combine
                (Datatypes.length (word_to_bytes a))
                (HList.tuple.of_list (word_to_bytes a))) = word.unsigned a).
      {
        unfold word_to_bytes.
        rewrite (Htuple_of_list_to_list _ _(HList.tuple.length_to_list _)).
        destruct (HList.tuple.length_to_list _).
        cbn.
        rewrite LittleEndian.combine_split.
        rewrite HList.tuple.length_to_list.
        rewrite Z2Nat.id.
        {
          replace (width/8 *8) with width.
          rewrite word.wrap_unsigned; auto.
          pose proof width_mod_8.
          destruct width_cases as [H' | H']; rewrite H'; compute; auto.          
        }
        {
          pose proof width_at_least_32.
          apply Z.div_pos; lia.
        }
      }
      {
        simpl in *.
        match type of H0 with
        | context [scalar _ ?e] =>
          assert (e = a)
        end.
        {
          rewrite <- word.of_Z_unsigned.
          f_equal.
          exact H1.
        }
        rewrite H2 in H0.
        ecancel_assumption.
      }
    }
    {
      cbn [nth].
      replace (width/8 * Z.of_nat (S n)) with (width/8 + (width/8* Z.of_nat n)) by lia.
      unfold to_byte_table; simpl; fold to_byte_table.
      match goal with
        [|- load _ _ (word.of_Z (?w + _)) = _ ] =>
        assert (w = Z.of_nat (Datatypes.length (word_to_bytes a)))
      end.
      {
        unfold word_to_bytes.
        rewrite HList.tuple.length_to_list.
        rewrite Z2Nat.id; try lia.
        destruct width_cases as [H' | H']; rewrite H';
          intro cmp; inversion cmp.
      }
      rewrite H0 at 1.
      erewrite load_of_list_word.
      apply IHt.
      (*{ inversion cell_bounds; assumption. }*)
      {
        unfold word_to_bytes in table_bounds;
        simpl in table_bounds;
        fold word_to_bytes in table_bounds.
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
         
  (* a lemma to compile the call to nth as a static lookup *)
  Lemma compile_table_nth {n t} {tr mem locals functions}:
    let v := nth n t (word.of_Z 0) in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
           (R : _ -> Prop) var idx_var,
      (n < Datatypes.length t)%nat ->
      (Z.of_nat (Datatypes.length (to_byte_table t)) <= 2 ^ width) ->
      R mem ->
      map.get locals idx_var = Some (word.of_Z (Z.of_nat n)) ->
      
      (let v := v in
       forall m,
         R m ->
         <{ Trace := tr;
            Memory := m;
            Locals := map.put locals var v;
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
                                    (expr.op bopname.mul (expr.literal (width/8)) (expr.var idx_var))))
               k_impl)
      <{ pred (nlet_eq [var] v k) }>.
  Proof.
    intros; repeat straightline.
    exists v.
    split.
    {
      repeat straightline.
      exists (word.of_Z (Z.of_nat n)).
      split; auto.
      exists v.
      split; auto.
      unfold v0.
      rewrite <- word.ring_morph_mul.
      apply load_from_word_table; auto.
    }
    {
      repeat straightline.
      eauto.
    }
  Qed.
  
  Hint Extern 1 => simple eapply @compile_table_nth; shelve : compiler.

(*
  Definition set_local_nat locals var n :=
    (map.put locals var (word.of_Z (Z.of_nat n) : Semantics.word)).
*)

  Hint Extern 1 => simple eapply compile_table_nth; shelve : compiler.


  Ltac solve_get_put :=
    repeat(
        (rewrite map.get_put_same; auto;easy)
        ||  rewrite map.get_put_diff); easy.

      
  Hint Extern 1 => simple eapply @compile_byte_unsizedlistarray_get; shelve : compiler.

  
  Lemma Nsucc_double_preserves_leq n p
    : Z.of_N n <= Z.pos p -> Z.of_N (Pos.Nsucc_double n) <= Z.pos p~1.
  Proof.
    revert p.
    induction n;intros; simpl in *; lia.
  Qed.

  Lemma Ndouble_preserves_leq_0 n p
    : Z.of_N n <= Z.pos p -> Z.of_N (Pos.Ndouble n) <= Z.pos p~0.
  Proof.
    revert p.
    induction n;intros; simpl in *; lia.
  Qed.
  
  Lemma Ndouble_preserves_leq_1 n p
    : Z.of_N n <= Z.pos p -> Z.of_N (Pos.Ndouble n) <= Z.pos p~1.
  Proof.
    revert p.
    induction n;intros; simpl in *; lia.
  Qed.
  
  Lemma Z_and_leq_right a b
    : 0 <= a -> 0 <= b -> Z.land a b <= b.
  Proof.
    case a; rewrite ?Z.land_0_l; try solve [lia].
    intro p_a.
    case b; rewrite ?Z.land_0_r; try solve [lia].
    intros p_b _ _.
    simpl.
    revert p_b; induction p_a; destruct p_b; simpl; intros; try lia.
    all: eauto using Nsucc_double_preserves_leq, Ndouble_preserves_leq_0,Ndouble_preserves_leq_1.
  Qed.
  
  Lemma word_and_leq_right (a b : Semantics.word)
    : (word.unsigned (word.and a b)) <= (word.unsigned b).
  Proof.
    rewrite word.unsigned_and_nowrap.
    apply Z_and_leq_right.
    all: apply word.unsigned_range.
  Qed.
    
  
  Instance spec_of_crc32 : spec_of "crc32" :=
    fnspec! "crc32" data_ptr len / (data : list byte) R ~> r,
    { requires fns tr mem :=
        (word.unsigned len = Z.of_nat (length data) /\
        (listarray_value AccessByte data_ptr data * R)%sep mem);
      ensures tr' mem' :=
        tr' = tr /\
        r = crc32' data /\
        (listarray_value AccessByte  data_ptr data * R)%sep mem' }.

  
  Derive crc32_body SuchThat
         (defn! "crc32" ("data", "len") ~> "crc32" { crc32_body },
          implements crc32')
         As body_correct.
  Proof.
    compile_setup.    
    repeat (repeat compile_step).
    
    simple apply compile_nlet_as_nlet_eq.
    apply compile_ranged_for_w
      with (signed := false)
           (loop_pred := (fun idx acc tr' mem' locals' =>
                            (*TODO: existential is bad; need partial computation?*)
          (listarray_value AccessByte data_ptr data * R)%sep mem'
          /\ tr' = tr
          /\ locals' = map.put
                         (map.put 
                            (map.put (map.put map.empty "data" data_ptr) "idx" idx)
                            "len" (word.of_Z (Z.of_nat (Datatypes.length data))))
                         "crc32" acc)).
    exact word.of_Z_unsigned.
    repeat compile_step; apply word.unsigned_range.
    repeat compile_step.
    repeat compile_step.
    {
      rewrite <- H0.
      rewrite word.of_Z_unsigned.
      repeat (repeat compile_step).
    }
    {
      repeat compile_step.
      {
        rewrite <-H0 in Hr.
        rewrite word.of_Z_unsigned in Hr.
        rewrite H0 in Hr.
        assumption.
      }
      {
        unfold v2.
        simpl.
        zify.
        intuition try lia.
        subst z4.
        lazymatch goal with
          [|- word.unsigned (word.and ?l ?r) < _] =>
          pose proof (@word_and_leq_right l r)
        end.
        rewrite word.unsigned_of_Z in H1.
        rewrite word.wrap_small in H1; try lia.
        destruct width_cases as [H' | H']; rewrite H'; lia.
      }
      {
        rewrite length_to_byte_table.
        change (Datatypes.length crc_table) with 256%nat.
        destruct width_cases as [H' | H']; rewrite H'; try lia.
        compute; inversion 1.
        compute; inversion 1.
      }
    }
    {
      repeat compile_step.
      cbn -[crc_table].
      repeat compile_step.
    }
  Qed.
  
  Hint Extern 1 => simple eapply @compile_table_nth; shelve : compiler.


  (*
    -Notes: what is the right memoryLayout? should I be abstract?
    -Rupicola generate fn
    -running the compiler requires instantiating things, right? (so I shouldn't)
    -WP.call -> exec : is that sound_cmd? sound_call?
   *)
  
End __.
