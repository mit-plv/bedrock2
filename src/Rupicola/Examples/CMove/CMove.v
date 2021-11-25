Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Loops.
Require Import bedrock2.Semantics.
Require Import coqutil.Word.Interface coqutil.Byte.
Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Examples.Cells.Cells.

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {wordok : word.ok word} {mapok : map.ok mem}.
  Context {localsok : map.ok locals}.
  Context {envok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Section Gallina.
    
    Definition all_1s : word := word.of_Z (-1).

    Definition is_mask mask : Prop :=
      mask = all_1s \/ mask = word.of_Z 0.

    Definition mask_of_bool (b : bool) :=
      if b then all_1s else word.of_Z 0.
      
    (*idea: if b then true_val else false_val *)
    Definition select_word (mask : word) true_val false_val :=
      let/n nmask := (word.sub (word.of_Z (-1)) mask) in
      let/n r := word.or (word.and mask true_val) (word.and nmask false_val) in
      r.

    (*Rupicola doesn't appear to behave well w/ a call to select_word*)
    Definition cmove_word (mask : word) (c1 c2 : cell) :=
      let/n nmask := (word.sub (word.of_Z (-1)) mask) in
      let/n true_val := get c1 in
      let/n false_val := get c2 in
      let/n r := word.or (word.and mask true_val) (word.and nmask false_val) in
      let/n c1 := put r in
      c1.

    Definition cswap_word (mask : word) (c1 c2 : cell) :=
      let/n nmask := (word.sub (word.of_Z (-1)) mask) in
      let/n true_val := get c1 in
      let/n false_val := get c2 in
      let/n r := word.or (word.and mask true_val) (word.and nmask false_val) in
      let/n c1 := put r in
      let/n r := word.or (word.and mask false_val) (word.and nmask true_val) in
      let/n c2 := put r in
      (c1,c2).

    
    Instance HasDefault_word : HasDefault word :=
      word.of_Z 0.

    Definition cmove_array mask len 
               (a1: ListArray.t word.rep)
               (a2: ListArray.t word.rep) :=
      let/n from := word.of_Z 0 in
      let/n nmask := (word.sub (word.of_Z (-1)) mask) in
      let/n a1 := ranged_for_u
                    from len
                    (fun a1 tok idx Hlt =>
                       let/n v1 := ListArray.get a1 idx in
                       let/n v2 := ListArray.get a2 idx in
                       let/n r := word.or (word.and mask v1)
                                          (word.and nmask v2) in
                       let/n a1 :=
                          ListArray.put a1 idx r in
                       (tok, a1)) a1 in
      (a1,a2).

    Definition cswap_array mask len
               (a1: ListArray.t word.rep)
               (a2: ListArray.t word.rep) :=
      let/n from := word.of_Z 0 in
      let/n nmask := (word.sub (word.of_Z (-1)) mask) in
      let/n (a1, a2) :=
         ranged_for_u
           from len
           (fun p tok idx Hlt =>
              let/n v1 := ListArray.get (P2.car p) idx in
              let/n v2 := ListArray.get (P2.cdr p) idx in
              let/n r1 := word.or (word.and mask v1)
                                 (word.and nmask v2) in
              let/n r2 := word.or (word.and mask v2)
                                 (word.and nmask v1) in
              let/n a1 := ListArray.put (P2.car p) idx r1 in
              let/n a2 := ListArray.put (P2.cdr p) idx r2 in
              (tok, \< a1, a2 \>)) \< a1, a2 \> in
      (a1, a2).
  End Gallina.

  
  Lemma z_lt_width : 0 <= width.
  Proof.
    destruct width_cases; lia.
  Qed.
  

  
  Lemma all_1s_and : forall x, word.and all_1s x = x.
  Proof.
    intros.
    unfold all_1s.
    rewrite <- (word.of_Z_unsigned (word.of_Z (-1))).
    rewrite -> word.unsigned_of_Z_minus1.
    rewrite <- (word.of_Z_unsigned x) at 1.
    rewrite <- word.morph_and.
    rewrite Z.land_comm.
    rewrite Z.land_ones.
    rewrite word.wrap_unsigned.
    rewrite word.of_Z_unsigned.
    reflexivity.
    apply z_lt_width.
  Qed.

  Lemma word_not_all1s : word.not all_1s = word.of_Z 0.
  Proof.
    rewrite <- (word.of_Z_signed (word.not all_1s)).
    rewrite word.signed_not.
    unfold all_1s.    
    rewrite word.signed_of_Z.
    rewrite !word.swrap_inrange.
    change (-1) with (-(1)).
    rewrite Z.lnot_m1; reflexivity.
    destruct width_cases as [H|H]; rewrite !H; lia.
    {
      rewrite word.swrap_inrange.
      let x := eval compute in ( Z.lnot (-1)) in
          change ( Z.lnot (-1)) with x.
      destruct width_cases as [H|H]; rewrite !H; lia.
      destruct width_cases as [H|H]; rewrite !H; lia.
    }
  Qed.    

  Lemma zero_and (x : word)
    : word.and (word.of_Z 0) x = word.of_Z 0.
  Proof.
    rewrite <- (word.of_Z_unsigned x) at 1.
    rewrite <- word.morph_and.
    rewrite Z.land_0_l.
    reflexivity.
  Qed.

  
  Lemma zero_or (x : word)
    : word.or (word.of_Z 0) x = x.
  Proof.
    rewrite <- (word.of_Z_unsigned x) at 1.
    rewrite <- word.morph_or.
    rewrite Z.lor_0_l.
    rewrite word.of_Z_unsigned.
    reflexivity.
  Qed.

  Lemma or_comm (a b : word) : word.or a b = word.or b a.
  Proof.
    rewrite <- (word.of_Z_signed a).
    rewrite <- (word.of_Z_signed b).
    rewrite <-word.morph_or.
    rewrite Z.lor_comm.
    rewrite word.morph_or.
    reflexivity.
  Qed.
    
  Lemma cmove_word_is_conditional mask c1 c2
    : is_mask mask ->
      cmove_word mask c1 c2 = if word.eqb mask (word.of_Z 0) then c2 else c1.
  Proof.
    case (word.eqb_spec mask (word.of_Z 0)).
    {
      unfold cmove_word; intros;
      destruct c1; destruct c2.
      cbv[nlet put get Cells.data].
      f_equal.
      subst.
      rewrite <-word.ring_morph_sub.
      simpl.
      rewrite !zero_and.
      rewrite  all_1s_and.
      rewrite zero_or.
      reflexivity.
    }
    {
      unfold is_mask.
      intuition; subst.
      unfold cmove_word; intros;
        destruct c1; destruct c2.
       cbv[nlet put get Cells.data].
      f_equal.
      subst.
      unfold all_1s.
      rewrite <-word.ring_morph_sub.
      simpl.
      rewrite !zero_and.
      rewrite  all_1s_and.
      rewrite or_comm.
      rewrite zero_or.
      reflexivity.
    }
  Qed.

  Lemma cswap_word_is_conditional mask c1 c2
    : is_mask mask ->
      cswap_word mask c1 c2 =
      if word.eqb mask (word.of_Z 0) then (c2,c1) else (c1,c2).
  Proof.
    case (word.eqb_spec mask (word.of_Z 0)).
    {
      unfold cswap_word; intros;
      destruct c1; destruct c2.
      cbv[nlet put get Cells.data].
      repeat f_equal.

      all:subst; rewrite <-word.ring_morph_sub.
      all:simpl; rewrite !zero_and.
      all: rewrite  all_1s_and.
      all: rewrite zero_or.
      all:reflexivity.
    }
    {
      unfold is_mask.
      intuition; subst.
      unfold cswap_word; intros;
        destruct c1; destruct c2.
      cbv[nlet put get Cells.data].
      repeat f_equal.

      all:subst; unfold all_1s.
      all:rewrite <-word.ring_morph_sub.
      all:simpl; rewrite !zero_and.
      all:rewrite  all_1s_and.
      all:rewrite or_comm.
      all:rewrite zero_or.
      all:reflexivity.
    }
  Qed.

  Instance spec_of_cmove_word : spec_of "cmove_word" :=
    fnspec! "cmove_word" mask ptr1 ptr2 / c1 c2 R,
    { requires tr mem :=
        is_mask mask /\
        (cell_value ptr1 c1 * cell_value ptr2 c2 * R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        (cell_value ptr1 (cmove_word mask c1 c2)
         * cell_value ptr2 c2 * R)%sep mem' }.
  
  Derive cmove_word_br2fn SuchThat
         (defn! "cmove_word" ("mask", "c1", "c2") { cmove_word_br2fn },
          implements cmove_word)
         As cmove_br2fn_ok.
  Proof.
    compile.
  Qed.

  Instance spec_of_cswap_word : spec_of "cswap_word" :=
    fnspec! "cswap_word" mask ptr1 ptr2 / c1 c2 R,
    { requires tr mem :=
        is_mask mask /\
        (cell_value ptr1 c1 * cell_value ptr2 c2 * R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        let (c1',c2') := (cswap_word mask c1 c2) in
        (cell_value ptr1 c1'
         * cell_value ptr2 c2' * R)%sep mem' }.
  
  Derive cswap_word_br2fn SuchThat
         (defn! "cswap_word" ("mask", "c1", "c2") { cswap_word_br2fn },
          implements cswap_word)
         As cswap_br2fn_ok.
  Proof.
    compile.
  Qed.


  
  Instance spec_of_cmove_array : spec_of "cmove_array" :=
    fnspec! "cmove_array" mask len ptr1 ptr2 / n c1 c2 R,
    (*TODO: if b then bw should be all 1s*)
    { requires tr mem :=
        word.unsigned len = Z.of_nat n /\
        is_mask mask /\
        (sizedlistarray_value AccessWord n ptr1 c1
         * sizedlistarray_value AccessWord n ptr2 c2 * R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        let (c1,c2) := cmove_array mask len c1 c2 in
        (sizedlistarray_value AccessWord n ptr1 c1
         * sizedlistarray_value AccessWord n ptr2 c2 * R)%sep mem' }.

  Import SizedListArrayCompiler.
  Import LoopCompiler.
  Hint Extern 10 (_ < _) => lia: compiler_side_conditions.

  Derive cmove_array_br2fn SuchThat
         (defn! "cmove_array" ("mask", "len", "a1", "a2") { cmove_array_br2fn },
          implements cmove_array)
         As cmove_array_br2fn_ok.
  Proof.
    compile.
  Qed.

  Instance spec_of_cswap_array : spec_of "cswap_array" :=
    fnspec! "cswap_array" mask len ptr1 ptr2 / n c1 c2 R,
    (*TODO: if b then bw should be all 1s*)
    { requires tr mem :=
        word.unsigned len = Z.of_nat n /\
        is_mask mask /\
        (sizedlistarray_value AccessWord n ptr1 c1
         * sizedlistarray_value AccessWord n ptr2 c2 * R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        let (c1,c2) := cswap_array mask len c1 c2 in
        (sizedlistarray_value AccessWord n ptr1 c1
         * sizedlistarray_value AccessWord n ptr2 c2 * R)%sep mem' }.

  Derive cswap_array_br2fn SuchThat
         (defn! "cswap_array" ("mask", "len", "a1", "a2") { cswap_array_br2fn },
          implements cswap_array)
         As cswap_array_br2fn_ok.
  Proof.
    compile.
  Qed.
End __.
