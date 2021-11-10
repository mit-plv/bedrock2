Require Import Coq.Strings.Byte Coq.Strings.String.

Section Spec.
  Open Scope string_scope.

  Definition string_map (f: byte -> byte) (s: String.string) :=
    string_of_list_byte (List.map f (list_byte_of_string s)).

  Definition upchar_spec (c: byte) :=
    match c with
    | "a" => "A" | "b" => "B" | "c" => "C" | "d" => "D"
    | "e" => "E" | "f" => "F" | "g" => "G" | "h" => "H"
    | "i" => "I" | "j" => "J" | "k" => "K" | "l" => "L"
    | "m" => "M" | "n" => "N" | "o" => "O" | "p" => "P"
    | "q" => "Q" | "r" => "R" | "s" => "S" | "t" => "T"
    | "u" => "U" | "v" => "V" | "w" => "W" | "x" => "X"
    | "y" => "Y" | "z" => "Z" | c => c
    end%byte.

  Definition upstr_spec (s: string) :=
    string_map upchar_spec s.

  Compute upstr_spec "rupicola".
End Spec.

Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Loops.
Require Import Rupicola.Lib.Arrays.
Require Import bedrock2.BasicC32Semantics.

Section Impl.
  Definition upchar_impl (b: byte) :=
    if word.wrap (byte.unsigned b - byte.unsigned "a"%byte) <? 26
    then byte_land b x5f else b.

  Lemma upchar_impl_ok b:
    upchar_spec b = upchar_impl b.
  Proof. destruct b; reflexivity. Qed.

  Definition upstr_impl (s: list byte) :=
    let/n s := nd_ranged_for_all
                0 (Z.of_nat (length s))
                (fun s idx =>
                   let/n b := ListArray.get s idx in
                   let/n b := upchar_impl b in
                   let/n s := ListArray.put s idx b in
                   s) s in
    s.

  Lemma upstr_impl_ok bs:
    upstr_impl bs = list_byte_of_string (upstr_spec (string_of_list_byte bs)).
  Proof.
    unfold upstr_spec, upstr_impl, string_map, nlet,
      ListArray.get, ListArray.put, cast, Convertible_Z_nat.
    rewrite !list_byte_of_string_of_list_byte;
      symmetry; apply map_as_nd_ranged_for_all.
    intros; erewrite !Nat2Z.id, nth_indep, upchar_impl_ok by lia;
      reflexivity.
  Qed.

  Lemma upstr_impl_ok' s:
    upstr_spec s = string_of_list_byte (upstr_impl (list_byte_of_string s)).
  Proof. rewrite upstr_impl_ok, !string_of_list_byte_of_string; reflexivity. Qed.
End Impl.

Section Compiler.
  Lemma wrap_unsigned_lt (z1 z2: Z) (z: Z) :
    0 <= z < 2 ^ 32 ->
    (word.wrap (z1 - z2) <? z) =
    (word.ltu (word.sub (word := word) (word.of_Z z1) (word.of_Z z2))
              (word.of_Z z)).
  Proof.
    rewrite <- word.ring_morph_sub, word.unsigned_ltu, !word.unsigned_of_Z.
    intros; rewrite (word.wrap_small z); eauto.
  Qed.

  Lemma dexpr_compile_upper {mem locals} {e} {z1 z2: Z}:
    WeakestPrecondition.dexpr
      mem locals e
      (word.b2w (word := word)
                (word.ltu (word.sub (word := word) (word.of_Z z1) (word.of_Z z2))
                          (word.of_Z 26))) ->
    WeakestPrecondition.dexpr
      mem locals e
      (word.b2w (word := word)
                (word.wrap (z1 - z2) <? 26)).
  Proof. intros; rewrite wrap_unsigned_lt by lia; eassumption. Qed.
End Compiler.

Section Upstr.
  Instance spec_of_upstr : spec_of "upstr" :=
    fnspec! "upstr" s_ptr wlen / (s : list byte) R,
      { requires tr mem :=
          wlen = word.of_Z (Z.of_nat (length s)) /\
          Z.of_nat (Datatypes.length s) < 2 ^ 32 /\ (* FIXME implied by sep *)
          (sizedlistarray_value AccessByte (length s) s_ptr s * R)%sep mem;
        ensures tr' mem' :=
          tr' = tr /\
          (sizedlistarray_value AccessByte (length s) s_ptr (upstr_impl s) * R)%sep mem' }.

  Import LoopCompiler.
  Import SizedListArrayCompiler.

  #[local] Hint Extern 1 => simple apply dexpr_compile_upper; shelve : compiler_side_conditions.

  #[local] Hint Extern 1 => lia : arith.
  Hint Rewrite Z2Nat.id using eauto with arith : compiler_side_conditions.

  Hint Rewrite Nat2Z.id : compiler_cleanup.
  #[local] Hint Unfold upchar_impl : compiler_cleanup.
  #[local] Hint Extern 10 => cbn; Z.div_mod_to_equations; nia : compiler_side_conditions.

  Derive upstr_body SuchThat
         (defn! "upstr" ("s", "len")
           { upstr_body },
           implements upstr_impl)
         As body_correct.
  Proof.
    Time compile.
    eapply compile_nlet_as_nlet_eq.
    ExprReflection.compile_let_as_expr.
    ExprReflection.reify_change_dexpr.

    eapply ExprReflection.interp_sound.
    reflexivity.
    eapply map.mapped_compat_of_list.
    cbv [List.map fst snd ExprReflection.er_T2w ExprReflection.expr_byte_denotation].
    rewrite ?word.of_Z_unsigned
    lazymatch goal with
    | |- context[expr_Z_denotation] => (* LATER Use reification to speed up this rewrite *)
        cbv [List.map fst snd er_T2w expr_Z_denotation]; rewrite ?word.of_Z_unsigned
      | _ => idtac
      end; reflexivity
      | .. ].


    ExprReflection.compile_prove_reified_dexpr.
      compile_assignment.
    compile_step.
  Time Qed.

End Upstr.
Require Import bedrock2.ToCString.
Compute c_func ("upstr", (["s"; "len"], ["chk16"], upstr_body)).
