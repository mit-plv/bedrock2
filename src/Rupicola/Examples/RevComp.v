(* https://benchmarksgame-team.pages.debian.net/benchmarksgame/description/revcomp.html *)
Require Import Coq.Strings.String Coq.Strings.Ascii.

Section Spec.
  Open Scope string_scope.

  Fixpoint string_map (f: ascii -> ascii) (s: String.string) :=
    match s with
    | EmptyString => EmptyString
    | String a s => String (f a) (string_map f s)
    end.

  Definition rev1_spec (c: ascii) :=
    match c with
    | "A" => "T"
    | "C" => "G"
    | "G" => "C"
    | "T" => "A"
    | "U" => "A"
    | "M" => "K"
    | "R" => "Y"
    | "W" => "W"
    | "S" => "S"
    | "Y" => "R"
    | "K" => "M"
    | "V" => "B"
    | "H" => "D"
    | "D" => "H"
    | "B" => "V"
    | "N" => "N"
    | _ => c
    end%char.

  Definition revcomp_spec (s: string) :=
    string_map rev1_spec s.

  Compute revcomp_spec "rupicola".
End Spec.

Require Import Coq.Strings.Byte.
Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Loops.
Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Lib.InlineTables.
Require Import bedrock2.BasicC64Semantics.

Section Impl.
  Definition table: InlineTable.t byte :=
    Eval compute in
    List.map (fun n =>
                match Byte.of_nat n with
                | None => x00
                | Some b => byte_of_ascii (rev1_spec (ascii_of_byte b))
                end)
             (seq 0 256).

  Definition rev1_impl (b: byte) :=
    InlineTable.get table b.

  Lemma rev1_impl_ok a:
    rev1_spec a = ascii_of_byte (rev1_impl (byte_of_ascii a)).
  Proof. destruct a as [[|][|][|][|][|][|][|][|]]; reflexivity. Qed.

  Lemma rev1_impl_ok' b:
    byte_of_ascii (rev1_spec (ascii_of_byte b)) = rev1_impl b.
  Proof. destruct b; reflexivity. Qed.

  Definition revcomp_impl (s: list byte) :=
    let/n s := nd_ranged_for_all
                0 (Z.of_nat (length s))
                (fun s idx =>
                   let/n b := ListArray.get s idx in
                   let/n b := rev1_impl b in
                   let/n s := ListArray.put s idx b in
                   s) s in
    s.

  Lemma string_map_is_map f s:
    string_map f s = string_of_list_ascii (List.map f (list_ascii_of_string s)).
  Proof. induction s; simpl; congruence. Qed.

  Lemma revcomp_impl_ok bs:
    revcomp_impl bs = list_byte_of_string (revcomp_spec (string_of_list_byte bs)).
  Proof.
    unfold revcomp_spec, revcomp_impl, nlet,
      list_byte_of_string, string_of_list_byte,
      ListArray.get, ListArray.put, cast, Convertible_Z_nat.
    rewrite string_map_is_map, !list_ascii_of_string_of_list_ascii, !map_map.
      symmetry; apply map_as_nd_ranged_for_all.
    intros; erewrite !Nat2Z.id, nth_indep, rev1_impl_ok' by lia.
      reflexivity.
  Qed.

  Lemma revcomp_impl_ok' s:
    revcomp_spec s = string_of_list_byte (revcomp_impl (list_byte_of_string s)).
  Proof. rewrite revcomp_impl_ok, !string_of_list_byte_of_string; reflexivity. Qed.
End Impl.

Section Hints.
  Lemma bytes_in_table b:
    (Z.to_nat (byte.unsigned b) < List.length table)%nat.
  Proof. pose proof byte.unsigned_range b; simpl; lia. Qed.

  Lemma byte_pos b:
    0 <= byte.unsigned b.
  Proof. pose proof byte.unsigned_range b; lia. Qed.
End Hints.

Section Revcomp.
  Instance spec_of_revcomp : spec_of "revcomp" :=
    fnspec! "revcomp" s_ptr wlen / (s : list byte) R,
      { requires tr mem :=
          wlen = word.of_Z (Z.of_nat (length s)) /\
          Z.of_nat (Datatypes.length s) < 2 ^ 32 /\ (* FIXME implied by sep *)
          (sizedlistarray_value AccessByte (length s) s_ptr s * R)%sep mem;
        ensures tr' mem' :=
          tr' = tr /\
          (sizedlistarray_value AccessByte (length s) s_ptr (revcomp_impl s) * R)%sep mem' }.

  Import LoopCompiler.
  Import SizedListArrayCompiler.

  Hint Rewrite Nat2Z.id : compiler_cleanup.
  Hint Rewrite Z2Nat.id using eauto with lia : compiler_side_conditions.

  #[local] Hint Unfold rev1_impl : compiler_cleanup.
  #[local] Hint Extern 1 => cbn; nia : compiler_side_conditions.
  #[local] Hint Resolve bytes_in_table byte_pos : compiler_side_conditions.

  Derive revcomp_body SuchThat
         (defn! "revcomp" ("s", "len")
           { revcomp_body },
           implements revcomp_impl)
         As body_correct.
  Proof.
    Time compile.
  Time Qed.
End Revcomp.

Definition revcomp_br2func : func := ("revcomp", (["s"; "len"], ["chk16"], revcomp_body)).

Require Import bedrock2.ToCString.
Definition revcomp_cbytes := Eval vm_compute in
  list_byte_of_string (ToCString.c_module [revcomp_br2func]).
