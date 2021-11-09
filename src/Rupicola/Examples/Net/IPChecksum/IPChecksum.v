From Rupicola.Examples Require Import IPChecksum.Impl.

Instance spec_of_ip_checksum : spec_of "ip_checksum" :=
  fnspec! "ip_checksum" data_ptr wlen / (data : list byte) R ~> chk,
    { requires tr mem := (* FIXME can length be a nat? *)
        wlen = word.of_Z (Z.of_nat (length data)) /\
        Z.of_nat (Datatypes.length data) < 2 ^ 32 /\ (* FIXME implied by sep *)
        (listarray_value AccessByte data_ptr data * R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        chk = ip_checksum_impl data /\
        (listarray_value AccessByte data_ptr data * R)%sep mem' }.

Import UnsizedListArrayCompiler.
#[local] Hint Unfold co_word_of_Z co_word_of_byte : compiler_cleanup.

Hint Rewrite Nat2Z.id : compiler_side_conditions.
#[local] Hint Extern 10 => cbn; lia : compiler_side_conditions.

Ltac compile_ranged_for ::=
  lazymatch goal with
  | [ |- WeakestPrecondition.cmd _ _ _ _ ?locals (_ (nlet_eq _ ?v _)) ] =>
      lazymatch v with
      | (ranged_for 0%Z ?to _ _) =>
          _compile_ranged_for locals to (compile_ranged_for_fresh false)
      | (ranged_for _ ?to _ _) =>
          _compile_ranged_for locals to (compile_ranged_for_fresh true)
      | (ranged_for_u _ ?to _ _) =>
          _compile_ranged_for locals to compile_ranged_for_u
      | (ranged_for_s _ ?to _ _) =>
          _compile_ranged_for locals to compile_ranged_for_s
      end
  end.

Hint Extern 1 (WP_nlet (nd_ranged_for_all _ _ _ _)) =>
       rewrite nd_as_ranged_for_all; shelve : compiler_cleanup.
Hint Extern 1 (WP_nlet (ranged_for_all _ _ _ _)) =>
       rewrite ranged_for_all_as_ranged_for; shelve : compiler_cleanup.

Hint Unfold ip_checksum_upd : compiler_cleanup.

Ltac compile_binding ::=
  (* We want to flip nlets before introducing nlet_eq. *)
  repeat simple apply compile_nested_nlet;
  (* We don't want to show users goals with nlet_eq, so compile_nlet_as_nlet_eq
     isn't in the ‘compiler’ hint db. *)
  try simple apply compile_nlet_as_nlet_eq;
  step_with_db compiler.

Hint Extern 1 (_ < _) => Z.div_mod_to_equations; nia : compiler_side_conditions.
Hint Extern 1 (_ <= _) => Z.div_mod_to_equations; nia : compiler_side_conditions.

Derive ip_checksum_body SuchThat
       (defn! "ip_checksum" ("data", "len") ~> "chk16"
         { ip_checksum_body },
         implements ip_checksum_impl)
       As body_correct.
Proof.
  compile_setup.
  Time repeat compile_step.

  Import LoopCompiler.
  Import UnsizedListArrayCompiler.

  compile_step; try solve [repeat compile_step].

  replace (word.of_Z (Z.of_nat (Datatypes.length data) / 2))
    with (word.of_Z (Z.of_nat (Datatypes.length data)) >>w 1) by admit.
  repeat compile_step.

  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.

  Lemma compile_push_pair {tr mem locals functions} {T A B} vs1 (t: T) (v1: A) (k1: A -> B):
    let v := (t, nlet vs1 v1 k1) in
    forall {pred: T * B -> predicate} {cmd},
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd
      <{ pred (nlet vs1 v1 (fun v1 => (t, k1 v1))) }> ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd
      <{ pred (t, nlet vs1 v1 k1) }>.
  Proof. intros; assumption. Qed.

  (* FIXME this needs to be in yet another database that applies before moving to nlet_eq (like the un-nesting lemma, and it needs to be on repeat *)
  Hint Extern 1 => simple eapply compile_push_pair; shelve : compiler.

  repeat (simple apply compile_push_pair || compile_step).
  all: repeat compile_step.

  Hint Rewrite Z2Nat.id using lia : compiler_side_conditions.
  all: repeat compile_step.

  replace (word.b2w (Z.odd (Z.of_nat (Datatypes.length data))))
    with (word.and (word := word) (word.of_Z (Z.of_nat (Datatypes.length data))) (word.of_Z 1)) by admit.
  repeat compile_step.

  {
  rewrite Z2Nat.id; [compile_step|].
  (* Odd means sub 1 gt 0 *)
  admit.
  }

  {
    rewrite Z2Nat.id; [compile_step|].
    (* Odd means sub 1 gt 0 *)
    admit.
  }

  {
    replace (~w v1 &w word.of_Z 65535)
    with ((v1 ^w 0xffff) &w word.of_Z 65535) by admit.
    repeat compile_step.
    repeat compile_step.
  }

  admit.
Qed.

Require Import bedrock2.ToCString.
Compute c_func ("ip_checksum", (["data"; "len"], ["c"; "e"; "offset"], ip_checksum_body)).
