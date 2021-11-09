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
#[local] Hint Unfold co_word_of_Z co_word_of_byte : compiler_side_conditions.

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

Derive ip_checksum_body SuchThat
       (defn! "ip_checksum" ("data", "len") ~> "chk16"
         { ip_checksum_body },
         implements ip_checksum_impl)
       As body_correct.
Proof.
  compile_setup.

  Time repeat compile_step.

  (* FIXME use these notations to prevent inlinetables lemmas and array lemmas from firing too often. *)

  Hint Extern 1 (WP_nlet (ranged_for_all_nd _ _ _ _)) =>
         rewrite nd_as_ranged_for_all; shelve : compiler_cleanup.
  Hint Extern 1 (WP_nlet (ranged_for_all _ _ _ _)) =>
         rewrite ranged_for_all_as_ranged_for; shelve : compiler_cleanup.

  Hint Unfold ip_checksum_upd : compiler_cleanup.

  repeat compile_step.
  Import LoopCompiler.
  Import UnsizedListArrayCompiler.
  repeat compile_step.

  replace (word.of_Z (Z.of_nat (Datatypes.length data) / 2))
    with (word.of_Z (Z.of_nat (Datatypes.length data)) >>w 1) by admit.

  all: repeat compile_step.

  solve [Z.div_mod_to_equations; nia].
  solve [Z.div_mod_to_equations; nia].
  cbn [fst snd ExitToken.branch ExitToken.new].

  2: {
    replace (word.b2w (Z.odd (Z.of_nat (Datatypes.length data))))
    with (word.and (word := word) (word.of_Z (Z.of_nat (Datatypes.length data))) (word.of_Z 1)) by admit.
    repeat compile_step. }

  2: {
    rewrite Z2Nat.id.
    compile_step.
    admit.
  }

  2: {
    rewrite Z2Nat.id.
    compile_step.
    admit.
  }

  Ltac compile_binding ::=
    (* We want to flip nlets before introducing nlet_eq. *)
    repeat simple apply compile_nested_nlet;
    (* We don't want to show users goals with nlet_eq, so compile_nlet_as_nlet_eq
     isn't in the ‘compiler’ hint db. *)
    try simple apply compile_nlet_as_nlet_eq;
    step_with_db compiler.

  all: repeat compile_step.
  2: {
    replace (~w v1 &w word.of_Z 65535)
    with ((v1 ^w 0xffff) &w word.of_Z 65535) by admit.
    repeat compile_step.
    repeat compile_step. }

  solve_map_get_goal_step.
  admit.
Qed.

Require Import bedrock2.ToCString.
Compute c_func ("ip_checksum", (["data"; "len"], ["c"; "e"; "offset"], ip_checksum_body)).
