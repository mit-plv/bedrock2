(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import bedrock2.TraceInspection.
Require Import bedrock2.e1000_state.
Require Import bedrock2.e1000_read_write_step.
Require Import LiveVerifExamples.e1000_mmio_spec.

Load LiveVerifBitwidth.

(* subset of `Load LiveVerif.`, but without ext_spec/ext_spec_ok context variables *)
Section LiveVerif.
  Import Coq.Strings.String.
  Context {word: word.word bitwidth} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Local Open Scope word_scope.
  Local Open Scope string_scope. Local Open Scope Z_scope.
  Import ZList.List.ZIndexNotations.
  Import DoubleBraceUpdate.
  Local Open Scope zlist_scope.
  Local Open Scope sep_bullets_scope.
  Local Open Scope sepapp_bullets_scope.
  Local Open Scope live_scope.
  Local Open Scope bool_scope.

  Local Hint Mode Word.Interface.word - : typeclass_instances.

  Add Ring wring : (Properties.word.ring_theory (word := word))
        ((*This preprocessing is too expensive to be always run, especially if
           we do many ring_simplify in a sequence, in which case it's sufficient
           to run it once before the ring_simplify sequence.
           preprocess [autorewrite with rew_word_morphism],*)
         morphism (Properties.word.ring_morph (word := word)),
         constants [Properties.word_cst]).

  Instance locals: Interface.map.map String.string word := SortedListString.map _.
  Instance env: Interface.map.map String.string Syntax.func := SortedListString.map _.
  Instance locals_ok: Interface.map.ok locals := SortedListString.ok _.
  Instance env_ok: Interface.map.ok env := SortedListString.ok _.

  Arguments locals: simpl never.
  Arguments env: simpl never.

  Import bedrock2.memory_mapped_ext_spec. (* get ext_spec instance *)


  (* Note: Not C syntax, because in bedrock2, we represent MMIO as external calls,
     whereas in C, it's represented as actual memory accesses.
     Note: Not using the (fun_correct! e1000_read_RDH) notation, because it gets
     confused by the e1000_read_RDH name already in scope *)
  Derive e1000_read_RDH SuchThat (program_logic_goal_for "e1000_read_RDH" e1000_read_RDH)
    As e1000_read_RDH_ok.
    start. fwd.
    eapply wp_read_RDH with (r := RETNAME); try eassumption.
    close_function. (* instantiate list of callees to nil *)
    intros.
    eapply mk_expect_1expr_return. 1: reflexivity.
    eauto 10.
  Qed.

End LiveVerif.
