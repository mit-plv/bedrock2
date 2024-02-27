(* This file needs to be included with `Load LiveVerif`, after importing LiveVerifLib *)

(* Somewhere on the load path, there needs to be a file named LiveVerifBitwidth.v which
   contains either
   `Require Import coqutil.Word.Bitwidth32.` or
   `Require Import coqutil.Word.Bitwidth64.`
  The current file doesn't contain this because it is designed to be bitwidth-independent. *)
Load LiveVerifBitwidth.

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

  (* TODO should we remove this an require users to specify their own each time? *)
  Context {ext_spec: Semantics.ExtSpec} {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Instance locals: Interface.map.map String.string word := SortedListString.map _.
  Instance env: Interface.map.map String.string Syntax.func := SortedListString.map _.
  Instance locals_ok: Interface.map.ok locals := SortedListString.ok _.
  Instance env_ok: Interface.map.ok env := SortedListString.ok _.

  Arguments locals: simpl never.
  Arguments env: simpl never.

  Local Set Default Goal Selector "1".
  Local Set Ltac Backtrace.
  Local Set Ltac2 Backtrace.

  Local Arguments after_if {width BW word mem locals ext_spec fs b Q1 Q2 rest post}.
