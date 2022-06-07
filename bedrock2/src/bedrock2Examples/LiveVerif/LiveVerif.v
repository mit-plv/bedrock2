Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import coqutil.Z.Lia.
Require Import coqutil.Byte coqutil.Datatypes.HList.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Datatypes.Inhabited.
Require Import coqutil.Tactics.letexists coqutil.Tactics.Tactics coqutil.Tactics.rewr coqutil.Tactics.rdelta.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require coqutil.Map.SortedListString. (* for function env, other maps are kept abstract *)
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.fwd.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Array.
Require Import bedrock2.ZnWords.
Require Import bedrock2.groundcbv.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Require Import bedrock2.WeakestPrecondition bedrock2.ProgramLogic bedrock2.Loops.
Require Import coqutil.Word.Bitwidth32.
Require coqutil.Datatypes.String coqutil.Map.SortedList coqutil.Map.SortedListString.
Require Import bedrock2Examples.LiveVerif.string_to_ident.
Require Import bedrock2.ident_to_string.
Require Import bedrock2.autorew.
Import WordRingAutorewr HypAutorewr ListNoSCAutorewr
       PushPullIfAutorewr LiaSCAutorewr ZnWordsSCAutorewr.
Require Import bedrock2.SepBulletPoints.
Require Import bedrock2.SepAutoArray bedrock2.SepAutoExports.
Require Import bedrock2.OperatorOverloading.

Section LiveVerif.
  Import Syntax BinInt String List.ListNotations ZArith.
  Context {word: word.word 32} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Local Set Implicit Arguments.
  Local Open Scope string_scope. Local Open Scope Z_scope.
  (* Not a Definition because if the Z.of_nat is visible, lia knows it's positive *)
  Notation "'len' l" := (Z.of_nat (List.length l)) (at level 10).
  Notation "'bytetuple' sz" := (HList.tuple byte (@Memory.bytes_per 32 sz)) (at level 10).
  Local Open Scope oo_scope.
  Local Open Scope list_index_scope.
  Local Open Scope conversion_parse_scope.
  Local Open Scope conversion_print_scope.
  Local Open Scope sep_bullets_scope.

  Add Ring wring : (Properties.word.ring_theory (word := word))
        ((*This preprocessing is too expensive to be always run, especially if
           we do many ring_simplify in a sequence, in which case it's sufficient
           to run it once before the ring_simplify sequence.
           preprocess [autorewrite with rew_word_morphism],*)
         morphism (Properties.word.ring_morph (word := word)),
         constants [Properties.word_cst]).

  (* TODO should we remove this an require users to specify their own each time? *)
  Context {ext_spec: ExtSpec} {ext_spec_ok : ext_spec.ok ext_spec}.

  Instance locals: Interface.map.map String.string word := SortedListString.map _.
  Instance env: Interface.map.map String.string (list String.string * list String.string * cmd) :=
    SortedListString.map _.
  Instance locals_ok: Interface.map.ok locals := SortedListString.ok _.
  Instance env_ok: Interface.map.ok env := SortedListString.ok _.

  Arguments locals: simpl never.
  Arguments env: simpl never.

  Ltac fwd_rewrites ::= autorew_in_hyps.
