Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import coqutil.Datatypes.Inhabited.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require coqutil.Map.SortedListString. (* for function env, other maps are kept abstract *)
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Byte.
Require Import coqutil.Tactics.fwd.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Array.
Require Import bedrock2.ZnWords.
Require Import bedrock2.groundcbv.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Require Import coqutil.Word.Bitwidth32.
Require coqutil.Datatypes.String coqutil.Map.SortedList coqutil.Map.SortedListString.
Require Import bedrock2.SepBulletPoints.
Require Import coqutil.Datatypes.ZList.
Require Import bedrock2.WordNotations. Local Open Scope word_scope.
Require Import bedrock2.find_hyp.
Require Import bedrock2.HeapletwiseHyps.
Require Import bedrock2.bottom_up_simpl_ltac1.
Require Import bedrock2Examples.LiveVerif.LiveRules.
Require Import bedrock2Examples.LiveVerif.PackageContext.
Require Import bedrock2Examples.LiveVerif.LiveTactics.
Require Import bedrock2Examples.LiveVerif.LiveParsing.
Require Import Ltac2.Ltac2.

Local Set Ltac Backtrace.
Local Set Ltac2 Backtrace.

Section LiveVerif.
  Import Coq.Strings.String.
  Context {word: word.word 32} {mem: map.map word Byte.byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Local Open Scope string_scope. Local Open Scope Z_scope.
  Import ZList.List.ZIndexNotations.
  Local Open Scope zlist_scope.
  Local Open Scope sep_bullets_scope.
  Local Open Scope live_scope.

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

  Local Set Default Goal Selector "all".

  Local Arguments after_if {width BW word mem locals ext_spec fs b Q1 Q2 rest post}.
