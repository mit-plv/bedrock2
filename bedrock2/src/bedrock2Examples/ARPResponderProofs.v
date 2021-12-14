From Coq Require Import Strings.String Lists.List ZArith.BinInt.
From coqutil.Word Require Import Interface.
From bedrock2 Require Import Semantics BasicC32Semantics ProgramLogic.
Require Import coqutil.Byte.
Require Import coqutil.Z.Lia.

Require Import bedrock2Examples.ARPResponder.

Import Datatypes List ListNotations.
Local Open Scope string_scope. Local Open Scope list_scope. Local Open Scope Z_scope.

From bedrock2 Require Import Array Scalars Separation.
From coqutil.Tactics Require Import letexists rdelta.
Local Notation bytes := (array scalar8 (word.of_Z 1)).

Ltac seplog_use_array_load1 H i :=
  let iNat := eval cbv in (Z.to_nat i) in
  unshelve SeparationLogic.seprewrite_in @array_index_nat_inbounds H;
    [exact iNat|exact (word.of_Z 0)|blia|];
  change ((word.unsigned (word.of_Z 1) * Z.of_nat iNat)%Z) with i in *.


Local Instance spec_of_arp : spec_of "arp" := fun functions =>
  forall t m packet ethbuf len R,
    (sep (array scalar8 (word.of_Z 1) ethbuf packet) R) m ->
    word.unsigned len = Z.of_nat (length packet) ->
  WeakestPrecondition.call functions "arp" t m [ethbuf; len] (fun T M rets => True).

Local Hint Mode Word.Interface.word - : typeclass_instances.

Goal program_logic_goal_for_function! arp.
  eexists; split; repeat straightline.
  1: exact eq_refl.
  letexists; split; [solve[repeat straightline]|]; split; [|solve[repeat straightline]]; repeat straightline.
  eapply Properties.word.if_nonzero in H1.
  rewrite word.unsigned_ltu, word.unsigned_of_Z in H1. cbv [word.wrap] in H1.
  rewrite Z.mod_small in H1; cycle 1. { cbv. split; congruence. }
  eapply Z.ltb_lt in H1.
  repeat (letexists || straightline).
  split.
  1: repeat (split || letexists || straightline).
  Ltac tload :=
  lazymatch goal with |- Memory.load Syntax.access_size.one ?m (word.add ?base (word.of_Z ?i)) = Some ?v =>
  lazymatch goal with H: _ m |- _ =>
    let iNat := eval cbv in (Z.to_nat i) in
    SeparationLogic.seprewrite_in @array_index_nat_inbounds H;
    [instantiate (1 := iNat); blia|match goal with H : _ |- _ => instantiate (1 := byte.of_Z 0) in H end];
    eapply load_one_of_sep;
    change (word.of_Z (word.unsigned (word.of_Z 1) * Z.of_nat iNat)) with (word.of_Z i) in *;
    SeparationLogic.ecancel_assumption
  end end.

  all:try tload.
  1: subst v0; exact eq_refl.
  split; [|solve[repeat straightline]]; repeat straightline.

  letexists; split; [|split; [|solve[repeat straightline]]].
  1: solve [repeat (split || letexists || straightline || tload)].

  repeat straightline.

  lazymatch goal with |- WeakestPrecondition.store Syntax.access_size.one ?m ?a ?v ?post =>
  lazymatch goal with H: _ m |- _ =>
      idtac H;
    let av := rdelta a in
    let i := lazymatch av with word.add ?base (word.of_Z ?i) => i end in
    let iNat := eval cbv in (Z.to_nat i) in
    pose i;
    SeparationLogic.seprewrite_in @array_index_nat_inbounds H;
    [instantiate (1 := iNat); blia|match goal with H : _ |- _ => instantiate (1 := byte.of_Z 0) in H end];
    eapply store_one_of_sep;
    change (word.of_Z (word.unsigned (word.of_Z 1) * Z.of_nat iNat)) with (word.of_Z i) in *;
    [SeparationLogic.ecancel_assumption|]
  end end.

  straightline.
  straightline.
  straightline.
  straightline.
  straightline.

  unshelve erewrite (_:a = word.add ethbuf (word.of_Z (Z.of_nat (length (firstn 21 packet))))) in H4. {
    rewrite List.length_firstn_inbounds by blia.
    trivial. }
Abort.
