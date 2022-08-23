Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList coqutil.Map.SortedListString.
Require Import coqutil.Word.Interface coqutil.Map.SortedListWord.
Require Import processor.KamiWord.
Require Import compiler.RiscvWordProperties.
Require Import end2end.KamiRiscvWordProperties.
Require Import compilerExamples.MMIO.

Import String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition MMIOREAD : string := "MMIOREAD".
Definition MMIOWRITE : string := "MMIOWRITE".

#[global] Instance word: word.word 32 := KamiWord.word 32.
#[global] Instance word_ok: word.ok word := KamiWord.ok 32 eq_refl.

#[global] Instance word_riscv_ok: word.riscv_ok word.
refine (@kami_word_riscv_ok 5 _ _).
all: cbv; congruence.
Qed.

#[global] Instance mem: Interface.map.map word Byte.byte := SortedListWord.map _ _.
#[global] Instance mem_ok: Interface.map.ok mem := SortedListWord.ok _ _.

Add Ring wring : (Properties.word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word)),
       constants [Properties.word_cst]).
