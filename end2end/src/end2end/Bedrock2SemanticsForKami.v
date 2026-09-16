Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList coqutil.Map.SortedListString.
Require Import coqutil.Word.Bitwidth32 coqutil.Map.SortedListWord.
Require Import compilerExamples.MMIO.

Import Strings.String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition MMIOREAD : string := "MMIOREAD".
Definition MMIOWRITE : string := "MMIOWRITE".

#[global] Instance mem: Interface.map.map (bits 32) Byte.byte := SortedListWord.map _ _.
#[global] Instance mem_ok: Interface.map.ok mem := SortedListWord.ok _ _.
