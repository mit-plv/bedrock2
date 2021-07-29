Require Import bedrock2.NotationsCustomEntry.

Import Syntax Syntax.Coercions BinInt String List List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Require Import bedrock2.WeakestPrecondition bedrock2.Semantics bedrock2.ProgramLogic.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface bedrock2.Map.SeparationLogic.

(*Require Import bedrock2.ptsto_bytes.*)
Require Import coqutil.Map.OfListWord.
Local Notation "xs $@ a" := (map.of_list_word_at a xs) (at level 10, format "xs $@ a").
Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing) (* experiment*).

Section WithParameters.
  Context {width} {BW: Bitwidth width}.
  Context {word: word.word width} {mem: map.map word Byte.byte} {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Import ProgramLogic.Coercions.


  Instance spec_of_memmove : spec_of "memmove" :=
    fnspec! "memmove" dst src (n : word) / d s R Rs,
    { requires t m := m =* s$@src * Rs /\ m =* d$@dst * R /\
      length s = n :> Z /\ length d = n :> Z /\ n < 2^(width-1);
      ensures t' m' := t=t' /\ sep (eq(s$@dst)) R m }.
End WithParameters.
