Require Import bedrock2.NotationsCustomEntry.

Import Syntax Syntax.Coercions BinInt String List List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Require Import bedrock2.WeakestPrecondition bedrock2.Semantics bedrock2.ProgramLogic.
Require Import coqutil.Word.Interface coqutil.Map.Interface bedrock2.Map.SeparationLogic.

(*Require Import bedrock2.ptsto_bytes.*)
Require Import coqutil.Map.OfListWord.
Local Notation "xs $@ a" := (map.of_list_word_at a xs) (at level 10, format "xs $@ a").

Section WithParameters.
  Context {p : Semantics.parameters}.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Coercion word.unsigned : word.rep >-> Z.

  Local Hint Mode map.map + + : typeclass_instances.
  Let sepclause {key value} {map : map.map key value} := map -> Prop.
  Local Coercion map_eq {key value map} (m : @map.rep key value map)
    : sepclause := Logic.eq m.
  Local Definition sep {key value} {map : map.map key value}
    : sepclause -> sepclause -> sepclause := sep (map:=map).
  Local Infix "*" := sep : sep_scope.
  Local Notation "m =* P" := ((P%sep:sepclause) m) (at level 70, only parsing).

  Instance spec_of_memmove : spec_of "memmove" :=
    fnspec! "memmove" dst src (n : Semantics.word) / d s R Rs,
    { requires t m := m =* s$@src * Rs /\ m =* d$@dst * R /\
      length s = n :> Z /\ length d = n :> Z /\ n < 2^(width-1);
      ensures t' m' := t=t' /\ sep (eq(s$@dst)) R m }.
End WithParameters.
