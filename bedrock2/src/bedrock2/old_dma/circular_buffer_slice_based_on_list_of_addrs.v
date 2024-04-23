Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require coqutil.Map.SortedListZ.
Require Import coqutil.Datatypes.ZList.
Import ZList.List.ZIndexNotations. Local Open Scope zlist_scope.
Require Import coqutil.Datatypes.RecordSetters. Import DoubleBraceUpdate.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.WordNotations. Local Open Scope word_scope.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.SepLib.
Require Import bedrock2.SepBulletPoints.
Require Import bedrock2.RecordPredicates.

Section WithMem.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Byte.byte}.

  (* TODO move,
     and maybe this could be used to define array and sepapps more conveniently? *)
  Section WithElem.
    Context {E: Type}.

    Definition layout_absolute(ps: list (word -> mem -> Prop))(addrs: list word) :=
      seps' (List.map (fun '(p, a) => p a) (List.combine ps addrs)).

    Definition layout_offsets(ps: list (word -> mem -> Prop))(offsets: list Z)(addr: word):
      mem -> Prop :=
      layout_absolute ps (List.map (fun ofs => word.add addr (word.of_Z ofs)) offsets).

    Definition scattered_array(elem: E -> word -> mem -> Prop)
                              (vs: list E)(addrs: list word): mem -> Prop :=
      layout_absolute (List.map elem vs) addrs.

    Definition array'(elem: E -> word -> mem -> Prop){sz: PredicateSize elem}
                     (vs: list E): word -> mem -> Prop :=
      layout_offsets (List.map elem vs)
             (List.map (fun i => sz * Z.of_nat i) (List.seq O (List.length vs))).

    (* starts with 0 and has same length as given list, so the last element sum
       excludes the last element *)
    Fixpoint prefix_sums_starting_at(s: Z)(l: list Z): list Z :=
      match l with
      | nil => nil
      | cons h t => cons (s + h) (prefix_sums_starting_at (s + h) t)
      end.
    Definition prefix_sums: list Z -> list Z := prefix_sums_starting_at 0.

    Definition sepapps'(l: list sized_predicate): word -> mem -> Prop :=
      layout_offsets (List.map proj_predicate l) (prefix_sums (List.map proj_size l)).

    Definition circular_interval(modulus start: Z)(count: nat): list Z :=
      List.unfoldn (fun x => (x + 1) mod modulus) count start.

    (* The address a passed to this predicate is the base address. The area
       occupied by the whole buffer is a..a+modulus*sz, but there might actually
       be nothing at a, since the slice starts at a+startIndex*sz. *)
    Definition circular_buffer_slice(elem: E -> word -> mem -> Prop)
      {sz: PredicateSize elem}(modulus startIndex: Z)(vs: list E): word -> mem -> Prop :=
      layout_offsets (List.map elem vs)
             (List.map (Z.mul sz) (circular_interval modulus startIndex (List.length vs))).
  End WithElem.

End WithMem.
