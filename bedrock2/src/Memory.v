Require Coq.Lists.List.
Require Import coqutil.sanity.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList coqutil.Datatypes.List.
Require Import coqutil.Map.Interface.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.LittleEndian.
Require Import bedrock2.Notations bedrock2.Syntax.


Section Memory.
  Context {byte: word 8} {width: Z} {word: word width} {mem: map.map word (option byte)}.

  Definition footprint(a: word)(sz: nat): tuple word sz :=
    tuple.unfoldn (fun w => word.add w (word.of_Z 1)) sz a.

  Definition load_bytes(sz: nat)(m: mem)(addr: word): option (tuple byte sz) :=
    match map.getmany_of_tuple m (footprint addr sz) with
    | Some optbytes => tuple.option_all optbytes
    | None => None
    end.

  Definition unchecked_store_bytes(sz: nat)(m: mem)(a: word)(bs: tuple byte sz): mem :=
    map.putmany_of_tuple (footprint a sz) (tuple.map Some bs) m.

  Definition store_bytes(sz: nat)(m: mem)(a: word)(v: tuple byte sz): option mem :=
    match load_bytes sz m a with
    | Some _ => Some (unchecked_store_bytes sz m a v)
    | None => None (* some addresses were invalid *)
    end.

  Definition bytes_per sz :=
    match sz with
      | access_size.one => 1 | access_size.two => 2 | access_size.four => 4
      | access_size.word => Z.to_nat (Z.div (Z.add width 7) 8)
    end%nat.

  Definition load(sz: access_size)(m: mem)(a: word): option word :=
    match load_bytes (bytes_per sz) m a with
    | Some bs => Some (word.of_Z (LittleEndian.combine _ bs))
    | None => None
    end.

  Definition store(sz: access_size)(m: mem)(a: word)(v: word): option mem :=
    store_bytes (bytes_per sz) m a (LittleEndian.split _ (word.unsigned v)).

End Memory.
