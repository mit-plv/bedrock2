Require Coq.Lists.List.
Require Import coqutil.sanity.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList.
Require Import bedrock2.Notations bedrock2.Syntax coqutil.Map.Interface.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.LittleEndian.

(* TODO: moveme *)
Module List.
  Section WithA.
    Context {A : Type}.
    Fixpoint option_all (xs : list (option A)) {struct xs} : option (list A) :=
      match xs with
      | nil => Some nil
      | cons ox xs =>
        match ox, option_all xs with
        | Some x, Some ys => Some (cons x ys)
        | _ , _ => None
        end
      end.

    Section WithStep.
      Context (step : A -> A).
      Fixpoint unfoldn (n : nat) (start : A) :=
        match n with
        | 0%nat => nil
        | S n => cons start (unfoldn n (step start))
        end.
    End WithStep.
  End WithA.
End List.

Section Memory.
  Context {byte: word 8} {width: Z} {word: word width} {mem: map.map word byte}.

  Definition bytes_per sz :=
    match sz with
      | access_size.one => 1 | access_size.two => 2 | access_size.four => 4
      | access_size.word => Z.to_nat (Z.div (Z.add width 7) 8)
    end%nat.

  Definition footprint(a: word)(sz: access_size) :=
    List.unfoldn (fun w => word.add w (word.of_Z 1)) (bytes_per sz) a.
  Definition load(sz: access_size)(m: mem)(a: word): option word :=
    'Some bs <- List.option_all (List.map (map.get m) (footprint a sz)) | None ;
    Some (word.of_Z (LittleEndian.combine _ (tuple.of_list bs))).
  Definition unchecked_store(sz: access_size)(m: mem)(a: word)(v: word) : option mem :=
    map.putmany_of_list
      (footprint a sz)
      (tuple.to_list (LittleEndian.split (bytes_per sz) (word.unsigned v)))
      m.
  Definition store(sz: access_size)(m: mem)(a: word)(v: word): option mem :=
    'Some _ <- load sz m a | None;
    unchecked_store sz m a v.

End Memory.
