Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.omega.Omega.
Require Import bbv.Word.
Require Import compiler.Decidable.
Require Import compiler.Tactics.
Require Import compiler.ListLib.


Section Memory.

  Variable w: nat. (* bit width of addresses and memory words *)

  Class Memory(M: Type) := mkMemory {
    isReadableAddr: M -> word w -> Prop; (* or bool? *)
    isWriteableAddr: M -> word w -> Prop;

    readMem: M -> word w -> option (word w);
    writeMem: M -> word w -> word w -> option M;

    readMem_succeeds: forall (m: M) (a: word w),
      isReadableAddr m a -> exists v, readMem m a = Some v;

    writeMem_succeeds: forall (m: M) (a v: word w),
      isWriteableAddr m a -> exists m', writeMem m a v = Some m';

    writeMem_preserves_isReadableAddr: forall (m: M) (a v: word w),
      match writeMem m a v with
      | Some m' => isReadableAddr m = isReadableAddr m'
      | None => True
      end;

    writeMem_preserves_isWriteableAddr: forall (m: M) (a v: word w),
      match writeMem m a v with
      | Some m' => isWriteableAddr m = isWriteableAddr m'
      | None => True
      end;

    readWriteMem_same: forall (m m': M) (a v v': word w),
      writeMem m a v = Some m' ->
      readMem m' a = Some v' ->
      v' = v;

    readWriteMem_diff: forall (m m': M) (a b v: word w),
      writeMem m a v = Some m' ->
      forall b, b <> a -> readMem m' b = readMem m b;
  }.

  (* TODO divide every address by 4? *)
  Instance ListIsMemory: Memory (list (word w)) := {|
    isReadableAddr := fun m a => wordToNat a < length m;
    isWriteableAddr := fun m a => wordToNat a < length m;
    readMem := fun m a => nth_error m (wordToNat a);
    writeMem := fun m a v => listUpdate_error m (wordToNat a) v
  |}.
  all: intros.
  - apply nth_error_Some in H. destruct (nth_error m # (a)); [eauto|contradiction].
  - unfold listUpdate_error. destruct_one_match; [eauto|contradiction].
  - unfold listUpdate_error. destruct (dec (# (a) < length m)); [|trivial].
    rewrite listUpdate_length by assumption.
    reflexivity.
  - destruct_one_match; [|trivial].
    apply listUpdate_error_length in E. rewrite E. reflexivity.
  - eauto using nth_error_listUpdate_error_same.
  - eapply nth_error_listUpdate_error_diff; [eassumption|].
    apply wordToNat_neq_inj. assumption.
  Defined.

    (*
    readable_dec: forall (m: M) (a: word w),
      {exists v, readMem m a = Some v} + {readMem m a = None};
      (* this fact trivially follows from option *)

    writeable_dec: forall (m: M) (a: word w),
      {forall v, exists m', writeMem m a v = Some m'} + {forall v, writeMem m a v = None};
      (* disallows discrimination based on the value being written *)

    writeMem_preserves_readable_dec: forall (m: M) (a v: word w),
      match writeMem m a v with
      | Some m' => readable_dec m = readable_dec m'
          (* type mismatch because lhs and rhs talk about different memories, would have to say
          "left <-> left, right <-> right" *)
      | None => True
      end;
     *)

    (*
    writeMem_spec: forall (a v: word w) (m m': M),
      let m' := writeMem m a v in
        forall b, readMem m' b = None <-> readMem m b = None /\
                  writeMem m' b = None <-> writeMem 
     *)

  (* Note: returning "option" (instead of returning a default and requiring the language semantics
     to check that the address is valid) simplifies the higher-level semantics, because they don't
     have to do any check. *)

  (* Or include memory as part of the "state" as in stateMap, and create type "location" which is
     variable (register) or memory address?
     No because don't focus too much on "extends" statement between states, in some optimizations
     or transformations, the low-level state might actually not extend the high-level state because
     some memory changes have been optimized away. *)

  (* Note: If we define writeMem as
       writeMem: M -> word w -> word w -> option M;
     then whether a location is writable could depend on the value being written (instead of only
     the address, and we'd need another spec to exclude that *)

End Memory.

