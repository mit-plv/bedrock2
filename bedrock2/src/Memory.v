Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Coq.Lists.List.
Require Import coqutil.sanity.
Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList coqutil.Datatypes.List.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics coqutil.Datatypes.Option.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.LittleEndian.
Require Import bedrock2.Notations bedrock2.Syntax.

Open Scope Z_scope.

Section Memory.
  Context {byte: word 8} {width: Z} {word: word width} {mem: map.map word byte}.

  Definition footprint(a: word)(sz: nat): tuple word sz :=
    tuple.unfoldn (fun w => word.add w (word.of_Z 1)) sz a.

  Definition load_bytes(sz: nat)(m: mem)(addr: word): option (tuple byte sz) :=
    map.getmany_of_tuple m (footprint addr sz).

  Definition unchecked_store_bytes(sz: nat)(m: mem)(a: word)(bs: tuple byte sz): mem :=
    map.putmany_of_tuple (footprint a sz) bs m.

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

  Lemma load_None: forall sz m a,
      8 <= width ->
      map.get m a = None ->
      load sz m a = None.
  Proof.
    intros.
    destruct sz;
      try solve [
            cbv [load load_bytes map.getmany_of_tuple footprint
                 tuple.option_all tuple.map tuple.unfoldn bytes_per];
            rewrite H0; reflexivity].
    cbv [load load_bytes map.getmany_of_tuple footprint bytes_per].
    destruct (Z.to_nat ((width + 7) / 8)) eqn: E.
    - exfalso.
      assert (0 < (width + 7) / 8) as A. {
        apply Z.div_str_pos. lia.
      }
      change O with (Z.to_nat 0) in E.
      apply Z2Nat.inj in E; lia.
    - cbv [tuple.option_all tuple.map tuple.unfoldn].
      rewrite H0.
      reflexivity.
  Qed.

  Context {mem_ok: map.ok mem}.
  Context {word_eq_dec: DecidableEq word}.

  Lemma store_preserves_domain: forall sz m a v m',
      store sz m a v = Some m' ->
      forall k, map.get m k = None <-> map.get m' k = None.
  Proof.
    destruct sz;
      cbv [store store_bytes bytes_per load_bytes unchecked_store_bytes];
      intros;
      (destruct_one_match_hyp; [|discriminate]);
      inversion_option;
      (eapply map.putmany_of_tuple_preserves_domain; [|exact H]);
      intro A;
      rewrite A in E;
      discriminate E || let t := type of E in idtac t.
  Qed.

End Memory.
