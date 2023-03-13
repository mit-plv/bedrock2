Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.SepLib.
Require Export bedrock2.sepapp.

Inductive record_field_description{width: Z}{BW: Bitwidth width}{word: word.word width}
  {mem: map.map word Byte.byte}(R: Type): Type :=
| mk_record_field_description(F: Type)(getter: R -> F)(pred: F -> word -> mem -> Prop).

Arguments mk_record_field_description{width}{BW}{word}{mem}{R}{F}.

(* Given a record_field_description for some type R and a variable r of type R,
   looks up the size of that record field (might depend on r) using typeclass search,
   and returns it as a sized_predicate *)
Ltac infer_size r descr :=
  lazymatch descr with
  | mk_record_field_description ?getter ?pred =>
      constr:(mk_sized_predicate (pred (getter r)) _)
  end.

Ltac create_predicate fields :=
  lazymatch goal with
  | r: _ |- @word.rep _ _ -> @map.rep _ _ _ -> Prop =>
      let res := map_with_ltac ltac:(infer_size r) fields in
      exact (sepapps res)
  end.

#[export] Hint Extern 20 (PredicateSize ?p) =>
  let h := head p in unfold h; typeclasses eauto
: typeclass_instances.

(* TODO replace by a notation that looks like C struct definitions *)
Notation "'record!' fields" := ltac:(create_predicate fields)
  (at level 10, only parsing).

Module Examples_TODO_move.

  Definition ARPOperationRequest: Z := 1.
  Definition ARPOperationReply: Z := 2.

  Record ARPPacket_t := mkARPPacket {
    htype: Z; (* hardware type *)
    ptype: Z; (* protocol type *)
    hlen: Z;  (* hardware address length (6 for MAC addresses) *)
    plen: Z;  (* protocol address length (4 for IPv4 addresses) *)
    oper: Z;
    sha: list Z; (* sender hardware address *)
    spa: list Z; (* sender protocol address *)
    tha: list Z; (* target hardware address *)
    tpa: list Z; (* target protocol address *)
  }.

  Record EthernetHeader_t := mkEthernetHeader {
    dstMAC: list Z;
    srcMAC: list Z;
    etherType: Z;
  }.

  Record var_size_foo_t := {
    foo_size: Z;
    foo_stuff: Z;
    foo_payload: list Z;
    foo_trailer: Z;
  }.

  Section WithMem.
    Local Open Scope Z_scope.
    Context {width: Z} {BW: Bitwidth width} {word: word.word width} {word_ok: word.ok word}.
    Context {mem: map.map word Byte.byte} {mem_ok: map.ok mem}.

    Definition ARPPacket(r: ARPPacket_t): word -> mem -> Prop := record!
      (cons (mk_record_field_description htype (uint 16))
      (cons (mk_record_field_description ptype (uint 16))
      (cons (mk_record_field_description hlen (uint 8))
      (cons (mk_record_field_description plen (uint 8))
      (cons (mk_record_field_description oper (uint 16))
      (cons (mk_record_field_description sha (array (uint 8) 6))
      (cons (mk_record_field_description spa (array (uint 8) 4))
      (cons (mk_record_field_description tha (array (uint 8) 6))
      (cons (mk_record_field_description tpa (array (uint 8) 4)) nil))))))))).

    Goal forall p, (_ : PredicateSize (ARPPacket p)) = 28. intros. reflexivity. Abort.

    Definition EthernetHeader(r: EthernetHeader_t): word -> mem -> Prop := record!
      (cons (mk_record_field_description dstMAC (array (uint 8) 6))
      (cons (mk_record_field_description srcMAC (array (uint 8) 6))
      (cons (mk_record_field_description etherType (uint 16)) nil))).

    Goal forall p, (_ : PredicateSize (EthernetHeader p)) = 14. intros. reflexivity. Abort.

    Definition var_size_foo(r: var_size_foo_t): word -> mem -> Prop := record!
      (cons (mk_record_field_description foo_size (uint 32))
      (cons (mk_record_field_description foo_stuff (uint 16))
      (cons (mk_record_field_description foo_payload (array (uint 8) (foo_size r)))
      (cons (mk_record_field_description foo_trailer (uint 16)) nil)))).

    Goal forall p, (_ : PredicateSize (var_size_foo p)) = 6 + (foo_size p * 1 + 2).
    Proof. intros. reflexivity. Abort.

    (* not a Lemma because this kind of goal will be solved inline by sepcalls canceler *)
    Goal forall (bs: list Z) (R: mem -> Prop) a m (Rest: EthernetHeader_t -> Prop),
        sep (array (uint 8) 14 bs a) R m ->
        exists h, sep (EthernetHeader h a) R m /\ Rest h.
    Proof.
      intros.
      eexists (mkEthernetHeader _ _ _).
      unfold EthernetHeader.
      cbn.
    Abort.
  End WithMem.
End Examples_TODO_move.
