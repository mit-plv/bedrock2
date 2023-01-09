Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.RecordEta.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.SepLib.

(* Note: Not using a Section here because `Hint Extern` declared inside a Section cannot
   be exported) *)

Definition sepapp{width: Z}{BW: Bitwidth width}{word: word.word width}
  {mem: map.map word Byte.byte}
  (P1 P2: word -> mem -> Prop){P1size: PredicateSize P1}: word -> mem -> Prop :=
  fun addr => sep (P1 addr) (P2 (word.add addr (word.of_Z P1size))).

#[export] Hint Extern 1 (PredicateSize (sepapp ?P1 ?P2)) =>
  lazymatch constr:(_: PredicateSize P1) with
  | ?sz1 => lazymatch constr:(_: PredicateSize P2) with
            | ?sz2 => exact (Z.add sz1 sz2)
            end
  end
: typeclass_instances.

Definition RepPredicate{width: Z}{BW: Bitwidth width}{word: word.word width}
  {mem: map.map word Byte.byte}(T: Type) := T -> word -> mem -> Prop.
Existing Class RepPredicate.

#[export] Hint Extern 1 (RepPredicate (uint_t ?nbits)) =>
  exact (uint nbits) : typeclass_instances.

#[export] Hint Extern 1 (RepPredicate (array_t ?T ?n)) =>
  match constr:(_: RepPredicate T) with
  | ?elem => exact (array elem n)
  end
: typeclass_instances.

#[export] Hint Extern 1 (RepPredicate (@word.rep ?width ?word)) =>
  exact (@uintptr width _ word _) : typeclass_instances.

Goal forall width (BW: Bitwidth width) (word: word width) (mem: map.map word Byte.byte)
            (n: Z),
  RepPredicate (array_t word n).
  intros. typeclasses eauto.
Abort.

Ltac create_predicate_rec refine_already_introd :=
  lazymatch goal with
  | |- forall (lastField: ?T), ?wo -> ?mem -> Prop =>
      let f := fresh lastField in
      intro f;
      refine_already_introd;
      match constr:(_ : RepPredicate T) with
      | ?p => exact (p f)
      end
  | |- forall (name: ?T), _ =>
      let f := fresh name in
      intro f;
      match constr:(_ : RepPredicate T) with
      | ?p => create_predicate_rec ltac:(refine_already_introd; refine (sepapp (p f) _))
      end
  end.

(* Given a match expression of the form
   (match r with {| field1 := x1; ... fieldN := xn |} => body end),
   returns a proof that this expression equals
   body[field1 r/x1, ... fieldN r/xn] *)
Ltac replace_match_by_projections_proof m :=
  lazymatch m with
  | (match ?d with _ => _ end) =>
      let r := reconstruct_record d in
      constr:(ltac:(replace d with r at 1 by (destruct d; reflexivity); reflexivity)
               : m = _)
  end.

Ltac create_predicate :=
  let G := lazymatch goal with |- ?G => G end in
  let t := constr:(ltac:(
             let p := fresh in intro p; case p; create_predicate_rec idtac) : G) in
  lazymatch constr:(ltac:(
    let p := fresh in intro p;
    let m := eval cbv beta in (t p) in
    let pf := replace_match_by_projections_proof m in
    lazymatch type of pf with
    | m = ?m' => exact m'
    end))
  with ?x => exact x end.

#[export] Hint Extern 20 (PredicateSize ?p) =>
  let h := head p in unfold h; typeclasses eauto
: typeclass_instances.

Module Examples_TODO_move.

Definition MAC := array_t (uint_t 8) 6.
#[export] Hint Extern 1 (RepPredicate MAC) =>
   exact (array (uint 8) 6) : typeclass_instances.

Definition IPv4 := array_t (uint_t 8) 4.
#[export] Hint Extern 1 (RepPredicate IPv4) =>
  exact (array (uint 8) 4) : typeclass_instances.

Definition ARPOperationRequest: Z := 1.
Definition ARPOperationReply: Z := 2.

Record ARPPacket_t := mkARPPacket {
  htype: uint_t 16; (* hardware type *)
  ptype: uint_t 16; (* protocol type *)
  hlen: uint_t 8;   (* hardware address length (6 for MAC addresses) *)
  plen: uint_t 8;   (* protocol address length (4 for IPv4 addresses) *)
  oper: uint_t 16;
  sha: MAC;  (* sender hardware address *)
  spa: IPv4; (* sender protocol address *)
  tha: MAC;  (* target hardware address *)
  tpa: IPv4; (* target protocol address *)
}.

Record EthernetHeader_t := mkEthernetHeader {
  dstMAC: MAC;
  srcMAC: MAC;
  etherType: uint_t 16;
}.

Record var_size_foo_t := {
  foo_size: uint_t 32;
  foo_payload: array_t (uint_t 8) foo_size;
}.

Section WithMem.
  Local Open Scope Z_scope.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {word_ok: word.ok word}.
  Context {mem: map.map word Byte.byte} {mem_ok: map.ok mem}.

  Instance ARPPacket: RepPredicate ARPPacket_t :=
    ltac:(create_predicate).

  Goal forall p, (_ : PredicateSize (ARPPacket p)) = 28. intros. reflexivity. Abort.

  Instance EthernetHeader: RepPredicate EthernetHeader_t :=
    ltac:(create_predicate).

  Goal forall p, (_ : PredicateSize (EthernetHeader p)) = 14. intros. reflexivity. Abort.

  Instance var_size_foo: RepPredicate var_size_foo_t :=
    ltac:(create_predicate).

  Goal forall p, (_ : PredicateSize (var_size_foo p)) = 4 + foo_size p * 1.
  Proof. intros. reflexivity. Abort.

  (* not a Lemma because this kind of goal will be solved inline by sepcalls canceler *)
  Goal forall (bs: list (uint_t 8)) (R: mem -> Prop) a m (Rest: EthernetHeader_t -> Prop),
      sep (array (uint 8) 14 bs a) R m ->
      exists h, sep (EthernetHeader h a) R m /\ Rest h.
  Proof.
    intros.
    eexists (mkEthernetHeader _ _ _).
    unfold EthernetHeader.
    unfold sepapp.
  Abort.

End WithMem.
End Examples_TODO_move.
