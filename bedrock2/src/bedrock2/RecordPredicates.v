From Coq Require Import ZArith.
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
      constr:(mk_inferred_size_predicate (pred (getter r)))
  end.

Ltac create_predicate fields :=
  lazymatch type of fields with
  | list (record_field_description ?R) =>
      lazymatch goal with
      | r: R |- @word.rep _ _ -> @map.rep _ _ _ -> Prop =>
          let res := map_with_ltac ltac:(infer_size r) fields in
          exact (sepapps res)
      end
  end.

#[export] Hint Extern 20 (PredicateSize ?p) =>
  let h := head p in
  (* seemingly superfluous match strips cast added by unfold *)
  lazymatch constr:(ltac:(unfold h; typeclasses eauto) : PredicateSize p) with
  | ?sz => exact sz
  end
: typeclass_instances.

(* Try if predicate size is value-independent *)
#[export] Hint Extern 2 (PredicateSize (fun _ => _)) =>
  lazymatch goal with
  | |- PredicateSize (fun v: ?T => ?body) =>
      lazymatch constr:(_ : forall v: T, PredicateSize body) with
      | (fun _ => ?sz_maybe_with_casts) =>
          lazymatch sz_maybe_with_casts with
          | ?sz => exact sz
          end
      end
  end
: typeclass_instances.

Notation "'record!' fields" := ltac:(create_predicate fields)
  (at level 10, only parsing).

(* The user can decide whether to put the array size between /**# #**/ or not.
   C compilers will not accept arbitrary Coq expressions in uncommented sizes,
   but we do not attempt to check that in Coq, because it seems that
   there is no way to distinguish whether the user wrote `3` or `(Zpos (xI xH))`. *)
Declare Custom Entry c_array_size.
Notation "x" := x (in custom c_array_size at level 2, x constr at level 0).
Notation "/* *# x #* */" := x (in custom c_array_size at level 2, x constr at level 100).

Declare Custom Entry c_type_as_predicate.
Notation "'uintptr_t'" := uintptr (in custom c_type_as_predicate).
Notation "'uint64_t'" := (uint 64) (in custom c_type_as_predicate).
Notation "'uint32_t'" := (uint 32) (in custom c_type_as_predicate).
Notation "'uint16_t'" := (uint 16) (in custom c_type_as_predicate).
Notation "'uint8_t'" := (uint 8) (in custom c_type_as_predicate).
Notation "'NOT_C!(' x )" := x (in custom c_type_as_predicate, x constr).

(*
C                 Separation Logic   Description
----------------- ------------------ -----------------------------------------------------
uintptr_t         uintptr            32 or 64 bit, value is of type word
uint8/16/32/64_t  uint 8/16/32/64    value is of type Z, and predicate ensures bounds on Z
size_t            uint 32/64         value is of type Z, and predicate ensures bounds on Z
*)
Ltac exact_uint_of_bitwidth :=
  let bw := constr:(_ : Bitwidth _) in
  lazymatch type of bw with
  | Bitwidth ?w => exact (uint w)
  end.
Notation "'size_t'" := (ltac:(exact_uint_of_bitwidth))
  (in custom c_type_as_predicate, only parsing).

Declare Custom Entry c_struct_field.
Declare Scope c_struct_field_scope.
Open Scope c_struct_field_scope.
Notation "'c_struct_field:(' x ')'" := x
  (at level 0, x custom c_struct_field at level 2, format "c_struct_field:( x )")
  : c_struct_field_scope.
Notation "pred fieldname ;" := (mk_record_field_description fieldname pred)
  (in custom c_struct_field at level 2,
   pred custom c_type_as_predicate at level 0,
   fieldname constr at level 0)
  : c_struct_field_scope.
Notation "pred fieldname [ sz ] ;" :=
  (mk_record_field_description fieldname (array pred sz))
  (in custom c_struct_field at level 2,
   pred custom c_type_as_predicate at level 0,
   fieldname constr at level 0,
   sz custom c_array_size at level 2)
  : c_struct_field_scope.

Declare Custom Entry c_struct_field_list.
Notation "'c_struct_field_list:(' x ')'" := x (x custom c_struct_field_list)
  : c_struct_field_scope.
Notation "{ x1 .. xN }" := (cons x1 .. (cons xN nil) ..)
  (in custom c_struct_field_list at level 2,
   x1 custom c_struct_field, xN custom c_struct_field).

Notation ".* */ 'typedef' 'struct' '__attribute__' '((__packed__))' fs name ; /* *" :=
  (match fs with (* <-- typechecking x before passing it to Ltac improves error messages *)
   | name => (* <-- name given to record in C is ignored by Coq *)
       ltac:(create_predicate fs)
   end)
  (at level 200, fs custom c_struct_field_list at level 2, only parsing).

Module Examples_TODO_move.

  Definition ARPOperationRequest: Z := 1.
  Definition ARPOperationReply: Z := 2.

  Record ARPPacket: Set := mkARPPacket {
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

  Record EthernetHeader: Set := mkEthernetHeader {
    dstMAC: list Z;
    srcMAC: list Z;
    etherType: Z;
  }.

  Record var_size_foo: Set := {
    foo_size: Z;
    foo_stuff: Z;
    foo_payload: list Z;
  }.

  Section WithMem.
    Local Open Scope Z_scope.
    Context {width: Z} {BW: Bitwidth width}
            {word: word.word width} {word_ok: word.ok word}
            {mem: map.map word Byte.byte} {mem_ok: map.ok mem}.

    Goal c_struct_field:(uint32_t foo_size;) =
         mk_record_field_description foo_size (uint 32).
    Proof. reflexivity. Abort.

    Goal forall l, c_struct_field:(uint16_t foo_payload[/**# Z.of_nat (S l) #**/];) =
             mk_record_field_description foo_payload (array (uint 16) (Z.of_nat (S l))).
    Proof. reflexivity. Abort.

    Goal c_struct_field:(uint16_t foo_payload[4];) =
         mk_record_field_description foo_payload (array (uint 16) 4).
    Proof. reflexivity. Abort.

    Goal forall r, c_struct_field_list:({
      uint32_t foo_size;
      uint32_t foo_stuff;
      uint32_t foo_payload[/**# foo_size r #**/];
    }) =
    (cons (mk_record_field_description foo_size (uint 32))
    (cons (mk_record_field_description foo_stuff (uint 32))
    (cons (mk_record_field_description foo_payload (array (uint 32) (foo_size r))) nil))).
    Proof. reflexivity. Abort.

    Definition var_size_foo_t(r: var_size_foo): word -> mem -> Prop := .**/
      typedef struct __attribute__ ((__packed__)) {
        uint32_t foo_size;
        uint32_t foo_stuff;
        uint8_t foo_payload[/**# foo_size r #**/];
      } var_size_foo_t;
    /**.

    Goal forall p, (_ : PredicateSize (var_size_foo_t p)) = 8 + (foo_size p * 1).
    Proof. intros. reflexivity. Abort.

    Definition ARPPacket_t(r: ARPPacket): word -> mem -> Prop := .**/
      typedef struct __attribute__ ((__packed__)) {
        uint16_t htype;
        uint16_t ptype;
        uint8_t hlen;
        uint8_t plen;
        uint16_t oper;
        uint8_t sha[6];
        uint8_t spa[4];
        uint8_t tha[6];
        uint8_t tpa[4];
      } ARPPacket_t;
    /**.

    Goal forall p, (_ : PredicateSize (ARPPacket_t p)) = 28.
    Proof. intros. reflexivity. Abort.

    Goal (_ : PredicateSize ARPPacket_t) = 28.
    Proof. reflexivity. Abort.

    Goal sizeof ARPPacket_t = 28.
    Proof. reflexivity. Abort.

    Definition EthernetHeader_t(r: EthernetHeader): word -> mem -> Prop := .**/
      typedef struct __attribute__ ((__packed__)) {
        uint8_t dstMAC[6];
        uint8_t srcMAC[6];
        uint16_t etherType;
      } EthernetHeader_t;
    /**.

    Goal forall p, (_ : PredicateSize (EthernetHeader_t p)) = 14.
    Proof. intros. reflexivity. Abort.

    (* not a Lemma because this kind of goal will be solved inline by sepcalls canceler *)
    Goal forall (bs: list Z) (R: mem -> Prop) a m (Rest: EthernetHeader -> Prop),
        sep (array (uint 8) 14 bs a) R m ->
        exists h, sep (EthernetHeader_t h a) R m /\ Rest h.
    Proof.
      intros.
      eexists (mkEthernetHeader _ _ _).
      unfold EthernetHeader_t.
      cbn.
    Abort.
  End WithMem.
End Examples_TODO_move.
