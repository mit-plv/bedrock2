Require Import Coq.derive.Derive.
Require Import coqutil.Z.Lia.
Require coqutil.Word.BigEndian.
Require Import coqutil.Byte coqutil.Datatypes.HList.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Tactics.letexists coqutil.Tactics.Tactics coqutil.Tactics.rewr coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.rewr.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.FE310CSemantics.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Array.
Require Import bedrock2.ZnWords.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Require Import bedrock2.WeakestPrecondition bedrock2.ProgramLogic.
Require Import bedrock2.ZnWords.
Require Import coqutil.Word.SimplWordExpr.
Require Import bedrock2.footpr.

Definition TODO{T: Type}: T. Admitted.

Infix "^+" := word.add  (at level 50, left associativity).
Infix "^-" := word.sub  (at level 50, left associativity).
Infix "^*" := word.mul  (at level 40, left associativity).
Infix "^<<" := word.slu  (at level 37, left associativity).
Infix "^>>" := word.sru  (at level 37, left associativity).
Notation "/[ x ]" := (word.of_Z x)       (* squeeze a Z into a word (beat it with a / to make it smaller) *)
  (format "/[ x ]").
Notation "\[ x ]" := (word.unsigned x)   (* \ is the open (removed) lid of the modulo box imposed by words, *)
  (format "\[ x ]").                     (* let a word fly into the large Z space *)

Section WithParameters.
  Import Syntax BinInt String List.ListNotations ZArith.
  Context {word: word.word 32} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Local Set Implicit Arguments.
  Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
  Coercion Z.of_nat : nat >-> Z.
  Coercion byte.unsigned : byte >-> Z.
  Notation len := List.length.
  Notation "'bytetuple' sz" := (HList.tuple byte (@Memory.bytes_per 32 sz)) (at level 10).

  Add Ring wring : (Properties.word.ring_theory (word := word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := word)),
         constants [Properties.word_cst]).

  Implicit Types m : mem.

  (* TODO move (to Scalars.v?) *)
  Lemma load_bounded_Z_of_sep: forall sz addr (value: Z) R m,
      0 <= value < 2 ^ (Z.of_nat (bytes_per (width:=32) sz) * 8) ->
      sep (truncated_scalar sz addr value) R m ->
      Memory.load_Z sz m addr = Some value.
  Proof.
    intros.
    assert (List.length (LittleEndianList.le_split (bytes_per(width:=32) sz) value) = bytes_per(width:=32) sz) as pf
      by (rewrite LittleEndianList.length_le_split; trivial).
    unfold load_Z.
    unshelve erewrite load_bytes_of_sep; [|shelve|..]; destruct pf.
    1:eapply tuple.of_list.
    2:{ unfold truncated_scalar, littleendian, ptsto_bytes in *.
       rewrite tuple.to_list_of_list in *; eauto. }
    1:rewrite tuple.to_list_of_list, LittleEndianList.le_combine_split, Z.mod_small; trivial.
  Qed.

  Lemma load_of_sep_truncated_scalar: forall sz addr (value: Z) R m,
      0 <= value < 2 ^ (Z.of_nat (bytes_per (width:=32) sz) * 8) ->
      sep (truncated_scalar sz addr value) R m ->
      Memory.load sz m addr = Some (word.of_Z value).
  Proof.
    intros. unfold Memory.load.
    erewrite load_bounded_Z_of_sep by eassumption.
    reflexivity.
  Qed.

  Definition BEBytesToWord{n: nat}(bs: tuple byte n): word := word.of_Z (BigEndian.combine n bs).

  Definition byteToWord(b: byte): word := word.of_Z (byte.unsigned b).

  (* An n-byte unsigned little-endian number v at address a.
     Enforces that v fits into n bytes. *)
  Definition LEUnsigned(n: nat)(addr: word)(v: Z)(m: mem): Prop :=
    exists bs: tuple byte n, ptsto_bytes n addr bs m /\ v = LittleEndianList.le_combine (tuple.to_list bs).

  (* Enforces that v fits into (bytes_per sz) bytes.
     To be used as the one and only base-case separation logic assertion, because using
     load1/2/4/8 will convert the value it puts into the dst register to word anyways,
     so it makes sense to hardcode the type of v to be word. *)
  Definition value(sz: access_size)(addr v: word): mem -> Prop :=
    LEUnsigned (bytes_per (width:=32) sz) addr (word.unsigned v).

  Lemma load_of_sep_value: forall sz addr v R m,
      sep (value sz addr v) R m ->
      Memory.load sz m addr = Some v.
  Proof.
    unfold value, Memory.load, Memory.load_Z, LEUnsigned. intros.
    assert (exists bs : tuple Init.Byte.byte (bytes_per sz),
               sep (ptsto_bytes (bytes_per(width:=32) sz) addr bs) R m /\
               word.unsigned v = LittleEndianList.le_combine (tuple.to_list bs)) as A. {
      unfold sep in *.
      destruct H as (mp & mq & A & B & C).
      destruct B as (bs & B & E).
      eauto 10.
    }
    clear H. destruct A as (bs & A & E).
    erewrite load_bytes_of_sep by eassumption.
    eapply f_equal.
    setoid_rewrite <- E.
    rewrite word.of_Z_unsigned.
    reflexivity.
  Qed.

  Inductive TypeSpec: Type -> Type :=
  | TValue{R: Type}(sz: access_size)(encode: R -> word): TypeSpec R
  | TStruct{R: Type}(fields: list (FieldSpec R)): TypeSpec R
  (* dynamic number of elements: *)
  | TArray{E: Type}(elemSize: Z)(elemSpec: TypeSpec E): TypeSpec (list E)
  (* number of elements statically known: *)
  | TTuple{E: Type}(count: nat)(elemSize: Z)(elemSpec: TypeSpec E): TypeSpec (tuple E count)
  with FieldSpec: Type -> Type :=
  | FField{R F: Type}(getter: R -> F)(setter: R -> F -> R)(fieldSpec: TypeSpec F)
    : FieldSpec R.

  Fixpoint TypeSpec_size{R: Type}(sp: TypeSpec R): R -> Z :=
    match sp with
    | TValue sz _ => fun r => bytes_per (width:=32) sz
    | TStruct fields => fun r => List.fold_right (fun f res => FieldSpec_size f r + res) 0 fields
    | TArray elemSize _ => fun l => List.length l * elemSize
    | TTuple n elemSize _ => fun t => n * elemSize
    end
  with FieldSpec_size{R: Type}(f: FieldSpec R): R -> Z :=
    match f with
    | FField getter setter sp => fun r => TypeSpec_size sp (getter r)
    end.

  (* sum of the sizes of the first i fields *)
  Definition offset{R: Type}(r: R)(fields: list (FieldSpec R))(i: nat): Z :=
    List.fold_right (fun f res => FieldSpec_size f r + res) 0 (List.firstn i fields).

  Section dataAt_recursion_helpers.
    Context (dataAt: forall {R: Type}, TypeSpec R -> word -> R -> mem -> Prop).

    Definition fieldAt{R: Type}(f: FieldSpec R)(i: nat): list (FieldSpec R) -> word -> R -> mem -> Prop :=
      match f with
      | FField getter setter sp => fun fields base r => dataAt sp (base ^+ /[offset r fields i]) (getter r)
      end.

    Definition fieldsAt{R: Type}(fields: list (FieldSpec R))(start: word)(r: R): list (mem -> Prop) :=
      List.map_with_index (fun f i => fieldAt f i fields start r) fields.

    Definition arrayAt{E: Type}(elemSize: Z)(elem: TypeSpec E)(start: word): list E -> list (mem -> Prop) :=
      List.map_with_index (fun e i => dataAt elem (start ^+ /[i * elemSize]) e).
  End dataAt_recursion_helpers.

  Fixpoint dataAt{R: Type}(sp: TypeSpec R){struct sp}: word -> R -> mem -> Prop :=
    match sp with
    | TValue sz encoder => fun addr r => value sz addr (encoder r)
    | @TStruct R fields => fun base r => seps (fieldsAt (@dataAt) fields base r)
    | @TArray E elemSize elem => fun base l => seps (arrayAt (@dataAt) elemSize elem base l)
    | @TTuple E n elemSize elem => fun base t => seps (arrayAt (@dataAt) elemSize elem base (tuple.to_list t))
    end.

  (* ** Packet Formats *)

  Definition EtherTypeARP := [Byte.x08; Byte.x06].
  Definition EtherTypeIPv4 := [Byte.x08; Byte.x00].

  Definition ETHERTYPE_IPV4_LE: Z :=
    Eval compute in (LittleEndianList.le_combine EtherTypeIPv4).

  Definition ETHERTYPE_ARP_LE: Z :=
    Eval compute in (LittleEndianList.le_combine EtherTypeARP).

  Definition MAC := tuple byte 6.

  Definition encodeMAC: MAC -> list byte := tuple.to_list.

  Definition IPv4 := tuple byte 4.

  Definition encodeIPv4: IPv4 -> list byte := tuple.to_list.

  Definition encodeCRC(crc: Z): list byte := tuple.to_list (BigEndian.split 4 crc).

  Record EthernetPacket(Payload: Type) := mkEthernetARPPacket {
    dstMAC: MAC;
    srcMAC: MAC;
    etherType: tuple byte 2; (* <-- must initially accept all possible two-byte values *)
    payload: Payload;
  }.

  Definition byte_spec: TypeSpec byte := TValue access_size.one byteToWord.

  Definition EthernetPacket_spec{Payload: Type}(Payload_spec: TypeSpec Payload) := TStruct [
    FField (@dstMAC Payload) TODO (TTuple 6 1 byte_spec);
    FField (@srcMAC Payload) TODO (TTuple 6 1 byte_spec);
    FField (@etherType Payload) TODO (TValue access_size.two (@BEBytesToWord 2));
    FField (@payload Payload) TODO Payload_spec
  ].

  (* Note: At the moment we want to allow any padding and crc, so we use an isXxx predicate rather
     than an encodeXxx function *)
  Definition isEthernetPacket{P: Type}(payloadOk: P -> list byte -> Prop)(p: EthernetPacket P)(bs: list byte) :=
    exists data padding crc,
      bs = encodeMAC p.(srcMAC) ++ encodeMAC p.(dstMAC) ++ tuple.to_list p.(etherType)
           ++ data ++ padding ++ encodeCRC crc /\
      payloadOk p.(payload) data /\
      46 <= Z.of_nat (List.length (data ++ padding)) <= 1500.
      (* TODO could/should also verify CRC *)

  Definition ARPOperationRequest := Byte.x01.
  Definition ARPOperationReply := Byte.x02.

  Record ARPPacket := mkARPPacket {
    htype: tuple byte 2; (* hardware type *)
    ptype: tuple byte 2; (* protocol type *)
    hlen: byte;          (* hardware address length (6 for MAC addresses) *)
    plen: byte;          (* protocol address length (4 for IPv4 addresses) *)
    oper: byte;
    sha: MAC;  (* sender hardware address *)
    spa: IPv4; (* sender protocol address *)
    tha: MAC;  (* target hardware address *)
    tpa: IPv4; (* target protocol address *)
  }.

  Definition ARPPacket_spec: TypeSpec ARPPacket := TStruct [
    FField htype TODO (TValue access_size.two (@BEBytesToWord 2));
    FField ptype TODO (TValue access_size.two (@BEBytesToWord 2));
    FField hlen TODO byte_spec;
    FField plen TODO byte_spec;
    FField oper TODO byte_spec;
    FField sha TODO (TTuple 6 1 byte_spec);
    FField spa TODO (TTuple 4 1 byte_spec);
    FField tha TODO (TTuple 6 1 byte_spec);
    FField tpa TODO (TTuple 4 1 byte_spec)
  ].

  Definition encodeARPPacket(p: ARPPacket): list byte :=
    tuple.to_list p.(htype) ++
    tuple.to_list p.(ptype) ++
    [p.(hlen)] ++ [p.(plen)] ++ [p.(oper)] ++
    encodeMAC p.(sha) ++ encodeIPv4 p.(spa) ++ encodeMAC p.(tha) ++ encodeIPv4 p.(tpa).

  Definition HTYPE := tuple.of_list [Byte.x00; Byte.x01].
  Definition PTYPE := tuple.of_list [Byte.x80; Byte.x00].
  Definition HLEN := Byte.x06.
  Definition PLEN := Byte.x04.
  Definition OPER_REQUEST := Byte.x01.
  Definition OPER_REPLY := Byte.x02.

  Definition HTYPE_LE := 0x0100.
  Definition PTYPE_LE := 0x0080.

  Definition isEthernetARPPacket: EthernetPacket ARPPacket -> list byte -> Prop :=
    isEthernetPacket (fun arpP => eq (encodeARPPacket arpP)).

  Record ARPConfig := mkARPConfig {
    myMAC: MAC;
    myIPv4: IPv4;
  }.

  Context (cfg: ARPConfig).

  (* high-level protocol definition (does not mention lists of bytes) *)

  Definition needsARPReply(req: EthernetPacket ARPPacket): Prop :=
    req.(etherType) = tuple.of_list EtherTypeARP /\
    req.(payload).(oper) = ARPOperationRequest /\
    req.(payload).(tpa) = cfg.(myIPv4). (* <-- we only reply to requests asking for our own MAC *)

  Definition ARPReply(req: EthernetPacket ARPPacket): EthernetPacket ARPPacket :=
    {| dstMAC := req.(payload).(sha);
       srcMAC := cfg.(myMAC);
       etherType := tuple.of_list EtherTypeARP;
       payload := {|
         htype := HTYPE;
         ptype := PTYPE;
         hlen := HLEN;
         plen := PLEN;
         oper := ARPOperationReply;
         sha := cfg.(myMAC); (* <-- the actual reply *)
         spa := cfg.(myIPv4);
         tha := req.(payload).(sha);
         tpa := req.(payload).(spa)
       |}
    |}.

  (* not sure if we need this definition, or just inline it *)
  Definition ARPReqResp(req resp: EthernetPacket ARPPacket): Prop :=
    needsARPReply req /\ resp = ARPReply req.

  Definition addr_in_range(a start: word)(len: Z): Prop :=
    word.unsigned (word.sub a start) <= len.

  Definition subrange(start1: word)(len1: Z)(start2: word)(len2: Z): Prop :=
    0 <= len1 <= len2 /\ addr_in_range start1 start2 (len2-len1).

  Notation "a ,+ m 'c=' b ,+ n" := (subrange a m b n)
    (no associativity, at level 10, m at level 1, b at level 1, n at level 1,
     format "a ,+ m  'c='  b ,+ n").

  Record dummy_packet := {
    dummy_src: tuple byte 4;
 (* if we want dependent field types (instead of just dependent field lengths), we also need
    to figure out how to set/update such fields...
    dummy_dst_kind: bool;
    dummy_dst: if dummy_dst_kind then tuple byte 4 else tuple byte 6;
    *)
    dummy_dst: tuple byte 4;
    dummy_len: Z;
    dummy_data: list byte;
    dummy_padding: list byte (* non-constant offset *)
  }.

  Definition set_dummy_src d x :=
    Build_dummy_packet x (dummy_dst d) (dummy_len d) (dummy_data d) (dummy_padding d).
  Definition set_dummy_dst d x :=
    Build_dummy_packet (dummy_src d) x (dummy_len d) (dummy_data d) (dummy_padding d).
  Definition set_dummy_len d x :=
    Build_dummy_packet (dummy_src d) (dummy_dst d) x (dummy_data d) (dummy_padding d).
  Definition set_dummy_data d x :=
    Build_dummy_packet (dummy_src d) (dummy_dst d) (dummy_len d) x (dummy_padding d).
  Definition set_dummy_padding d x :=
    Build_dummy_packet (dummy_src d) (dummy_dst d) (dummy_len d) (dummy_data d) x.

  Definition dummy_spec: TypeSpec dummy_packet := TStruct [
    FField dummy_src set_dummy_src (TValue access_size.four (@BEBytesToWord 4));
    FField dummy_dst set_dummy_dst (TValue access_size.four (@BEBytesToWord 4));
    FField dummy_len set_dummy_len (TValue access_size.two word.of_Z);
    FField dummy_data set_dummy_data (TArray 1 (TValue access_size.one byteToWord));
    FField dummy_padding set_dummy_padding (TArray 1 (TValue access_size.one byteToWord))
  ].

  Record foo := {
    foo_count: Z;
    foo_packet: dummy_packet;
    foo_packets: list dummy_packet;
  }.
  Definition set_foo_count f x :=
    Build_foo x (foo_packet f) (foo_packets f).
  Definition set_foo_packet f x :=
    Build_foo (foo_count f) x (foo_packets f).
  Definition set_foo_packets f x :=
    Build_foo (foo_count f) (foo_packet f) x.

  Definition foo_spec: TypeSpec foo := TStruct [
    FField foo_count set_foo_count (TValue access_size.four word.of_Z);
    FField foo_packet set_foo_packet dummy_spec;
    FField foo_packets set_foo_packets (TArray 256 dummy_spec)
  ].

  (*
  (* `path R F` is a path digging into a record of type R, leading to a field of type F.
  Note: "reversed" (snoc direction rather than cons) so that we can append easily to the right to dig deeper. *)
  Inductive path: Type -> Type -> Type :=
  | PNil(R: Type): path R R
  | PField{R S F: Type}(prefix: path R S)(getter: S -> F): path R F
  | PIndex{R E: Type}(prefix: path R (list E))(i: Z): path R E.

  Fixpoint path_value{R F: Type}(pth: path R F){struct pth}: R -> option F :=
    match pth as p in (path R F) return (R -> option F) with
    | PNil R => Some
    | PField prefix getter => fun r => match path_value prefix r with
                                       | Some x => Some (getter x)
                                       | None => None
                                       end
    | PIndex prefix i => fun r => match path_value prefix r with
                                  | Some l => List.nth_error l (Z.to_nat i)
                                  | None => None
                                 end
    end.

  Inductive path_TypeSpec: forall {R F: Type}, TypeSpec R -> path R F -> TypeSpec F -> Prop :=
  | path_TypeSpec_Nil: forall R (sp: TypeSpec R),
      path_TypeSpec sp (PNil R) sp
  | path_TypeSpec_Field: forall R S F (prefix: path R S) (getter: S -> F) setter fields i sp sp',
      path_TypeSpec sp prefix (TStruct fields) ->
      List.nth_error fields i = Some (FField getter setter sp') ->
      path_TypeSpec sp (PField prefix getter) sp'
  | path_TypeSpec_Index: forall R E (sp: TypeSpec R) len prefix i (sp': TypeSpec E),
      path_TypeSpec sp prefix (TArray len sp') ->
      (* note: no bounds check here yet... *)
      path_TypeSpec sp (PIndex prefix i) sp'.
  *)

  (* append-at-front direction (for constructing a path using backwards reasoning) *)
  Inductive lookup_path:
    (* input: start type, end type, *)
    forall {R F: Type},
    (* type spec, base address, and whole value found at empty path *)
    TypeSpec R -> word -> R ->
    (* output: type spec, address and value found at given path *)
    TypeSpec F -> word -> F -> Prop :=
  | lookup_path_Nil: forall R (sp: TypeSpec R) addr addr' r,
      addr = addr' ->
      lookup_path sp addr r
                  sp addr' r
  | lookup_path_Field: forall R F R' (getter: R -> F) setter fields i sp sp' addr addr' (r: R) (r': R'),
      List.nth_error fields i = Some (FField getter setter sp) ->
      lookup_path sp (addr ^+ /[offset r fields i]) (getter r)
                  sp' addr' r' ->
      lookup_path (TStruct fields) addr r
                  sp' addr' r'
  | lookup_path_Index: forall R E (sp: TypeSpec R) r' len i (sp': TypeSpec E) l e addr addr',
      List.nth_error l i = Some e ->
      lookup_path sp (addr ^+ /[i * len]) e
                  sp' addr' r' ->
      lookup_path (TArray len sp) addr l
                  sp' addr' r'.

  (* append-at-end alternative (for constructing a path using forward reasoning)
  Inductive lookup_path:
    (* input: start type, end type, *)
    forall {R F: Type},
    (* type spec, base address, and whole value found at empty path *)
    TypeSpec R -> word -> R ->
    (* output: type spec, address and value found at given path *)
    TypeSpec F -> word -> F -> Prop :=
  | lookup_path_Nil: forall R (sp: TypeSpec R) addr r,
      lookup_path sp addr r
                  sp addr r
  | lookup_path_Field: forall R S F (getter: S -> F) setter fields i sp sp' addr addr' (r: R) r',
      lookup_path sp addr r
                  (TStruct fields) addr' r' ->
      List.nth_error fields i = Some (FField getter setter sp') ->
      lookup_path sp addr r
                  sp' (addr' ^+ /[offset r' fields i]) (getter r')
  | lookup_path_Index: forall R E (sp: TypeSpec R) r len i (sp': TypeSpec E) l e addr addr',
      lookup_path sp addr r
                  (TArray len sp') addr' l ->
      List.nth_error l i = Some e ->
      lookup_path sp addr r
                  sp' (addr' ^+ /[i * len]) e. *)

  Ltac assert_lookup_range_feasible :=
    match goal with
    | |- lookup_path ?sp ?addr ?v ?sp' ?addr' ?v' =>
      let range_start := eval cbn -[Z.add] in addr in
      let range_size := eval cbn -[Z.add] in (TypeSpec_size sp v) in
      let target_start := addr' in
      let target_size := eval cbn -[Z.add] in (TypeSpec_size sp' v') in
      assert (target_start,+target_size c= range_start,+range_size)
    end.

  Ltac check_lookup_range_feasible :=
    assert_succeeds (assert_lookup_range_feasible; [solve [unfold subrange, addr_in_range; ZnWords]|]).

  Axiom ZnWords_needs_lia_of_Coq_master: False.

  Goal forall base f R m,
      seps [dataAt foo_spec base f; R] m ->
      exists V (v: V) encoder,
        lookup_path foo_spec base f
                    (TValue access_size.two encoder) (base ^+ /[12]) v.
  Proof.
    intros.

    Check f.(foo_packet).(dummy_len).
    do 3 eexists.

    (*Eval simpl in (path_value (PField (PField (PNil _) foo_packet) dummy_len) f).*)

    (* t = load2(base ^+ /[4] ^+ /[8])
       The range `(base+12),+2` corresponds to the field `f.(foo_packet).(dummy_len)`.
       Goal: use lia to find this path. *)
    set (target_start := (base ^+ /[12])).
    set (target_size := 2%Z).

    (* backward reasoning: *)

    (* check that path is still good *)
    match goal with
    | |- lookup_path ?sp ?addr ?v _ _ _ =>
      pose (range_start := addr); cbn -[Z.add] in range_start;
      pose (range_size := (TypeSpec_size sp v)); cbn -[Z.add] in range_size
    end.
    assert (target_start,+target_size c= range_start,+range_size) as T. {
      unfold subrange, addr_in_range. case ZnWords_needs_lia_of_Coq_master.
    }
    clear range_start range_size T.

    eapply lookup_path_Field with (i := 1%nat); [reflexivity|]. (* <-- i picked by backtracking *)
    cbn.

    (* check that path is still good *)
    check_lookup_range_feasible.

    eapply lookup_path_Field with (i := 2%nat); [reflexivity|]. (* <-- i picked by backtracking *)
    cbn.

    (* check that path is still good *)
    check_lookup_range_feasible.

    eapply lookup_path_Nil.
    ZnWords.
  Qed.

  (* mappings between expr for offset and semantic offset (word/Z)?

fieldEncoder providing both?

node:
leftPtr: word
value: word
rightPtr: word

additional accessors:
leftChild: dereferences leftPtr, = load(offset of leftPtr)

padding: = offset of previous field + load(offset of length field)

but what if I already loaded the length before? Don't load again
weird mix between high-level and low-level

access to fields should also be possible by constructing the offset expression manually,
and have lia figure out where it lands inside the record

Given:
Gallina datatype, its getters, its setters, and its layout in memory
A load to some address => Find its symbolic value in the Gallina datatype
A store at some address => update the Gallina datatype in the sep clause

"some address" might be constructed manually (eg using a for loop that increases a pointer instead of a[i], or a+previously_loaded_dynamic_offset) or using some syntactic sugar to denote offsets for record field access, sugar to be defined later.

What about unions/sum types/Gallina inductives with more than one constructor?
getters/setters returning option?
But how to know which case?


VST: fieldAt t addr path value
     dataAt t addr value := fieldAt t addr nil value

address <--> accessor   mappings bidirectional

address --> accessor                        (invert by testing for each accessor if address matches??)
accessor --> expr --denote-->address        (only needed for syntactic sugar)

given address & access size, look at address range covered by sep clauses and drill down

can we even do many dereferences, eg l->tail->tail->head?

given a sep clause, get its footprint and its subparts
if not in footprint, try next sep clause, else try each subpart

footprint = union of ranges

allow abstract footprints, eg if we don't know whether l->tail is cons or nil, we don't know a range for it


ll a v := match v with
          | nil => a = null
          | cons h t => exists a', a |-> h /\ a+4 |-> a' /\ ll a' t
          end

footprint (ll a v) := match v with
                      | nil => {}
                      | cons h t => a,+8 \u footprint (ll *(a+4) t)
                      end

Will be hard to say for sure that something is *not* in the footprint of a clause, but that's fine,
we only need to say that something *is* in the footprint

Not only need 1,2,4,8 byte access, but also access to whole structs to pass them to other functions

range tree with increasing subdivision granularity?
*)

  Inductive footpr :=
  | FPRange(start len: Z)
  | FPUnion(l r: footpr).


(* or reuse compiler.SeparationLogic.footpr ?
   "very semantic"


a \in (footpr P) -> "load a" can be resolved by looking only at P

how to obtain `a \in (footpr P)` from lia hypotheses?
Using helper lemmas for each separation logic predicate, eg:

addr <= a < addr + sz * length l ->
a \in (footpr (array elem sz addr l))

addr <= a < addr + 4 or 8 ->
a \in (footpr (ptsto_word addr v))

addr <= a < addr + 8 \/ a in footpr of tail ->
a \in (footpr (ll addr l))

Or rather: subsets of footpr because we load/store/pass to function more than just 1 byte

subrange a,+sz1 addr,+(sz2*length l) ->
subset a,+sz1 (footpr (array elem sz2 addr l))


can we not derive this from the basic ptsto?
tricky as soon as recursion appears
human insight helpful to merge adjacent blocks


(getter, setter, predicate)


use
{p |-> {| foo := a; bar := b |} * R}
f(p.bar)
{p |-> {| foo := a; bar := symbolic_f(b) |} * R}

def
{p |-> x * R}
f(p)
{p |-> symbolic_f(x) * R}

or allow non-det functions:

use
{p |-> {| foo := a; bar := b |} * R}
f(p.bar)
{p |-> {| foo := a; bar := b' |} * R} /\ rel b b'

def
{p |-> x * R}
f(p)
exists x', {p |-> x' * R} /\ rel x x'


myRecordAt p {| foo := a; bar := b |} := p |-> a * (p+12) |-> b
[
  (foo, with_foo, fun r base => base |-> foo r);
  (bar; with_bar, fun r base => (base+12) |- bar r)
]

frame rule for function call where frame refers to a nested record with a hole?
C[x] built from setters?

C[x] := with_dummy (with_bar (dummy original) x) original

back to just loading:

{base |-> {| f1 := x; f2 := y; dummy := {| foo := a; bar := b |} |} * R /\ p = base + 12}
t = load4(p)
{... /\ t = b}

*)


  (* ** Program logic rules *)

  Context {ext_spec: ExtSpec}.
  (* We have two rules for conditionals depending on whether there are more commands afterwards *)

  Lemma if_split: forall e c b thn els t m l mc post,
      dexpr m l c b ->
      (word.unsigned b <> 0 -> exec e thn t m l mc post) ->
      (word.unsigned b =  0 -> exec e els t m l mc post) ->
    exec e (cmd.cond c thn els) t m l mc post.
  Admitted.

  Lemma if_merge: forall e t m l mc c thn els rest b Q1 Q2 post,
      dexpr m l c b ->
      (word.unsigned b <> 0 -> exec e thn t m l mc Q1) ->
      (word.unsigned b = 0  -> exec e els t m l mc Q2) ->
      (forall t' m' l' mc', word.unsigned b <> 0 /\ Q1 t' m' l' mc' \/
                            word.unsigned b = 0  /\ Q2 t' m' l' mc' ->
                            exec e rest t' m' l' mc' post) ->
      exec e (cmd.seq (cmd.cond c thn els) rest) t m l mc post.
  Admitted.

  Lemma assignment: forall e x a t m l mc rest post,
      WeakestPrecondition.expr m l a
        (fun v => forall mc, exec e rest t m (map.put l x v) mc post) ->
      exec e (cmd.seq (cmd.set x a) rest) t m l mc post.
  Admitted.

  Implicit Type post: trace -> mem -> locals -> MetricLogging.MetricLog -> Prop.

  Definition wand(P Q: mem -> Prop)(m: mem): Prop :=
    forall m1 m2, map.split m2 m m1 -> P m1 -> Q m2.

  (* an "existential" version of wand, also called the dual of wand, or septraction [Bannister et al, ITP'18].
     Roughly, P is a subheap of Q, and 'Q without P' holds on m *)
  Definition dwand(P Q: mem -> Prop)(m: mem): Prop :=
    exists m1 m2, map.split m2 m m1 /\ P m1 /\ Q m2.

  Lemma wand_adjoint: forall P Q R,
      impl1 (sep P Q) R <-> impl1 P (wand Q R).
  Proof.
    unfold impl1, wand, sep. clear. firstorder eauto.
  Qed.

  Lemma wand_self_impl: forall (P: mem -> Prop),
      unique_footprint P ->
      non_contrad P ->
      iff1 (emp True) (wand P P).
  Proof.
    intros P U N.
    unfold emp, wand, iff1. intros. split; intros.
    - destruct H. destruct H0. subst. rewrite map.putmany_empty_l. assumption.
    - split; [|trivial]. unfold unique_footprint, non_contrad in *.
      destruct N as [mn N].
      assert (P x \/ ~ P x) as EM by admit . destruct EM as [A | A].
      + (*

      assert (P map.empty \/ ~ P map.empty) as EM by admit . destruct EM as [A | A].
      + specialize (U m1 map.empty N A). assert (m1 = map.empty) by admit.
      *)
  Abort.

  Lemma wand_self_impl: forall (P: mem -> Prop),
      iff1 (fun _ => True) (wand P P).
  Proof.
    unfold emp, wand, iff1, map.split. intros. split; intros.
    - destruct H. destruct H0. subst.
  Abort.

(*
It seems that in linear SL, `P -* P` is *not* equivalent to `fun m => True`:
When trying to prove `P -* P`, I need to show that if `P` holds on some heap `m`, no matter what disjoint heap `m1` I add, `P` will still hold on the combined heap, but if `P` restricts the domain of the heap to one fixed set, that won't hold.
So maybe `P -* P` is equivalent to `emp`? No, because from `P -* P`, `emp` only follows if `P` is required to have a unique footprint.


*)

  Lemma dwand_self_impl: forall (P: mem -> Prop),
      iff1 P (dwand P P).
  Proof.
    intros.
    unfold emp, dwand, iff1. split; intros.
    - exists map.empty, x.
  Abort.

  Lemma dwand_self_impl: forall (P: mem -> Prop),
      unique_footprint P ->
      non_contrad P ->
      iff1 (emp True) (dwand P P).
  Proof.
    intros P U N.
    unfold emp, dwand, iff1. split; intros.
    - destruct H. subst. unfold non_contrad in N. destruct N as (mn & N).
      exists mn, mn. rewrite map.split_empty_l. auto.
    - destruct H as (m1 & m2 & H & p1 & p2).
      split; [|trivial].
      unfold unique_footprint in U.
      specialize U with (1 := p1) (2 := p2).
      apply map.map_ext.
      intro k. destruct (map.get x k) eqn: E. 2: {
        rewrite map.get_empty. reflexivity.
      }
      exfalso.
      unfold map.split, map.disjoint in H. destruct H as [? H]. subst m2.
      destruct (map.get m1 k) eqn: F. 1: solve[eauto].
      destruct U as [U1 U2]. unfold map.sub_domain in *.
      specialize (U2 k b). rewrite map.get_putmany_dec in U2. rewrite F in U2.
      specialize (U2 E). destruct U2. discriminate.
  Qed.

  Lemma sep_dwand_self_impl: forall (R P: mem -> Prop) m,
      R m ->
      sep R (dwand P P) m.
  Proof.
    intros. unfold sep, dwand.
    exists m, map.empty. rewrite map.split_empty_r. repeat split; auto.
  Abort.

  Goal forall P Q,
      iff1 Q (sep P (dwand P Q)).
  Proof.
  Abort.
  (* Note: this one only holds if P "is part of" Q and satisfiable,
     and we will use lookup_path below to assert that *)
  Goal forall P Q, iff1 Q (sep P (wand P Q)).
  Abort.

  Lemma seps_nth_error_to_head: forall i Ps (P : mem -> Prop),
      List.nth_error Ps i = Some P ->
      iff1 (seps Ps) (sep P (seps (app (firstn i Ps) (tl (skipn i Ps))))).
  Proof.
    intros.
    etransitivity.
    - symmetry. eapply seps_nth_to_head.
    - eapply List.nth_error_to_hd_skipn in H. rewrite H. reflexivity.
  Qed.

  Lemma expose_lookup_path: forall R F sp base (r: R) sp' addr (v: F),
      lookup_path sp base r sp' addr v ->
      exists Frame, iff1 (dataAt sp base r) (sep (dataAt sp' addr v) Frame).
  Proof.
    induction 1.
    - subst. exists (emp True). cancel.
    - destruct IHlookup_path as [Frame IH]. simpl in IH.
      eexists.
      cbn.
      unfold fieldsAt at 1.
      eapply List.map_with_index_nth_error in H.
      rewrite seps_nth_error_to_head. 2: exact H.
      unfold fieldAt at 1.
      rewrite IH.
      ecancel.
    - destruct IHlookup_path as [Frame IH]. simpl in IH.
      eexists.
      cbn.
      unfold arrayAt at 1.
      eapply List.map_with_index_nth_error in H.
      rewrite seps_nth_error_to_head. 2: exact H.
      rewrite IH.
      ecancel.
  Qed.

  Lemma load_field: forall sz m addr M i R sp (r: R) base (F: Type) encoder (v: F),
      seps M m ->
      List.nth_error M i = Some (dataAt sp base r) ->
      lookup_path sp base r (TValue sz encoder) addr v ->
      Memory.load sz m addr = Some (encoder v).
  Proof.
    intros.
    destruct (expose_lookup_path H1) as (Frame & P).
    simpl in P.
    eapply seps_nth_error_to_head in H0.
    eapply H0 in H.
    seprewrite_in P H.
    eapply load_of_sep_value.
    ecancel_assumption.
  Qed.

  (* optimized for easy backtracking *)
  Lemma load_field': forall sz m addr M R sp (r: R) base (F: Type) encoder (v: F),
      seps M m ->
      (exists i,
          List.nth_error M i = Some (dataAt sp base r) /\
          lookup_path sp base r (TValue sz encoder) addr v) ->
      Memory.load sz m addr = Some (encoder v).
  Proof.
    intros. destruct H0 as (i & ? & ?). eauto using load_field.
  Qed.

  Lemma load_field'': forall sz m addr R sp (r: R) base (F: Type) encoder (v: F) (post: word -> Prop),
      (exists M,
        seps M m /\
        exists i,
          List.nth_error M i = Some (dataAt sp base r) /\
          lookup_path sp base r (TValue sz encoder) addr v /\
          post (encoder v)) ->
      WeakestPrecondition.load sz m addr post.
  Proof.
    intros. unfold WeakestPrecondition.load. decompose [ex and] H. eauto using load_field.
  Qed.

  Definition vc_func e '(innames, outnames, body) (t: trace) (m: mem) (argvs: list word)
                     (post : trace -> mem -> list word -> Prop) :=
    exists l, map.of_list_zip innames argvs = Some l /\ forall mc,
      exec e body t m l mc (fun t' m' l' mc' =>
        exists retvs : list word, map.getmany_of_list l' outnames = Some retvs /\ post t' m' retvs).

  Fixpoint firstn_as_tuple{A: Type}(default: A)(n: nat)(l: list A): tuple A n :=
    match n as n return tuple A n with
    | O => tt
    | S m => PrimitivePair.pair.mk (List.hd default l) (firstn_as_tuple default m (List.tl l))
    end.

  Lemma to_list_firstn_as_tuple: forall A (default: A) n (l: list A),
      (n <= List.length l)%nat ->
      tuple.to_list (firstn_as_tuple default n l) = List.firstn n l.
  Proof.
    induction n; intros.
    - reflexivity.
    - destruct l. 1: cbv in H; exfalso; blia.
      simpl in *.
      f_equal. eapply IHn. blia.
  Qed.

  Lemma to_list_BigEndian_split: forall n (l: list byte),
      (n <= List.length l)%nat ->
      tuple.to_list (BigEndian.split n (BigEndian.combine n (firstn_as_tuple Byte.x00 n l))) = List.firstn n l.
  Proof.
    intros. rewrite BigEndian.split_combine.
    apply to_list_firstn_as_tuple.
    assumption.
  Qed.

  Lemma list_eq_cancel_step{A: Type}: forall (xs ys l: list A),
    List.firstn (List.length xs) l = xs ->
    List.skipn (List.length xs) l = ys ->
    l = xs ++ ys.
  Proof.
    intros. remember (List.length xs) as n. subst xs ys. symmetry. apply List.firstn_skipn.
  Qed.

  Lemma list_eq_cancel_firstn: forall A (l rest: list A) n,
      (n <= List.length l)%nat ->
      List.skipn n l = rest ->
      l = List.firstn n l ++ rest.
  Proof. intros. subst rest. symmetry. apply List.firstn_skipn. Qed.

  Ltac length_getEq t :=
    match t with
    | context[List.length (tuple.to_list ?xs)] => constr:(tuple.length_to_list xs)
    | context[List.length (?xs ++ ?ys)] => constr:(List.app_length xs ys)
    | context[List.length (?x :: ?xs)] => constr:(List.length_cons x xs)
    | context[List.length (@nil ?A)] => constr:(@List.length_nil A)
    | context[List.skipn ?n (List.skipn ?m ?xs)] => constr:(List.skipn_skipn n m xs)
    | context[List.length (List.skipn ?n ?l)] => constr:(List.skipn_length n l)
    end.

  Lemma list_instantiate_evar{A: Type}: forall l1 l2 l3 (xs1 xs3 evar lhs rhs: list A),
      (* reshape rhs: *)
      rhs = xs1 ++ evar ++ xs3 ->
      (* equations for lengths l1, l2, l3 *)
      l1 = List.length xs1 ->
      l2 = (List.length lhs - l1 - l3)%nat ->
      l3 = List.length xs3 ->
      (* sidecondition on lengths *)
      (l1 + l3 <= List.length lhs)%nat ->
      (* equations for lists xs1, evar, xs3 *)
      xs1 = List.firstn l1 lhs ->
      evar = List.firstn (List.length lhs - l1 - l3) (List.skipn l1 lhs) ->
      xs3 = List.skipn (List.length lhs - l3) lhs ->
      lhs = rhs.
  Proof.
    intros. subst xs1 xs3 evar. subst rhs.
    apply list_eq_cancel_step. {
      f_equal. symmetry. assumption.
    }
    apply list_eq_cancel_step. {
      rewrite <- H0. f_equal. rewrite List.length_firstn_inbounds. 1: reflexivity.
      rewrite List.length_skipn.
      blia.
    }
    rewr length_getEq in |-*.
    f_equal.
    rewrite List.length_firstn_inbounds.
    1: blia.
    rewrite List.length_skipn.
    blia.
  Qed.

  Lemma instantiate_tuple_from_list{A: Type}: forall (n: nat) (evar: tuple A n) (l: list A) (default: A),
      n = Datatypes.length l ->
      evar = firstn_as_tuple default n l ->
      tuple.to_list evar = l.
  Proof.
    intros. subst.
    rewrite to_list_firstn_as_tuple. 2: reflexivity.
    apply List.firstn_all2. reflexivity.
  Qed.

  Ltac list_eq_cancel_step :=
    apply list_eq_cancel_step;
    (* can't use normal rewrite because COQBUG https://github.com/coq/coq/issues/10848 *)
    rewr length_getEq in |-*.

  Lemma interpretEthernetARPPacket: forall bs,
      Z.of_nat (List.length bs) = 64 ->
      (* conditions collected while trying to prove the lemma: *)
      List.firstn 2 (List.skipn 12 bs) = [Byte.x08; Byte.x06] ->
      List.firstn 6 (List.skipn 14 bs) = [Byte.x00; Byte.x01; Byte.x80; Byte.x00; Byte.x06; Byte.x04] ->
      List.firstn 1 (List.skipn 20 bs) = [Byte.x01] -> (* we only interpret requests at the moment, no replies *)
      exists packet: EthernetPacket ARPPacket, isEthernetARPPacket packet bs.
  Proof.
    intros.
    unfold isEthernetARPPacket, isEthernetPacket, encodeARPPacket, encodeMAC, encodeIPv4, encodeCRC.
    eexists ({| payload := {| oper := _ |} |}).
    cbn [dstMAC srcMAC etherType payload htype ptype hlen plen oper sha spa tha tpa].
    repeat eexists.
    (* can't use normal rewrite because COQBUG https://github.com/coq/coq/issues/10848 *)
    all: rewr (fun t => match t with
           | context [ List.length (?xs ++ ?ys) ] => constr:(List.app_length xs ys)
           | context [ List.length (?h :: ?t) ] => constr:(List.length_cons h t)
           | context [ (?xs ++ ?ys) ++ ?zs ] => constr:(eq_sym (List.app_assoc xs ys zs))
           end) in |-*.
    {
      list_eq_cancel_step. {
        symmetry. apply to_list_firstn_as_tuple with (default := Byte.x00). ZnWords.
      }
      list_eq_cancel_step. {
        symmetry. apply to_list_firstn_as_tuple with (default := Byte.x00). ZnWordsL.
      }
      list_eq_cancel_step. {
        instantiate (1 := tuple.of_list EtherTypeARP).
        assumption.
      }
  Abort. (*
      list_eq_cancel_step. {
        assumption.
      }
      list_eq_cancel_step. {
        instantiate (1 := ARPOperationRequest).
        assumption.
      }
      list_eq_cancel_step. {
        symmetry. apply to_list_firstn_as_tuple with (default := Byte.x00). ZnWords.
      }
      list_eq_cancel_step. {
        symmetry. apply to_list_firstn_as_tuple with (default := Byte.x00). ZnWords.
      }
      list_eq_cancel_step. {
        symmetry. apply to_list_firstn_as_tuple with (default := Byte.x00). ZnWords.
      }
      list_eq_cancel_step. {
        symmetry. apply to_list_firstn_as_tuple with (default := Byte.x00). ZnWords.
      }
      cbn -[List.skipn tuple.to_list].
      eapply list_instantiate_evar with (xs1 := nil). {
        cbn [List.app].
        f_equal.
      }
      { cbn [List.length]. reflexivity. }
      { reflexivity. }
      { reflexivity. }
      { rewrite tuple.length_to_list. rewrite List.length_skipn. blia. }
      { reflexivity. }
      { (* finally, we can "automatically" instantiate the evar ?padding *)
        reflexivity.  }
      rewr length_getEq in |-*.
      rewrite BigEndian.split_combine.
      etransitivity. 2: apply tuple.to_list_of_list.
      match goal with
      | |- @tuple.to_list _ ?n1 _ = @tuple.to_list _ ?n2 _ =>
        replace n2 with n1 by (rewr length_getEq in |-*; blia)
      end.
      eapply instantiate_tuple_from_list with (default := Byte.x00). 2: reflexivity.
      rewr length_getEq in |-*.
      blia.
    }
    {
      rewr length_getEq in |-*.
      rewrite List.firstn_length.
      rewr length_getEq in |-*.
      blia.
    }
    {
      rewr length_getEq in |-*.
      rewrite List.firstn_length.
      rewr length_getEq in |-*.
      blia.
    }
  Qed. *)

  Lemma bytesToEthernetARPPacket: forall a bs,
      64 = len bs ->
      exists p: EthernetPacket ARPPacket,
        iff1 (array ptsto /[1] a bs) (dataAt (EthernetPacket_spec ARPPacket_spec) a p).
  Proof.
    intros.
    eexists {| payload := {| oper := _ |} |}. cbn.
    (* TODO messy *)
  Admitted.

Inductive snippet :=
| SSet(x: string)(e: expr)
| SIf(cond: expr)(merge: bool)
| SEnd
| SElse.

Inductive note_wrapper: string -> Type := mkNote(s: string): note_wrapper s.
Notation "s" := (note_wrapper s) (at level 200, only printing).
Ltac add_note s := let n := fresh "Note" in pose proof (mkNote s) as n; move n at top.

(* backtrackingly tries all nats strictly smaller than n *)
Ltac pick_nat n :=
  multimatch n with
  | S ?m => constr:(m)
  | S ?m => pick_nat m
  end.

Ltac add_snippet s :=
  lazymatch s with
(*
  | SSet ?y (expr.load ?SZ ?A) =>
    eapply load_stmt with (x := y) (a := A) (sz := SZ);
    [ solve [repeat straightline]
    | once (match goal with
            (* backtrack over choice of Hm in case there are several *)
            | Hm: seps ?lm ?m |- exists l, seps l ?m /\ _ =>
              exists lm; split; [exact Hm|];
              let n := eval cbv [List.length] in (List.length lm) in
              (* backtrack over choice of i *)
              let i := pick_nat n in
              eexists i, _, _; split; [cbv [List.nth_error]; reflexivity|];
              split; [unfold bytes_per, subrange, addr_in_range; ZnWords|]
            end) ]
*)
  | SSet ?y ?e => eapply assignment with (x := y) (a := e)
  | SIf ?cond false => eapply if_split with (c := cond); [| |add_note "'else' expected"]
  | SEnd => eapply exec.skip
  | SElse => lazymatch goal with
             | H: note_wrapper "'else' expected" |- _ => clear H
             end
  end.


Ltac ring_simplify_hyp_rec t H :=
  lazymatch t with
  | ?a = ?b => ring_simplify_hyp_rec a H || ring_simplify_hyp_rec b H
  | word.unsigned ?a => ring_simplify_hyp_rec a H
  | word.of_Z ?a => ring_simplify_hyp_rec a H
  | _ => progress ring_simplify t in H
  end.

Ltac ring_simplify_hyp H :=
  let t := type of H in ring_simplify_hyp_rec t H.

Ltac simpli_getEq t :=
  match t with
  | context[@word.and ?wi ?wo (if ?b1 then _ else _) (if ?b2 then _ else _)] =>
    constr:(@word.and_bool_to_word wi wo _ b1 b2)
  | context[@word.unsigned ?wi ?wo (word.of_Z ?x)] => constr:(@word.unsigned_of_Z_nowrap wi wo _ x)
  | context[@word.of_Z ?wi ?wo (word.unsigned ?x)] => constr:(@word.of_Z_unsigned wi wo _ x)
  end.

(* random simplifications *)
Ltac simpli :=
  repeat ((rewr simpli_getEq in *  by ZnWords) ||
         match goal with
         | H: word.unsigned (if ?b then _ else _) = 0 |- _ => apply word.if_zero in H
         | H: word.unsigned (if ?b then _ else _) <> 0 |- _ => apply word.if_nonzero in H
         | H: word.eqb ?x ?y = true  |- _ => apply (word.eqb_true  x y) in H
         | H: word.eqb ?x ?y = false |- _ => apply (word.eqb_false x y) in H
         | H: andb ?b1 ?b2 = true |- _ => apply (Bool.andb_true_iff b1 b2) in H
         | H: andb ?b1 ?b2 = false |- _ => apply (Bool.andb_false_iff b1 b2) in H
         | H: orb ?b1 ?b2 = true |- _ => apply (Bool.orb_true_iff b1 b2) in H
         | H: orb ?b1 ?b2 = false |- _ => apply (Bool.orb_false_iff b1 b2) in H
         | H: ?x = word.of_Z ?y |- _ => match isZcst y with
                                        | true => subst x
                                        end
         | x := word.of_Z ?y |- _ => match isZcst y with
                                     | true => subst x
                                     end
         | H: word.of_Z ?x = word.of_Z ?y |- _ =>
           assert (x = y) by (apply (word.of_Z_inj_small H); ZnWords); clear H
         | H: _ |- _ => ring_simplify_hyp H
         | H: ?T |- _ => clear H; assert_succeeds (assert T by ZnWords)
         end);
  simpl (bytes_per _) in *;
  simpl_Z_nat.

Ltac straightline_cleanup ::=
  match goal with
  | x : @Word.Interface.word.rep _ _ |- _ => clear x
  | x : Init.Byte.byte |- _ => clear x
  | x : Semantics.trace |- _ => clear x
  | x : Syntax.cmd |- _ => clear x
  | x : Syntax.expr |- _ => clear x
  | x : coqutil.Map.Interface.map.rep |- _ => clear x
  | x : BinNums.Z |- _ => clear x
  | x : unit |- _ => clear x
  | x : bool |- _ => clear x
  | x : list _ |- _ => clear x
  | x : nat |- _ => clear x
  | x := _ : @Word.Interface.word.rep _ _ |- _ => clear x
  | x := _ : Init.Byte.byte |- _ => clear x
  | x := _ : Semantics.trace |- _ => clear x
  | x := _ : Syntax.cmd |- _ => clear x
  | x := _ : Syntax.expr |- _ => clear x
  | x := _ : coqutil.Map.Interface.map.rep |- _ => clear x
  | x := _ : BinNums.Z |- _ => clear x
  | x := _ : unit |- _ => clear x
  | x := _ : bool |- _ => clear x
  | x := _ : list _ |- _ => clear x
  | x := _ : nat |- _ => clear x
  | |- forall _, _ => intros
  | |- let _ := _ in _ => intros
  | |- dlet.dlet ?v (fun x => ?P) => change (let x := v in P); intros
  | _ => progress (cbn [Semantics.interp_binop] in * )
  | H: exists _, _ |- _ => destruct H
(*| H: _ /\ _ |- _ => destruct H *)
  | H: _ /\ _ |- _ => lazymatch type of H with
                      | _ <  _ <  _ => fail
                      | _ <  _ <= _ => fail
                      | _ <= _ <  _ => fail
                      | _ <= _ <= _ => fail
                      | _ => destruct H
                      end
  | x := ?y |- ?G => is_var y; subst x
  | H: ?x = ?y |- _ => constr_eq x y; clear H
  (*
  | H: ?x = ?y |- _ => is_var x; is_var y; assert_fails (idtac; let __ := eval cbv [x] in x in idtac); subst x
  | H: ?x = ?y |- _ => is_var x; is_var y; assert_fails (idtac; let __ := eval cbv [y] in y in idtac); subst y
  | H: ?x = ?v |- _ =>
    is_var x;
    lazymatch v with context[x] => fail | _ => idtac end;
    let x' := fresh x in
    rename x into x';
    simple refine (let x := v in _);
    change (x' = x) in H;
    symmetry in H;
    destruct H
  *)
  end.

Ltac after_snippet := repeat (straightline || simpli).
(* For debugging, this can be useful:
Ltac after_snippet ::= idtac.
*)


  Hint Resolve EthernetPacket_spec: TypeSpec_instances.
  Hint Resolve ARPPacket_spec: TypeSpec_instances.

  Goal TypeSpec (EthernetPacket ARPPacket). eauto 2 with TypeSpec_instances. all: fail. Abort.

  Ltac index_of_getter getter fields :=
    lazymatch fields with
    | FField getter _ _ :: _ => constr:(O)
    | FField _ _ _ :: ?tail => let r := index_of_getter getter tail in constr:(S r)
    end.

  Ltac offset_of_getter getter :=
    lazymatch type of getter with
    | ?R -> ?F =>
      let sp := constr:(ltac:(eauto 2 with TypeSpec_instances) : TypeSpec R) in
      lazymatch eval hnf in sp with
      | TStruct ?fields =>
        let i := index_of_getter getter fields in
        lazymatch eval cbn in (fun r: R => offset r fields i) with
        (* value-dependent offsets are not supported here *)
        | fun _ => ?x => x
        end
      end
    end.

  Goal False.
    let ofs := offset_of_getter (@dstMAC ARPPacket) in idtac ofs.
    let ofs := offset_of_getter (@srcMAC ARPPacket) in idtac ofs.
    let ofs := offset_of_getter (@etherType ARPPacket) in idtac ofs.
    let ofs := offset_of_getter (@payload ARPPacket) in idtac ofs.
    let ofs := offset_of_getter plen in idtac ofs.
    let ofs := offset_of_getter spa in idtac ofs.
  Abort.

Tactic Notation "$" constr(s) "$" := add_snippet s; after_snippet.

Notation "/*number*/ e" := e (in custom bedrock_expr at level 0, e constr at level 0).

Notation "base @ getter" :=
  (expr.op bopname.add base (expr.literal ltac:(let ofs := offset_of_getter getter in exact ofs)))
  (in custom bedrock_expr at level 6, left associativity, only parsing,
   base custom bedrock_expr, getter constr).

Declare Custom Entry snippet.

Notation "*/ s /*" := s (s custom snippet at level 100).
Notation "x = e ;" := (SSet x e) (in custom snippet at level 0, x ident, e custom bedrock_expr).
Notation "'if' ( e ) '/*merge*/' {" := (SIf e true) (in custom snippet at level 0, e custom bedrock_expr).
Notation "'if' ( e ) '/*split*/' {" := (SIf e false) (in custom snippet at level 0, e custom bedrock_expr).
Notation "}" := SEnd (in custom snippet at level 0).
Notation "'else' {" := SElse (in custom snippet at level 0).

  Let nth n xs := hd (emp (map:=mem) True) (skipn n xs).
  Let remove_nth n (xs : list (mem -> Prop)) :=
    (firstn n xs ++ tl (skipn n xs)).

  (* TODO also needs to produce equivalence proof *)
  Ltac move_evar_to_head l :=
    match l with
    | ?h :: ?t =>
      let __ := match constr:(Set) with _ => is_evar h end in
      constr:(l)
    | ?h :: ?t =>
      let r := move_evar_to_head t in
      match r with
      | ?h' :: ?t' => constr:(h' :: h :: t)
      end
    end.

  Goal forall (a b c d: nat),
      exists e1 e2, [a; b; e1; c; d; e2] = nil.
  Proof.
    intros. eexists. eexists.
    match goal with
    | |- ?LHS = _ => let r := move_evar_to_head LHS in idtac r
    end.
  Abort.

  (* `Cancelable ?R LHS RHS P` means that if `P` holds, then `?R * LHS <-> RHS` *)
  Inductive Cancelable: (mem -> Prop) -> list (mem -> Prop) -> list (mem -> Prop) -> Prop -> Prop :=
  | cancel_done: forall R R' (P: Prop),
      R = seps R' -> P -> Cancelable R nil R' P
  | cancel_at_indices: forall i j R LHS RHS P,
      Cancelable R (remove_nth i LHS) (remove_nth j RHS) (nth i LHS = nth j RHS /\ P) ->
      Cancelable R LHS RHS P.

  Lemma Cancelable_to_iff1: forall R LHS RHS P,
      Cancelable R LHS RHS P ->
      Lift1Prop.iff1 (sep R (seps LHS)) R /\ P.
  Abort.

  Lemma cancel_array_at_indices{T}: forall i j xs ys P elem sz addr1 addr2 (content: list T),
      (* these two equalities are provable right now, where we still have evars, whereas the
         equation that we push into the conjunction needs to be deferred until all the canceling
         is done and the evars are instantiated [not sure if that's true...] *)
      nth i xs = array elem sz addr1 content ->
      nth j ys = array elem sz addr2 content ->
      Lift1Prop.iff1 (seps (remove_nth i xs)) (seps (remove_nth j ys)) /\
      (addr1 = addr2 /\ P) ->
      Lift1Prop.iff1 (seps xs) (seps ys) /\ P.
  Abort.

  Definition nFields{A: Type}(sp: TypeSpec A): option nat :=
    match sp with
    | TStruct fields => Some (List.length fields)
    | _ => None
    end.

  Ltac lookup_field_step := once (
    let n := lazymatch goal with
    | |- lookup_path ?sp ?base ?r _ _ _ =>
      let l := eval cbv in (nFields sp) in
      lazymatch l with
      | Some ?n => n
      end
    end in
    let j := pick_nat n in
    eapply lookup_path_Field with (i := j); [reflexivity|]; cbn;
    check_lookup_range_feasible).

  Ltac lookup_done :=
    eapply lookup_path_Nil; ZnWords.

Import WeakestPrecondition.
Ltac straightline ::=
  match goal with
  | _ => straightline_cleanup
  | |- @list_map _ _ (get _) _ _ => unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | |- @list_map _ _ (expr _ _) _ _ => unfold1_list_map_goal; cbv beta match delta [list_map_body]
  | |- @list_map _ _ _ nil _ => cbv beta match fix delta [list_map list_map_body]
  | |- expr _ _ _ _ => unfold1_expr_goal; cbv beta match delta [expr_body]
  | |- dexpr _ _ _ _ => cbv beta delta [dexpr]
  | |- dexprs _ _ _ _ => cbv beta delta [dexprs]
  | |- literal _ _ => cbv beta delta [literal]
  | |- get _ _ _ => cbv beta delta [get]
  | |- load _ _ _ _ => eapply load_field'';
       once (match goal with
             (* backtrack over choice of Hm in case there are several *)
             | Hm: seps ?lm ?m |- exists l, seps l ?m /\ _ =>
               exists lm; split; [exact Hm|];
               let n := eval cbv [List.length] in (List.length lm) in
                   (* backtrack over choice of i *)
                   let i := pick_nat n in
                   eexists i; split; [cbv [List.nth_error]; reflexivity|];
                   split; [ repeat (lookup_done || lookup_field_step) |]
             end)
  | |- @eq (@coqutil.Map.Interface.map.rep String.string Interface.word.rep _) _ _ =>
    eapply SortedList.eq_value; exact eq_refl
  | |- @map.get String.string Interface.word.rep ?M ?m ?k = Some ?e' =>
    let e := rdelta e' in
    is_evar e;
    once (let v := multimatch goal with x := context[@map.put _ _ M _ k ?v] |- _ => v end in
          (* cbv is slower than this, cbv with whitelist would have an enormous whitelist, cbv delta for map is slower than this, generalize unrelated then cbv is slower than this, generalize then vm_compute is slower than this, lazy is as slow as this: *)
          unify e v; exact (eq_refl (Some v)))
  | |- @coqutil.Map.Interface.map.get String.string Interface.word.rep _ _ _ = Some ?v =>
    let v' := rdelta v in is_evar v'; (change v with v'); exact eq_refl
  | |- ?x = ?y =>
    let y := rdelta y in is_evar y; change (x=y); exact eq_refl
  | |- ?x = ?y =>
    let x := rdelta x in is_evar x; change (x=y); exact eq_refl
  | |- ?x = ?y =>
    let x := rdelta x in let y := rdelta y in constr_eq x y; exact eq_refl
  | |- exists l', Interface.map.of_list_zip ?ks ?vs = Some l' /\ _ =>
    letexists; split; [exact eq_refl|] (* TODO: less unification here? *)
  | |- exists l', Interface.map.putmany_of_list_zip ?ks ?vs ?l = Some l' /\ _ =>
    letexists; split; [exact eq_refl|] (* TODO: less unification here? *)
  | |- exists x, ?P /\ ?Q =>
    let x := fresh x in refine (let x := _ in ex_intro (fun x => P /\ Q) x _);
                        split; [solve [repeat straightline]|]
(*
  | |- exists x, Markers.split (?P /\ ?Q) =>
    let x := fresh x in refine (let x := _ in ex_intro (fun x => P /\ Q) x _);
                        split; [solve [repeat straightline]|]
  | |- Markers.unique (exists x, Markers.split (?P /\ ?Q)) =>
    let x := fresh x in refine (let x := _ in ex_intro (fun x => P /\ Q) x _);
                        split; [solve [repeat straightline]|]
  | |- Markers.split ?G => change G; split
*)
  | |- True => exact I
  | |- False \/ _ => right
  | |- _ \/ False => left
(*
  | |- BinInt.Z.modulo ?z (Memory.bytes_per_word Semantics.width) = BinInt.Z0 /\ _ =>
      lazymatch Coq.setoid_ring.InitialRing.isZcst z with
      | true => split; [exact eq_refl|]
      end
  | |- _ => straightline_stackalloc
  | |- _ => straightline_stackdealloc
*)
  end.

Set Default Goal Selector "1".
Import Syntax.

  Definition arp: (string * {f: list string * list string * cmd &
    forall e t m ethbufAddr ethBufData L R,
      seps [array ptsto (word.of_Z 1) ethbufAddr ethBufData; R] m ->
      word.unsigned L = Z.of_nat (List.length ethBufData) ->
      vc_func e f t m [ethbufAddr; L] (fun t' m' retvs =>
        t' = t /\ (
        (* Success: *)
        (retvs = [word.of_Z 1] /\ exists request response ethBufData',
           seps [array ptsto (word.of_Z 1) ethbufAddr ethBufData'; R] m' /\
           isEthernetARPPacket request  ethBufData  /\
           isEthernetARPPacket response ethBufData' /\
           ARPReqResp request response) \/
        (* Failure: *)
        (retvs = [word.of_Z 0] /\ seps [array ptsto (word.of_Z 1) ethbufAddr ethBufData; R] m' /\ (
           L <> word.of_Z 64 \/
           (* malformed request *)
           (~ exists request, isEthernetARPPacket request ethBufData) \/
           (* request needs no reply because it's not for us *)
           (forall request, isEthernetARPPacket request ethBufData -> request.(payload).(tpa) <> cfg.(myIPv4))))
      ))}).
    pose "ethbuf" as ethbuf. pose "ln" as ln. pose "doReply" as doReply. pose "tmp" as tmp.
    refine ("arp", existT _ ([ethbuf; ln], [doReply], _) _).
    intros. cbv [vc_func]. letexists. split. 1: subst l; reflexivity. intros.

    $*/
    doReply = /*number*/0; /*$. $*/
    if (ln == /*number*/64) /*split*/ {
      /*$. edestruct (bytesToEthernetARPPacket ethbufAddr _ H0) as (pk & A). seprewrite_in A H.
           change (seps [dataAt (EthernetPacket_spec ARPPacket_spec) ethbufAddr pk; R] m) in H.
           case ZnWords_needs_lia_of_Coq_master. (*
$*/
      if ((load2(ethbuf @ (@etherType ARPPacket)) == ETHERTYPE_ARP_LE) &
          (load2(ethbuf @ (@payload ARPPacket) @ htype) == HTYPE_LE) &
          (load2(ethbuf @ (@payload ARPPacket) @ ptype) == PTYPE_LE) &
          (load1(ethbuf @ (@payload ARPPacket) @ hlen) == HLEN) &
          (load1(ethbuf @ (@payload ARPPacket) @ plen) == PLEN) &
          (load1(ethbuf @ (@payload ARPPacket) @ oper) == OPER_REQUEST)) /*split*/ { /*$.

      idtac.

      exact TODO.
*)
      (* TODO *) $*/
    else { /*$. (* nothing to do *) $*/
    } /*$.
      eexists.
      split. 1: reflexivity.
      split. 1: reflexivity.
      right.
      split. 1: reflexivity.
      exact TODO.
    Unshelve.
    all: try exact (word.of_Z 0).
    all: try exact nil.
    all: try (exact (fun _ => False)).
    all: try exact TODO.
  Defined.

  Goal False.
    let r := eval unfold arp in match arp with
                                | (fname, existT _ (argnames, retnames, body) _) => body
                                end
      in pose r.
  Abort.

End WithParameters.
