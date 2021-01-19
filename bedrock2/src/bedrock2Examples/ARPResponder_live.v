Require Import Coq.derive.Derive.
Require Import coqutil.Z.Lia.
Require coqutil.Word.BigEndian.
Require Import coqutil.Byte coqutil.Datatypes.HList.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Tactics.letexists coqutil.Tactics.Tactics coqutil.Tactics.rewr.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.NotationsCustomEntry coqutil.Z.HexNotation.
Require Import bedrock2.FE310CSemantics.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Array.
Require Import bedrock2.ZnWords.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Require Import bedrock2.WeakestPrecondition bedrock2.ProgramLogic.
Require Import bedrock2.ZnWords.
Require Import bedrock2.SimplWordExpr.
Require Import bedrock2.footpr.

(* TODO put into coqutil and also use in lightbulb.v *)
Module word. Section WithWord.
  Import ZArith.
  Local Open Scope Z_scope.
  Context {width} {word: word.word width} {ok : word.ok word}.
  Lemma unsigned_of_Z_nowrap x:
    0 <= x < 2 ^ width -> word.unsigned (word.of_Z x) = x.
  Proof.
    intros. rewrite word.unsigned_of_Z. unfold word.wrap. rewrite Z.mod_small; trivial.
  Qed.
  Lemma of_Z_inj_small{x y}:
    word.of_Z x = word.of_Z y -> 0 <= x < 2 ^ width -> 0 <= y < 2 ^ width -> x = y.
  Proof.
    intros. apply (f_equal word.unsigned) in H. rewrite ?word.unsigned_of_Z in H.
    unfold word.wrap in H. rewrite ?Z.mod_small in H by assumption. assumption.
  Qed.
End WithWord. End word.

Module List.
  Import List.ListNotations. Open Scope list_scope.
  Section MapWithIndex.
    Context {A B: Type} (f: A -> nat -> B).
    Fixpoint map_with_start_index(start: nat)(l: list A): list B :=
      match l with
      | nil => nil
      | h :: t => f h start :: map_with_start_index (S start) t
      end.
    Definition map_with_index: list A -> list B := map_with_start_index O.

    Lemma map_with_start_index_app: forall l l' start,
        map_with_start_index start (l ++ l') =
        map_with_start_index start l ++ map_with_start_index (start + List.length l) l'.
    Proof.
      induction l; intros.
      - simpl. rewrite PeanoNat.Nat.add_0_r. reflexivity.
      - simpl. f_equal. rewrite IHl. f_equal. f_equal. Lia.lia.
    Qed.

    Lemma map_with_index_app: forall l l',
        map_with_index (l ++ l') = map_with_index l ++ map_with_start_index (List.length l) l'.
    Proof. intros. apply map_with_start_index_app. Qed.

    Lemma map_with_start_index_cons: forall a l start,
        map_with_start_index start (a :: l) = f a start :: map_with_start_index (S start) l.
    Proof. intros. reflexivity. Qed.

    Lemma map_with_index_cons: forall a l,
        map_with_index (a :: l) = f a 0 :: map_with_start_index 1 l.
    Proof. intros. reflexivity. Qed.

    Lemma skipn_map_with_start_index: forall i start l,
        skipn i (map_with_start_index start l) = map_with_start_index (start + i) (skipn i l).
    Proof.
      induction i; intros.
      - simpl. rewrite PeanoNat.Nat.add_0_r. reflexivity.
      - destruct l; simpl. 1: reflexivity. rewrite IHi. f_equal. Lia.lia.
    Qed.

    Lemma map_with_start_index_nth_error: forall (n start: nat) (l: list A) d,
        List.nth_error l n = Some d ->
        List.nth_error (map_with_start_index start l) n = Some (f d (start + n)).
    Proof.
      induction n; intros.
      - destruct l; simpl in *. 1: discriminate. rewrite PeanoNat.Nat.add_0_r. congruence.
      - destruct l; simpl in *. 1: discriminate. erewrite IHn. 2: eassumption. f_equal. f_equal. Lia.lia.
    Qed.

    Lemma map_with_index_nth_error: forall (n: nat) (l : list A) d,
        List.nth_error l n = Some d ->
        List.nth_error (map_with_index l) n = Some (f d n).
    Proof. intros. eapply map_with_start_index_nth_error. assumption. Qed.

  End MapWithIndex.

  Section WithA.
    Context {A: Type}.

    Lemma nth_error_to_hd_skipn: forall n (l: list A) a d,
        List.nth_error l n = Some a ->
        hd d (skipn n l) = a.
    Proof.
      induction n; intros.
      - destruct l; simpl in *. 1: discriminate. congruence.
      - destruct l; simpl in *. 1: discriminate. eauto.
    Qed.

    Definition generate(len: nat)(f: nat -> A): list A := List.map f (List.seq 0 len).
  End WithA.
End List.

Section WithParameters.
  Context {p : FE310CSemantics.parameters}.
  Import Syntax BinInt String List.ListNotations ZArith.
  Local Set Implicit Arguments.
  Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
  Local Coercion expr.literal : Z >-> expr.
  Local Coercion expr.var : String.string >-> expr.
  Infix "\*" := sep (at level 45, right associativity).

  (* ** Packet Formats *)

  Inductive EtherType := EtherTypeARP | EtherTypeIPv4.

  Definition encodeEtherType(t: EtherType): list byte :=
    match t with
    | EtherTypeARP => [Byte.x08; Byte.x06]
    | EtherTypeIPv4 => [Byte.x08; Byte.x00]
    end.

  Definition ETHERTYPE_IPV4_LE: Z :=
    Eval compute in (LittleEndian.combine 2 (tuple.of_list (encodeEtherType EtherTypeIPv4))).

  Definition ETHERTYPE_ARP_LE: Z :=
    Eval compute in (LittleEndian.combine 2 (tuple.of_list (encodeEtherType EtherTypeARP))).

  Definition MAC := tuple byte 6.

  Definition encodeMAC: MAC -> list byte := tuple.to_list.

  Definition IPv4 := tuple byte 4.

  Definition encodeIPv4: IPv4 -> list byte := tuple.to_list.

  Definition encodeCRC(crc: Z): list byte := tuple.to_list (BigEndian.split 4 crc).

  Record EthernetPacket(Payload: Type) := mkEthernetARPPacket {
    dstMAC: MAC;
    srcMAC: MAC;
    etherType: EtherType;
    payload: Payload;
  }.

  (* Note: At the moment we want to allow any padding and crc, so we use an isXxx predicate rather
     than an encodeXxx function *)
  Definition isEthernetPacket{P: Type}(payloadOk: P -> list byte -> Prop)(p: EthernetPacket P)(bs: list byte) :=
    exists data padding crc,
      bs = encodeMAC p.(srcMAC) ++ encodeMAC p.(dstMAC) ++ encodeEtherType p.(etherType)
           ++ data ++ padding ++ encodeCRC crc /\
      payloadOk p.(payload) data /\
      46 <= Z.of_nat (List.length (data ++ padding)) <= 1500.
      (* TODO could/should also verify CRC *)

  Inductive ARPOperation := ARPOperationRequest | ARPOperationReply.

  Definition encodeARPOperation(oper: ARPOperation): list byte :=
    match oper with
    | ARPOperationRequest => [Byte.x01]
    | ARPOperationReply => [Byte.x02]
    end.

  Record ARPPacket := mkARPPacket {
    oper: ARPOperation;
    sha: MAC;  (* sender hardware address *)
    spa: IPv4; (* sender protocol address *)
    tha: MAC;  (* target hardware address *)
    tpa: IPv4; (* target protocol address *)
  }.

  Definition encodeARPPacket(p: ARPPacket): list byte :=
    [
      Byte.x00; Byte.x01; (* hardware type: Ethernet *)
      Byte.x80; Byte.x00; (* protocol type *)
      Byte.x06;           (* hardware address length (6 for MAC addresses) *)
      Byte.x04            (* protocol address length (4 for IPv4 addresses) *)
    ] ++ encodeARPOperation p.(oper)
    ++ encodeMAC p.(sha) ++ encodeIPv4 p.(spa) ++ encodeMAC p.(tha) ++ encodeIPv4 p.(tpa).

  Definition HTYPE_LE := Ox"0100".
  Definition PTYPE_LE := Ox"0080".
  Definition HLEN := Ox"06".
  Definition PLEN := Ox"04".
  Definition OPER_REQUEST := Ox"01".
  Definition OPER_REPLY := Ox"02".

  Definition isEthernetARPPacket: EthernetPacket ARPPacket -> list byte -> Prop :=
    isEthernetPacket (fun arpP => eq (encodeARPPacket arpP)).

  Record ARPConfig := mkARPConfig {
    myMAC: MAC;
    myIPv4: IPv4;
  }.

  Context (cfg: ARPConfig).

  (* high-level protocol definition (does not mention lists of bytes) *)

  Definition needsARPReply(req: EthernetPacket ARPPacket): Prop :=
    req.(etherType) = EtherTypeARP /\
    req.(payload).(oper) = ARPOperationRequest /\
    req.(payload).(tpa) = cfg.(myIPv4). (* <-- we only reply to requests asking for our own MAC *)

  Definition ARPReply(req: EthernetPacket ARPPacket): EthernetPacket ARPPacket :=
    {| dstMAC := req.(payload).(sha);
       srcMAC := cfg.(myMAC);
       etherType := EtherTypeARP;
       payload := {|
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

  Coercion Z.of_nat : nat >-> Z.
  Notation len := List.length.
  Notation "'bytetuple' sz" := (HList.tuple byte (@Memory.bytes_per width sz)) (at level 10).

Infix "^+" := word.add  (at level 50, left associativity).
Infix "^-" := word.sub  (at level 50, left associativity).
Infix "^*" := word.mul  (at level 40, left associativity).
Infix "^<<" := word.slu  (at level 37, left associativity).
Infix "^>>" := word.sru  (at level 37, left associativity).
Notation "/[ x ]" := (word.of_Z x)       (* squeeze a Z into a word (beat it with a / to make it smaller) *)
  (format "/[ x ]").
Notation "\[ x ]" := (word.unsigned x)   (* \ is the open (removed) lid of the modulo box imposed by words, *)
  (format "\[ x ]").                     (* let a word fly into the large Z space *)

  Definition addr_in_range(a start: word)(len: Z): Prop :=
    word.unsigned (word.sub a start) <= len.

  Definition subrange(start1: word)(len1: Z)(start2: word)(len2: Z): Prop :=
    0 <= len1 <= len2 /\ addr_in_range start1 start2 (len2-len1).

  Notation "a ,+ m 'c=' b ,+ n" := (subrange a m b n)
    (no associativity, at level 10, m at level 1, b at level 1, n at level 1,
     format "a ,+ m  'c='  b ,+ n").

  (* TODO move (to Scalars.v?) *)
  Lemma load_bounded_Z_of_sep: forall sz addr (value: Z) R m,
      0 <= value < 2 ^ (Z.of_nat (bytes_per (width:=width) sz) * 8) ->
      sep (truncated_scalar sz addr value) R m ->
      Memory.load_Z sz m addr = Some value.
  Proof.
    intros.
    cbv [load scalar littleendian load_Z] in *.
    erewrite load_bytes_of_sep. 2: exact H0.
    apply f_equal.
    rewrite LittleEndian.combine_split.
    apply Z.mod_small.
    assumption.
  Qed.

  Lemma load_of_sep_truncated_scalar: forall sz addr (value: Z) R m,
      0 <= value < 2 ^ (Z.of_nat (bytes_per (width:=width) sz) * 8) ->
      sep (truncated_scalar sz addr value) R m ->
      Memory.load sz m addr = Some (word.of_Z value).
  Proof.
    intros. unfold Memory.load.
    erewrite load_bounded_Z_of_sep by eassumption.
    reflexivity.
  Qed.

  Definition BEBytesToWord{n: nat}(bs: tuple byte n): word := word.of_Z (BigEndian.combine n bs).

  Definition byteToWord(b: byte): word := word.of_Z (byte.unsigned b).
(*
can the program logic automation for load1/2/4/8 support any (potentially not-yet-defined)
separation logic predicate to load from?

eg load4 should work for
(ptsto_bytes 4 addr myByte4Tuple)
(truncated_scalar access_size.four addr myZ)
(scalar addr v)
(array ptsto (word.of_Z 1) addr my4ByteList)
(myCustomPred addr myCustomValue)

Maybe, but note that the common datatype being stored in local variables is word anyways,
so we can also use that one datatype in the sep clauses:

word.unsigned (customThingyToWord v) <= 2^sz
sep (truncated_word sz addr (customThingyToWord v)) R m
  x = load2(addr)
(map.put l x (customThingyToWord v))
*)

  (* An n-byte unsigned little-endian number v at address a.
     Enforces that v fits into n bytes. *)
  Definition LEUnsigned(n: nat)(addr: word)(v: Z)(m: mem): Prop :=
    exists bs: tuple byte n, ptsto_bytes n addr bs m /\ v = LittleEndian.combine n bs.

  (* enforces that v fits into (bytes_per sz) bytes *)
  Definition value(sz: access_size)(addr v: word): mem -> Prop :=
    LEUnsigned (bytes_per (width:=width) sz) addr (word.unsigned v).

  Lemma load_of_sep_value: forall sz addr v R m,
      sep (value sz addr v) R m ->
      Memory.load sz m addr = Some v.
  Proof.
    unfold value, Memory.load, Memory.load_Z, LEUnsigned. intros.
    assert (exists bs : tuple Init.Byte.byte (bytes_per sz),
               sep (ptsto_bytes (bytes_per sz) addr bs) R m /\
               word.unsigned v = LittleEndian.combine (bytes_per (width:=width) sz) bs) as A. {
      unfold sep in *.
      destruct H as (mp & mq & A & B & C).
      destruct B as (bs & B & E).
      eauto 10.
    }
    clear H. destruct A as (bs & A & E).
    erewrite load_bytes_of_sep by eassumption.
    rewrite <- E.
    rewrite word.of_Z_unsigned.
    reflexivity.
  Qed.

  Inductive TypeSpec: Type -> Type :=
  | TValue{R: Type}(sz: access_size)(encode: R -> word): TypeSpec R
  | TStruct{R: Type}(fields: list (FieldSpec R)): TypeSpec R
  | TArray{E: Type}(elemSize: Z)(elemSpec: TypeSpec E): TypeSpec (list E)
  with FieldSpec: Type -> Type :=
  | FField{R F: Type}(getter: R -> F)(setter: R -> F -> R)(fieldSpec: TypeSpec F)
    : FieldSpec R.

  Fixpoint TypeSpec_size{R: Type}(sp: TypeSpec R): R -> Z :=
    match sp with
    | TValue sz _ => fun r => bytes_per (width:=width) sz
    | TStruct fields => fun r => List.fold_right (fun f res => FieldSpec_size f r + res) 0 fields
    | TArray elemSize _ => fun l => List.length l * elemSize
    end
  with FieldSpec_size{R: Type}(f: FieldSpec R): R -> Z :=
    match f with
    | FField getter setter sp => fun r => TypeSpec_size sp (getter r)
    end.

  (* sum of the sizes of the first i fields *)
  Definition offset{R: Type}(r: R)(fields: list (FieldSpec R))(i: Z): Z :=
    List.fold_right (fun f res => FieldSpec_size f r + res) 0 (List.firstn (Z.to_nat i) fields).

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
    end.

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
    FField foo_count set_foo_count (TValue access_size.two word.of_Z);
    FField foo_packet set_foo_packet dummy_spec;
    FField foo_packets set_foo_packets (TArray 256 dummy_spec)
  ].

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

  Inductive lookup_path:
    (* input: start type, end type, path, *)
    forall {R F: Type}, path R F ->
    (* type spec, base address, and whole value found at empty path *)
    TypeSpec R -> word -> R ->
    (* output: type spec, address and value found at given path *)
    TypeSpec F -> word -> F -> Prop :=
  | lookup_path_Nil: forall R (sp: TypeSpec R) addr r,
      lookup_path (PNil R)
                  sp addr r
                  sp addr r
  | lookup_path_Field: forall R S F (prefix: path R S) (getter: S -> F) setter fields i sp sp' addr addr' r r',
      lookup_path prefix
                  sp addr r
                  (TStruct fields) addr' r' ->
      List.nth_error fields i = Some (FField getter setter sp') ->
      lookup_path (PField prefix getter)
                  sp addr r
                  sp' (addr' ^+ /[offset r' fields i]) (getter r')
  | lookup_path_Index: forall R E (sp: TypeSpec R) r len prefix i (sp': TypeSpec E) l e addr addr',
      lookup_path prefix
                  sp addr r
                  (TArray len sp') addr' l ->
      List.nth_error l i = Some e ->
      lookup_path (PIndex prefix i)
                  sp addr r
                  sp' (addr' ^+ /[i * len]) e.

  Goal forall base f R m,
      seps [dataAt foo_spec base f; R] m ->
      False.
  Proof.
    intros.

    Check f.(foo_packet).(dummy_len).

    Eval simpl in (path_value (PField (PField (PNil _) foo_packet) dummy_len) f).

    set (range_size := (TypeSpec_size foo_spec f)).
    cbn -[Z.add] in range_size.

    (* t = load2(base ^+ /[4] ^+ /[8])
       The range `(base+12),+2` corresponds to the field `f.(foo_packet).(dummy_len)`.
       Goal: use lia to find this path. *)

    (* forward reasoning: *)
    pose proof (lookup_path_Nil foo_spec base f) as P.
    let H := fresh "P" in rename P into H; pose proof (lookup_path_Field 1 H eq_refl) as P.
    cbn in P.
    let H := fresh "P" in rename P into H; pose proof (lookup_path_Field 2 H eq_refl) as P.
    cbn in P.


(*
       store2(base ^+ /[4] ^+ /[8], t)

       f(base ^+ /[4] ^+ /[8], otherargs)
*)
  Abort.

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

  Notation "bs @ a" := (array ptsto (word.of_Z 1) a bs)
    (at level 40, no associativity).

  Implicit Type post: trace -> mem -> locals -> MetricLogging.MetricLog -> Prop.

  (* later, we might also support loads in expressions, maybe under the restriction that
     expressig the loaded value does not require splitting lists *)
  Lemma load_stmt: forall e sz x a a' t m l mc rest post,
      dexpr m l a a' ->
      (exists R,
          seps R m /\
          exists i b bs,
            List.nth_error R i = Some (bs @ b) /\
            a',+(Z.of_nat (@Memory.bytes_per width sz)) c= b,+(len bs) /\
            (forall bs_l (v: Z) bs_r mc,
                bs = bs_l ++ tuple.to_list (LittleEndian.split (@Memory.bytes_per width sz) v) ++ bs_r ->
                0 <= v < 2 ^ (8 * Z.of_nat (@Memory.bytes_per width sz)) ->
                \[a' ^- b] = len bs_l ->
                exec e rest t m (map.put l x (word.of_Z v)) mc post)) ->
      exec e (cmd.seq (cmd.set x (expr.load sz a)) rest) t m l mc post.
  Admitted.

  Definition wand(P Q: mem -> Prop)(m: mem): Prop :=
    forall m1 m2, map.split m2 m m1 -> P m1 -> Q m2.

  (* an "existential" version of wand, also called the dual of wand, or septraction [Bannister et al, ITP'18].
     Roughly, P is a subheap of Q, and 'Q without P' holds on m *)
  Definition dwand(P Q: mem -> Prop)(m: mem): Prop :=
    exists m1 m2, map.split m2 m m1 /\ P m1 /\ Q m2.

  Lemma wand_adjoint: forall P Q R,
      impl1 (sep P Q) R <-> impl1 P (wand Q R).
  Proof.
    unfold impl1, wand, sep. firstorder eauto.
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

  Lemma seps_nth_error_to_head: forall i Ps P,
      List.nth_error Ps i = Some P ->
      iff1 (seps Ps) (sep P (seps (app (firstn i Ps) (tl (skipn i Ps))))).
  Proof.
    intros.
    etransitivity.
    - symmetry. eapply seps_nth_to_head.
    - eapply List.nth_error_to_hd_skipn in H. rewrite H. reflexivity.
  Qed.

  Lemma expose_lookup_path: forall R F (pth: path R F) sp base (r: R) sp' addr (v: F),
      lookup_path pth sp base r sp' addr v ->
      exists Frame, iff1 (dataAt sp base r) (sep (dataAt sp' addr v) Frame).
  Proof.
    induction 1.
    - exists (emp True). cancel.
    - destruct IHlookup_path as [Frame IH]. simpl in IH.
      eexists.
      etransitivity; [exact IH|clear IH].
      unfold fieldsAt at 1.
      eapply List.map_with_index_nth_error in H0.
      rewrite seps_nth_error_to_head. 2: exact H0.
      unfold fieldAt at 1. ecancel.
    - destruct IHlookup_path as [Frame IH]. simpl in IH.
      eexists.
      etransitivity; [exact IH|clear IH].
      unfold arrayAt at 1.
      eapply List.map_with_index_nth_error in H0.
      rewrite seps_nth_error_to_head. 2: exact H0.
      ecancel.
  Qed.

  Lemma load_field: forall sz m addr M i R sp (r: R) base (F: Type) (pth: path R F) encoder v,
      seps M m ->
      List.nth_error M i = Some (dataAt sp base r) ->
      lookup_path pth sp base r (TValue sz encoder) addr v ->
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

  (* later, we might also support loads in expressions, maybe under the restriction that
     expressig the loaded value does not require splitting lists *)
  Lemma load_byte_field_stmt: forall e sz x a a' t m l mc encoder rest post,
      dexpr m l a a' ->
      (exists M,
          seps M m /\
          exists i R sp (r: R) base,
            List.nth_error M i = Some (dataAt sp base r) /\
            exists (pth: path R (bytetuple sz)) v,
              lookup_path pth sp base r (TValue sz encoder)
                 a' v /\
              (forall mc,
                  exec e rest t m (map.put l x /[LittleEndian.combine _ v]) mc post)) ->
      exec e (cmd.seq (cmd.set x (expr.load sz a)) rest) t m l mc post.
  Proof.
    intros.
    repeat match goal with
           | H: exists x, _ |- _ => destruct H as [x H]
           | H: _ /\ _ |- _ => destruct H
           end.
    destruct (expose_lookup_path H2) as (Frame & P).
    simpl in P.
    eapply seps_nth_error_to_head in H1.
    eapply H1 in H0.
    seprewrite_in P H0.

  Admitted.

  Definition vc_func e '(innames, outnames, body) (t: trace) (m: mem) (argvs: list word)
                     (post : trace -> mem -> list word -> Prop) :=
    exists l, map.of_list_zip innames argvs = Some l /\ forall mc,
      exec e body t m l mc (fun t' m' l' mc' =>
        exists retvs : list word, map.getmany_of_list l' outnames = Some retvs /\ post t' m' retvs).

  Lemma length_encodeARPOperation: forall op, List.length (encodeARPOperation op) = 1%nat.
  Proof. intros. destruct op; reflexivity. Qed.

  Lemma length_encodeEtherType: forall et, List.length (encodeEtherType et) = 2%nat.
  Proof. intros. destruct et; reflexivity. Qed.

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
    | context[List.length (encodeEtherType ?et)] => constr:(length_encodeEtherType et)
    | context[List.length (encodeARPOperation ?op)] => constr:(length_encodeARPOperation op)
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

  Definition TODO{T: Type}: T. Admitted.

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
    cbn [dstMAC srcMAC etherType payload oper sha spa tha tpa].
    repeat eexists.
    (* can't use normal rewrite because COQBUG https://github.com/coq/coq/issues/10848 *)
    all: rewr (fun t => match t with
           | context [ List.length (?xs ++ ?ys) ] => constr:(List.app_length xs ys)
           | context [ List.length (encodeARPOperation ?op) ] => constr:(length_encodeARPOperation op)
           | context [ List.length (?h :: ?t) ] => constr:(List.length_cons h t)
           | context [ (?xs ++ ?ys) ++ ?zs ] => constr:(eq_sym (List.app_assoc xs ys zs))
           end) in |-*.
    {
      list_eq_cancel_step. {
        symmetry. apply to_list_firstn_as_tuple with (default := Byte.x00). ZnWords.
      }
      list_eq_cancel_step. {
        symmetry. apply to_list_firstn_as_tuple with (default := Byte.x00). ZnWords.
      }
      list_eq_cancel_step. {
        instantiate (1 := EtherTypeARP).
        assumption.
      }
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
  Qed.

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

(* random simplifications *)
Ltac simpli :=
  repeat (so fun hyporgoal =>
               match hyporgoal with
               | context[match ?x with _ => _ end] => destr x; try (exfalso; ZnWords); []
               end);
  repeat match goal with
         | H: _ |- _ => rewrite word.unsigned_of_Z_nowrap in H by ZnWords
         | H: _ |- _ => rewrite word.of_Z_unsigned in H
         | H: word.of_Z ?x = word.of_Z ?y |- _ =>
           assert (x = y) by (apply (word.of_Z_inj_small H); ZnWords); clear H
         | H: _ |- _ => ring_simplify_hyp H
         | H: ?T |- _ => clear H; assert_succeeds (assert T by ZnWords)
         end;
  simpl (bytes_per _) in *;
  simpl_Z_nat.

Ltac straightline_cleanup ::=
  match goal with
  | x : Word.Interface.word.rep _ |- _ => clear x
  | x : Semantics.word |- _ => clear x
  | x : Init.Byte.byte |- _ => clear x
  | x : Semantics.locals |- _ => clear x
  | x : Semantics.trace |- _ => clear x
  | x : Syntax.cmd |- _ => clear x
  | x : Syntax.expr |- _ => clear x
  | x : coqutil.Map.Interface.map.rep |- _ => clear x
  | x : BinNums.Z |- _ => clear x
  | x : unit |- _ => clear x
  | x : bool |- _ => clear x
  | x : list _ |- _ => clear x
  | x : nat |- _ => clear x
  | x := _ : Word.Interface.word.rep _ |- _ => clear x
  | x := _ : Semantics.word |- _ => clear x
  | x := _ : Init.Byte.byte |- _ => clear x
  | x := _ : Semantics.locals |- _ => clear x
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

Ltac after_snippet := repeat straightline; simpli.
(* For debugging, this can be useful:
Ltac after_snippet ::= idtac.
*)

Tactic Notation "$" constr(s) "$" := add_snippet s; after_snippet.

Notation "/*number*/ e" := e (in custom bedrock_expr at level 0, e constr at level 0).

Declare Custom Entry snippet.

Notation "*/ s /*" := s (s custom snippet at level 100).
Notation "x = e ;" := (SSet x e) (in custom snippet at level 0, x ident, e custom bedrock_expr).
Notation "'if' ( e ) '/*merge*/' {" := (SIf e true) (in custom snippet at level 0, e custom bedrock_expr).
Notation "'if' ( e ) '/*split*/' {" := (SIf e false) (in custom snippet at level 0, e custom bedrock_expr).
Notation "}" := SEnd (in custom snippet at level 0).
Notation "'else' {" := SElse (in custom snippet at level 0).

  Let nth n xs := hd (emp True) (skipn n xs).
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
      Lift1Prop.iff1 (R \* seps LHS) R /\ P.
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

  Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).

Set Default Goal Selector "1".

  Definition arp: (string * {f: list string * list string * cmd &
    forall e t m ethbufAddr ethBufData L R,
      seps [ethBufData @ ethbufAddr; R] m ->
      word.unsigned L = Z.of_nat (List.length ethBufData) ->
      vc_func e f t m [ethbufAddr; L] (fun t' m' retvs =>
        t' = t /\ (
        (* Success: *)
        (retvs = [word.of_Z 1] /\ exists request response ethBufData',
           seps [ethBufData' @ ethbufAddr; R] m' /\
           isEthernetARPPacket request  ethBufData  /\
           isEthernetARPPacket response ethBufData' /\
           ARPReqResp request response) \/
        (* Failure: *)
        (retvs = [word.of_Z 0] /\ seps [ethBufData @ ethbufAddr; R] m' /\ (
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
    if (ln == /*number*/64) /*split*/ { /*$. $*/
      tmp = load2(ethbuf + /*number*/12); /*$. (* ethertype in little endian order *)

{
  eexists. split. {
    eapply load_field.
    - eassumption.
    - apply TODO.
    - apply TODO.
}

Abort. (*
$*/
      if (tmp == ETHERTYPE_ARP_LE) /*split*/ { /*$. $*/
        tmp = load2(ethbuf + /*number*/14); /*$. $*/
        if (tmp == HTYPE_LE) /*split*/ { /*$.


(*
  Definition HTYPE_LE := Ox"0100".
  Definition PTYPE_LE := Ox"0080".
  Definition HLEN := Ox"06".
  Definition PLEN := Ox"04".
  Definition OPER_REQUEST := Ox"01".
*)

      idtac.

      exact TODO.

      (* TODO *) $*/
    else { /*$. (* nothing to do *) $*/
    } /*$.
      eexists.
      split. 1: reflexivity.
      split. 1: reflexivity.
      right.
      split. 1: reflexivity.
      auto.

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
*)

End WithParameters.
