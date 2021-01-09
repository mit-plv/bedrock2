Require Import Coq.derive.Derive.
Require Import coqutil.Z.Lia.
Require coqutil.Word.BigEndian.
Require Import coqutil.Byte coqutil.Datatypes.HList.
Require Import coqutil.Tactics.letexists coqutil.Tactics.Tactics coqutil.Tactics.rewr.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.NotationsCustomEntry coqutil.Z.HexNotation.
Require Import bedrock2.FE310CSemantics.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Array.
Require Import bedrock2.ZnWords.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Require Import bedrock2.WeakestPrecondition bedrock2.ProgramLogic.
Require Import bedrock2.ZnWords.
Require Import bedrock2.SimplWordExpr.

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

  Inductive FieldEncoder(R: Type): Type :=
    fieldEncoder(F: Type)(accessor: R -> F)(offset: (*R -> word*) Z)(pred: word -> F -> mem -> Prop).

  Definition fieldAt{R: Type}(e: FieldEncoder R): word -> R -> mem -> Prop :=
    match e with
    | fieldEncoder accessor offset pred =>
      fun base r => pred (word.add base (word.of_Z offset)) (accessor r)
    end.

  Definition Encoder(R: Type) := list (FieldEncoder R).

  Fixpoint structAt{R: Type}(e: Encoder R): word -> R -> mem -> Prop :=
    match e with
    | nil => fun a r => emp True
    | cons h t => fun a r => sep (fieldAt h a r) (structAt t a r)
    end.

  Definition indexEncoder(E: Type)(sz i: Z)(pred: word -> E -> mem -> Prop): FieldEncoder (list E) :=
    fieldEncoder (fun l => List.nth_error l (Z.to_nat i))
                 (i * sz)
                 (fun a o => match o with
                             | Some e => pred a e
                             | None => fun _ => False
                             end).

  Definition arrayAt{E: Type}(pred: word -> E -> mem -> Prop)(sz: Z)(addr: word)(l: list E): mem -> Prop :=
    structAt (List.map (fun i => indexEncoder sz (Z.of_nat i) pred) (List.seq 0 (List.length l))) addr l.

  Record dummy_packet := {
    dummy_src: tuple byte 4;
    dummy_dst: tuple byte 4;
    dummy_len: Z;
    dummy_data: list byte;
    (* dummy_padding: list byte; not supported (yet?) because non-constant offset *)
  }.

  Definition dummy_encoder: Encoder dummy_packet := [
    fieldEncoder dummy_src 0 (ptsto_bytes 4);
    fieldEncoder dummy_dst 4 (ptsto_bytes 4);
    fieldEncoder dummy_len 8 (truncated_scalar access_size.two);
    fieldEncoder dummy_data 10 (array ptsto (word.of_Z 1))
    (*; offset depending on the value of the record
    fieldEncoder dummy_padding
                   (fun r => word.of_Z (10 + Z.of_nat (List.length (dummy_data r))))
                   (array ptsto (word.of_Z 1)) *)
  ].

  Record foo := {
    foo_count: Z;
    foo_packets: list dummy_packet;
  }.

  Definition foo_encoder: Encoder foo := [
    fieldEncoder foo_count 0 (truncated_scalar access_size.four);
    fieldEncoder foo_packets 4 (arrayAt (structAt dummy_encoder) 256)
  ].

  (* path digging into a record of type R *)
  Inductive path{Index: Type}: Type -> Type :=
  | PNil{R: Type}: path R
  | PField{R F: Type}(accessor: R -> F)(tail: path F): path R
  | PIndex{E: Type}(i: Index)(tail: path E): path (list E).

  Arguments path: clear implicits.

  Definition semantic_path := path Z.
  Definition syntactic_path := path expr.

  Fixpoint path_type{Index R: Type}(p: path Index R): Type :=
    match p with
    | PNil => R
    | PField _ tail => path_type tail
    | PIndex _ tail => path_type tail
    end.

  Fixpoint lookup_path{R: Type}(pth: semantic_path R){struct pth}: R -> option (path_type pth) :=
    match pth as p in (path _ T) return (T -> option (path_type p)) with
    | PNil => Some
    | PField accessor tail => fun r => lookup_path tail (accessor r)
    | PIndex i tail => fun l => match List.nth_error l (Z.to_nat i) with
                                 | Some e => lookup_path tail e
                                 | None => None
                                 end
    end.

  (* Not using a Fixpoint because in IPField, we would have to ensure that the two accessors
     return the same field type and use this equality to typecheck the recursive call *)
  Inductive interp_path(m: mem)(l: locals): forall R, syntactic_path R -> semantic_path R -> Prop :=
  | IPNil: forall R,
      interp_path m l (@PNil expr R) (@PNil Z R)
  | IPField: forall R F (acc: R -> F) tail tail',
      interp_path m l tail tail' ->
      interp_path m l (PField acc tail) (PField acc tail')
  | IPIndex: forall E i i' (tail: syntactic_path E) (tail': semantic_path E),
      dexpr m l i i' ->
      interp_path m l tail tail' ->
      interp_path m l (PIndex i tail) (PIndex (word.unsigned i') tail').

  Inductive construct_offset: forall R, syntactic_path R -> expr -> Prop :=
  | CONil: forall R,
      construct_offset (@PNil expr R) (expr.literal 0)
  | COFieldOrIndex: forall R F (acc: R -> F) pred (i: nat) (e: Encoder R) tail ofs1 ofs2,
      List.nth_error e i = Some (fieldEncoder acc ofs1 pred) ->
      construct_offset tail ofs2 ->
      (* TODO (expr.literal ofs1) only works for constant indices *)
      construct_offset (PField acc tail) (expr.op bopname.add (expr.literal ofs1) ofs2).

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

  Lemma assignment: forall e x a v t m l mc rest post,
      dexpr m l a v ->
      (forall mc, exec e rest t m (map.put l x v) mc post) ->
      exec e (cmd.seq (cmd.set x a) rest) t m l mc post.
  Admitted.

  Notation "bs @ a" := (array ptsto (word.of_Z 1) a bs)
    (at level 40, no associativity).

  Definition addr_in_range(a start: word)(len: Z): Prop :=
    word.unsigned (word.sub a start) <= len.

  Definition subrange(start1: word)(len1: Z)(start2: word)(len2: Z): Prop :=
    0 <= len1 <= len2 /\ addr_in_range start1 start2 (len2-len1).

  Notation "a ,+ m 'c=' b ,+ n" := (subrange a m b n)
    (no associativity, at level 10, m at level 1, b at level 1, n at level 1,
     format "a ,+ m  'c='  b ,+ n").

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

  (* later, we might also support loads in expressions, maybe under the restriction that
     expressig the loaded value does not require splitting lists *)
  Lemma load_field_stmt: forall e sz x a a' t m l mc rest post,
      dexpr m l a a' ->
      (exists M,
          seps M m /\
          exists i R enc (r: R),
            List.nth_error M i = Some (structAt enc a' r) /\
            (forall bs_l (v: Z) bs_r mc,
                exec e rest t m (map.put l x (word.of_Z v)) mc post)) ->
      exec e (cmd.seq (cmd.set x (expr.load sz a)) rest) t m l mc post.
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

Definition foo: Z := Ox"123".

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
      tmp = load2(ethbuf + /*number*/12); /*$. (* ethertype in little endian order *) $*/
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

End WithParameters.
