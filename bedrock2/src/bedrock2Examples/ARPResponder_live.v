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
Require Import bedrock2.WeakestPrecondition bedrock2.ProgramLogic.

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
           ++ data ++ padding ++ crc /\
      payloadOk p.(payload) data /\
      46 <= Z.of_nat (List.length (data ++ padding)) <= 1500 /\
      Z.of_nat (List.length crc) = 4. (* TODO could/should also verify CRC *)

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

  Definition isEthernetARPPacket: EthernetPacket ARPPacket -> list byte -> Prop :=
    isEthernetPacket (fun arpP => eq (encodeARPPacket arpP)).

  Record ARPConfig := mkARPConfig {
    myMAC: MAC;
    myIPv4: IPv4;
  }.

  Context (cfg: ARPConfig).

  (* high-level protocol definition (does not mention lists of bytes) *)
  Definition ARPReqResp(req resp: EthernetPacket ARPPacket): Prop :=
    req.(etherType) = EtherTypeARP /\
    req.(payload).(oper) = ARPOperationRequest /\
    req.(payload).(tpa) = cfg.(myIPv4) /\ (* <-- we only reply to requests asking for our own MAC *)
    resp.(dstMAC) = req.(payload).(sha) /\
    resp.(srcMAC) = cfg.(myMAC) /\
    resp.(etherType) = EtherTypeARP /\
    resp.(payload).(oper) = ARPOperationReply /\
    resp.(payload).(sha) = cfg.(myMAC) /\ (* <-- the actual reply *)
    resp.(payload).(spa) = cfg.(myIPv4) /\
    resp.(payload).(tha) = req.(payload).(sha) /\
    resp.(payload).(tpa) = req.(payload).(spa).

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

  Definition vc_func e '(innames, outnames, body) (t: trace) (m: mem) (argvs: list word)
                     (post : trace -> mem -> list word -> Prop) :=
    exists l, map.of_list_zip innames argvs = Some l /\ forall mc,
      exec e body t m l mc (fun t' m' l' mc' =>
        exists retvs : list word, map.getmany_of_list l' outnames = Some retvs /\ post t' m' retvs).

  (* ** ARP-specific helper lemmas *)

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

  Ltac list_eq_cancel_step :=
    apply list_eq_cancel_step;
    rewrite ?tuple.length_to_list, ?List.length_cons, ?List.length_nil, ?List.skipn_skipn,
            ?length_encodeEtherType, ?length_encodeARPOperation.

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
    unfold isEthernetARPPacket, isEthernetPacket, encodeARPPacket, encodeMAC, encodeIPv4.
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
        symmetry. apply to_list_firstn_as_tuple. ZnWords.
      }
      list_eq_cancel_step. {
        symmetry. apply to_list_firstn_as_tuple. ZnWords.
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
        symmetry. apply to_list_firstn_as_tuple. ZnWords.
      }
      list_eq_cancel_step. {
        symmetry. apply to_list_firstn_as_tuple. ZnWords.
      }
      list_eq_cancel_step. {
        symmetry. apply to_list_firstn_as_tuple. ZnWords.
      }
      list_eq_cancel_step. {
        symmetry. apply to_list_firstn_as_tuple. ZnWords.
      }
      case (@TODO False).
    }
    all: case (@TODO False).
    Unshelve.
    all: try exact Byte.x00.
    all: try exact nil.
  Qed.

  Definition arp: (string * {f: list string * list string * cmd &
    forall e t m ethbufAddr ethBufData len R,
      (array ptsto (word.of_Z 1) ethbufAddr ethBufData \* R) m ->
      word.unsigned len = Z.of_nat (List.length ethBufData) ->
      vc_func e f t m [ethbufAddr; len] (fun t' m' retvs =>
        t' = t /\ (
        (* Success: *)
        (retvs = [word.of_Z 1] /\ exists request response ethBufData',
           (array ptsto (word.of_Z 1) ethbufAddr ethBufData' \* R) m' /\
           isEthernetARPPacket request  ethBufData  /\
           isEthernetARPPacket response ethBufData' /\
           ARPReqResp request response) \/
        (* Failure: *)
        (retvs = [word.of_Z 0] /\ (array ptsto (word.of_Z 1) ethbufAddr ethBufData \* R) m' /\ (
           len <> word.of_Z 64 \/
           (* malformed request *)
           (~ exists request, isEthernetARPPacket request ethBufData) \/
           (* request needs no reply because it's not for us *)
           (forall request, isEthernetARPPacket request ethBufData -> request.(payload).(tpa) <> cfg.(myIPv4))))
      ))}).
    refine ("arp", existT _ (["ethbuf"; "len"], ["doReply"], _) _).
    intros. cbv [vc_func]. letexists. split. 1: subst l; reflexivity. intros.

    (* doReply = 0 // by default *)
    eapply assignment with (x := "doReply") (a := 0).
    1: repeat straightline. intros.

    (* if (len == 64) *)
    eapply if_split with (c := expr.op bopname.eq "len" 64).
    1: repeat straightline.
    all: intros D.
    { (* then (len == 64) *)
      destr (word.eqb len (word.of_Z 64)). 2: exfalso; ZnWords.


      instantiate (1 := TODO).
      exact TODO.
    }
    { (* else (len <> 64) *)
      destr (word.eqb len (word.of_Z 64)). 1: exfalso; ZnWords.
      (* nop *)
      eapply exec.skip.
      eexists.
      split. 1: reflexivity.
      split. 1: reflexivity.
      right.
      split. 1: reflexivity.
      auto.
    }
  Defined.

  Goal False.
    let r := eval unfold arp in match arp with
                                | (fname, existT _ (argnames, retnames, body) _) => body
                                end
      in pose r.
  Abort.

End WithParameters.
