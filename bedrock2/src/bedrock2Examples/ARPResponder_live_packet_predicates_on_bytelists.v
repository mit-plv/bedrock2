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

End WithParameters.
