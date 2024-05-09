(* Alternative to sepapp:
   Instead of concatenating predicates of type (word -> mem -> Prop), we concatenate
   predicates of type (list byte -> Prop).
   Advantages:
   * No need to deal with the concept of "address"
   * Notion of predicate size is grounded in proof (rather than just a Z returned by
     typeclass search)
   * Better compatibility with network packets that are modeled as lists of bytes
   Disadvantage:
   * Predicates can't refer to further memory, so something like the following
     would not be expressible:

       Definition pointer_to(P: word -> mem -> Prop)(pointerAddr: word): mem -> Prop :=
         EX targetAddr, uintptr targetAddr pointerAddr * P targetAddr.

     and also can't be included in sepapps like this:

      <{ + pointer_to (uint 32 v)
         + pointer_to (ethernet_header h) }>
*)

Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import coqutil.Byte.

Lemma bp_ext: forall (P Q: list byte -> Prop), (forall bs, P bs <-> Q bs) -> P = Q.
Proof. intros. extensionality bs. eapply propositional_extensionality. apply H. Qed.

Definition bp_app(P Q: list byte -> Prop): list byte -> Prop :=
  fun bs => exists bs1 bs2, bs = bs1 ++ bs2 /\ P bs1 /\ Q bs2.

Fixpoint bp_concat(Ps: list (list byte -> Prop)): list byte -> Prop :=
  match Ps with
  | nil => eq nil
  | cons h t => bp_app h (bp_concat t)
  end.

Definition bp_and(P Q: list byte -> Prop): list byte -> Prop :=
  fun bs => P bs /\ Q bs.

Definition bp_or(P Q: list byte -> Prop): list byte -> Prop :=
  fun bs => P bs \/ Q bs.

Definition bp_ex[A: Type](P: A -> list byte -> Prop): list byte -> Prop :=
  fun bs => exists x: A, P x bs.

Lemma bp_and_comm: forall P Q, bp_and P Q = bp_and Q P.
Proof. unfold bp_and. intros. apply bp_ext. intuition. Qed.

Lemma bp_or_comm: forall P Q, bp_or P Q = bp_or Q P.
Proof. unfold bp_or. intros. apply bp_ext. intuition. Qed.

(* This one needs to be combined with bp_app (which is not commutative in general),
   so we uselessly have to pick an order *)
Definition bp_pure(P: Prop): list byte -> Prop := fun bs => bs = nil /\ P.

(* This allows any byte list, so it needs to be combined with bp_and, which is commutative
   and thus allows us to change the order.
   Naming: bp_impure takes a pure Prop and makes it impure (by allowing any byte list). *)
Definition bp_impure(P: Prop): list byte -> Prop := fun _ => P.

Lemma bp_app_nil_l: forall P, bp_app (eq nil) P = P.
Proof.
  intros. apply bp_ext. unfold bp_app. intros. split; intros.
  - destruct H as (? & ? & ? & ? & ?). subst. simpl. assumption.
  - repeat eexists. 2: eassumption. reflexivity.
Qed.

Lemma bp_app_nil_r: forall P, bp_app P (eq nil) = P.
Proof.
  intros. apply bp_ext. unfold bp_app. intros. split; intros.
  - destruct H as (? & ? & ? & ? & ?). subst. rewrite List.app_nil_r. assumption.
  - repeat eexists. 2: eassumption. symmetry. apply List.app_nil_r.
Qed.

Lemma bp_app_assoc: forall P Q R,
    bp_app (bp_app P Q) R = bp_app P (bp_app Q R).
Proof.
  intros. unfold bp_app. apply bp_ext. intros. split; intros.
  - destruct H as (? & ? & ? & (? & ? & ? & ? & ?) & ?). subst.
    rewrite <- List.app_assoc. eauto 10.
  - destruct H as (? & ? & ? & ? & (? & ? & ? & ? & ?)). subst.
    rewrite List.app_assoc. eauto 10.
Qed.

Lemma bp_concat_app: forall Ps Qs,
    bp_concat (Ps ++ Qs) = bp_app (bp_concat Ps) (bp_concat Qs).
Proof.
  induction Ps; intros; simpl.
  - rewrite bp_app_nil_l. reflexivity.
  - rewrite IHPs. symmetry. apply bp_app_assoc.
Qed.

Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.

Section Array.
  Context [E: Type] (elem: E -> list byte -> Prop).

  Definition raw_array(vs: list E): list byte -> Prop :=
    bp_concat (List.map elem vs).

  Lemma raw_array_app: forall vs1 vs2,
      raw_array (vs1 ++ vs2) = bp_app (raw_array vs1) (raw_array vs2).
  Proof. unfold raw_array. intros. rewrite List.map_app. apply bp_concat_app. Qed.

  Definition array(n: Z)(vs: list E): list byte -> Prop :=
    bp_and (bp_impure (Z.of_nat (List.length vs) = n))
           (raw_array vs).

End Array.

Require Import coqutil.Word.LittleEndianList.
Import ListNotations. Local Open Scope list_scope.

Require Import bedrock2.NetworkPackets. (* only used in examples below, but also defines a conflicting be_uint *)

Definition uint(nbits val: Z)(bs: list byte): Prop :=
  Z.of_nat (List.length bs) * 8 = nbits /\ le_combine bs = val.

Lemma uint_range: forall nbits val bs, uint nbits val bs -> 0 <= val < 2 ^ nbits.
Proof.
  unfold uint. intros * (? & ?). subst. rewrite Z.mul_comm. apply le_combine_bound.
Qed.

Definition be_uint(nbits val: Z)(bs: list byte): Prop :=
  Z.of_nat (List.length bs) * 8 = nbits /\ le_combine (List.rev bs) = val.

Lemma be_uint_range: forall nbits val bs, be_uint nbits val bs -> 0 <= val < 2 ^ nbits.
Proof.
  unfold uint. intros * (? & ?). subst. rewrite Z.mul_comm.
  rewrite <- List.rev_length. apply le_combine_bound.
Qed.

Lemma raw_array_id: forall (vs: list byte),
    raw_array (uint 8) (List.map byte.unsigned vs) vs.
Proof.
  intros. induction vs; intros; unfold raw_array in *; simpl.
  - reflexivity.
  - unfold bp_app at 1. repeat eexists.
    4: eassumption.
    1: change (a :: vs) with ([a] ++ vs); reflexivity.
    1: reflexivity.
    unfold le_combine. rewrite Z.shiftl_0_l. rewrite Z.lor_0_r. reflexivity.
Qed.

Lemma array_id: forall (vs: list byte) n,
    n = Z.of_nat (List.length vs) ->
    array (uint 8) n (List.map byte.unsigned vs) vs.
Proof.
  intros. subst. unfold array. unfold bp_and, bp_impure. split.
  - rewrite List.map_length. reflexivity.
  - apply raw_array_id.
Qed.

Fixpoint arrows(Ts: list Type)(R: Type): Type :=
  match Ts with
  | h :: t => h -> arrows t R
  | nil => R
  end.

Fixpoint ByteListPredicateSize(Ts: list Type): arrows Ts (list byte -> Prop) -> Z -> Prop :=
  match Ts with
  | nil => fun (pred: list byte -> Prop) sz => forall (bs: list byte),
               pred bs -> Z.of_nat (List.length bs) = sz
  | h :: t => fun (pred: h -> arrows t (list byte -> Prop)) sz =>
                forall (x: h), ByteListPredicateSize t (pred x) sz
  end.

Existing Class ByteListPredicateSize.

#[export] Instance uint_size(nbits: Z):
  ByteListPredicateSize [_] (uint nbits) (nbits / 8).
Proof.
  simpl. unfold uint. intros * (? & ?). subst.
  symmetry. apply Z.div_mul. discriminate.
Qed.

#[export] Instance be_uint_size(nbits: Z):
  ByteListPredicateSize [_] (be_uint nbits) (nbits / 8).
Proof.
  simpl. unfold be_uint. intros * (? & ?). subst.
  symmetry. apply Z.div_mul. discriminate.
Qed.

#[export] Instance bp_app_size(P1 P2: list byte -> Prop)(sz1 sz2: Z)
  (S1: ByteListPredicateSize [] P1 sz1)(S2: ByteListPredicateSize [] P2 sz2):
  ByteListPredicateSize [] (bp_app P1 P2) (sz1 + sz2).
Proof.
  simpl in *. unfold bp_app. intros * (? & ? & ? & ? & ?). subst.
  rewrite List.app_length. rewrite Nat2Z.inj_add. rewrite S1, S2 by assumption.
  reflexivity.
Qed.

#[export] Instance bp_eq_nil_size: ByteListPredicateSize [] (eq nil) 0.
Proof. simpl. intros. subst. reflexivity. Qed.

#[export] Instance generalize_predicate_size(t: Type)(ts: list Type)
  (pred: t -> arrows ts (list byte -> Prop))(x: t)(sz: Z)
  (S1: ByteListPredicateSize (cons t ts) pred sz):
  ByteListPredicateSize ts (pred x) sz.
Proof. simpl in *. apply S1. Qed.

(* Need to require that pred is syntactically a lambda, otherwise cyclic! *)
Lemma ungeneralize_predicate_size(t: Type)(ts: list Type)
  (pred: t -> arrows ts (list byte -> Prop))(sz: Z)
  (S1: forall x, ByteListPredicateSize ts (pred x) sz):
  ByteListPredicateSize (cons t ts) pred sz.
Proof. simpl in *. apply S1. Qed.

#[export] Hint Extern 4 (ByteListPredicateSize (cons _ _) (fun _ => _) ?sz) =>
  eapply ungeneralize_predicate_size; typeclasses eauto
: typeclass_instances.

(*
#[export] Instance bp_and_size
#[export] Instance bp_or_size
#[export] Instance bp_pure_size
#[export] Instance raw_array_size
*)

(* Note: raw_array can't have a ByteListPredicateSize because it would be value-dependent *)

#[export] Instance array_size[E: Type](elem: E -> list byte -> Prop)(n sz: Z)
  (ElemSize: ByteListPredicateSize [_] elem sz):
  ByteListPredicateSize [_] (array elem n) (n * sz).
Proof.
  unfold ByteListPredicateSize, array, bp_and, bp_impure in *.
  intros vs bs (? & ?). subst n.
  generalize dependent bs. induction vs; cbn -[Z.of_nat Z.mul]; intros.
  - subst bs. reflexivity.
  - destruct H0 as (bs1 & bs2 & ? & H1 & H2). subst bs.
    rewrite List.app_length. rewrite Nat2Z.inj_add.
    rewrite (ElemSize _ _ H1). rewrite (IHvs _ H2).
    rewrite Nat2Z.inj_succ. rewrite Z.mul_succ_l. apply Z.add_comm.
Qed.

Ltac reify_arg_types t :=
  lazymatch t with
  | list byte -> Prop => constr:(@nil Type)
  | ?a -> ?b => let r := reify_arg_types b in constr:(@cons Type a r)
  end.

Ltac exact_predicate_size p :=
  let t := type of p in
  let ts := reify_arg_types t in
  let e := open_constr:(_ : Z) in
  let c := constr:(_ : ByteListPredicateSize ts p e) in
  let sz := eval cbv in e in exact sz.

Definition sizeof_bad[Vs: list Type](pred: arrows Vs (list byte -> Prop))
  {sz: Z}{pf: ByteListPredicateSize Vs pred sz} := sz.

Fail Goal sizeof_bad (uint 8) = 1.

Notation sizeof p :=
  (match p with (* force typechecking before ltac *)
   | _ => ltac:(exact_predicate_size p)
   end) (only parsing).

Goal sizeof (uint 8) = 1. reflexivity. Succeed Qed. Abort.

Goal forall x, sizeof (uint 8 x) = 1. intros. reflexivity. Succeed Qed. Abort.

Goal forall x y: Z, sizeof (bp_app (uint 32 x) (uint 32 y)) = 8.
  intros. reflexivity.
Succeed Qed. Abort.

Require Import coqutil.Tactics.Tactics.

#[export] Hint Extern 20 (ByteListPredicateSize ?Vs ?pred ?sz) =>
  let h := head pred in unfold h;
  lazymatch goal with
  | |- ByteListPredicateSize _ (fun _ => bp_concat (cons _ _)) _ => typeclasses eauto
  end
: typeclass_instances.



Definition ethernet_header(h: ethernet_header_t): list byte -> Prop := bp_concat [
  array (uint 8) 6 (src_mac h);
  array (uint 8) 6 (dst_mac h);
  be_uint 16 (ethertype h)
].

Goal exists z, ByteListPredicateSize [_] ethernet_header z.
Proof.
  eexists.
  lazymatch goal with
  | |- ByteListPredicateSize ?Vs ?pred ?sz => let h := head pred in unfold h
  end.
  typeclasses eauto.
Succeed Qed. Abort.

Goal sizeof ethernet_header = 14. reflexivity. Succeed Qed. Abort.

Definition arp_packet(p: arp_packet_t): list byte -> Prop := bp_concat [
  be_uint 16 (arp_htype p);
  be_uint 16 (arp_ptype p);
  uint 8 (arp_hlen p);
  uint 8 (arp_plen p);
  be_uint 16 (arp_oper p);
  array (uint 8) 6 (arp_sha p);
  array (uint 8) 4 (arp_spa p);
  array (uint 8) 6 (arp_tha p);
  array (uint 8) 4 (arp_tpa p)
].

Goal sizeof arp_packet = 28. reflexivity. Succeed Qed. Abort.

Definition ip_header(h: ip_header_t): list byte -> Prop := bp_concat [
  uint 8 (ip_v_and_ihl h);
  uint 8 (ip_traffic_class h);
  be_uint 16 (ip_length h);
  be_uint 16 (ip_frag_id h);
  be_uint 16 (ip_frag_ofs h);
  uint 8 (ip_ttl h);
  uint 8 (ip_proto h);
  be_uint 16 (ip_chksum h);
  array (uint 8) 4 (ip_src h);
  array (uint 8) 4 (ip_dst h)
].

Goal sizeof ip_header = 20. reflexivity. Succeed Qed. Abort.

Definition udp_header(h: udp_header_t): list byte -> Prop := bp_concat [
  be_uint 16 (src_port h);
  be_uint 16 (dst_port h);
  be_uint 16 (udp_length h);
  be_uint 16 (udp_checksum h)
].

Goal sizeof udp_header = 8. reflexivity. Succeed Qed. Abort.

Require Import coqutil.Tactics.fwd.

Goal bp_ex (fun v: list Z => array (uint 8) 14 v)
   = bp_ex (fun v: ethernet_header_t => bp_concat [
               array (uint 8) 6 (src_mac v);
               array (uint 8) 6 (dst_mac v);
               be_uint 16 (ethertype v) ]).
Proof.
  apply bp_ext.
  unfold bp_ex.
  intro bs; split; intros; fwd.
  { eexists {| src_mac := _ |}. cbn. unfold bp_app.
    repeat eexists; unfold bp_impure; try eapply raw_array_id.
    2-3: rewrite List.map_length.
    all: admit. }
  {
Abort.

Goal bp_ex (fun v: list Z => array (uint 8) 14 v)
   = bp_ex (fun v: ethernet_header_t => bp_concat [
               array (uint 8) 6 (src_mac v);
               array (uint 8) 6 (dst_mac v);
               be_uint 16 (ethertype v) ]).
Proof.
  unfold bp_ex, bp_concat, bp_app.
  apply bp_ext.
  intro bs; split; intros; fwd.
  2: {
    eexists. eapply array_id. unfold array, bp_and, bp_impure in *.
    fwd. rewrite !List.app_length.
    admit.
  }
  {
    do 3 eexists.
    ssplit.
    3: {
      do 2 eexists.
      ssplit.
      1: reflexivity.
      2: {
        do 3 eexists. 1: reflexivity.
        split. 2: reflexivity.
Abort.
