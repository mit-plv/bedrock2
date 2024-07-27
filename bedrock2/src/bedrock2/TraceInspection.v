From Coq Require Import String.
From Coq Require Import ZArith.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import bedrock2.Syntax bedrock2.Semantics.

Record RegisterSpec{width: Z}{BW: Bitwidth width}{word: word.word width} := {
  initial_register_value: option word;
  register_address: word;
}.

Record RegisterBehavior{width: Z}{BW: Bitwidth width}{word: word.word width} := {
  read: Prop;
  write: word -> Prop;
}.

Section WithMem.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Byte.byte}.

  Definition get_rw_reg_in_event(e: LogItem)(addr: word): option word :=
    let '((mGive, action, args), (mRcv, rets)) := e in
    if String.eqb action "MMIOWRITE" then
      match args with
      | cons a (cons v nil) => if word.eqb a addr then Some v else None
      | _ => None
      end
    else if String.eqb action "MMIOREAD" then
      match args with
      | cons a nil =>
          if word.eqb a addr then
            match rets with
            | cons v nil => Some v
            | _ => None
            end
          else None
      | _ => None
      end
    else None.

  Definition InitializedRegister(addr initial: Z): RegisterSpec := {|
    initial_register_value := Some (word.of_Z initial);
    register_address := word.of_Z addr;
  |}.

  Definition UninitializedRegister(addr: Z): RegisterSpec := {|
    initial_register_value := None;
    register_address := word.of_Z addr;
  |}.


  Fixpoint get_rw_reg0(t: trace)(addr: word): option word :=
    match t with
    | nil => None
    | cons e rest =>
        match get_rw_reg_in_event e addr with
        | Some v => Some v
        | None => get_rw_reg0 rest addr
        end
    end.

  (* the same definition with a more separation-logic-like signature: *)
  Definition uninitialized_rw_reg(val addr: word): trace -> Prop :=
    fix rec t :=
      match t with
      | nil => False
      | cons e tail =>
          match get_rw_reg_in_event e addr with
          | Some v => v = val
          | None => rec tail
          end
      end.

  Definition initialized_rw_reg(initial val addr: word): trace -> Prop :=
    fix rec t :=
      match t with
      | nil => initial = val
      | cons e tail =>
          match get_rw_reg_in_event e addr with
          | Some v => v = val
          | None => rec tail
          end
      end.

  Definition rw_reg(r: RegisterSpec)(val: word): trace -> Prop :=
    fix rec t :=
      match t with
      | nil => initial_register_value r = Some val
      | cons e tail =>
          match get_rw_reg_in_event e (register_address r) with
          | Some v => v = val
          | None => rec tail
          end
      end.

  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma uninitialized_rw_reg_unique: forall t addr val1 val2,
      uninitialized_rw_reg val1 addr t ->
      uninitialized_rw_reg val2 addr t ->
      val1 = val2.
  Proof.
    induction t; simpl; intros.
    - contradiction.
    - destruct_one_match_hyp. 1: congruence. eauto.
  Qed.

  Lemma initialized_rw_reg_unique: forall t addr init val1 val2,
      initialized_rw_reg init val1 addr t ->
      initialized_rw_reg init val2 addr t ->
      val1 = val2.
  Proof.
    induction t; simpl; intros.
    - congruence.
    - destruct_one_match_hyp. 1: congruence. eauto.
  Qed.

  Lemma rw_reg_unique: forall r t val1 val2,
      rw_reg r val1 t ->
      rw_reg r val2 t ->
      val1 = val2.
  Proof.
    destruct r as (init & addr).
    induction t; simpl; intros.
    - congruence.
    - destruct_one_match_hyp. 1: congruence. eauto.
  Qed.

  Definition get_rw_reg(r: RegisterSpec)(t: trace)(k: word -> Prop): Prop :=
    exists val, rw_reg r val t /\ k val.

  (* TODO can we define separating conjunction on (trace -> Prop)? *)

  (* TODO getters for different write semantics and different initial values,
     then define get_E1000_MYREG using one of these getters --> looks like section 13 *)

  (* Interesting registers:
     13.4.17 Interrupt Cause Read Register ICR: read-only, clear-on-read,
     but writing also allowed, writing 1 clears bit, writing 0 has no effect.
     13.4.19 Interrupt Cause Set Register ICS: write-only,
     writing 1 sets bit in ICR, writing 0 has no effect.
     13.4.20 Interrupt Mask Set/Read Register IMS: read-write,
     writing 1 sets bit, writing 0 has no effect, reading returns all enabled bits.
     13.4.21 Interrupt Mask Clear Register IMC: write-only,
     writing 1 clears bit in IMS, writing 0 has no effect *)

  (* (externally_owned_mem t m) means that after trace t has happened, the memory
     owned by the external world (i.e the memory that was given away by software
     and not yet received back) is m *)
  Fixpoint externally_owned_mem(t: trace)(m: mem): Prop :=
    match t with
    | nil => m = map.empty
    | cons ((mGive, action, args), (mReceive, rets)) tail =>
        (* Note: The names  "mGive" and "mReceive" are from the CPU's perspective,
           which is the opposite of the NIC's perspective *)
        exists mExtPrev, externally_owned_mem tail mExtPrev /\
        exists mExtBigger, map.split mExtBigger mExtPrev mGive /\
        map.split mExtBigger m mReceive
    end.

  Lemma externally_owned_mem_unique: forall t m1 m2,
      externally_owned_mem t m1 ->
      externally_owned_mem t m2 ->
      m1 = m2.
  Proof.
    induction t; simpl; intros.
    - subst. reflexivity.
    - destruct a as (((mGive & action) & args) & (mReceive & rets)). fwd.
      specialize IHt with (1 := H0p0) (2 := Hp0). subst mExtPrev0.
      pose proof (map.split_det Hp1p0 H0p1p0). subst mExtBigger0.
      apply (proj1 (map.split_diff (map.same_domain_refl _) Hp1p1 H0p1p1)).
  Qed.

  Definition dispatch(action: String.string)(args: list word):
    list (RegisterSpec * RegisterBehavior) -> Prop :=
    fix rec bs :=
      match bs with
      | nil => False
      | cons (r, b) tail =>
          match args with
          | cons addr args' =>
              if word.eqb (register_address r) addr then
                match args' with
                | nil => action = "MMIOREAD"%string /\ b.(read)
                | cons val nil => action = "MMIOWRITE"%string /\ b.(write) val
                | _ => False
                end
              else rec tail
          | _ => False
          end
      end.
End WithMem.
