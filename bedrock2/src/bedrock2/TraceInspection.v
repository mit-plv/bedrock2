Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import bedrock2.Syntax bedrock2.Semantics.

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

  Fixpoint get_rw_reg(t: trace)(addr: word): option word :=
    match t with
    | nil => None
    | cons e rest =>
        match get_rw_reg_in_event e addr with
        | Some v => Some v
        | None => get_rw_reg rest addr
        end
    end.

  (* the same definition with a more separation-logic-like signature: *)
  Definition rw_reg(val addr: word): trace -> Prop :=
    fix rec t :=
      match t with
      | nil => False
      | cons e tail =>
          match get_rw_reg_in_event e addr with
          | Some v => v = val
          | None => rec tail
          end
      end.

  (* TODO can we define separating conjunction on (trace -> Prop)? *)

  (* TODO clear-on-write semantics etc? *)
  (* TODO getters for different write semantics and different initial values,
     then define get_E1000_MYREGNAME using one of these getters --> looks like section 13 *)

  (* (externally_owned_mem t m) means that after trace t has happened, the memory
     owned by the external world (i.e the memory that was given away by software
     and not yet received back) is m *)
  Fixpoint externally_owned_mem(t: trace)(m: mem): Prop :=
    match t with
    | nil => m = map.empty
    | cons ((mGive, action, args), (mReceive, rets)) tail =>
        exists m_prev, externally_owned_mem tail m_prev /\
                       exists mKeep, map.split m_prev mKeep mGive /\
                                     map.split m mKeep mReceive
    end.
End WithMem.
