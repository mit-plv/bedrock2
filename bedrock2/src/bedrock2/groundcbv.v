Require Import ZArith Ring.
Require Import coqutil.Tactics.rdelta.

Ltac is_ground_const e :=
  lazymatch e with
  | Z.of_nat => idtac
  | Z.to_nat => idtac
  | Z.of_N => idtac
  | Z.to_N => idtac
  | N.of_nat => idtac
  | N.to_nat => idtac

  | Z.succ => idtac
  | Z.pred => idtac
  | Z.add => idtac
  | Z.sub => idtac
  | Z.mul => idtac
  | Z.div => idtac
  | Z.pred => idtac
  | Z.succ => idtac
  | Z.ones => idtac
  | Z.opp => idtac
  | Z.lnot => idtac
  | Z.log2 => idtac
  | Z.log2_up => idtac
  | Z.add => idtac
  | Z.sub => idtac
  | Z.mul => idtac
  | Z.div => idtac
  | Z.modulo => idtac
  | Z.quot => idtac
  | Z.rem => idtac
  | Z.pow => idtac
  | Z.shiftl => idtac
  | Z.shiftr => idtac
  | Z.land => idtac
  | Z.lor => idtac
  | Z.lxor => idtac
  | Z.ldiff => idtac
  | Z.clearbit => idtac
  | Z.setbit => idtac
  | Z.min => idtac
  | Z.max => idtac
  | Z.gcd => idtac
  | Z.lcm => idtac

  | N.succ => idtac
  | N.pred => idtac
  | N.add => idtac
  | N.sub => idtac
  | N.mul => idtac
  | N.div => idtac
  | N.pred => idtac
  | N.succ => idtac
  | N.ones => idtac
  | N.lnot => idtac
  | N.log2 => idtac
  | N.log2_up => idtac
  | N.add => idtac
  | N.sub => idtac
  | N.mul => idtac
  | N.div => idtac
  | N.modulo => idtac
  | N.pow => idtac
  | N.shiftl => idtac
  | N.shiftr => idtac
  | N.land => idtac
  | N.lor => idtac
  | N.lxor => idtac
  | N.ldiff => idtac
  | N.clearbit => idtac
  | N.setbit => idtac
  | N.min => idtac
  | N.max => idtac
  | N.gcd => idtac
  | N.lcm => idtac

  | Nat.succ => idtac
  | Nat.pred => idtac
  | Nat.add => idtac
  | Nat.sub => idtac
  | Nat.mul => idtac
  | Nat.div => idtac
  | Nat.pred => idtac
  | Nat.succ => idtac
  | Nat.ones => idtac
  | Nat.lnot => idtac
  | Nat.log2 => idtac
  | Nat.log2_up => idtac
  | Nat.add => idtac
  | Nat.sub => idtac
  | Nat.mul => idtac
  | Nat.div => idtac
  | Nat.modulo => idtac
  | Nat.pow => idtac
  | Nat.shiftl => idtac
  | Nat.shiftr => idtac
  | Nat.land => idtac
  | Nat.lor => idtac
  | Nat.lxor => idtac
  | Nat.ldiff => idtac
  | Nat.clearbit => idtac
  | Nat.setbit => idtac
  | Nat.min => idtac
  | Nat.max => idtac
  | Nat.gcd => idtac
  | Nat.lcm => idtac
  end.

Ltac is_number_constructor e :=
  lazymatch e with
  | Zpos => idtac
  | Z0 => idtac
  | Zneg => idtac
  | N0 => idtac
  | Npos => idtac
  | xI => idtac
  | xO => idtac
  | xH => idtac
  | S => idtac
  | O => idtac
  end.

Ltac is_ground_atom var_allowed e :=
  match e with
  | _ => is_const e; is_ground_const e
  | _ => is_constructor e; is_number_constructor e
  | _ => is_var e; var_allowed e
  | _ => fail "not ground"
  end.

Ltac is_ground' var_allowed e :=
  let is_ground e := is_ground' var_allowed e in
  match e with
  | ?f ?x => is_ground f; is_ground x
  | _ => is_ground_atom var_allowed e
  (* note: lambdas could be implemented here I think *)
  end.
Ltac is_ground e := is_ground' ltac:(fun _ => fail) e.

Ltac cbv_if_number e :=
  let t := type of e in
  lazymatch rdelta t with
  | Z => eval cbv in e
  | N => eval cbv in e
  | nat => eval cbv in e
  | positive => eval cbv in e
  | _ => e
  end.

Inductive groundcbv_delayed :=.
Ltac groundcbv' e :=
  match e with
  | ?f ?x =>
      let gsf := groundcbv' f in
      let gsx := groundcbv' x in
      lazymatch gsx with
      | groundcbv_delayed =>
          lazymatch gsf with
          | groundcbv_delayed => constr:(groundcbv_delayed)
          | _ => let vx := cbv_if_number x in
                 constr:(gsf vx)
          end
      | ?gsx =>
          lazymatch gsf with
          | groundcbv_delayed => constr:(f gsx)
          | _ => constr:(gsf gsx)
          end
      end
  | ?P -> ?Q =>
      let gP := groundcbv' P in
      let gQ := groundcbv' Q in
      lazymatch gQ with
      | groundcbv_delayed =>
          lazymatch gP with
          | groundcbv_delayed => constr:(groundcbv_delayed)
          | _ => let vQ := cbv_if_number Q in
                 constr:(gP -> vQ)
          end
      | ?gQ =>
          lazymatch gP with
          | groundcbv_delayed => let vP := cbv_if_number P in constr:(vP -> gQ)
          | _ => constr:(gP -> gQ)
          end
      end
  | if ?c then ?a else ?b =>
      let gc := groundcbv c in
      lazymatch gc with
      | true =>
          let ga := groundcbv' a in
          lazymatch ga with
          | groundcbv_delayed => constr:(groundcbv_delayed)
          | _ => ga
          end
      | false =>
          let gb := groundcbv' b in
          lazymatch gb with
          | groundcbv_delayed => constr:(groundcbv_delayed)
          | _ => gb
          end
      | _ =>
          let ga := groundcbv a in
          let gb := groundcbv b in
          constr:(if gc then ga else gb)
      end
  | _ =>
      let __ := match constr:(Set) with _ => is_ground_atom ltac:(fun _ => fail) e end in
      constr:(groundcbv_delayed)
  | _ => e
  end
with groundcbv e :=
  let e' := groundcbv' e in
  lazymatch e' with
  | groundcbv_delayed => cbv_if_number e
  | ?e => e
  end.

Ltac groundcbv_in_goal :=
  repeat match goal with
  | |- ?t =>  let t' := groundcbv t in progress change t'
  end.

Ltac groundcbv_in_all :=
  repeat match goal with
  | H : ?t |- _ =>  let t' := groundcbv t in progress change t' in H
  | x := ?t |- _ =>  let t' := groundcbv t in progress change t' in (value of x)
  | |- ?t =>  let t' := groundcbv t in progress change t'
  end.

Goal Z.add 1 3 = Z.of_nat 4 -> True.
  intros. groundcbv_in_all.
  match goal with
  | _: 4%Z = 4%Z |- _ => idtac
  end.
Abort.
