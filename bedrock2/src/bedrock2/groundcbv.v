Require Import ZArith Ring.

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

Ltac is_ground_atom var_allowed e :=
  match e with
  | _ => is_constructor e
  | _ => is_proj e
  | _ => is_ind e
  | _ => is_const e; is_ground_const e
  | _ => is_var e; var_allowed e
  | _ => lazymatch isZcst e with
         | true => idtac
         end
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
          | _ => let vx := eval cbv in x in
                 constr:(gsf vx)
          end
      | ?gsx =>
          match gsf with
          | groundcbv_delayed => constr:(f gsx)
          | _ => constr:(gsf gsx)
          end
      end
  | _ =>
      let __ := match constr:(Set) with _ => is_ground_atom ltac:(fun _ => fail) e end in
      constr:(groundcbv_delayed)
  | _ => e
  end.
Ltac groundcbv e :=
  let e' := groundcbv' e in
  lazymatch e' with
  | groundcbv_delayed => eval cbv in e
  | ?e => e
  end.

Ltac groundcbv_in_all :=
  repeat match goal with
  | H : ?t |- _ =>  let t' := groundcbv t in progress change t' in H
  | x := ?t |- _ =>  let t' := groundcbv t in progress change t' in (value of x)
  | |- ?t =>  let t' := groundcbv t in progress change t'
  end.
