From Coq Require Import
     String Numbers.DecimalString.

Definition _gs (prefix: string) (n: nat) :=
  ("_gs_" ++ prefix ++ NilEmpty.string_of_uint (Nat.to_uint n))%string.

Definition gs {prefix: string} {n: nat} (str: string) :=
  str.

Ltac gensym_next locals prefix n :=
  match locals with
  | context[gs prefix n] => gensym_next locals prefix (S n)
  | _ => n
  end.

Ltac gensym locals prefix :=
  let n0 := match locals with
           | context[gs prefix ?n] => constr:(S n)
           | _ => constr:(0%nat)
           end in
  let n := gensym_next locals prefix n0 in
  let str := constr:(_gs prefix n) in
  let str := (eval vm_compute in str) in
  constr:(@gs prefix n str).

#[export] Hint Unfold gs : solve_map_get_goal.
