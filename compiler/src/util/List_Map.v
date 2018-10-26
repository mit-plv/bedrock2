Require Import Coq.Lists.List.
Require Import compiler.util.Set.
Require Import compiler.Decidable.
Require Import compiler.util.Map.
Require Import compiler.util.ListLib.
Require Import compiler.util.List_Set.

Definition TODO{T: Type}: T. Admitted.

Require Import Coq.ZArith.ZArith.

Definition list_map_remove{K V: Type}{keq: DecidableEq K}(M: list (K * V))(k: K): list (K * V) :=
  filter (fun '(ki, vi) => if keq k ki then false else true) M.

Instance List_Map(K V: Type){keq: DecidableEq K}{veq: DecidableEq V}: MapFunctions K V :=
{|
  map := list (K * V);

  map_domain_set := List_Set _;
  map_range_set := List_Set _;

  empty_map := nil;
  get M k := match find (fun '(ki, vi) => if keq ki k then true else false) M with
             | Some (_, v) => Some v
             | None => None
             end;
  remove_key := list_map_remove;
  remove_keys M Ks := filter (fun '(ki, vi) => if dec (contains Ks ki) then false else true) M;
  put M k v := (k, v) :: (list_map_remove M k);
  restrict M A := filter (fun '(ki, vi) => if dec (contains A ki) then true else false) M;
  domain M := of_list (List.map fst M);
  range M := of_list (List.map snd M);
  reverse_get M v := match find (fun '(ki, vi) => if veq vi v then true else false) M with
             | Some (k, _) => Some k
             | None => None
             end;
  intersect_map M1 M2 := @list_intersect (K * V) (dec_eq_pair keq veq) M1 M2;
  remove_by_value M v := filter (fun '(ki, vi) => if veq vi v then false else true) M;
  remove_values M vs := filter (fun '(ki, vi) => if dec (contains vs vi) then false else true) M;
  update_map M1 M2 :=
    (filter (fun '(k1, v1) =>
               if (find (fun '(k2, v2) => if keq k1 k2 then false else true) M2)
               then false else true) M1) ++ M2;

|}.
all:
  assert (K = Z) by (apply TODO);
  assert (V = Z) by (apply TODO);
  subst;
  assert (keq = Z.eq_dec) by (apply TODO);
  assert (veq = Z.eq_dec) by (apply TODO);
  subst;
  abstract (apply TODO).
Defined.

(*
Check List_Map_subproof.
Check List_Map_subproof0.
Check List_Map_subproof1.

From QuickChick Require Import QuickChick. Import QcNotation.

(* Suppress some annoying warnings: *)
Set Warnings "-extraction-opaque-accessed,-extraction".

(*
Goal False.
  let t := type of List_Map_subproof17 in set (x := _ : Checkable t).
  Set Printing Implicit.
*)

(*
Instance SmallZs: GenSized Z := {|
  arbitrarySized n := match n mod 3 with
                      | 0 => returnGen (Z.neg 1)
                      | 1 => returnGen Z0
                      | _ => returnGen 1%Z
                      end
|}.
Print genZSized.

Set Printing Implicit.
Check (arbitrary: G Z).

Sample (arbitrary: G Z).
Sample (arbitrary: G (list (Z * Z))).
*)

QuickChick List_Map_subproof.
QuickChick List_Map_subproof0.
QuickChick List_Map_subproof1.
QuickChick List_Map_subproof2.
QuickChick List_Map_subproof3.
QuickChick List_Map_subproof4.
QuickChick List_Map_subproof5.
(* QuickChick List_Map_subproof6. "exists" is hard to evaluate *)
(* QuickChick List_Map_subproof7. "exists" is hard to evaluate *)
QuickChick List_Map_subproof8.

(*
QuickChecking List_Map_subproof8
[(-2,0); (-2,1)]
-2
1
*** Failed after 283 tests and 0 shrinks. (0 discards)

  reverse_get_Some: forall m k v, reverse_get m v = Some k -> get m k = Some v;

*)


(* QuickChick List_Map_subproof9. TODO *)
(* QuickChick List_Map_subproof10. TODO *)
QuickChick List_Map_subproof11.

(*
QuickChecking List_Map_subproof11
3
-3
[(3,-3); (3,0)]
*** Failed after 137 tests and 2 shrinks. (0 discards)

  remove_by_value_same: forall k v m,
      get m k = Some v -> get (remove_by_value m v) k = None;
*)

QuickChick List_Map_subproof12.
QuickChick List_Map_subproof13.
QuickChick List_Map_subproof14.
QuickChick List_Map_subproof15.
QuickChick List_Map_subproof16.
QuickChick List_Map_subproof17.
 *)
