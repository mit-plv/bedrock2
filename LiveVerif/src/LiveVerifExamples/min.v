(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib. Load LiveVerif.

(* TODO support functions that don't access any memory *)
Definition dummy: mem -> Prop := emp True.

#[export] Instance spec_of_u_min: fnspec :=                                     .**/

uintptr_t u_min (uintptr_t a, uintptr_t b) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := sep dummy R m;
  ensures t' m' retv := t' = t /\ sep dummy R m' /\
      (\[a] < \[b] /\ retv = a \/ \[b] <= \[a] /\ retv = b) #**/           /**.
Derive u_min SuchThat (fun_correct! u_min) As u_min_ok.                         .**/
{                                                                          /**. .**/
  uintptr_t r = 0;                                                         /**. .**/
  if (a < b) {                                                             /**. .**/
    r = a;                                                                 /**. .**/
  } else {                                                                 /**. .**/
    r = b;                                                                 /**. .**/
  } /**. end if.                                                                .**/
  return r;                                                                /**.

(* TODO __Zdef_c : c = word.ltu a b should be more zified *)
rewrite word.unsigned_ltu in __Zdef_c.

 .**/
}                                                                          /*?.

step.
clear __Zdef_c0  __Zdef_r0. (* TODO don't dupicate *)
step. step. step. step. step. step. step. step.

(* TODO zify ifs if their boolean condition is understood by lia *)

assert ((\[a] <? \[b]) = true /\ \[if c then a else b] = \[a] \/
        (\[a] <? \[b]) = false /\ \[if c then a else b] = \[b]) as __Zdef_if_0.
{ rewrite ?word.unsigned_ltu in __Zdef_c. clearbody c. subst c. destruct_one_match; auto. }

step.

Qed.

#[export] Instance spec_of_u_min3: fnspec :=                                    .**/

uintptr_t u_min3 (uintptr_t a, uintptr_t b, uintptr_t c) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := sep dummy R m;
  (* TODO make start_canceling work if just one R, or better, specialcase memoryless
     functions with m'=m in postcondition? *)
  ensures t' m' retv := t' = t /\ sep dummy R m' /\
      \[retv] = Z.min \[a] (Z.min \[b] \[c]) #**/                          /**.
Derive u_min3 SuchThat (fun_correct! u_min3) As u_min3_ok.                      .**/
{                                                                          /**. .**/
  uintptr_t r = u_min(a, b);                                               /**. .**/
  uintptr_t s = u_min(r, c);                                               /**. .**/
  return s;                                                                /**. .**/
}                                                                          /**.
Qed.

End LiveVerif. Comments .**/ //.
