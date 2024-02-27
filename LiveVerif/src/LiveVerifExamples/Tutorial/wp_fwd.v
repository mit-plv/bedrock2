Require Import LiveVerif.LiveVerifLib.
Require Import bedrock2.NotationsCustomEntry.

Lemma evars_demo: forall (a b c: Z),
    a < b ->
    c > b ->
    a < c.
Proof.
  intros.
  (* apply Z.lt_trans. *)
  (* apply Z.lt_trans with (m := b). *)
  eapply Z.lt_trans.
  - eassumption.
  - apply Z.gt_lt. assumption.
Qed.


Load LiveVerif.

Notation "{{{ c }}}" := c (at level 0, c custom bedrock_cmd, format "{{{  c  }}}").
Notation wp := exec.

Definition ex1 := {{{ $"b" = $"a" - $42; $"c" = $"b" + $42 }}}.

Lemma ex1_ok: forall fs t m a,
    wp fs ex1
       t m (map.of_list [|("a", a)|])
       (fun t' m' l' => t' = t /\ m' = m /\
          l' = map.of_list [|("a", a); ("b", a ^- /[42]); ("c", a)|]).
Proof.
  unfold ex1.
  intros.
  eapply wp_seq.
  eapply wp_set00.
  eapply dexpr_binop.
  eapply dexpr_var. compute. reflexivity.
  eapply dexpr_literal.

  change (map.put (map.of_list [|("a", a)|]) "b" (interp_binop bopname.sub a /[42]))
    with (map.of_list [|("a", a); ("b", a ^- /[42])|]).

  eapply wp_set00.
  eapply dexpr_binop.
  eapply dexpr_var. reflexivity.
  eapply dexpr_literal.
  ssplit.
  reflexivity.
  reflexivity.
  unfold interp_binop.
  replace (a ^- /[42] ^+ /[42]) with a by ring.
  reflexivity.
Qed.

(* next: evars (above) *)

Derive ex2 SuchThat
  (forall fs t m a,
    wp fs ex2
       t m (map.of_list [|("a", a)|])
       (fun t' m' l' => t' = t /\ m' = m /\
          l' = map.of_list [|("a", a); ("b", a ^- /[42]); ("c", a)|]))
As ex2_ok.
  subst ex2. instantiate (1 := ?[c]). (* rename evar for presentation *)
  intros.
  eapply wp_seq.
  eapply wp_set00 with (x := "b") (e := bedrock_expr:($"a" - $42)).
  eapply dexpr_binop.
  eapply dexpr_var. compute. reflexivity.
  eapply dexpr_literal.

  change (map.put (map.of_list [|("a", a)|]) "b" (interp_binop bopname.sub a /[42]))
    with (map.of_list [|("a", a); ("b", a ^- /[42])|]).

  eapply wp_set00 with (x := "c") (e := bedrock_expr:($"b" + $42)).
  eapply dexpr_binop.
  eapply dexpr_var. reflexivity.
  eapply dexpr_literal.
  ssplit.
  reflexivity.
  reflexivity.
  unfold interp_binop.
  replace (a ^- /[42] ^+ /[42]) with a by ring.
  reflexivity.
Qed.

(*
Print ex2.
About ex2_ok.
*)

#[export] Instance spec_of_ex3: fnspec :=                                    .**/

uintptr_t ex3(uintptr_t a) /**#
  ghost_args := stuff (R: mem -> Prop);
  requires t m := <{ * uint 32 stuff a
                     * R }> m;
  ensures t' m' r := t' = t /\ r = a /\
       <{ * uint 32 stuff a
          * R }> m' #**/                                                   /**.
Derive ex3 SuchThat (fun_correct! ex3) As ex3_ok.                               .**/
{                                                                          /**. .**/
  uintptr_t b = a + 42;                                                    /**. .**/
  uintptr_t c = b - 42;                                                    /**. .**/
  return c;                                                                /**. .**/
}                                                                          /**.
Qed.

(*
Print ex3.
*)

End LiveVerif.
