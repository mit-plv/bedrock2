(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.onesize_malloc.

(* TODO move *)

Module List.
  (* alternative: Coq.Structures.OrdersEx.String_as_OT.compare, but that's on strings,
     not on list of byte *)
  Section Lexicographic.
    Context {T: Type} (compare_elem: T -> T -> comparison).

    Fixpoint compare(a b: list T): comparison :=
      match a, b with
      | nil, nil => Eq
      | nil, _ => Lt
      | cons _ _, nil => Gt
      | cons a_head a_tail, cons b_head b_tail =>
          match compare_elem a_head b_head with
          | Lt => Lt
          | Gt => Gt
          | Eq => compare a_tail b_tail
          end
      end.
  End Lexicographic.
End List.

Load LiveVerif.

Definition nt_str(s: list Z)(a: word): mem -> Prop :=
  sep (array (uint 8) (len s + 1) (s ++ [| 0 |]) a)
      (emp (~ List.In 0 s)).

#[local] Hint Unfold nt_str : heapletwise_always_unfold.

#[export] Instance str_cmp: fnspec :=                                           .**/

uintptr_t strcmp(uintptr_t p1, uintptr_t p2) /**#
  ghost_args := (s1 s2: list Z) (R: mem -> Prop);
  requires t m := <{ * nt_str s1 p1
                     * nt_str s2 p2
                     * R }> m;
  ensures t' m' res := t' = t /\
                       List.compare Z.compare s1 s2 = Z.compare (word.signed res) 0 /\
                       <{ * nt_str s1 p1
                          * nt_str s2 p2
                          * R }> m' #**/                                   /**.
Derive strcmp SuchThat (fun_correct! strcmp) As strcmp_ok.                      .**/
{                                                                          /**. .**/
  uintptr_t c1 = 0;                                                        /**. .**/
  uintptr_t c2 = 0;                                                        /**.

  delete #(c1 = ??).
  delete #(c2 = ??).
  loop invariant above c1.
  move p1 before c1. move p2 before c1.
  unfold ready.
  (* pattern out ghost vars from functionpost to get post of do-while lemma: *)
  lazymatch goal with
  | |- exec ?fs ?body ?t ?m ?l ?P =>
      lazymatch eval pattern s1, s2, R, (len s1) in P with
      | ?f s1 s2 R (len s1) =>
          change (exec fs body t m l ((fun (g: list Z * list Z * (mem -> Prop)) (v: Z) =>
          let (g, R) := g in
          let (s1, s2) := g in
          f s1 s2 R v) (s1, s2, R) (len s1)))
      end
  end.
  eapply wp_dowhile_tailrec_use_functionpost.
  { eauto with wf_of_type. }
  {  Ltac log_packaged_context P ::= idtac P.
    package_heapletwise_context. }
  start_loop_body.
  steps.

  .**/
  c1 = deref8(p1);                                                         /**. .**/
  c2 = deref8(p2);                                                         /**. .**/
  p1 = p1 + 1;                                                             /**. .**/
  p2 = p2 + 1;                                                             /**.

  unfold ready.

  let e := constr:(live_expr:(c1 == c2 && c1 != 0)) in
  lazymatch goal with
  (* from hypothesis of do-while lemma: *)
  | |- exec _ _ ?t ?m ?l (fun t' m' l' =>
     exists b, dexpr_bool3 _ _ ?condEvar _ _ _ _) => unify condEvar e
  end.
  step. step.

  .**/ } /**. new_ghosts(s1[1:], s2[1:], _).

  assert (0 < len s1). {
    assert (len s1 <> 0). {
      intro C. destruct s1.
      - bottom_up_simpl_in_hyps. congruence.
      - discriminate C.
    }
    lia.
  }

  assert (0 < len s2). {
    assert (len s2 <> 0). {
      intro C. destruct s2.
      - bottom_up_simpl_in_hyps. congruence.
      - discriminate C.
    }
    lia.
  }

step. step. step. step. step. step. step. step. step. step. step. step. step. step.
step. step. step. step. step. step. step. step. step. step. step. step. step. step.
step. step. step. step. step. step. step.

(*  ~ List.In 0 s1[1:] *)

Abort.

End LiveVerif. Comments .**/ //.
