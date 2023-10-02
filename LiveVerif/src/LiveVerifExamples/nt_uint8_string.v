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
  let h := constr:(#(len s1)) in loop invariant above h.
  unfold ready.
  lazymatch goal with
  | |- exec ?fs ?body ?t ?m ?l ?P =>
      lazymatch eval pattern s1, s2, p1, p2, R in P with
      | ?f s1 s2 p1 p2 R =>
          change (exec fs body t m l ((fun (g: list Z * list Z * word * word * (mem -> Prop)) (_: Z) =>
     (*let '(s1, s2, p1, p2, R) := g in f s1 s2 p1 p2 R) (s1, s2, p1, p2, R) (len s1)))*)
          let (g, R) := g in
          let (g, p2) := g in
          let (g, p1) := g in
          let (s1, s2) := g in
          f s1 s2 p1 p2 R) (s1, s2, p1, p2, R) (len s1)))
      end
  end.
  eapply wp_dowhile_tailrec_use_functionpost.
  { eauto with wf_of_type. }
  { (* Ltac log_packaged_context P ::= idtac P. *)
    package_heapletwise_context. }
  start_loop_body.
  steps.

  .**/
  c1 = load8(p1);                                                          /**.
  (* TODO: how to simplify (l[0] :: l[1:]) back into l?
     Or more also/more generally: (l[i:] ++ l[:i]) back into l?

     OR could say
     * on operations that don't modify memory: use m'=m -> no merging back is needed
     * on opeartions taht modify memory, typically the list will change, so no
       opportunity for this kind of simplifications *)
  .**/
  c2 = load8(p2);                                                          /**.

  replace ((s2 ++ [|0|])[0] :: (s2 ++ [|0|])[1:]) with (s2 ++ [|0|]) in *.
  2: {
    destruct s2.
    - bottom_up_simpl_in_goal. reflexivity.
    - try bottom_up_simpl_in_goal. (* TODO this should simplify but doesn't *) admit.
  }
  replace ((s1 ++ [|0|])[0] :: (s1 ++ [|0|])[1:]) with (s1 ++ [|0|]) in * by admit.

  unfold ready.

  lazymatch goal with
  (* from hypothesis of do-while lemma: *)
  | |- exec _ _ ?t ?m ?l (fun t' m' l' =>
     exists b, dexpr_bool3 _ _ ?condEvar _ _ _ _) => idtac condEvar
  end.

Abort.

End LiveVerif. Comments .**/ //.
