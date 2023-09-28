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

Module byte.
  Definition compare(x y: byte): comparison :=
    Z.compare (byte.unsigned x) (byte.unsigned y).
End byte.

Load LiveVerif.

Definition char(c: byte): word -> mem -> Prop :=
  uint 8 (byte.unsigned c).

Definition nt_str(s: list byte)(a: word): mem -> Prop :=
  sep (array char (len s + 1) (s ++ [| Byte.x00 |]) a)
      (emp (~ List.In Byte.x00 s)).

#[local] Hint Unfold nt_str : heapletwise_always_unfold.

#[export] Instance str_cmp: fnspec :=                                           .**/

uintptr_t strcmp(uintptr_t p1, uintptr_t p2) /**#
  ghost_args := (s1 s2: list byte) (R: mem -> Prop);
  requires t m := <{ * nt_str s1 p1
                     * nt_str s2 p2
                     * R }> m;
  ensures t' m' res := t' = t /\
                       List.compare byte.compare s1 s2 = Z.compare (word.signed res) 0 /\
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
          change (exec fs body t m l ((fun (g: list byte * list byte * word * word * (mem -> Prop)) (_: Z) =>
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

  repeat match goal with
    | H: sep _ _ ?M |- _ => clear M H
    end;
  clear_until_LoopInvOrPreOrPost_marker;
  (* Note: will also appear after loop, where we'll have to clear it,
     but we have to pose it here because the foralls are shared between
     loop body and after the loop *)
  (let n := fresh "Scope0" in pose proof (mk_scope_marker LoopBody) as n);
  cbv beta.

  repeat pair_destructuring_intros_step. (* <-- TODO preserve names here *)


  unpackage_context;
  lazymatch goal with
  | |- exists b, dexpr_bool3 _ (map.of_list ?ksvs) _ b _ _ _ =>
      fix_local_names ksvs;
      eexists
  | |- loop_body_marker (exec _ _ _ _ (map.of_list ?ksvs) _) =>
      fix_local_names ksvs
  | |- _ => fail "assertion failure: hypothesis of loop lemma has unexpected shape"
  end.

  (* start_loop_body. *)

  steps.

Abort.

End LiveVerif. Comments .**/ //.
