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
  uintptr_t diff = 0;                                                      /**.

Abort.

End LiveVerif. Comments .**/ //.
