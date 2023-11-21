(* -*- eval: (load-file "../../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Local Instance BW: .**/
ASSERT_BITWIDTH(32);
/**. constructor. Defined.

Load LiveVerif.

#[export] Instance spec_of_test_local_from_branches: fnspec := .**/

uintptr_t test_local_from_branches(uintptr_t px, uintptr_t py) /**#
  ghost_args := (R: mem -> Prop) x1 x2 y1 y2;
  requires t m := <{ * uint 32 (x1 + x2) px
                     * uint 32 (y1 + y2) py
                     * R }> m;
  ensures t' m' retv := t' = t /\
            <{ * uint 32 (x1 + x2) px
               * uint 32 (y1 + y2) py
               * R }> m' #**/                                              /**.
Derive test_local_from_branches SuchThat
   (fun_correct! test_local_from_branches) As test_local_from_branches_ok.      .**/
{                                                                          /**. .**/
  uintptr_t g = 0;                                                         /**. .**/
  if (load32(px) < load32(py)) {                                           /**. .**/
    uintptr_t r = load32(px);                                              /**. .**/
    g = r + 1;                                                             /**. .**/
  } else {                                                                 /**. .**/
    uintptr_t r = load32(py);                                              /**. .**/
    g = r - 1;                                                             /**. .**/
  } /**. merge.

  lazymatch goal with
  | |- @ready (wp_cmd ?fs ?c ?t ?m (map.of_list [|("g", g); ("px", px); ("py", py)|]) ?post)
    => idtac (* note that the list of locals does not contain r, even though it was
                added in both branches *)
  end.

  assert_succeeds (
    idtac;
    .**/ uintptr_t test = r; /** ;
    lazymatch goal with
    | |- dexpr1 _ _ _ ?v _ => is_evar v
    end).

  .**/ uintptr_t test = g; /**.
  .**/ return test; /**.
.**/ } /**.
Qed.

#[export] Instance spec_of_test_local_from_loop_body: fnspec := .**/

uintptr_t test_local_from_loop_body(uintptr_t px) /**#
  ghost_args := (R: mem -> Prop) x1 x2;
  requires t m := <{ * uint 32 (x1 + x2) px
                     * R }> m;
  ensures t' m' retv := t' = t /\
            <{ * uint 32 (x1 + x2) px
               * R }> m' #**/                                              /**.
Derive test_local_from_loop_body SuchThat
   (fun_correct! test_local_from_loop_body) As test_local_from_loop_body_ok.    .**/
{                                                                          /**. .**/
  uintptr_t g = 0;                                                         /**. .**/
  uintptr_t i = 0;                                                         /**.

  assert (0 <= \[i] <= 10) by steps.
  loop invariant above i.
  swap /[0] with (i ^* i) in #(g = ??).
  delete #(i = ??).
                                                                                .**/
  while (i < 10) /* decreases (10 - \[i]) */ {                             /**. .**/
    i = i + 1;                                                             /**. .**/
    uintptr_t t = i * i;                                                   /**. .**/
    g = t;                                                                 /**. .**/
  } /**.
  (* TODO: turn lower+upper bound into equality whenever possible *)

  lazymatch goal with
  | |- @ready (wp_cmd ?fs ?c ?t ?m (map.of_list [|("g", g); ("i", i); ("px", px)|]) ?post)
    => idtac (* note that the list of locals does not contain t, but that's not
                surprising because if no loop iteration is run at all, it's not set *)
  end.
                                                                                .**/
  return g;                                                                /**. .**/
}                                                                          /**.
Qed.

End LiveVerif. Comments .**/ //.
