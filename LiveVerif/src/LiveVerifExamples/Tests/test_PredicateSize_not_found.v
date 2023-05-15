(* -*- eval: (load-file "../../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

Context (my_pred1 my_pred2: word -> mem -> Prop).

#[export] Instance spec_of_test: fnspec :=                                      .**/

void test(uintptr_t p, uintptr_t q) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * my_pred1 p
                     * my_pred2 q
                     * R }> m;
  ensures t' m' := t' = t /\
            <{ * my_pred1 p
               * my_pred2 q
               * R }> m' #**/                                              /**.
Derive test SuchThat (fun_correct! test) As test_ok.                            .**/
{                                                                          /**.
  lazymatch goal with
  | _: message_scope_marker (cannot_purify (my_pred1 p)) |- _ => idtac
  end.
  lazymatch goal with
  | _: message_scope_marker (cannot_purify (my_pred2 q)) |- _ => idtac
  end.

  (* Test: should not loop infinitely: *)
  .**/ uintptr_t a = load(p); /**.

  lazymatch goal with
  | _: message_scope_marker (PredicateSize_not_found my_pred1) |- _ => idtac
  end.
  lazymatch goal with
  | _: message_scope_marker (PredicateSize_not_found my_pred2) |- _ => idtac
  end.

  test_error Error:("Exactly one of the following subrange claims should hold:" nil).
Abort.

End LiveVerif.

Comments .**/ //.
