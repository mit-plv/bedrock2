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
            <{ * my_pred2 p (* <-- deliberate typo: my_pred2 instead of my_pred1 *)
               * my_pred2 q
               * R }> m' #**/                                              /**.
Derive test SuchThat (fun_correct! test) As test_ok.                            .**/
{                                                                          /**.
  lazymatch goal with
  | _: warning_marker (cannot_purify (my_pred1 p)) |- _ => idtac
  end.
  lazymatch goal with
  | _: warning_marker (cannot_purify (my_pred2 q)) |- _ => idtac
  end.
  clear Warning Warning0.

  (* Test: should not loop infinitely: *)
  .**/ uintptr_t a = load(p); /**.

  lazymatch goal with
  | _: warning_marker (PredicateSize_not_found my_pred1) |- _ => idtac
  end.
  lazymatch goal with
  | _: warning_marker (PredicateSize_not_found my_pred2) |- _ => idtac
  end.

  test_error Error:("Exactly one of the following claims should hold:" nil).

  clear Error.
  unexplain.
  do 2 match goal with
       | W: PredicateSize_not_found _ |- _ => clear W
       end.
  do 2 match goal with
       | W: cannot_purify _ |- _ => clear W
       end.

  Local Hint Extern 1 (PredicateSize_not_found my_pred1)
      => constructor : suppressed_warnings.

  (* Test: should not loop infinitely: *)
  steps.

  lazymatch goal with
  | _: warning_marker (PredicateSize_not_found my_pred2) |- _ => idtac
  end.
  lazymatch goal with
  | _: warning_marker (PredicateSize_not_found my_pred1) |- _ =>
      fail "should have been suppressed"
  | |- _ => idtac
  end.

Abort.

Local Hint Extern 1 (cannot_purify _)
      => constructor : suppressed_warnings.

Derive test SuchThat (fun_correct! test) As test_ok.                            .**/
{                                                                          /**. .**/
}                                                                          /**.
  (* maybe my_pred2 could be split off from my_pred1, so we should inform
     the user that this option could not be considered because my_pred2's
     size is not known (and my_pred1's neither) *)
  lazymatch goal with
  | _: warning_marker (PredicateSize_not_found my_pred2) |- _ => idtac
  end.
Abort.

End LiveVerif.

Comments .**/ //.
