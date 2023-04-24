(* Tactics that are useful for manually tweaking the current hypotheses/conclusion.
   They differ from standard Coq tactics as follows:
   - Instead of accepting hypothesis names as arguments (which makes it tempting to
     rely on auto-generated hypothesis names, which leads to brittle proof scripts),
     these tactics accept arguments of type constr, but only a var referring to a hyp
     is allowed. This enables use of the find_hyp notation. So instead of `clear H7`,
     one can write `clear #(i = ??)`.
   - On all sideconditions, a configurable sidecondition solver tactic is run.
   - Unresolved sideconditions are always added before the main goal, never after. *)

Ltac tweak_sidecond_hook := idtac.

Ltac prove c := assert c; [tweak_sidecond_hook | ].
Ltac prove_as c h := assert c as h; [tweak_sidecond_hook | ].
Tactic Notation "prove" constr(c) := prove c.
Tactic Notation "prove" constr(c) "as" ident(h) := prove_as c h.

Ltac swap_with_in old new h :=
  (replace old with new in h; cycle 1); [tweak_sidecond_hook .. | ].

Tactic Notation "swap" constr(old) "with" constr(new) "in" constr(h) :=
  swap_with_in old new h.

(* Note: This is more than just an alias: `clear` syntactically only accepts idents
   (but multiple of them), whereas `delete` also accepts a constr obtained using
   find_hyp, which will implicilty get casted to an ident before invoking `clear` *)
Ltac delete h := clear h.
