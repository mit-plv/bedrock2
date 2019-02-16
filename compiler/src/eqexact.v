Ltac make_args_match e1 e2 :=
  match e1 with
  | _ => unify e1 e2
  | ?e1a ?e1b => match e2 with
                 | ?e2a ?e2b =>
                   make_args_match e1a e2a; [
                     match tt with
                     | _ => unify e1b e2b
                     | _ => replace e2b with e1b
                     end
                   | .. ]
                 end
  end.

(* Given a hypothesis H of type "t1 t2 ... tn", and a goal of type "u1 u2 ... un",
   tries to unify each ti with the corresponding ui, and if unification fails,
   it replaces ui with ti (opening a new proof obligation for the equality).
   So the goal becomes "t1 t2 ... tn", and then H is applied. *)
Ltac eqexact H :=
  match goal with
  | |- ?E2 => match type of H with
              | ?E1 => make_args_match E1 E2
              end
  end;
  [ exact H | .. ].
