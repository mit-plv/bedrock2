Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.

Ltac push_mod_step :=
  match goal with
  | |- context [ (?op ?a ?b) mod ?m ] =>
    lazymatch a with
    | _ mod m =>
      lazymatch b with
      | _ mod m => fail
      | _ => idtac
      end
    | _ => idtac
    end;
    match op with
    | Z.add => rewrite (Zplus_mod a b m)
    | Z.sub => rewrite (Zminus_mod a b m)
    | Z.mul => rewrite (Zmult_mod a b m)
    end
  end.

Ltac push_mod := repeat push_mod_step.

Ltac mod_free t :=
  match t with
  | ?op ?t1 ?t2 =>
    match op with
    | Z.add => idtac
    | Z.sub => idtac
    | Z.mul => idtac
    end;
    mod_free t1;
    mod_free t2
  | _ => is_var t
  end.

Ltac pull_mod_step :=
  match goal with
  | |- context [ (?op (?a mod ?m) (?b mod ?m)) mod ?m ] =>
    mod_free a;
    mod_free b;
    match op with
    | Z.add => rewrite <- (Zplus_mod a b m)
    | Z.sub => rewrite <- (Zminus_mod a b m)
    | Z.mul => rewrite <- (Zmult_mod a b m)
    end
  end.

Ltac pull_mod := repeat pull_mod_step.

Ltac push_pull_mod :=
  push_mod;
  rewrite! Zmod_mod;
  pull_mod.

Ltac mod_equality :=
  push_pull_mod;
  match goal with
  | |- ?x mod _ = ?y mod _ => ring_simplify x y
  end;
  try reflexivity.

(* Useful for debugging parenthesis around mod:
Notation "[ a ]_ m" := (a mod m) (at level 40, format "[ a ]_ m").
*)

Goal forall v B M lo, (v + B) mod M =
  ((((v + B) mod M - B - lo + B) mod M - B + B) mod M - B + ((lo + B) mod M - B) + B) mod M.
Proof.
  intros.
  mod_equality.
Qed.
