Require Import Program.Tactics.
Require Import lib.fiat_crypto_tactics.Not.
Require Import riscv.Decidable.
Require Import lib.LibTacticsMin.

Ltac destruct_one_match :=
  match goal with
  | [ |- context[match ?e with _ => _ end] ] =>
      is_var e; destruct e
  | [ |- context[match ?e with _ => _ end] ] =>
      let E := fresh "E" in destruct e eqn: E
  end.

Ltac destruct_one_dec_eq :=
  match goal with
  (* we use an explicit type T because otherwise the inferred type might differ *)
  | |- context[dec (@eq ?T ?t1 ?t2)] => destruct (dec (@eq T t1 t2)); [subst *|]
  end.

Ltac destruct_one_match_hyp_test type_test :=
  match goal with
  | H: context[match ?e with _ => _ end] |- _ =>
      is_var e;
      let T := type of e in type_test T;
      destruct e
  | H: context[if ?e then _ else _] |- _ =>
      is_var e;
      let T := type of e in type_test T;
      destruct e
  | H: context[match ?e with _ => _ end] |- _ =>
      let T := type of e in type_test T;
      let E := fresh "E" in destruct e eqn: E
  | H: context[if ?e then _ else _] |- _ =>
      let T := type of e in type_test T;
      let E := fresh "E" in destruct e eqn: E
  end.

Ltac destruct_one_match_hyp_of_type T :=
  destruct_one_match_hyp_test ltac:(fun t => unify t T).

Ltac destruct_one_match_hyp :=
  destruct_one_match_hyp_test ltac:(fun t => idtac).

Tactic Notation "inversions" hyp(H) := inverts H.

Ltac inversionss :=
  repeat match goal with
  | H: ?a = ?b |- _ => inverts H;
                       match goal with
                       | H': a = b |- _ => fail 1
                       | _ => idtac
                       end
  end.

Ltac repeat_at_least_once tac := tac; repeat tac.
Tactic Notation "repeatplus" tactic(t) := (repeat_at_least_once t).

Ltac destruct_pair_eqs := repeatplus match goal with
  | H: (_, _) = (_, _) |- _ => inversion H; clear H
  end.

Ltac ensure_new H :=
  let t := type of H in
  not (clear H; match goal with
                | A: t |- _ => idtac
                end).

Tactic Notation "forget" constr(X) "as" ident(y) := set (y:=X) in *; clearbody y.

Ltac destruct_products :=
  repeat match goal with
  | H: _ /\ _ |- _ => let Hl := fresh H "l" in let Hr := fresh H "r" in destruct H as [Hl Hr]
  | E: exists y, _ |- _ => let yf := fresh y in destruct E as [y E]
  end.

(** [pose proof defn], but only if no hypothesis of the same type exists.
    most useful for proofs of a proposition *)
Tactic Notation "unique" "pose" "proof" constr(defn) "as" ident(H) :=
  let T := type of defn in
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => pose proof defn as H
  end.

Ltac assert_is_type E :=
  let T := type of E in
  first
  [ unify T Set
  | unify T Prop
  | unify T Type
  (* this error is almost certainly a bug, so we let it bubble up with level 10000, instead
     of being swallowed by try, repeat, ||, etc *)
  | fail 10000 "type of" E "is" T "but should be Set, Prop or Type" ].

Ltac specialize_with E :=
  (* Catch errors such as E is something like "@name: NameWithEq -> Set" instead of "name: Set" *)
  assert_is_type E;
  repeat match goal with
  | H: forall (x: E), _, y: E |- _ =>
    match type of H with
    | DecidableEq E => fail 1
    | _ => let H' := fresh H y in unique pose proof (H y) as H'
    end
  end.

Tactic Notation "unique" "apply" constr(p) "in" "copy" "of" ident(H) :=
  let H' := fresh H "uac" in
  pose proof H as H';
  apply p in H';
  ensure_new H'.
