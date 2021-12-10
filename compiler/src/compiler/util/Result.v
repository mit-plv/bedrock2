(* Almost everyone importing this file will need strings in their error messages *)
Require Export Coq.Strings.String. Open Scope string_scope.

Inductive dlist: Type :=
| dnil
| dcons{T: Type}(head: T)(tail: dlist).

Inductive result{A: Type}: Type :=
| Success(a: A)
| Failure(msg: dlist).
Arguments result: clear implicits.

Declare Scope error_scope.
Open Scope error_scope.

Notation "'error:(' x )" := (Failure (dcons x dnil))
  (at level 0, x at level 0, format "'error:(' x )")
  : error_scope.

Notation "'error:(' x y .. z )" := (Failure (dcons x (dcons y .. (dcons z dnil) ..)))
  (at level 0, x at level 0, y at level 0, z at level 0, format "'error:(' x  y  ..  z )")
  : error_scope.

Goal @id (result nat) error:(4 "is not a" bool) =
     Failure (dcons 4 (dcons "is not a" (dcons bool dnil))).
Proof. reflexivity. Abort.

Goal error:("just one string") = @Failure nat (dcons "just one string" dnil).
Proof. reflexivity. Abort.

Goal (fun (x: option nat) =>
        match x with
        | Some v => Success v
        | None => error:("got" x "instead of" (@Some nat))
        end) None <> Success 0.
Proof. cbv. congruence. Abort.

(* Note: won't parse if we remove the space after the colon *)
Goal forall (error: (list nat)), nil = (error: (list nat)). Abort.

Module result.
  Definition of_option{A: Type}(o: option A): result A :=
    match o with
    | Some a => Success a
    | None => error:((option A) "was" o)
    end.
End result.

Module ResultMonadNotations.
  Declare Scope result_monad_scope.
  Open Scope result_monad_scope.

  Notation "' pat <- c1 ;; c2" :=
    (match c1 with
     | Success pat => c2
     | Failure e => Failure e
     end)
    (at level 60, pat pattern, c1 at next level, right associativity) : result_monad_scope.

  Notation "x <- c1 ;; c2" :=
    (match c1 with
     | Success x => c2
     | Failure e => Failure e
     end)
    (at level 60, c1 at next level, right associativity) : result_monad_scope.

  Notation "c1 ;; c2" :=
    (match c1 with
     | Success _ => c2
     | Failure e => Failure e
     end)
    (at level 60, right associativity) : result_monad_scope.
End ResultMonadNotations.

Module List.
  Import ResultMonadNotations.
  Section WithA.
    Context {A: Type}.

    Fixpoint all_success(rs : list (result A)): result (list A) :=
      match rs with
      | nil => Success nil
      | cons r rest => x <- r;; xs <- all_success rest;; Success (cons x xs)
      end.

    Lemma length_all_success: forall {l1: list (result A)} {l2: list A},
        all_success l1 = Success l2 ->
        List.length l2 = List.length l1.
    Proof.
      induction l1; cbn; intros.
      { inversion H. trivial. }
      { case a in *; try inversion H.
        case (all_success l1) in *; try inversion H.
        subst. cbn. eapply f_equal, IHl1; trivial. }
    Qed.
  End WithA.
End List.

Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Tactics.destr.

Module map.
  Import ResultMonadNotations.

  Section WithMap.
    Context {key value : Type} {map : map.map key value} {map_ok : map.ok map}
            {keqb: key -> key -> bool} {keqb_spec: EqDecider keqb}.

    Definition forall_success(f: key -> value -> result unit): map -> result unit :=
      map.fold (fun res k v => res;; f k v) (Success tt).

    Lemma get_forall_success: forall f m,
        forall_success f m = Success tt -> forall k v, map.get m k = Some v -> f k v = Success tt.
    Proof.
      unfold forall_success. intros f m.
      eapply map.fold_spec; intros.
      - rewrite map.get_empty in H0. discriminate.
      - fwd. rewrite map.get_put_dec in H2. destr (keqb k k0); fwd; eauto.
    Qed.
  End WithMap.

  Section WithTwoMaps.
    Context {K V1 V2: Type}{M1: map.map K V1}{M2: map.map K V2}
            {keqb: K -> K -> bool} {keqb_spec: EqDecider keqb}
            {OK1: map.ok M1} {OK2: map.ok M2}.

    Definition try_map_values(f: V1 -> result V2): M1 -> result M2 :=
      map.fold (fun acc_res k v1 => acc <- acc_res;; v2 <- f v1;; Success (map.put acc k v2))
               (Success map.empty).

    Lemma try_map_values_fw(f: V1 -> result V2)(m1: M1)(m2: M2):
        try_map_values f m1 = Success m2 ->
        forall (k: K) (v1: V1),
        map.get m1 k = Some v1 ->
        exists v2, f v1 = Success v2 /\ map.get m2 k = Some v2.
    Proof.
      unfold try_map_values. revert m2.
      eapply map.fold_spec; intros.
      - rewrite map.get_empty in H0. discriminate.
      - fwd.
        rewrite map.get_put_dec. rewrite map.get_put_dec in H2.
        destr (keqb k k0); fwd; eauto.
    Qed.

    Lemma try_map_values_bw(f: V1 -> result V2)(m1: M1)(m2: M2):
        try_map_values f m1 = Success m2 ->
        forall (k: K) (v2: V2),
        map.get m2 k = Some v2 ->
        exists v1, f v1 = Success v2 /\ map.get m1 k = Some v1.
    Proof.
      unfold try_map_values. revert m2.
      eapply map.fold_spec; intros.
      - fwd. rewrite map.get_empty in H0. discriminate.
      - fwd.
        rewrite map.get_put_dec. rewrite map.get_put_dec in H2.
        destr (keqb k k0); fwd; eauto.
    Qed.
  End WithTwoMaps.
End map.
