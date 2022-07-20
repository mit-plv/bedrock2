Require Coq.Lists.List. Import List.ListNotations.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require coqutil.Datatypes.List.
Require Import bedrock2.ListPushPullIf.

(* Stores a rewrite opportunity. Will not show up in proof terms, only used in Ltac *)
Inductive rewr(P: Type): Type :=
| mk_rewr(T: Type)(x y: T)(e: x = y)(ctx: T -> Type).
Existing Class rewr.

Lemma rewr_fw{T: Type}{lhs rhs: T}:
  lhs = rhs ->
  forall P : T -> Type, P lhs -> P rhs.
Proof.
  intros. subst. assumption.
Qed.

Lemma rewr_bw{T: Type}{lhs rhs: T}:
  lhs = rhs ->
  forall P : T -> Type, P rhs -> P lhs.
Proof.
  intros. subst. assumption.
Qed.

Ltac rewr_step_in H :=
  let t := type of H in
  lazymatch constr:(_ : rewr t) with
  | mk_rewr _ ?T ?x ?y ?e ?ctx  =>
      let r := constr:(@rewr_fw T x y e ctx) in
      apply r in H
  end.

Ltac mk_rewr equ ctx :=
  refine (mk_rewr _ _ _ _ equ ctx).

Module WordRingAutorewr.
  Ltac mkr orig ctx :=
    refine (mk_rewr _ _ orig _ _ ctx);
    ring_simplify;
    let new := lazymatch goal with |- ?new = _ => new end in
    tryif constr_eq orig new then fail "no simplification opportunity" else reflexivity.

  Ltac mk_word_ring_simplify_rewr P :=
    match P with
    | context C[@word.add ?wi ?wo ?x ?y] =>
        mkr (@word.add wi wo x y) (fun hole => ltac:(let r := context C[hole] in exact r))
    | context C[@word.sub ?wi ?wo ?x ?y] =>
        mkr (@word.sub wi wo x y) (fun hole => ltac:(let r := context C[hole] in exact r))
    | context C[@word.opp ?wi ?wo ?x] =>
        mkr (@word.opp wi wo x) (fun hole => ltac:(let r := context C[hole] in exact r))
    | context C[@word.mul ?wi ?wo ?x ?y] =>
        mkr (@word.mul wi wo x y) (fun hole => ltac:(let r := context C[hole] in exact r))
    end.

  #[export] Hint Extern 5 (rewr ?P) => mk_word_ring_simplify_rewr P : typeclass_instances.
End WordRingAutorewr.

Module HypAutorewr.
  Ltac term_size t acc :=
    lazymatch t with
    | S ?x => lazymatch isnatcst x with
              | true => constr:(S acc)
              | false => term_size x (S acc)
              end
    | Zpos ?p => lazymatch isPcst p with
                 | true => constr:(S acc)
                 | false => term_size p (S acc)
                 end
    | Zneg ?p => lazymatch isPcst p with
                 | true => constr:(S acc)
                 | false => term_size p (S acc)
                 end
    | Z0 => constr:(S acc)
    | ?f ?a => let r := term_size f (S acc) in term_size a r
    | _ => let __ := match constr:(O) with
                     | _ => is_var t
                     | _ => is_const t
                     end in
           constr:(S acc)
    end.

  Ltac mk_rewr_with_hyp P :=
    match goal with
    | E: ?lhs = ?rhs |- _ =>
        lazymatch P with
        | lhs = rhs => fail (* don't rewrite a hypothesis with itself *)
        | context C[lhs] =>
            let s1 := term_size lhs O in
            let s2 := term_size rhs O in
            lazymatch eval cbv in (Nat.ltb s2 s1) with true =>
              let ctx := constr:(fun hole => ltac:(let r := context C[hole] in exact r)) in
              refine (mk_rewr P _ lhs rhs E ctx)
            end
        end
    end.

  #[export] Hint Extern 3 (rewr ?P) => mk_rewr_with_hyp P : typeclass_instances.
End HypAutorewr.

Module ListNoSCAutorewr.
  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[@List.firstn ?A (S ?n) (?a :: ?l)] =>
        let ctx := constr:(fun hole => ltac:(let r := context C[hole] in exact r)) in
        refine (mk_rewr P (list A) _ _ (List.firstn_cons n a l) ctx)
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[@List.skipn ?A (S ?n) (?a :: ?l)] =>
        let ctx := constr:(fun hole => ltac:(let r := context C[hole] in exact r)) in
        refine (mk_rewr P (list A) _ _ (List.skipn_cons n a l) ctx)
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[@List.firstn ?A O ?l] =>
        let ctx := constr:(fun hole => ltac:(let r := context C[hole] in exact r)) in
        refine (mk_rewr P (list A) _ _ (List.firstn_O l) ctx)
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[@List.skipn ?A O ?l] =>
        let ctx := constr:(fun hole => ltac:(let r := context C[hole] in exact r)) in
        refine (mk_rewr P (list A) _ _ (List.skipn_O l) ctx)
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[((?a :: ?x) ++ ?y)%list] =>
        let ctx := constr:(fun hole => ltac:(let r := context C[hole] in exact r)) in
        refine (mk_rewr P _ _ _ (eq_sym (List.app_comm_cons x y a)) ctx)
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[([] ++ ?l)%list] =>
        let ctx := constr:(fun hole => ltac:(let r := context C[hole] in exact r)) in
        refine (mk_rewr P _ _ _ (List.app_nil_l l) ctx)
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[(?l ++ [])%list] =>
        let ctx := constr:(fun hole => ltac:(let r := context C[hole] in exact r)) in
        refine (mk_rewr P _ _ _ (List.app_nil_r l) ctx)
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[((?l ++ ?m) ++ ?n)%list] =>
        mk_rewr (eq_sym (List.app_assoc l m n))
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[List.firstn ?n (?l1 ++ ?l2)] =>
        mk_rewr (List.firstn_app n l1 l2)
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[List.firstn ?i (List.firstn ?j ?l)] =>
        mk_rewr (List.firstn_firstn l i j)
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[List.length (List.firstn ?n ?l)] =>
        mk_rewr (List.firstn_length n l)
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[List.firstn ?m (List.skipn ?n ?l)] =>
        mk_rewr (List.firstn_skipn_comm m n l)
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[List.length (?x :: ?xs)] =>
        let ctx := constr:(fun hole => ltac:(let r := context C[hole] in exact r)) in
        refine (mk_rewr P _ (List.length (x :: xs)) (S (List.length xs)) eq_refl ctx)
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[List.length (@nil ?A)] =>
        let ctx := constr:(fun hole => ltac:(let r := context C[hole] in exact r)) in
        refine (mk_rewr P _ (List.length (@nil A)) O eq_refl ctx)
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[List.firstn ?m (List.skipn ?n ?l)] =>
        mk_rewr (List.firstn_skipn_comm m n l)
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[List.nth ?i (List.skipn ?j ?l) ?d] =>
        mk_rewr (List.nth_skipn i j l d)
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[List.repeat ?a O] =>
        let ctx := constr:(fun hole => ltac:(let r := context C[hole] in exact r)) in
        refine (mk_rewr P _ (List.repeat a O) nil eq_refl ctx)
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[List.skipn ?n (?xs ++ ?ys)] =>
        mk_rewr (List.skipn_app n xs ys)
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[List.skipn ?n (List.skipn ?m ?xs)] =>
        mk_rewr (List.skipn_skipn n m xs)
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[List.unfoldn ?f 0 ?start] =>
        mk_rewr (List.unfoldn_0 f start)
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[List.unfoldn ?f (S ?n) ?start] =>
        mk_rewr (List.unfoldn_S f start n)
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.
End ListNoSCAutorewr.

Module PushPullIfAutorewr.
  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[if ?b then ?a else ?a] =>
        mk_rewr (if_same b a)
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[List.firstn ?n (if ?b then ?l1 else ?l2)] =>
        mk_rewr (pull_if_firstn b l1 l2 n)
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[List.length (if ?b then ?l1 else ?l2)] =>
        mk_rewr (pull_if_length b l1 l2)
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[List.skipn ?n (if ?b then ?l1 else ?l2)] =>
        mk_rewr (pull_if_skipn b l1 l2 n)
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[if ?b then ?l1 ++ ?l2 else ?r] =>
        mk_rewr (push_if_app_l b l1 l2 r)
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[if ?b then ?l else ?r1 ++ ?r2] =>
        mk_rewr (push_if_app_r b l r1 r2)
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.

  #[export] Hint Extern 1 (rewr ?P) =>
    lazymatch P with
    | context C[if ?b then [?a1] else [?a2]] =>
        mk_rewr (push_if_singleton b a1 a2)
                (fun hole => ltac:(let r := context C[hole] in exact r))
    end
  : typeclass_instances.
End PushPullIfAutorewr.

Module LiaSCAutorewr.
  #[export] Hint Extern 5 (rewr ?P) =>
    match P with
    | context C[word.unsigned (word.of_Z ?x)] =>
        let ctx := constr:(fun hole => ltac:(let r := context C[hole] in exact r)) in
        refine (mk_rewr P _ _ _ (word.unsigned_of_Z_nowrap x _) ctx); lia
    end
  : typeclass_instances.

  #[export] Hint Extern 5 (rewr ?P) =>
    match P with
    | context C[List.nth ?j (List.firstn ?i ?l) ?d] =>
        let ctx := constr:(fun hole => ltac:(let r := context C[hole] in exact r)) in
        refine (mk_rewr P _ _ _ (List.nth_firstn i l j d _) ctx); lia
    end
  : typeclass_instances.
End LiaSCAutorewr.

Require Import bedrock2.SepAutoArray bedrock2.ZnWords.

Module ZnWordsSCAutorewr.
  #[export] Hint Extern 10 (rewr ?P) =>
    match P with
    | context C[List.firstn ?n ?l] =>
        let ctx := constr:(fun hole => ltac:(let r := context C[hole] in exact r)) in
        refine (mk_rewr P _ _ _ (@List.firstn_all2 _ n l _) ctx);
        unfold List.upd, List.upds;
        list_length_rewrites_without_sideconds_in_goal;
        ZnWords
    end
  : typeclass_instances.

  #[export] Hint Extern 10 (rewr ?P) =>
    match P with
    | context C[List.firstn ?n ?l] =>
        let ctx := constr:(fun hole => ltac:(let r := context C[hole] in exact r)) in
        refine (mk_rewr P _ _ _ (List.firstn_eq_O n l _) ctx);
        unfold List.upd, List.upds;
        list_length_rewrites_without_sideconds_in_goal;
        ZnWords
    end
  : typeclass_instances.

  #[export] Hint Extern 10 (rewr ?P) =>
    match P with
    | context C[List.skipn ?n ?l] =>
        let ctx := constr:(fun hole => ltac:(let r := context C[hole] in exact r)) in
        refine (mk_rewr P _ _ _ (List.skipn_eq_O n l _) ctx);
        unfold List.upd, List.upds;
        list_length_rewrites_without_sideconds_in_goal;
        ZnWords
    end
  : typeclass_instances.

  #[export] Hint Extern 10 (rewr ?P) =>
    match P with
    | context C[List.skipn ?n ?l] =>
        let ctx := constr:(fun hole => ltac:(let r := context C[hole] in exact r)) in
        refine (mk_rewr P _ _ _ (@List.skipn_all2 _ n l _) ctx);
        unfold List.upd, List.upds;
        list_length_rewrites_without_sideconds_in_goal;
        ZnWords
    end
  : typeclass_instances.
End ZnWordsSCAutorewr.

Require Import bedrock2.groundcbv.

Ltac groundcbv_in H :=
  let t := type of H in
  let t' := groundcbv t in
  progress change t' in H.

Ltac autorew_in_hyps :=
  repeat match goal with
         | H: _ |- _ => rewr_step_in H || groundcbv_in H
         end.
