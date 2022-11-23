Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Datatypes.ZList.
Require Import bedrock2.WordNotations. Local Open Scope word_scope.

(* to encode a record as a function in Ltac1, we define its field names: *)
Inductive res_field_name :=
| NewTerm (* constr or uconstr *)
| EqProof (* constr or uconstr proving "old term = some term convertible to new term" *)
| DidSomething (* bool (constr) *)
| IsConvertible. (* bool (constr) *)

Ltac res_convertible new_term key :=
  lazymatch key with
  | NewTerm => new_term
  | EqProof => uconstr:(@eq_refl _ new_term)
  | DidSomething => constr:(true)
  | IsConvertible => constr:(true)
  end.

Ltac res_rewrite new_term eq_proof key :=
  lazymatch key with
  | NewTerm => new_term
  | EqProof => eq_proof
  | DidSomething => constr:(true)
  | IsConvertible => constr:(false)
  end.

Ltac res_nothing_to_simpl original_term key :=
  lazymatch key with
  | NewTerm => original_term
  | EqProof => uconstr:(@eq_refl _ original_term)
  | DidSomething => constr:(false)
  | IsConvertible => constr:(true)
  end.

(* original: term of shape (f a)
   f: constr
   r: result whose lhs is a *)
Ltac lift_res1 original f r :=
  lazymatch r DidSomething with
  | true =>
      let t := r NewTerm in
      lazymatch r IsConvertible with
      | true => res_convertible uconstr:(f t)
      | false => let pf := r EqProof in
                 res_rewrite uconstr:(f t) uconstr:(@f_equal _ _ f _ t pf)
      end
  | false => res_nothing_to_simpl original
  end.

(* original: term of shape (f a1 a2)
   f: constr
   r1: result whose lhs is a1
   r2: result whose lhs is a2 *)
Ltac lift_res2 original f r1 r2 :=
  let t1 := r1 NewTerm in
  let t2 := r2 NewTerm in
  lazymatch r1 DidSomething with
  | true =>
      lazymatch r1 IsConvertible with
      | true =>
          lazymatch r2 IsConvertible with
          | true => res_convertible uconstr:(f t1 t2)
          | false =>
              let pf1 := r1 EqProof in
              let pf2 := r2 EqProof in
              res_rewrite uconstr:(f t1 t2) uconstr:(@f_equal2 _ _ _ f _ t1 _ t2 pf1 pf2)
          end
      | false =>
          let pf1 := r1 EqProof in
          let pf2 := r2 EqProof in
          res_rewrite uconstr:(f t1 t2) uconstr:(@f_equal2 _ _ _ f _ t1 _ t2 pf1 pf2)
      end
  | false =>
      lazymatch r2 DidSomething with
      | true =>
          lazymatch r2 IsConvertible with
          | true => res_convertible uconstr:(f t1 t2)
          | false =>
              let pf2 := r2 EqProof in
              res_rewrite uconstr:(f t1 t2) uconstr:(@f_equal _ _ (f t1) _ t2 pf2)
          end
      | false => res_nothing_to_simpl original
      end
  end.

Lemma app_cong[A B: Type][f g: A -> B][x y: A]: f = g -> x = y -> f x = g y.
Proof. intros. subst. reflexivity. Qed.

(* original: term of shape (f a)
   r1: result whose lhs is f
   r2: result whose lhs is a *)
Ltac lift_res_app original r1 r2 :=
  let t1 := r1 NewTerm in
  let t2 := r2 NewTerm in
  lazymatch r1 DidSomething with
  | true =>
      lazymatch r1 IsConvertible with
      | true =>
          lazymatch r2 IsConvertible with
          | true => res_convertible uconstr:(t1 t2)
          | false =>
              let pf1 := r1 EqProof in
              let pf2 := r2 EqProof in
              res_rewrite uconstr:(t1 t2) uconstr:(@app_cong _ _ _ t1 _ t2 pf1 pf2)
          end
      | false =>
          let pf1 := r1 EqProof in
          let pf2 := r2 EqProof in
          res_rewrite uconstr:(t1 t2) uconstr:(@app_cong _ _ _ t1 _ t2 pf1 pf2)
      end
  | false =>
      lazymatch r2 DidSomething with
      | true =>
          lazymatch r2 IsConvertible with
          | true => res_convertible uconstr:(t1 t2)
          | false =>
              let pf2 := r2 EqProof in
              res_rewrite uconstr:(t1 t2) uconstr:(@f_equal _ _ t1 _ t2 pf2)
          end
      | false => res_nothing_to_simpl original
      end
  end.

Ltac chain_rewrite_res r1 r2 :=
  let t1 := r1 NewTerm in
  let pf1 := r1 EqProof in
  let t2 := r2 NewTerm in
  let pf2 := r2 EqProof in
  res_rewrite t2 uconstr:(@eq_trans _ _ t1 t2 pf1 pf2).

(* assumes rhs of r1 equals lhs of r2 *)
Ltac chain_res r1 r2 :=
  lazymatch r1 DidSomething with
  | true =>
      lazymatch r2 DidSomething with
      | true =>
          lazymatch r1 IsConvertible with
          | true =>
              lazymatch r2 IsConvertible with
              | true => let t2 := r2 NewTerm in res_convertible t2
              | false => r2
              end
          | false =>
              lazymatch r2 IsConvertible with
              | true => let t2 := r2 NewTerm in let pf := r1 EqProof in res_rewrite t2 pf
              | false => chain_rewrite_res r1 r2
              end
          end
      | false => r1
      end
  | false => r2
  end.

Ltac sidecond := xlia zchecker.

(* local_X_simpl tactics:
   Given a term with already simplified subterms, produce new simplified term and
   equality proof (or set flag indicating that it's convertible).
   Failing means no simplification opportunity. *)

Ltac local_zlist_simpl e :=
  match e with
  | List.from Z0 ?l => res_convertible l
  | @List.repeatz ?A _ Z0 => res_convertible uconstr:(@nil A)
  | List.app nil ?xs => res_convertible xs
  | List.app ?xs nil => res_rewrite xs uconstr:(List.app_nil_r xs)
  end.

Inductive expr_kind := WordRingExpr | ZRingExpr | OtherExpr.

Ltac expr_kind e :=
  lazymatch e with
  | Z.add _ _ => ZRingExpr
  | Z.sub _ _ => ZRingExpr
  | Z.mul _ _ => ZRingExpr
  | Z.opp _ => ZRingExpr
  | word.add _ _ => WordRingExpr
  | word.sub _ _ => WordRingExpr
  | word.mul _ _ => WordRingExpr
  | word.opp _ => WordRingExpr
  | _ => OtherExpr
  end.

Ltac local_ring_simplify parent e :=
  lazymatch expr_kind e with
  | parent => fail "nothing to do here because parent will be ring_simplified too"
  | _ => let rhs := open_constr:(_) in
         let x := fresh "x" in
         let pf := constr:(ltac:(intro x; progress ring_simplify; subst x; reflexivity)
                            : let x := rhs in e = x) in
         res_rewrite rhs pf
  end.

Goal forall (a b c: Z), a + b - 2 * a = c -> -a + b = c.
Proof.
  intros.
  lazymatch type of H with
  | ?e = _ =>
      let r := local_ring_simplify OtherExpr e in
      let rhs := r NewTerm in
      let pf := r EqProof in
      replace e with rhs in H by (symmetry; exact pf)
  end.
  exact H.
Abort.

Goal forall (a b: Z), True.
Proof.
  intros.
  assert_fails (
      idtac;
      let e := constr:(a + b) in
      let r := local_ring_simplify OtherExpr e in (* nothing to simplify (progress fails) *)
      idtac e).
Abort.

Ltac local_simpl_hook parent_kind e :=
  match constr:(Set) with
  | _ => local_zlist_simpl e
  | _ => local_ring_simplify parent_kind e
  | _ => res_nothing_to_simpl e
  end.

(* Nodes like eg (List.length (cons a (cons b (app (cons c xs) ys)))) can
   require an arbitrary number of simplification steps at the same node.

   ---> but that's more of a "push down List.length" algorithm, because once
   we have (len (cons c xs) + len ys), we need to recurse not at the current
   node, but down into the args of + !
Ltac saturate_local_simpl parent_kind e :=
  let r := local_simpl_hook parent_kind e in
  lazymatch r SimplAgain with
  | true => saturate_local_simpl parent_kind e'
  | false => r
  end.

-->
treat push-down separately:
- List.length/len
- word.unsigned
and don't treat them as push-down, but as "compute len/unsigned of given expression
in a bottom-up way"

*)

Ltac bottom_up_simpl parent_kind e :=
  lazymatch e with
  | Z.add ?x ?y => bottom_up_simpl_app2 e parent_kind ZRingExpr Z.add x y
  | Z.sub ?x ?y => bottom_up_simpl_app2 e parent_kind ZRingExpr Z.sub x y
  | Z.mul ?x ?y => bottom_up_simpl_app2 e parent_kind ZRingExpr Z.mul x y
  | Z.opp ?x    => bottom_up_simpl_app1 e parent_kind ZRingExpr Z.opp x
  | @word.add ?wi ?wo ?x ?y =>
      bottom_up_simpl_app2 e parent_kind WordRingExpr (@word.add wi wo) x y
  | @word.sub ?wi ?wo ?x ?y =>
      bottom_up_simpl_app2 e parent_kind WordRingExpr (@word.sub wi wo) x y
  | @word.mul ?wi ?wo ?x ?y =>
      bottom_up_simpl_app2 e parent_kind WordRingExpr (@word.mul wi wo) x y
  | @word.opp ?wi ?wo ?x    =>
      bottom_up_simpl_app1 e parent_kind WordRingExpr (@word.opp wi wo) x
  | ?f1 ?a1 =>
      lazymatch f1 with
      | ?f2 ?a2 =>
          lazymatch f2 with
          | _ _ => bottom_up_simpl_app e parent_kind f1 a1
          | _ => bottom_up_simpl_app2 e parent_kind OtherExpr f2 a2 a1
          end
      | _ => bottom_up_simpl_app1 e parent_kind OtherExpr f1 a1
      end
  | _ => local_simpl_hook parent_kind e
  end
with bottom_up_simpl_app1 e parent_kind current_kind f a1 :=
  let r1 := bottom_up_simpl current_kind a1 in
  let r := lift_res1 e f r1 in
  let e' := r NewTerm in
  let r' := local_simpl_hook parent_kind e' in
  chain_res r r'
with bottom_up_simpl_app2 e parent_kind current_kind f a1 a2 :=
  let r1 := bottom_up_simpl current_kind a1 in
  let r2 := bottom_up_simpl current_kind a2 in
  let r := lift_res2 e f r1 r2 in
  let e' := r NewTerm in
  let r' := local_simpl_hook parent_kind e' in
  chain_res r r'
with bottom_up_simpl_app e parent_kind f a :=
  let r1 := bottom_up_simpl OtherExpr f in
  let r2 := bottom_up_simpl OtherExpr a in
  let r := lift_res_app e r1 r2 in
  let e' := r NewTerm in
  let r' := local_simpl_hook parent_kind e' in
  chain_res r r'.

Section Tests.
  Set Ltac Backtrace.

  Context {word: word.word 32} {word_ok: word.ok word}.

  Add Ring wring : (Properties.word.ring_theory (word := word))
      ((* too expensive: preprocess [autorewrite with rew_word_morphism], *)
       morphism (Properties.word.ring_morph (word := word)),
       constants [Properties.word_cst]).

  Hypothesis P: Z -> Prop.
  Hypothesis Q: list Z -> Prop.

  Import ZList.List.ZIndexNotations. Local Open Scope zlist_scope.

  (*   List.repeatz (byte.of_Z \[b]) \[/[0]] ++ bs[\[/[0]]:] = bs *)

  Goal forall (b: Z) (bs: list Z), True.
    intros.
    let e := constr:(Q (List.repeatz b 0 ++ bs[0:])) in
    let r := bottom_up_simpl OtherExpr e in
    let e' := r NewTerm in
    let pf := r EqProof in
    idtac e'; idtac pf.
    (* TODO why is (nil ++ _) not simplified? *)
  Abort.

  (*

  (** ** Should work: *)

  Goal forall a: word, P (word.unsigned (a ^+ word.of_Z 8 ^- a) / 4) -> P 2.
  Proof.
    intros.
    ring_simplify ((a ^+ word.of_Z 8 ^- a)) in H.
  Abort.


  (** ** Not supported yet: *)

  Goal forall (z1 z2: Z) (y: word),
      word.of_Z (z1 + z2) ^- word.of_Z z1 = y ->
      word.of_Z z2 = y.
  Proof.
    intros. ring_simplify in H.
    (* only simplifies with preprocess [autorewrite with rew_word_morphism] *)
    autorewrite with rew_word_morphism in H.
    ring_simplify in H.
    exact H.
  Abort.

  Context (f: Z -> Z).

  Goal forall x y z1 z2: Z, x = f (z1 + z2) + y - f (z2 + z1) -> x = y.
  Proof.
    intros.
    (* no effect: *)
    ring_simplify (z1 + z2) in H.
    ring_simplify (z2 + z1) in H.
    (* has effect: *)
    ring_simplify (z1 + z2) (z2 + z1) in H.
    ring_simplify in H.
    assumption.
  Abort.
*)
End Tests.
