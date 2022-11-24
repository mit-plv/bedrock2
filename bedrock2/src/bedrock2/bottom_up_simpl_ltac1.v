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

Ltac bottomup_simpl_sidecond_hook := lia. (* OR xlia zchecker if already zified *)

(* local_X_simpl tactics:
   Given a term with already simplified subterms, produce new simplified term and
   equality proof (or set flag indicating that it's convertible).
   Failing means no simplification opportunity. *)

Goal forall (f: Z -> Z), True.
  intros.
  let t := uconstr:(f 1) in
  lazymatch constr:(t) with (* <-- constr:() is needed because we can't match on uconstr *)
  | ?a ?b => idtac a
  end.
Abort.

Ltac local_zlist_simpl e :=
  match constr:(e) with (* <-- can't match on uconstr => quadratic retypechecking!*)
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

Ltac non_ring_expr_size e :=
  lazymatch e with
  | Zneg _ => uconstr:(2)
  | _ => lazymatch isZcst e with
         | true => uconstr:(1)
         | false => uconstr:(2)
         end
  end.

Ltac ring_expr_size e :=
  let r1 x :=
    let s := ring_expr_size x in uconstr:(1 + s) in
  let r2 x y :=
    let s1 := ring_expr_size x in let s2 := ring_expr_size y in uconstr:(1 + s1 + s2) in
  lazymatch e with
  | Z.add ?x ?y => r2 x y
  | Z.sub ?x ?y => r2 x y
  | Z.mul ?x ?y => r2 x y
  | Z.opp ?x => r1 x
  | word.add ?x ?y => r2 x y
  | word.sub ?x ?y => r2 x y
  | word.mul ?x ?y => r2 x y
  | word.opp ?x => r1 x
  | word.of_Z ?x => non_ring_expr_size x
  | _ => non_ring_expr_size e
  end.

Ltac local_ring_simplify parent e0 :=
  let e := constr:(e0) in (* <-- can't match on uconstr => quadratic retypechecking!*)
  lazymatch expr_kind e with
  | parent => fail "nothing to do here because parent will be ring_simplified too"
  | _ => let rhs := open_constr:(_) in
         let x := fresh "x" in
         let pf := constr:(ltac:(intro x; progress ring_simplify; subst x; reflexivity)
                            : let x := rhs in e = x) in
         let sz1 := ring_expr_size e in
         let sz2 := ring_expr_size rhs in
         let is_shrinking := eval cbv in (Z.ltb sz2 sz1) in
         lazymatch is_shrinking with
         | true => res_rewrite rhs pf
         | false => fail "ring_simplify does not shrink the expression size"
         end
  end.

Ltac is_unary_Z_op op :=
  lazymatch op with
  | Z.of_nat => idtac
  | Z.to_nat => idtac
  | Z.succ => idtac
  | Z.pred => idtac
  | Z.opp => idtac
  | Z.log2 => idtac
  | Z.log2_up => idtac
  end.

Ltac is_unary_nat_op op :=
  lazymatch op with
  | Nat.succ => idtac
  | Nat.pred => idtac
  end.

Ltac is_binary_Z_op op :=
  lazymatch op with
  | Z.add => idtac
  | Z.sub => idtac
  | Z.mul => idtac
  | Z.div => idtac
  | Z.modulo => idtac
  | Z.quot => idtac
  | Z.rem => idtac
  | Z.pow => idtac
  | Z.shiftl => idtac
  | Z.shiftr => idtac
  | Z.land => idtac
  | Z.lor => idtac
  | Z.lxor => idtac
  | Z.ldiff => idtac
  | Z.clearbit => idtac
  | Z.setbit => idtac
  | Z.min => idtac
  | Z.max => idtac
  end.

Ltac is_binary_nat_op op :=
  lazymatch op with
  | Nat.add => idtac
  | Nat.sub => idtac
  | Nat.mul => idtac
  | Nat.div => idtac
  | Nat.min => idtac
  | Nat.max => idtac
  end.

Ltac local_ground_number_simpl e :=
  match constr:(e) with (* <-- can't match on uconstr => quadratic retypechecking!*)
  | ?f ?x ?y =>
      let __ := match constr:(Set) with
                | _ => is_const f; is_binary_Z_op f
                end in
      lazymatch isZcst x with
      | true => lazymatch isZcst y with
                | true => let v := eval cbv in e in res_convertible v
                end
      end
  | ?f ?x ?y =>
      let __ := match constr:(Set) with
                | _ => is_const f; is_binary_nat_op f
                end in
      lazymatch isnatcst x with
      | true => lazymatch isnatcst y with
                | true => let v := eval cbv in e in res_convertible v
                end
      end
  | ?f ?x =>
      let __ := match constr:(Set) with
                | _ => is_const f; is_unary_Z_op f
                end in
      lazymatch isZcst x with
      | true => let v := eval cbv in e in res_convertible v
      end
  | ?f ?x =>
      let __ := match constr:(Set) with
                | _ => is_const f; is_unary_nat_op f
                end in
      lazymatch isnatcst x with
      | true => let v := eval cbv in e in res_convertible v
      end
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

Ltac local_word_simpl e :=
  lazymatch constr:(e) with (* <-- can't match on uconstr => quadratic retypechecking!*)
  | @word.unsigned ?wi ?wo (word.of_Z ?x) =>
      res_rewrite x (@word.unsigned_of_Z_nowrap wi wo _ x
                       ltac:(bottomup_simpl_sidecond_hook))
  end.

Ltac local_simpl_hook parent_kind e :=
  match constr:(Set) with
  | _ => local_zlist_simpl e
  | _ => local_ring_simplify parent_kind e
  | _ => local_ground_number_simpl e
  | _ => local_word_simpl e
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

Lemma rew_Prop_hyp: forall (P1 P2: Prop) (pf: P1 = P2), P1 -> P2.
Proof. intros. subst. assumption. Qed.

Lemma rew_Prop_goal: forall (P1 P2: Prop) (pf: P1 = P2), P2 -> P1.
Proof. intros. subst. assumption. Qed.

Ltac bottom_up_simpl_in_hyp H :=
  let t := type of H in
  let r := bottom_up_simpl OtherExpr t in
  lazymatch r DidSomething with
  | false => fail "nothing to simplify"
  | true =>
      let pf := r EqProof in
      let t' := r NewTerm in
      eapply (rew_Prop_hyp t t' pf) in H
  end.

Ltac bottom_up_simpl_in_goal :=
  let t := lazymatch goal with |- ?g => g end in
  let r := bottom_up_simpl OtherExpr t in
  lazymatch r DidSomething with
  | false => fail "nothing to simplify"
  | true =>
      let pf := r EqProof in
      let t' := r NewTerm in
      eapply (rew_Prop_goal t t' pf)
  end.

Local Hint Mode Word.Interface.word - : typeclass_instances.

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

  Goal forall (n b: Z) (bs: list Z),
      Q (List.repeatz b (n - n) ++ bs[2/4:] ++
           List.repeatz b (word.unsigned (word.of_Z 0))) = Q bs.
  Proof.
    intros. bottom_up_simpl_in_goal. reflexivity.
  Qed.

  Goal forall (byte_of_Z: Z -> Byte.byte) (b: word) (bs: list Byte.byte),
      List.repeatz (byte_of_Z \[b]) \[/[0]] ++ bs[\[/[0]]:] = bs.
  Proof.
    intros. bottom_up_simpl_in_goal. reflexivity.
  Qed.

  Goal forall a: word, P (word.unsigned (a ^+ word.of_Z 8 ^- a) / 4) -> P 2.
  Proof.
    intros. bottom_up_simpl_in_hyp H. exact H.
  Qed.

  Goal forall a b: Z, (a + a, a + 1) = (2 * a, 1 + b) -> (2 * a, a + 1) = (2 * a, 1 + b).
  Proof.
    (* should not do simplifications that only reorder / don't decrease the size *)
    intros. bottom_up_simpl_in_hyp H.
    exact H.
  Abort.

  Goal forall mtvec_base: Z,
      (word.add (word.add (word.mul (word.of_Z 4) (word.of_Z mtvec_base)) (word.of_Z 144))
         (word.of_Z (4 * Z.of_nat (S (Z.to_nat (word.unsigned (word.sub (word.add
            (word.mul (word.of_Z 4) (word.of_Z (Z.of_nat 29))) (word.add
               (word.mul (word.of_Z 4) (word.of_Z mtvec_base)) (word.of_Z 28)))
                  (word.add (word.mul (word.of_Z 4) (word.of_Z mtvec_base))
                     (word.of_Z 144))) / 4)))))) = /[4] ^* /[mtvec_base] ^+ /[148].
  Proof.
    intros. bottom_up_simpl_in_goal. reflexivity.
  Qed.

  Goal forall (stack_hi: Z) (f: word -> Z),
      f (word.add (word.of_Z stack_hi) (word.of_Z (-128))) =
      f (word.sub (word.of_Z stack_hi) (word.of_Z 128)).
  Proof.
    intros. bottom_up_simpl_in_goal. reflexivity.
  Qed.

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

End Tests.
