Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Datatypes.ZList.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.foreach_hyp.
Require Import Ltac2.Ltac2. Set Default Proof Mode "Classic".
Require Import bedrock2.WordNotations. Local Open Scope word_scope.

(* needed for compatibility with simplification strategies that choose not
   to simplify powers of 2 *)
Ltac is_Z_const e :=
  lazymatch e with
  | Z.pow ?x ?y =>
      lazymatch isZcst x with
      | true => lazymatch isZcst y with
                | true => constr:(true)
                | false => constr:(false)
                end
      | false => constr:(false)
      end
  | _ => isZcst e
  end.

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

(* original: term of shape (f (g a))
   f: constr
   g: constr
   r: result whose lhs is a *)
Ltac lift_res11 original f g r :=
  lazymatch r DidSomething with
  | true =>
      let t := r NewTerm in
      lazymatch r IsConvertible with
      | true => res_convertible uconstr:(f (g t))
      | false => let pf := r EqProof in
                 res_rewrite uconstr:(f (g t))
                             uconstr:(@f_equal _ _ (fun x => f (g x)) _ t pf)
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

Ltac bottom_up_simpl_sidecond_hook := lia. (* OR xlia zchecker if already zified *)

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

(* inh: inhabited instance
   l:   any number of cons followed by nil or an abstract tail
   i:   fully simplified Z literal
   Returns an element or a List.get with a smaller index *)
Ltac convertible_list_get inh l i :=
  lazymatch l with
  | nil => constr:(@Inhabited.default _ inh)
  | cons ?h ?t =>
      lazymatch i with
      | Z0 => h
      | Zpos _ => let j := eval cbv in (Z.pred i) in convertible_list_get inh t j
      | Zneg _ => constr:(@Inhabited.default _ inh)
      end
  | _ => constr:(@List.get _ inh l i)
  end.

(* l:   any number of cons followed by nil or an abstract tail
   i:   fully simplified Z literal
   Returns a prefix of l or a few cons followed by a List.upto with a smaller index,
   eg (a :: b :: c :: l)[:5] --> a :: b :: c :: (l[:2]) *)
Ltac convertible_list_upto i l :=
  lazymatch l with
  | nil => l
  | @cons ?A ?h ?t =>
      lazymatch i with
      | Zpos _ => let j := eval cbv in (Z.pred i) in
                  let r := convertible_list_upto j t in
                  constr:(@cons A h r)
      | _ => constr:(@nil A)
      end
  | _ => lazymatch i with
         | Zpos _ => constr:(List.upto i l)
         | Z0 => uconstr:(@nil _)
         | Zneg _ => uconstr:(@nil _)
         end
  end.

(* l:   any number of cons followed by nil or an abstract tail
   i:   fully simplified Z literal
   Returns a suffix of l or a List.from with a smaller index *)
Ltac convertible_list_from i l :=
  lazymatch l with
  | nil => l
  | @cons ?A ?h ?t =>
      lazymatch i with
      | Zpos _ => let j := eval cbv in (Z.pred i) in convertible_list_from j t
      | _ => l
      end
  | _ => lazymatch i with
         | Zpos _ => constr:(List.from i l)
         | Z0 => l
         | Zneg _ => l
         end
  end.

(* only works if l1 is made up of just cons and nil *)
Ltac append_concrete_list l1 l2 :=
  lazymatch l1 with
  | cons ?h ?t => let r := append_concrete_list t l2 in constr:(cons h r)
  | nil => l2
  end.

Ltac is_concrete_enough i l is_nonpos_concrete_enough :=
  lazymatch l with
  | nil => isZcst i
  | cons _ _ => isZcst i
  | _ => lazymatch i with
         | Z0 => is_nonpos_concrete_enough
         | Zneg _ => is_nonpos_concrete_enough
         | _ => constr:(false)
         end
  end.

Ltac local_zlist_simpl e :=
  match e with
  | @List.get ?A ?inh ?l ?i =>
      lazymatch is_concrete_enough i l false with
      | true => let x := convertible_list_get inh l i in res_convertible x
      end
  | @List.from ?A ?i ?l =>
      lazymatch is_concrete_enough i l true with
      | true => let l' := convertible_list_from i l in res_convertible l'
      | false =>
          match l with
          | List.from ?j ?ll =>
              res_rewrite (List.from (Z.add j i) ll)
                (List.from_from ll j i ltac:(bottom_up_simpl_sidecond_hook)
                                       ltac:(bottom_up_simpl_sidecond_hook))
          | _ => res_rewrite l
                   (List.from_beginning l i ltac:(bottom_up_simpl_sidecond_hook))
          | _ => res_rewrite (@nil A)
                   (List.from_pastend l i ltac:(bottom_up_simpl_sidecond_hook))
          end
      end
  | @List.upto ?A ?i ?l =>
      match is_concrete_enough i l true with
      | true => let l' := convertible_list_upto i l in res_convertible l'
      | false => res_rewrite (@nil A)
                   (List.upto_beginning l i ltac:(bottom_up_simpl_sidecond_hook))
      | false => res_rewrite l
                   (List.upto_pastend l i ltac:(bottom_up_simpl_sidecond_hook))
      end
  | @List.repeatz ?A _ Z0 => res_convertible uconstr:(@nil A)
  | List.app ?xs nil => res_rewrite xs uconstr:(List.app_nil_r xs)
  | List.app ?l1 ?l2 => let l := append_concrete_list l1 l2 in res_convertible l
  (* TODO Doesn't do anything for ((xs ++ ys) ++ zs)[i:] if i points into ys,
     and the subtraction created by from_app_discard_l should be simplified
     immediately rather than only in the next outermost iteration *)
  | List.from ?i (List.app ?l1 ?l2) =>
      res_rewrite (List.from (i - Z.of_nat (length l1)) l2)
                  (List.from_app_discard_l l1 l2 i ltac:(bottom_up_simpl_sidecond_hook))
  | List.upto ?i (List.app ?l1 ?l2) =>
      res_rewrite (List.upto i l1)
                  (List.upto_app_discard_r l1 l2 i ltac:(bottom_up_simpl_sidecond_hook))
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
  | _ => lazymatch is_Z_const e with
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

Ltac ring_simplify_res_forcing_progress e :=
  let rhs := open_constr:(_) in
  let x := fresh "x" in
  let pf := constr:(ltac:(intro x; progress ring_simplify; subst x; reflexivity)
                     : let x := rhs in e = x) in
  res_rewrite rhs pf.

Ltac ring_simplify_res_or_nothing_to_simpl e :=
  match constr:(Set) with
  | _ => ring_simplify_res_forcing_progress e
  | _ => res_nothing_to_simpl e
  end.

Ltac local_ring_simplify parent e :=
  lazymatch expr_kind e with
  | parent => fail "nothing to do here because parent will be ring_simplified too"
  | _ => let r := ring_simplify_res_forcing_progress e in
         let rhs := r NewTerm in
         let sz1 := ring_expr_size e in
         let sz2 := ring_expr_size rhs in
         let is_shrinking := eval cbv in (Z.ltb sz2 sz1) in
         lazymatch is_shrinking with
         | true => r
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
  match e with
  | ?f ?x ?y =>
      let __ := match constr:(Set) with
                | _ => is_const f; is_binary_Z_op f;
                       lazymatch e with
                       | Z.pow 2 _ => fail (* don't simplify *)
                       | _ => idtac
                       end
                end in
      lazymatch is_Z_const x with
      | true => lazymatch is_Z_const y with
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
      lazymatch is_Z_const x with
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
  lazymatch e with
  | @word.unsigned ?wi ?wo (word.of_Z ?x) =>
      res_rewrite x (@word.unsigned_of_Z_nowrap wi wo _ x
                       ltac:(bottom_up_simpl_sidecond_hook))
  end.

(* Can be customized with ::= *)
Ltac is_substitutable_rhs rhs :=
  first [ is_var rhs
        | is_const rhs
        | lazymatch is_Z_const rhs with true => idtac end
        | lazymatch rhs with
          | word.of_Z ?x => is_substitutable_rhs x
          | word.unsigned ?x => is_substitutable_rhs x
          end ].

Ltac local_subst_small_rhs e :=
  let rhs := progress_rdelta_var e in
  let __ := match constr:(Set) with
            | _ => is_substitutable_rhs rhs
            end in
  res_convertible rhs.

Ltac local_nonring_nonground_Z_simpl e :=
  lazymatch e with
  | Z.div ?x 1 => res_rewrite x (Z.div_1_r x)
  | Z.div (Z.mul ?x ?y) ?y =>
      res_rewrite x (Z.div_mul x y ltac:(bottom_up_simpl_sidecond_hook))
  end.

Ltac local_simpl_hook parent_kind e0 :=
  let e := constr:(e0) in (* <-- can't match on uconstr => quadratic retypechecking!*)
  match constr:(Set) with
  | _ => local_subst_small_rhs e
  | _ => local_zlist_simpl e
  | _ => local_ring_simplify parent_kind e
  | _ => local_ground_number_simpl e
  | _ => local_word_simpl e
  | _ => local_nonring_nonground_Z_simpl e
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

OR treat them as "local_simpl has access to an API to indicate how/where to continue
simplifying the new term"?

(would also work for (xs ++ ys)[i:] = xs[i:] ++ ys[i - len xs :],
where we have to indicate that (i - len xs) might need further simplification

set, app, repeatz, from, upto

    Lemma len_set: forall (l: list A) i x, 0 <= i < len l -> len (set l i x) = len l.
    Lemma len_app: forall (l1 l2: list A), len (l1 ++ l2) = len l1 + len l2.
    Lemma len_repeatz: forall (x: A) (n: Z), 0 <= n -> len (repeatz x n) = n.
    Lemma len_from: forall (l: list A) i, 0 <= i <= len l -> len (from i l) = len l - i.
    Lemma len_upto: forall (l: list A) i, 0 <= i <= len l -> len (upto i l) = i.

pre-order vs post-order traversal:
len lemmas need to be applied before descending recursively, while others
need to be applied after descending recursively

some need intertwined application:
len_from should first simplify i (so that it's already simplified in the sidecond solving),
then simplify (len l) in a reusable way so that it appears simplified in the sidecondition
and in the rhs, and then apply len_from, and then simplify locally the rhs
(simplified_len_l - simplified_i)

*)

Section SimplLen.
  Import List.ZIndexNotations. Local Open Scope zlist_scope.
  Context [A: Type].

  Lemma simpl_len_from: forall (l: list A) i i' n r,
      i = i' ->
      len l = n ->
      0 <= i' <= n ->
      n - i' = r ->
      len l[i:] = r.
  Proof. intros. subst. eapply List.len_from. assumption. Qed.

  Lemma simpl_len_from_pastend: forall (l: list A) i i' n,
      i = i' ->
      len l = n ->
      n <= i' ->
      len l[i:] = 0.
  Proof. intros. subst. rewrite List.from_pastend by assumption. reflexivity. Qed.

  Lemma simpl_len_from_negative: forall (l: list A) i i' n,
      i = i' ->
      len l = n ->
      i' <= 0 ->
      len l[i:] = n.
  Proof.
    intros. subst. unfold List.from. replace (Z.to_nat i') with O by lia. reflexivity.
  Qed.

  Lemma simpl_len_upto: forall (l: list A) i i' n,
      i = i' ->
      len l = n ->
      0 <= i' <= n ->
      len l[:i] = i'.
  Proof. intros. subst. eapply List.len_upto. assumption. Qed.

  Lemma simpl_len_upto_pastend: forall (l: list A) i i' n,
      i = i' ->
      len l = n ->
      n <= i' ->
      len l[:i] = n.
  Proof. intros. subst. rewrite List.upto_pastend by assumption. reflexivity. Qed.

  Lemma simpl_len_upto_negative: forall (l: list A) i i' n,
      i = i' ->
      len l = n ->
      i' <= 0 ->
      len l[:i] = 0.
  Proof.
    intros. subst. unfold List.upto. replace (Z.to_nat i') with O by lia. reflexivity.
  Qed.

  Lemma simpl_len_app: forall (l1 l2: list A) n,
      len l1 + len l2 = n ->
      len (l1 ++ l2) = n.
  Proof. intros. subst. eapply List.len_app. Qed.

  Lemma simpl_len_set: forall (l: list A) i i' n x,
      i = i' ->
      len l = n ->
      0 <= i' < n ->
      len l[i := x] = n.
  Proof. intros. subst. eapply List.len_set. assumption. Qed.

  Lemma simpl_len_repeatz: forall (x: A) (n n': Z),
      n = n' ->
      0 <= n' ->
      len (List.repeatz x n) = n'.
  Proof. intros. subst. eapply List.len_repeatz. assumption. Qed.

  Lemma simpl_len_repeatz_max: forall (x: A) (n n': Z),
      n = n' ->
      len (List.repeatz x n) = Z.max n' 0.
  Proof.
    intros. subst n'. destr (n <? 0).
    - unfold List.repeatz. replace (Z.to_nat n) with O by lia. simpl. lia.
    - replace (Z.max n 0) with n by lia. eapply List.len_repeatz. assumption.
  Qed.
End SimplLen.

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
  | Z.of_nat (@List.length ?A ?l) => simpl_len e A l
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
  chain_res r r'
with simpl_len e A x := (* e must be (len x) *)
  lazymatch x with
  | List.from ?i ?l =>
      let r_i := bottom_up_simpl OtherExpr i in
      let i' := r_i NewTerm in
      let pf_i := r_i EqProof in
      let r_len_l := bottom_up_simpl OtherExpr (Z.of_nat (List.length l)) in
      let len_l' := r_len_l NewTerm in
      let pf_len_l := r_len_l EqProof in
      match constr:(Set) with
      | _ => (* Case: index i is within bounds *)
          let sidecond := constr:(ltac:(bottom_up_simpl_sidecond_hook): 0 <= i' <= len_l') in
          let r_diff := ring_simplify_res_or_nothing_to_simpl (Z.sub len_l' i') in
          let diff := r_diff NewTerm in
          let pf_diff := r_diff EqProof in
          res_rewrite diff
            uconstr:(@simpl_len_from A l i i' len_l' diff pf_i pf_len_l sidecond pf_diff)
      | _ => (* Case: index i is too big *)
          let sidecond := constr:(ltac:(bottom_up_simpl_sidecond_hook): len_l' <= i') in
          res_rewrite Z0
            uconstr:(@simpl_len_from_pastend A i i' len_l' pf_i pf_len_l sidecond)
      | _ => (* Case: index i is too small *)
          let sidecond := constr:(ltac:(bottom_up_simpl_sidecond_hook): i' <= 0) in
          res_rewrite len_l'
            uconstr:(@simpl_len_from_negative A i i' len_l' pf_i pf_len_l sidecond)
      | _ => (* Case: unknown whether index is is within bounds, so the List.from remains *)
          let r_l := bottom_up_simpl OtherExpr l in
          let l' := r_l NewTerm in
          let r := lift_res2 x (@List.from A) r_i r_l in
          lift_res11 e Z.of_nat (@List.length A) r
      end
  | List.upto ?i ?l =>
      let r_i := bottom_up_simpl OtherExpr i in
      let i' := r_i NewTerm in
      let pf_i := r_i EqProof in
      let r_len_l := bottom_up_simpl OtherExpr (Z.of_nat (List.length l)) in
      let len_l' := r_len_l NewTerm in
      let pf_len_l := r_len_l EqProof in
      match constr:(Set) with
      | _ => (* Case: index i is within bounds *)
          let sidecond := constr:(ltac:(bottom_up_simpl_sidecond_hook): 0 <= i' <= len_l') in
          res_rewrite i' uconstr:(@simpl_len_upto A l i i' len_l' pf_i pf_len_l sidecond)
      | _ => (* Case: index i is too big *)
          let sidecond := constr:(ltac:(bottom_up_simpl_sidecond_hook): len_l' <= i') in
          res_rewrite len_l'
            uconstr:(@simpl_len_upto_pastend A i i' len_l' pf_i pf_len_l sidecond)
      | _ => (* Case: index i is too small *)
          let sidecond := constr:(ltac:(bottom_up_simpl_sidecond_hook): i' <= 0) in
          res_rewrite Z0
            uconstr:(@simpl_len_upto_negative A i i' len_l' pf_i pf_len_l sidecond)
      | _ => (* Case: unknown whether index is is within bounds, so the List.upto remains *)
          let r_l := bottom_up_simpl OtherExpr l in
          let l' := r_l NewTerm in
          let r := lift_res2 x (@List.upto A) r_i r_l in
          lift_res11 e Z.of_nat (@List.length A) r
      end

(* TODO
  Lemma simpl_len_app: forall (l1 l2: list A) n,
      len l1 + len l2 = n ->
      len (l1 ++ l2) = n.
  Lemma simpl_len_set: forall (l: list A) i i' n x,
      i = i' ->
      len l = n ->
      0 <= i' < n ->
      len l[i := x] = n.
*)

  | List.repeatz ?a ?n =>
      let r_n := bottom_up_simpl OtherExpr n in
      let n' := r_n NewTerm in
      let pf_n := r_n EqProof in
      match constr:(Set) with
      | _ => (* Case: n is provably nonnegative *)
          let sidecond := constr:(ltac:(bottom_up_simpl_sidecond_hook): 0 <= n') in
          res_rewrite n' uconstr:(@simpl_len_repeatz A a n n' pf_n sidecond)
      | _ => (* Case: n might be negative *)
          res_rewrite (Z.max n' Z0) uconstr:(@simpl_len_repeatz_max A a n n' pf_n)
      end
  | _ =>
      let r := bottom_up_simpl OtherExpr x in
      lift_res11 e Z.of_nat (@List.length A) r
  end.

Lemma rew_Prop_hyp: forall (P1 P2: Prop) (pf: P1 = P2), P1 -> P2.
Proof. intros. subst. assumption. Qed.

Lemma rew_Prop_goal: forall (P1 P2: Prop) (pf: P1 = P2), P2 -> P1.
Proof. intros. subst. assumption. Qed.

Ltac2 starts_with_double_underscore(i: ident) :=
  let s := Ident.to_string i in
  if Int.le 2 (String.length s) then
    if Int.equal (Char.to_int (String.get s 0)) 95 then
      Int.equal (Char.to_int (String.get s 1)) 95
    else false
  else false.

Ltac _starts_with_double_underscore :=
  ltac2:(i |- if starts_with_double_underscore (Option.get (Ltac1.to_ident i)) then ()
              else Control.backtrack_tactic_failure "identifier does not start with __").

Tactic Notation "starts_with_double_underscore" ident(i) :=
  _starts_with_double_underscore i.

Ltac bottom_up_simpl_in_hyp H :=
  let t := type of H in
  lazymatch type of t with
  | Prop => idtac
  | _ => fail "not a Prop"
  end;
  let r := bottom_up_simpl OtherExpr t in
  lazymatch r DidSomething with
  | false => fail "nothing to simplify"
  | true =>
      let pf := r EqProof in
      let t' := r NewTerm in
      eapply (rew_Prop_hyp t t' pf) in H
  end.

Ltac bottom_up_simpl_in_hyp_of_type H t :=
  lazymatch type of t with
  | Prop =>
      let r := bottom_up_simpl OtherExpr t in
      lazymatch r DidSomething with
      | false => idtac (* don't force progress *)
      | true =>
          let pf := r EqProof in
          let t' := r NewTerm in
          eapply (rew_Prop_hyp t t' pf) in H
      end
  | _ =>  idtac (* don't force progress *)
  end.

Ltac bottom_up_simpl_in_hyp_of_type_unless__ H t :=
  tryif starts_with_double_underscore H then idtac else bottom_up_simpl_in_hyp_of_type H t.

Ltac bottom_up_simpl_in_letbound_var x b _t :=
  let r := bottom_up_simpl OtherExpr b in
  match r DidSomething with
  | true =>
      let pf := r EqProof in
      let b' := r NewTerm in
      let y := fresh in rename x into y;
      pose (x := b');
      move x after y;
      replace y with x in * by (subst x y; symmetry; exact pf);
      clear y
  | _ => idtac (* might get here because `r DidSomething = false` or because
                  x appears in the type of other expressions and rewriting in the body of x
                  would lead to ill-typed terms *)
  end.

Ltac bottom_up_simpl_in_letbound_var_unless__ x b _t :=
  tryif starts_with_double_underscore x then idtac
  else bottom_up_simpl_in_letbound_var x b _t.

Ltac bottom_up_simpl_in_goal :=
  let t := lazymatch goal with |- ?g => g end in
  lazymatch type of t with
  | Prop => idtac
  | _ => fail "not a Prop"
  end;
  let r := bottom_up_simpl OtherExpr t in
  lazymatch r DidSomething with
  | false => fail "nothing to simplify"
  | true =>
      let pf := r EqProof in
      let t' := r NewTerm in
      eapply (rew_Prop_goal t t' pf)
  end.

Ltac bottom_up_simpl_in_hyps :=
  foreach_hyp bottom_up_simpl_in_hyp_of_type.
Ltac bottom_up_simpl_in_hyps_unless__ :=
  foreach_hyp bottom_up_simpl_in_hyp_of_type_unless__.

Ltac bottom_up_simpl_in_vars :=
  foreach_var bottom_up_simpl_in_letbound_var.
Ltac bottom_up_simpl_in_vars_unless__ :=
  foreach_var bottom_up_simpl_in_letbound_var_unless__.

Ltac bottom_up_simpl_in_hyps_and_vars :=
  bottom_up_simpl_in_hyps; bottom_up_simpl_in_vars.
Ltac bottom_up_simpl_in_hyps_and_vars_unless__ :=
  bottom_up_simpl_in_hyps_unless__; bottom_up_simpl_in_vars_unless__.

Ltac bottom_up_simpl_in_all :=
  bottom_up_simpl_in_hyps; bottom_up_simpl_in_vars;
  try bottom_up_simpl_in_goal.
Ltac bottom_up_simpl_in_all_unless__ :=
  bottom_up_simpl_in_hyps_unless__; bottom_up_simpl_in_vars_unless__;
  try bottom_up_simpl_in_goal.

Local Hint Mode Word.Interface.word - : typeclass_instances.

Section Tests.
  Set Ltac Backtrace.

  Goal forall a: Z, a = a + 0 -> a = a + 0 -> True.
    intros ? __pure_E E.
    bottom_up_simpl_in_all_unless__.
  Abort.

  Context {word: word.word 32} {word_ok: word.ok word}.

  Add Ring wring : (Properties.word.ring_theory (word := word))
      ((* too expensive: preprocess [autorewrite with rew_word_morphism], *)
       morphism (Properties.word.ring_morph (word := word)),
       constants [Properties.word_cst]).

  Hypothesis P: Z -> Prop.
  Hypothesis Q: list Z -> Prop.

  Import ZList.List.ZIndexNotations. Local Open Scope zlist_scope.

  Ltac refl :=
    lazymatch goal with
    | |- ?x = ?x => reflexivity
    end.

  Goal forall (n b: Z) (bs: list Z),
      Q (List.repeatz b (n - n) ++ bs[2/4:] ++
           List.repeatz b (word.unsigned (word.of_Z 0))) = Q bs.
  Proof.
    intros. bottom_up_simpl_in_goal. refl.
  Qed.

  Goal forall (byte_of_Z: Z -> Byte.byte) (b: word) (bs: list Byte.byte),
      List.repeatz (byte_of_Z \[b]) \[/[0]] ++ bs[\[/[0]]:] = bs.
  Proof.
    intros. bottom_up_simpl_in_goal. refl.
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

  Goal forall a b c: Z, a + a + a = b -> a + a + a = c -> b = c.
  Proof.
    intros. bottom_up_simpl_in_hyps. rewrite <- H, H0. refl.
  Abort.

  Goal forall mtvec_base: Z,
      (word.add (word.add (word.mul (word.of_Z 4) (word.of_Z mtvec_base)) (word.of_Z 144))
         (word.of_Z (4 * Z.of_nat (S (Z.to_nat (word.unsigned (word.sub (word.add
            (word.mul (word.of_Z 4) (word.of_Z (Z.of_nat 29))) (word.add
               (word.mul (word.of_Z 4) (word.of_Z mtvec_base)) (word.of_Z 28)))
                  (word.add (word.mul (word.of_Z 4) (word.of_Z mtvec_base))
                     (word.of_Z 144))) / 4)))))) = /[4] ^* /[mtvec_base] ^+ /[148].
  Proof.
    intros. bottom_up_simpl_in_goal. refl.
  Qed.

  Goal forall (stack_hi: Z) (f: word -> Z),
      f (word.add (word.of_Z stack_hi) (word.of_Z (-128))) =
      f (word.sub (word.of_Z stack_hi) (word.of_Z 128)).
  Proof.
    intros. bottom_up_simpl_in_goal. refl.
  Qed.

  Goal forall (T: Type) (l: list T) (a b c: T),
      (a :: b :: c :: l)[:5] = a :: b :: c :: l[:2].
  Proof.
    intros. bottom_up_simpl_in_goal. refl.
  Abort.

  Goal forall (A: Type) (l: list A) (x y z: A),
      ([|x; y|] ++ l)[:2] ++ ([|x; y; z|] ++ l)[2:] = x :: y :: z :: l.
  Proof.
    intros. bottom_up_simpl_in_goal. refl.
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

End Tests.
