From Coq Require Import ZArith. Local Open Scope Z_scope.
From Coq Require Import Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Datatypes.ZList.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.foreach_hyp.
Require Import bedrock2.WordNotations. Local Open Scope word_scope.
Require Import bedrock2.cancel_div_ltac1.

(* needed for compatibility with simplification strategies that choose not
   to simplify powers of 2 *)
Ltac is_Z_const e :=
  lazymatch e with
  | Z.pow ?x ?y =>
      lazymatch isZcst x with
      | true => isZcst y
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

Module Import res.
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
End res.

Module (*Import*) res_debug.
  Ltac res_convertible new_term :=
    let __ := match constr:(Set) with
              | _ => idtac "convertible to" new_term
              end in
    fun key =>
    lazymatch key with
    | NewTerm => new_term
    | EqProof => uconstr:(@eq_refl _ new_term)
    | DidSomething => constr:(true)
    | IsConvertible => constr:(true)
    end.

  Ltac res_rewrite new_term eq_proof :=
    let __ := (let t := type of eq_proof in
               lazymatch eval cbv zeta in t with
               | ?l = ?r => idtac l "-->" r
               | _ => idtac "weird eq_proof type:" t
               end) in
    fun key =>
    lazymatch key with
    | NewTerm => new_term
    | EqProof => eq_proof
    | DidSomething => constr:(true)
    | IsConvertible => constr:(false)
    end.

  Ltac res_nothing_to_simpl original_term :=
    (*
    let __ := match constr:(Set) with
              | _ => idtac "nothing to simpl in" original_term
              end in
    *)
    fun key =>
    lazymatch key with
    | NewTerm => original_term
    | EqProof => uconstr:(@eq_refl _ original_term)
    | DidSomething => constr:(false)
    | IsConvertible => constr:(true)
    end.
End res_debug.

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

(* marker to make proof terms more readable *)
Definition xlia(P: Prop){pf: P}: P := pf.

Ltac debug_sidecond :=
  lazymatch goal with
  | |- ?g => idtac g
  end;
  time "Zify.zify" Zify.zify;
  refine (@xlia _ _);
  time "xlia zchecker" xlia zchecker.

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

Module List.
  Import List.ZIndexNotations. Local Open Scope zlist_scope.

  (* Given `e` of type `list A`, returns `xss` of type `list (list A)` such that
     `List.apps xss` is convertible to `e`, and as long as possible.
     (Side question: What would it take to prove such a spec?) *)
  Ltac reify_apps e :=
    lazymatch e with
    | List.app ?xs ?ys => let r := reify_apps ys in constr:(cons xs r)
    | _ => constr:([|e|])
    end.

  Goal forall l: list Z, True.
    intros.
    lazymatch reify_apps ([|1; 2|] ++ ([|3|] ++ [|4|]) ++ (l ++ [|5|])) with
    | [|[|1; 2|]; [|3|] ++ [|4|]; l; [|5|]|] => idtac
    end.
  Abort.

  Section WithA.
    Context [A: Type].

    (* TODO begin move *)
    Lemma upto_app: forall (i: Z) (l1 l2 : list A),
        List.upto i (l1 ++ l2) = List.upto i l1 ++ List.upto (i - len l1) l2.
    Proof. unfold List.upto. intros. rewrite List.firstn_app. f_equal. f_equal. lia. Qed.

    (* Note: the symmetric version of this lemma, ie
         forall (i j: Z) (l: list A), i <= j -> l[:i][:j] = l[:i]
       is a special case of List.upto_pastend *)
    Lemma upto_upto_subsume: forall (i j: Z) (l: list A), j <= i -> l[:i][:j] = l[:j].
    Proof. unfold List.upto. intros. rewrite List.firstn_firstn. f_equal. lia. Qed.
    (* TODO end move *)

    (* Same as List.concat, but does not result in a trailing `++ nil` when unfolded *)
    Fixpoint apps(xss: list (list A)): list A :=
      match xss with
      | nil => nil
      | ys :: nil => ys
      | h :: t => h ++ apps t
      end.

    Lemma apps_concat: forall (xss: list (list A)), apps xss = List.concat xss.
    Proof.
      induction xss. 1: reflexivity.
      simpl. rewrite <- IHxss.
      destruct xss; try reflexivity.
      simpl. symmetry. apply List.app_nil_r.
    Qed.

    Definition cbn_app: list (list A) -> list (list A) -> list (list A) :=
      Eval unfold List.app in @List.app (list A).

    Lemma reassoc_app: forall (xss yss: list (list A)) (xs ys zs: list A),
        apps xss = xs ->
        apps yss = ys ->
        apps (cbn_app xss yss) = zs ->
        List.app xs ys = zs.
    Proof.
      intros. subst. rewrite 3apps_concat. change cbn_app with (@List.app (list A)).
      symmetry. apply List.concat_app.
    Qed.

    Definition cbn_firstn: nat -> list (list A) -> list (list A) :=
      Eval unfold List.firstn in @List.firstn (list A).

    Definition cbn_dropRight(n: nat)(ls: list (list A)): list (list A) :=
      Eval unfold List.length, Nat.sub, List.firstn in
        List.firstn (Nat.sub (List.length ls) n) ls.

    Definition cbn_skipn: nat -> list (list A) -> list (list A) :=
      Eval unfold List.skipn in @List.skipn (list A).

    Fixpoint cbn_len_sum(xss: list (list A)): Z :=
      match xss with
      | nil => 0
      | h :: t => len h + cbn_len_sum t
      end.

    (* alternative to try out: zipper style: reversed left list of lists *)

    Lemma upto_apps0: forall n i (xs: list A) (xss: list (list A))
                            (ys: list A) (yss: list (list A)),
        i <= cbn_len_sum (cbn_firstn n xss) ->
        cbn_firstn n xss = yss ->
        apps xss = xs ->
        apps yss = ys ->
        List.upto i xs = List.upto i ys.
    Proof.
      intros. subst. rewrite 2apps_concat. revert i xss H.
      induction n; intros; simpl in *.
      - rewrite 2List.upto_beginning; trivial.
      - destruct xss. 1: reflexivity.
        simpl in *.
        do 2 rewrite upto_app. f_equal. apply IHn. lia.
    Qed.

    Lemma upto_apps: forall n i (xs: list A) (xss: list (list A))
                            (ys: list A) (yss: list (list A)),
        i <= cbn_len_sum (cbn_dropRight n xss) ->
        cbn_dropRight n xss = yss ->
        apps xss = xs ->
        apps yss = ys ->
        List.upto i xs = List.upto i ys.
    Proof. unfold cbn_dropRight. intros. eapply upto_apps0; eassumption. Qed.
  End WithA.
End List.

Section SimplListLemmas.
  Import List.ZIndexNotations. Local Open Scope zlist_scope.
  Context [A: Type].

  (* A list slice can be expressed in two ways:
     - indexed: xs[i:j], which is shorthand for xs[:j][i:]
     - sized: xs[i:][:n]
     Which one we prefer depends on the AST size of the second number:
     Sometimes, it's easier to express the end index, but sometimes, it's
     easier to express the size. *)

  Lemma indexed_slice_to_sized_slice: forall (l: list A) i j n,
      0 <= i <= j ->
      j - i = n ->
      l[i:j] = l[i:][:n].
  Proof.
    intros. subst. rewrite List.from_upto_comm by lia. f_equal. f_equal. lia.
  Qed.

  Lemma sized_slice_to_indexed_slice: forall (l: list A) i n j,
      0 <= i /\ 0 <= n ->
      i + n = j ->
      l[i:][:n] = l[i:j].
  Proof.
    intros * [? ?] **. subst. apply List.from_upto_comm; assumption.
  Qed.
End SimplListLemmas.

(* gen_stmt: ltac function taking a nat and returning a Prop
   tac: tactic to prove stmt, takes a dummy unit
   lower: min n to try
   upper: one more than max n to try *)
Ltac max_n_st gen_stmt tac lower upper :=
  let rec loop n :=
    let stmt := gen_stmt n in
    match constr:(Set) with
    | _ => constr:(ltac:(tac tt) : stmt)
    | _ => lazymatch n with
           | lower => fail "stmt does not hold for any n within the bounds"
           | S ?m => loop m
           | _ => fail "expected a nat above" lower ", got" n
           end
    end in
  lazymatch upper with
  | S ?n => loop n
  | _ => fail "upper should be a nonzero nat"
  end.

Goal forall (b: nat), b = 12%nat -> (3 * 3 < b)%nat.
  intros.
  let tac := (fun _ =>
    lazymatch goal with
    | |- ?g => idtac (*g*)
    end;
    cbn; lia) in
  let pf := max_n_st ltac:(fun n => constr:((n * n < b)%nat)) tac 2%nat 7%nat in
  pose proof pf as A.
  exact A.
Abort.

(* returns a proof whose LHS is (List.upto i l) and an RHS where the upto has been
   pushed down as far as nicely possible *)
Ltac push_down_upto force_progress treat_app tp i l :=
  (*non-lazy*)match l with
  | List.app _ _ =>
      lazymatch treat_app with true =>
        let xss := List.reify_apps l in
        let le_pf := max_n_st (* might fail *)
          ltac:(fun n => constr:(i <= List.cbn_len_sum (List.cbn_dropRight n xss)))
          ltac:(fun _ => cbn [List.cbn_len_sum List.cbn_dropRight];
                         bottom_up_simpl_sidecond_hook)
          1%nat
          ltac:(list_length xss) in
        (* n=0 (nothing to do) and n=list_length xss (result is nil) not handled here *)
        let ys := open_constr:(_) in
        let upto_apps_pf := constr:(List.upto_apps _ i l xss ys _ le_pf
                                      ltac:(cbn [List.cbn_dropRight]; reflexivity)
                                      eq_refl
                                      ltac:(cbn [List.apps]; reflexivity)) in
        let res_upto_apps := res_rewrite (List.upto i ys) upto_apps_pf in
        let res_rec := push_down_upto false false tp i ys in
        chain_res res_upto_apps res_rec
      end
    | List.from ?j ?l =>
      let n := i in (* sized slice of size n: l[j:][:n] *)
      let sz_n := ring_expr_size n in
      let r_sum := ring_simplify_res_or_nothing_to_simpl (Z.add j n) in
      let sum := r_sum NewTerm in
      let sz_sum := ring_expr_size sum in
      let is_shrinking := eval cbv in (Z.ltb sz_sum sz_n) in
      lazymatch is_shrinking with
      | false => fail "ring_simplify does not shrink the expression size"
      | true =>
          let pf_sum := r_sum EqProof in
          res_rewrite (List.from j (List.upto sum l))
            (sized_slice_to_indexed_slice l j n sum
               ltac:(bottom_up_simpl_sidecond_hook) pf_sum)
      end
  | List.upto ?j ?l =>
      let r1 := res_rewrite (List.upto i l)
                  (List.upto_upto_subsume j i l ltac:(bottom_up_simpl_sidecond_hook)) in
      let r2 := push_down_upto false true tp i l in
      chain_res r1 r2
  | _ =>
      match is_concrete_enough i l true with
      | true => let l' := convertible_list_upto i l in res_convertible l'
      | false => res_rewrite (@nil tp)
                   (List.upto_beginning l i ltac:(bottom_up_simpl_sidecond_hook))
      | false => res_rewrite l
                   (List.upto_pastend l i ltac:(bottom_up_simpl_sidecond_hook))
      end
  | _ => lazymatch force_progress with false => res_nothing_to_simpl (@List.upto tp i l) end
  end.

Ltac local_zlist_simpl e :=
  match e with
  | @List.upto ?tp ?i ?l => push_down_upto true true tp i l
  | @List.get ?A ?inh ?l ?i =>
      lazymatch is_concrete_enough i l false with
      | true => let x := convertible_list_get inh l i in res_convertible x
      end
  | @List.repeatz ?A _ Z0 => res_convertible uconstr:(@nil A)
  | List.app ?xs nil => res_rewrite xs uconstr:(List.app_nil_r xs)
  | List.app ?l1 ?l2 => let l := prepend_concrete_list l1 l2 in res_convertible l
  | List.app ?xs ?ys =>
      (* TODO also check if rightmost list in xss can be merged with leftmost list in yss *)
      let xss := List.reify_apps xs in
      lazymatch xss with
      | cons _ nil => fail "no need to reassoc"
      | cons _ (cons _ _) =>
          let yss := List.reify_apps ys in
          let zs := eval cbn [List.apps List.cbn_app] in
                             (List.apps (List.cbn_app xss yss)) in
          res_rewrite zs (List.reassoc_app xss yss xs ys zs eq_refl eq_refl eq_refl)
      | _ => fail 1000 "bug: List.reify_apps returned result of unexpected shape:" xss
      end
  (* TODO Doesn't do anything for ((xs ++ ys) ++ zs)[i:] if i points into ys,
     and the subtraction created by from_app_discard_l should be simplified
     immediately rather than only in the next outermost iteration *)
  | List.from ?i (List.app ?l1 ?l2) =>
      res_rewrite (List.from (i - Z.of_nat (length l1)) l2)
                  (List.from_app_discard_l l1 l2 i ltac:(bottom_up_simpl_sidecond_hook))
  | List.from ?i (List.upto ?j ?l) =>
      let sz_j := ring_expr_size j in
      let r_diff := ring_simplify_res_or_nothing_to_simpl (Z.sub j i) in
      let diff := r_diff NewTerm in
      let sz_diff := ring_expr_size diff in
      let is_shrinking := eval cbv in (Z.ltb sz_diff sz_j) in
      lazymatch is_shrinking with
      | false => fail "ring_simplify does not shrink the expression size"
      | true =>
          let pf_diff := r_diff EqProof in
          let rhs := constr:(List.upto diff (List.from i l)) in
          let lem1 := constr:(indexed_slice_to_sized_slice l i j diff) in
          res_rewrite (List.upto diff (List.from i l))
            (indexed_slice_to_sized_slice l i j diff
               ltac:(bottom_up_simpl_sidecond_hook) pf_diff)
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
  | Z.div ?x ?d =>
      let x_eq_prod_pf := cancel_div_rec d x in
      lazymatch type of x_eq_prod_pf with
      | x = d * ?q => res_rewrite q (@cancel_div_done d x q
                                       ltac:(bottom_up_simpl_sidecond_hook) x_eq_prod_pf)
      end
  end.

Module word.
  Section WithWord.
    Context {width} {word : word.word width} {word_ok : word.ok word}.

    (* Pushing down word.unsigned: *)

    Lemma unsigned_of_Z_modwrap: forall (z: Z),
        word.unsigned (word.of_Z (word := word) z) = z mod 2 ^ width.
    Proof. apply word.unsigned_of_Z. Qed.

    Lemma unsigned_opp_eq_nowrap: forall [a: word] [ua: Z],
        word.unsigned a = ua ->
        ua <> 0 ->
        word.unsigned (word.opp a) = 2 ^ width - ua.
    Proof. intros. subst. apply word.unsigned_opp_nowrap. assumption. Qed.
    (* and lemma word.unsigned_opp_0 can be used as-is *)

    Lemma unsigned_add_eq_nowrap: forall [a b: word] [ua ub: Z],
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        ua + ub < 2 ^ width ->
        word.unsigned (word.add a b) = ua + ub.
    Proof. intros. subst. apply word.unsigned_add_nowrap. assumption. Qed.

    Lemma unsigned_sub_eq_nowrap: forall [a b: word] [ua ub: Z],
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        0 <= ua - ub ->
        word.unsigned (word.sub a b) = ua - ub.
    Proof. intros. subst. apply word.unsigned_sub_nowrap. assumption. Qed.

    Lemma unsigned_mul_eq_nowrap: forall [a b: word] [ua ub: Z],
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        ua * ub < 2 ^ width ->
        word.unsigned (word.mul a b) = ua * ub.
    Proof. intros. subst. apply word.unsigned_mul_nowrap. assumption. Qed.

    (* Pushing down word.of_Z: *)

    (* lemma word.of_Z_unsigned can be used as-is *)

    Lemma of_Z_mod: forall (z: Z),
        word.of_Z (word := word) (z mod 2 ^ width) = word.of_Z (word := word) z.
    Proof.
      intros. change (z mod 2 ^ width) with (word.wrap z).
      rewrite <- word.unsigned_of_Z. apply word.of_Z_unsigned.
    Qed.

    Lemma of_Z_mod_eq: forall [z: Z] [w: word],
        word.of_Z z = w ->
        word.of_Z (z mod 2 ^ width) = w.
    Proof. intros. subst. apply of_Z_mod. Qed.

    Lemma of_Z_opp_eq: forall [z: Z] [w: word],
        word.of_Z z = w ->
        word.of_Z (- z) = word.opp w.
    Proof. intros. subst. apply word.ring_morph_opp. Qed.

    Lemma of_Z_add_eq: forall [z1 z2: Z] [w1 w2: word],
        word.of_Z z1 = w1 ->
        word.of_Z z2 = w2 ->
        word.of_Z (z1 + z2) = word.add w1 w2.
    Proof. intros. subst. apply word.ring_morph_add. Qed.

    Lemma of_Z_sub_eq: forall [z1 z2: Z] [w1 w2: word],
        word.of_Z z1 = w1 ->
        word.of_Z z2 = w2 ->
        word.of_Z (z1 - z2) = word.sub w1 w2.
    Proof. intros. subst. apply word.ring_morph_sub. Qed.

    Lemma of_Z_mul_eq: forall [z1 z2: Z] [w1 w2: word],
        word.of_Z z1 = w1 ->
        word.of_Z z2 = w2 ->
        word.of_Z (z1 * z2) = word.mul w1 w2.
    Proof. intros. subst. apply word.ring_morph_mul. Qed.

  End WithWord.
End word.

Ltac push_down_unsigned e w := (* e must be (word.unsigned w) *)
  lazymatch w with
  | ?f1 ?a0 =>
      lazymatch f1 with
      | @word.of_Z ?width ?word =>
          match constr:(Set) with
          | _ => res_rewrite a0 (@word.unsigned_of_Z_nowrap width word _ a0
                                   ltac:(bottom_up_simpl_sidecond_hook))
          | _ => res_rewrite (a0 mod 2 ^ width)
                   (@word.unsigned_of_Z_modwrap width word _ a0)
          end
      | @word.opp ?width ?word =>
          let r_a0 := push_down_unsigned (@word.unsigned width word a0) a0 in
          let ua0 := r_a0 NewTerm in
          let pf0 := r_a0 EqProof in
          lazymatch ua0 with
          | 0 => res_rewrite 0 (word.unsigned_opp_0 a0 pf0)
          | _ => match constr:(Set) with
                 | _ => res_rewrite (2 ^ width - ua0) (word.unsigned_opp_eq_nowrap pf0
                          ltac:(bottom_up_simpl_sidecond_hook))
                 | _ => res_nothing_to_simpl e
                 end
          end
      | ?f2 ?a1 =>
          lazymatch f2 with
          | @word.add ?width ?word =>
              push_down_unsigned_app2 e width word
                (@word.unsigned_add_eq_nowrap width word _ a1 a0) Z.add a1 a0
          | @word.sub ?width ?word =>
              push_down_unsigned_app2 e width word
                (@word.unsigned_sub_eq_nowrap width word _ a1 a0) Z.sub a1 a0
          | @word.mul ?width ?word =>
              push_down_unsigned_app2 e width word
                (@word.unsigned_mul_eq_nowrap width word _ a1 a0) Z.mul a1 a0
          | _ => res_nothing_to_simpl e
          end
      | _ => res_nothing_to_simpl e
      end
  | _ => res_nothing_to_simpl e
  end
with push_down_unsigned_app2 e width word lem zop a1 a0 :=
  let r_a0 := push_down_unsigned (@word.unsigned width word a0) a0 in
  let r_a1 := push_down_unsigned (@word.unsigned width word a1) a1 in
  let ua0 := r_a0 NewTerm in
  let ua1 := r_a1 NewTerm in
  let pf0 := r_a0 EqProof in
  let pf1 := r_a1 EqProof in
  match constr:(Set) with
  | _ => res_rewrite (zop ua1 ua0) (lem _ _ pf1 pf0 ltac:(bottom_up_simpl_sidecond_hook))
  | _ => res_nothing_to_simpl e
  end.

Ltac push_down_of_Z width word z :=
  lazymatch z with
  | ?f1 ?a0 =>
      lazymatch f1 with
      | @word.unsigned width word =>
          res_rewrite a0 (@word.of_Z_unsigned width word _ a0)
      | Z.opp =>
          let r_a0 := push_down_of_Z width word a0 in
          let a0w := r_a0 NewTerm in
          let pf0 := r_a0 EqProof in
          res_rewrite (@word.opp width word a0w) (word.of_Z_opp_eq pf0)
      | ?f2 ?a1 =>
          lazymatch f2 with
          | Z.modulo =>
              lazymatch a0 with
              | 2 ^ width =>
                  let r_a1 := push_down_of_Z width word a1 in
                  let a1w := r_a1 NewTerm in
                  let pf1 := r_a1 EqProof in
                  res_rewrite a1w (word.of_Z_mod_eq pf1)
              | _ => res_nothing_to_simpl (@word.of_Z width word z)
              end
          | Z.add => push_down_of_Z_app2 width word
                       (@word.of_Z_add_eq width word _ a1 a0) (@word.add width word) a1 a0
          | Z.sub => push_down_of_Z_app2 width word
                       (@word.of_Z_sub_eq width word _ a1 a0) (@word.sub width word) a1 a0
          | Z.mul => push_down_of_Z_app2 width word
                       (@word.of_Z_mul_eq width word _ a1 a0) (@word.mul width word) a1 a0
          | _ => res_nothing_to_simpl (@word.of_Z width word z)
          end
      | _ => res_nothing_to_simpl (@word.of_Z width word z)
      end
  | _ => res_nothing_to_simpl (@word.of_Z width word z)
  end
with push_down_of_Z_app2 width word lem wop a1 a0 :=
  let r_a0 := push_down_of_Z width word a0 in
  let r_a1 := push_down_of_Z width word a1 in
  let a0w := r_a0 NewTerm in
  let a1w := r_a1 NewTerm in
  let pf0 := r_a0 EqProof in
  let pf1 := r_a1 EqProof in
  res_rewrite (wop a1w a0w) (lem _ _ pf1 pf0).

Ltac local_word_simpl e :=
  lazymatch e with
  | word.unsigned ?w => push_down_unsigned e w
  (* Not sure if we want this one:
     It's useful as a preprocessing step for ring_simplify on words, but if we have
     \[/[z1 + z2]] where 0 <= z1 + z2 < 2^32, we don't want to push down the of_Z,
     so we can do the unsigned_of_Z rewrite.
     --> TODO maybe reactivate, but then, also, in (word.of_Z (word.unsigned (a ^+ b))),
         prevent push_down of word.unsigned! (because here, we don't even need a
         sidecondition to get rid of the roundtrip
  | @word.of_Z ?width ?word ?z => push_down_of_Z width word z *)
  (* Strictly local subset of the above push_down_of_Z: *)
  | @word.of_Z ?width ?word (?z mod 2 ^ ?width) =>
      res_rewrite (@word.of_Z width word z) (@word.of_Z_mod width word _ z)
  end.

Ltac local_simpl_hook parent_kind e0 :=
  let e := constr:(e0) in (* <-- can't match on uconstr => quadratic retypechecking!*)
  match constr:(Set) with
  | _ => local_subst_small_rhs e
  | _ => local_zlist_simpl e
  | _ => local_ring_simplify parent_kind e
  | _ => local_ground_number_simpl e
  | _ => local_word_simpl e (* <-- not strictly local, might do a whole traversal *)
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

  Lemma simpl_len_cons: forall a (l: list A) n,
      1 + len l = n ->
      len (cons a l) = n.
  Proof. intros. subst. rewrite List.length_cons. lia. Qed.

  Lemma simpl_len_app: forall (l1 l2: list A) n1 n2 n,
      len l1 = n1 ->
      len l2 = n2 ->
      n1 + n2 = n ->
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
(* Consider `word.unsigned (foo (a + 0) ^+ x ^- foo a ^+ y)`:
   The argument of word.unsigned needs a first full bottom-up traversal to simplify
   it into `x ^+ y`, and after that, another push-down-word.unsigned traversal to
   obtain `word.unsigned x + word.unsigned y` (if no overflow).

   On the other hand, if you start pushing down len too early, not a problem,
   because list operations don't cancel like word.sub does.

   Therefore, pushing down len is integrated into bottom_up_simpl, whereas
   pushing down word.unsigned runs after it in local_simpl_hook *)
with simpl_len e A x := (* e must be (len x) *)
  lazymatch x with
  | List.from ?i ?l =>
      let r_i := bottom_up_simpl OtherExpr i in
      let i' := r_i NewTerm in
      let pf_i := r_i EqProof in
      let r_len_l := simpl_len (Z.of_nat (List.length l)) A l in
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
      let r_len_l := simpl_len (Z.of_nat (List.length l)) A l in
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
  | nil => res_convertible Z0
  | cons ?h ?t =>
      lazymatch list_length_option t with
      | Some ?n => let z := eval cbv in (Z.of_nat (S n)) in res_convertible z
      | None =>
          let r_len_t := simpl_len (Z.of_nat (List.length t)) A t in
          let len_t := r_len_t NewTerm in
          let pf_len_t := r_len_t EqProof in
          let r_oneplus := ring_simplify_res_or_nothing_to_simpl (Z.add 1 len_t) in
          let oneplus := r_oneplus NewTerm in
          let pf_oneplus := r_oneplus EqProof in
          res_rewrite oneplus uconstr:(@simpl_len_cons A h t oneplus pf_oneplus)
      end
  | @List.app ?tp ?l1 ?l2 =>
      let r_len_l1 := simpl_len (Z.of_nat (@List.length tp l1)) tp l1 in
      let r_len_l2 := simpl_len (Z.of_nat (@List.length tp l2)) tp l2 in
      let len_l1 := r_len_l1 NewTerm in
      let len_l2 := r_len_l2 NewTerm in
      let r_sum_lens := ring_simplify_res_or_nothing_to_simpl (Z.add len_l1 len_l2) in
      let sum_lens := r_sum_lens NewTerm in
      let pf_len_l1 := r_len_l1 EqProof in
      let pf_len_l2 := r_len_l2 EqProof in
      let pf_sum_lens := r_sum_lens EqProof in
      res_rewrite sum_lens uconstr:(@simpl_len_app tp l1 l2 len_l1 len_l2 sum_lens
                                      pf_len_l1 pf_len_l2 pf_sum_lens)
  | @List.set ?tp ?l ?i ?x =>
      let r_i := bottom_up_simpl OtherExpr i in
      let i' := r_i NewTerm in
      let pf_i := r_i EqProof in
      let r_len_l := simpl_len (Z.of_nat (@List.length tp l)) tp l in
      let len_l := r_len_l NewTerm in
      let pf_len_l := r_len_l EqProof in
      let g := constr:(0 <= i' < len_l) in
      match constr:(Set) with
      | _ => let s := constr:(ltac:(bottom_up_simpl_sidecond_hook) : g) in
             res_rewrite len_l constr:(@simpl_len_set tp l i i' len_l x pf_i pf_len_l s)
      | _ => (* TODO this is the only place so far where bottom_up_simpl might fail.
                Design decisions: How to return failures? Should we fail in more places? *)
          fail 1 "setting element" i' "of" l "requires" g
            "but that's not provable by bottom_up_simpl_sidecond_hook"
      end
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

Ltac bottom_up_simpl_in_hyp_of_type_if test H t :=
  tryif test H t then bottom_up_simpl_in_hyp_of_type H t else idtac.

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

Ltac bottom_up_simpl_in_letbound_var_if test x b t :=
  tryif test x b t then bottom_up_simpl_in_letbound_var x b t else idtac.

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
Ltac bottom_up_simpl_in_hyps_if test :=
  foreach_hyp (bottom_up_simpl_in_hyp_of_type_if test).

Ltac bottom_up_simpl_in_vars :=
  foreach_var bottom_up_simpl_in_letbound_var.
Ltac bottom_up_simpl_in_vars_if test :=
  foreach_var (bottom_up_simpl_in_letbound_var_if test).

Ltac bottom_up_simpl_in_hyps_and_vars :=
  bottom_up_simpl_in_hyps; bottom_up_simpl_in_vars.

Ltac bottom_up_simpl_in_all :=
  bottom_up_simpl_in_hyps; bottom_up_simpl_in_vars;
  try bottom_up_simpl_in_goal.

Local Hint Mode Word.Interface.word - : typeclass_instances.

Section Tests.
  Set Ltac Backtrace.

  Goal forall a: Z, a = a + 0 -> a = a + 0 -> True.
    intros ? E_nosimpl E.
    bottom_up_simpl_in_hyps_if
      ltac:(fun h t => tryif unify h E_nosimpl then fail else idtac).
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

  Goal forall (a b: Z),
      0 <= a + b < 2 ^ 32 ->
      word.unsigned (word.of_Z (a + b)) - b = a.
  Proof.
    intros. bottom_up_simpl_in_goal. refl.
  Abort.

  Goal forall (foo: Z -> word) (a: Z) (x y: word),
       word.unsigned x + word.unsigned y < 2 ^ 32 ->
       word.unsigned (foo (a + 0) ^+ x ^- foo a ^+ y) = word.unsigned x + word.unsigned y.
  Proof.
    intros. bottom_up_simpl_in_goal. refl.
  Abort.

  Goal forall (z: Z), word.of_Z (word.unsigned (word.of_Z z)) = word.of_Z z.
  Proof.
    intros. bottom_up_simpl_in_goal. refl.
  Abort.

  Goal forall (i j k count d: Z),
      d <> 0 ->
      (d * j - i * d + k * d * count) / d - count * k = j - i.
  Proof. intros. bottom_up_simpl_in_goal. refl. Abort.

  Goal forall (A: Type) (xs ys: list A) i j,
      0 <= i <= 3 + j + i ->
      xs[i : 3 + i + j] = ys ->
      xs[i:][: j + 3] = ys.
  Proof. intros. bottom_up_simpl_in_hyps. assumption. Abort.

  Goal forall (A: Type) (xs ys: list A) i j,
      0 <= i <= j ->
      xs[i:][: j - i] = ys ->
      xs[i : j] = ys.
  Proof. intros. bottom_up_simpl_in_hyps. assumption. Abort.

  Goal forall (A: Type) (xs ys: list A),
      len (xs ++ ys) = len xs + len ys.
  Proof. intros. bottom_up_simpl_in_goal. refl. Abort.

  Goal forall (A: Type) (xs ys: list A) (x: A) (i: Z),
      0 <= i < len ys ->
      len (xs ++ ys ++ xs) = 2 * len xs + len ys.
  Proof. intros. bottom_up_simpl_in_goal. refl. Abort.

  Goal forall (A: Type) (xs ys: list A) (x: A) (i: Z) (j: Z),
      0 <= i < len ys ->
      0 <= j < i ->
      len (ys[j := x][i := x]) = len ys.
  Proof. intros. bottom_up_simpl_in_goal. refl. Abort.

  Goal forall (A: Type) (xs ys: list A) (x: A) (i: Z),
      0 <= i < len ys ->
      len (xs ++ ys[i := x] ++ xs) = 2 * len xs + len ys.
  Proof. intros. bottom_up_simpl_in_goal. refl. Abort.

  Goal forall (A: Type) (xs1 xs2 xs3 xs4 xs5 xs6: list A),
      (xs1 ++ xs2) ++ (xs3 ++ xs4 ++ xs5) ++ xs6 = xs1 ++ xs2 ++ xs3 ++ xs4 ++ xs5 ++ xs6.
  Proof. intros. bottom_up_simpl_in_goal. refl. Abort.

  Goal forall (A: Type) (l1 l2: list A) (i: Z),
      len l1 = i ->
      (l1 ++ l2)[:i] = l1.
  Proof. intros. bottom_up_simpl_in_goal. refl. Abort.

  Goal forall (A: Type) (l1 l2: list A) (i: Z),
      len l1 = i ->
      (l1 ++ l2)[0:][:i] = l1.
  Proof. intros. bottom_up_simpl_in_goal. refl. Abort.

  Goal forall (A: Type) (l1 l2: list A) (i: Z),
      0 <= i <= len l1 ->
      (l1 ++ l2)[:i] = l1[:i].
  Proof. intros. bottom_up_simpl_in_goal. refl. Abort.

  Ltac bottom_up_simpl_sidecond_hook ::=
    rewrite ?List.len_app, ?List.len_upto, ?List.len_from by lia; lia (*debug_sidecond*).

  Goal forall (A: Type) (xs1 xs2 xs3 xs4 xs5 xs6: list A) i j k s,
      0 <= j <= len xs3 ->
      s = len xs1 + len xs2 + len xs3 - j ->
      s <= i <= s + k ->
      k <= len xs4 ->
      ((xs1 ++ xs2) ++ (xs3[j:] ++ xs4[:k] ++ xs5) ++ xs6)[:i] =
      (xs1 ++ xs2 ++ xs3[j:] ++ xs4[:k])[:i].
  Proof.
    intros. bottom_up_simpl_in_goal.
    (* TODO heuristics to decide whether it's worth pushing it down further to obtain
       xs1 ++ xs2 ++ xs3[j:] ++ xs4[:k][:i - len xs1 - len xs2 - len x3 + j] *)
    refl.
  Abort.


  (** ** Not supported yet: *)

  Goal forall (A: Type) (l1 l2: list A) (x: A) (i: Z),
      len l1 = i ->
      (l1 ++ [|x|] ++ l2)[:i + 1] = l1 ++ [|x|].
  Proof. intros. bottom_up_simpl_in_goal. Fail refl. Abort.

  Goal forall (A: Type) (l1 l2: list A) (x: A) (i: Z),
      len l1 = i ->
      (l1 ++ x :: l2)[:i + 1] = l1 ++ [|x|].
  Proof. intros. Fail bottom_up_simpl_in_goal. Abort.

  Goal forall (z1 z2: Z) (y: word),
      word.of_Z (z1 + z2) ^- word.of_Z z1 = y ->
      word.of_Z z2 = y.
  Proof.
    intros.
    bottom_up_simpl_in_hyps.
    ring_simplify in H.
    (* TODO push_down_of_Z? *)
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
