Require Import coqutil.Ltac2Lib.Ltac2.
Require Import coqutil.Ltac2Lib.Failf coqutil.Ltac2Lib.rdelta coqutil.Ltac2Lib.Lia.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Datatypes.Inhabited.
Require Import coqutil.Datatypes.ZList.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.foreach_hyp.
Require Import bedrock2.WordPushDownLemmas.
Require bedrock2.WordNotations.
Require Import bedrock2.cancel_div.
Require Import bedrock2.LogSidecond.

Ltac2 rec is_positive_literal(e: constr): bool :=
  lazy_match! e with
  | xI ?p => is_positive_literal p
  | xO ?p => is_positive_literal p
  | xH => true
  | _ => false
  end.

(* Note: Not the same as Coq.setoid_ring.InitialRing.isZcst, because
   isZcst considers (Z.of_nat n) and (Z.of_N n) constant if n is constant *)
Ltac2 is_Z_literal(n: constr): bool :=
  lazy_match! n with
  | 0 => true
  | Z.pos ?p => is_positive_literal p
  | Z.neg ?p => is_positive_literal p
  | _ => false
  end.

(* needed for compatibility with simplification strategies that choose not
   to simplify powers of 2 *)
Ltac2 is_Z_const(n: constr): bool :=
  lazy_match! n with
  | 2 ^ ?x => is_Z_literal x
  | _ => is_Z_literal n
  end.

Ltac2 rec is_nat_const(n: constr): bool :=
  lazy_match! n with
  | O => true
  | S ?p => is_nat_const p
  | _ => false
  end.

(* To be treated opaquely and only manipulated through the API that follows.
   Alternative representations to try out:
   - Ltac2 records
   - uconstr
   - resulting term of simplification as constr, proof term as uconstr or custom type *)
Ltac2 Type res :=
  [ ResNop(constr) (* new and old term *)
  | ResConvertible(constr) (* new term *)
  | ResRewrite(constr, constr) (* new term, proof *) ].

Ltac2 new_term(r: res): constr :=
  match r with
  | ResNop t => t
  | ResConvertible t => t
  | ResRewrite t _ => t
  end.

Ltac2 eq_proof(r: res): constr :=
  match r with
  | ResNop t => '(@eq_refl _ $t)
  | ResConvertible t => '(@eq_refl _ $t)
  | ResRewrite _ pf => pf
  end.

Ltac2 did_something(r: res): bool :=
  match r with
  | ResNop _ => false
  | ResConvertible _ => true
  | ResRewrite _ _ => true
  end.

Ltac2 is_convertible(r: res): bool :=
  match r with
  | ResNop _ => true
  | ResConvertible _ => true
  | ResRewrite _ _ => false
  end.

Ltac2 res_convertible(new_term: constr): res :=
  ResConvertible new_term.

(* new_term must be convertible to the rhs of eq_proof's type *)
Ltac2 res_rewrite_to(new_term: constr)(eq_proof: constr): res :=
  ResRewrite new_term eq_proof.

Ltac2 res_rewrite(eq_proof: constr): res :=
  lazy_match! Constr.type eq_proof with
  | _ = ?rhs => ResRewrite rhs eq_proof
  end.

Ltac2 res_nothing_to_simpl(original_term: constr): res :=
  ResNop original_term.

(* original: term of shape (f a)
   f: constr
   r: result whose lhs is a *)
Ltac2 lift_res1(original: constr)(f: constr)(r: res): res :=
  if did_something r then
    let t := new_term r in
    if is_convertible r then
      res_convertible '($f $t)
    else
      let pf := eq_proof r in res_rewrite '(@f_equal _ _ $f _ $t $pf)
  else res_nothing_to_simpl original.

(* If we just used f_equal with f := (fun x => g (h x)), the RHS would be
   ((fun x => g (h x)) a') instead of (g (h a')). *)
Lemma f_equal11[A B C: Type](h: A -> B)(g: B -> C)[a a': A]: a = a' -> g (h a) = g (h a').
Proof. exact (@f_equal A C (fun x => g (h x)) a a'). Qed.

(* original: term of shape (f (g a))
   f: constr
   g: constr
   r: result whose lhs is a *)
Ltac2 lift_res11(original: constr)(f: constr)(g: constr)(r: res): res :=
  if did_something r then
    let t := new_term r in
    if is_convertible r then
      res_convertible '($f ($g $t))
    else
      let pf := eq_proof r in res_rewrite '(f_equal11 $f $g $pf)
  else res_nothing_to_simpl original.

(* original: term of shape (f a1 a2)
   f: constr
   r1: result whose lhs is a1
   r2: result whose lhs is a2 *)
Ltac2 lift_res2(original: constr)(f: constr)(r1: res)(r2: res): res :=
  let t1 := new_term r1 in
  let t2 := new_term r2 in
  if did_something r1 then
    if is_convertible r1 then
      if is_convertible r2 then
        res_convertible '($f $t1 $t2)
      else
        let pf1 := eq_proof r1 in
        let pf2 := eq_proof r2 in
        res_rewrite '(@f_equal2 _ _ _ $f _ $t1 _ $t2 $pf1 $pf2)
    else
      let pf1 := eq_proof r1 in
      let pf2 := eq_proof r2 in
      res_rewrite '(@f_equal2 _ _ _ $f _ $t1 _ $t2 $pf1 $pf2)
  else if did_something r2 then
    if is_convertible r2 then
      res_convertible '($f $t1 $t2)
    else
      let pf2 := eq_proof r2 in
      res_rewrite '(@f_equal _ _ ($f $t1) _ $t2 $pf2)
  else
    res_nothing_to_simpl original.

Lemma app_cong[A B: Type][f g: A -> B][x y: A]: f = g -> x = y -> f x = g y.
Proof. intros. subst. reflexivity. Qed.

(* original: term of shape (f a)
   r1: result whose lhs is f
   r2: result whose lhs is a *)
Ltac2 lift_res_app(original: constr)(r1: res)(r2: res): res :=
  let t1 := new_term r1 in
  let t2 := new_term r2 in
  if did_something r1 then
    if is_convertible r1 then
      if is_convertible r2 then
        res_convertible '($t1 $t2)
      else
        let pf1 := eq_proof r1 in
        let pf2 := eq_proof r2 in
        res_rewrite '(@app_cong _ _ _ $t1 _ $t2 $pf1 $pf2)
    else
      let pf1 := eq_proof r1 in
      let pf2 := eq_proof r2 in
      res_rewrite '(@app_cong _ _ _ $t1 _ $t2 $pf1 $pf2)
  else if did_something r2 then
    if is_convertible r2 then
      res_convertible '($t1 $t2)
    else
      let pf2 := eq_proof r2 in
      res_rewrite '(@f_equal _ _ $t1 _ $t2 $pf2)
  else
    res_nothing_to_simpl original.

Lemma if_cong[A: Type][b b': bool][thn thn' els els': A]:
    b = b' ->
    thn = thn' ->
    els = els' ->
    (if b then thn else els) = (if b' then thn' else els').
Proof. intros. subst. reflexivity. Qed.

(* original: term of shape (if b then a1 else a2)
   r0: result whose lhs is b
   r1: result whose lhs is a1
   r2: result whose lhs is a2 *)
Ltac2 lift_res_if(original: constr)(r0: res)(r1: res)(r2: res): res :=
  let t0 := new_term r0 in
  let t1 := new_term r1 in
  let t2 := new_term r2 in
  if did_something r0 || did_something r1 || did_something r2 then
    if is_convertible r0 && is_convertible r1 && is_convertible r2 then
      res_convertible '(if $t0 then $t1 else $t2)
    else
      let pf0 := eq_proof r0 in
      let pf1 := eq_proof r1 in
      let pf2 := eq_proof r2 in
      res_rewrite '(if_cong $pf0 $pf1 $pf2)
  else
    res_nothing_to_simpl original.

Lemma impl_cong[P P' Q Q': Prop]:
  P = P' ->
  Q = Q' ->
  (P -> Q) = (P' -> Q').
Proof. intros. subst. reflexivity. Qed.

(* original: term of shape (P -> Q)
   r1: result whose lhs is P
   r2: result whose lhs is Q *)
Ltac2 lift_res_impl(original: constr)(r1: res)(r2: res): res :=
  let t1 := new_term r1 in
  let t2 := new_term r2 in
  if did_something r1 || did_something r2 then
    if is_convertible r1 && is_convertible r2 then
      res_convertible '($t1 -> $t2)
    else
      let pf1 := eq_proof r1 in
      let pf2 := eq_proof r2 in
      res_rewrite '(impl_cong $pf1 $pf2)
  else
    res_nothing_to_simpl original.

Ltac2 chain_rewrite_res(r1: res)(r2: res): res :=
  let t1 := new_term r1 in
  let pf1 := eq_proof r1 in
  let t2 := new_term r2 in
  let pf2 := eq_proof r2 in
  res_rewrite '(@eq_trans _ _ $t1 $t2 $pf1 $pf2).

(* assumes rhs of r1 equals lhs of r2 *)
Ltac2 chain_res(r1: res)(r2: res): res :=
  if did_something r1 then
    if did_something r2 then
      if is_convertible r1 then r2
      else
        if is_convertible r2
        then res_rewrite_to (new_term r2) (eq_proof r1)
        else chain_rewrite_res r1 r2
    else r1
  else r2.

(* marker to make proof terms more readable *)
Definition xlia(P: Prop){pf: P}: P := pf.

Ltac2 mutable bottom_up_simpl_sidecond_hook () :=
  ltac1:(lia). (* OR xlia zchecker if already zified *)

(* local_X_simpl tactics:
   Given a term with already simplified subterms, produce new simplified term and
   equality proof (or set flag indicating that it's convertible).
   Failing means no simplification opportunity. *)

(* inh: inhabited instance
   l:   any number of cons followed by nil or an abstract tail
   i:   fully simplified Z literal
   Returns an element or a List.get with a smaller index *)
Ltac2 rec convertible_list_get inh l i :=
  lazy_match! l with
  | nil => '(@Inhabited.default _ $inh)
  | cons ?h ?t =>
      lazy_match! i with
      | Z0 => h
      | Zpos _ => let j := eval cbv in (Z.pred $i) in convertible_list_get inh t j
      | Zneg _ => '(@Inhabited.default _ $inh)
      end
  | _ => '(@List.get _ $inh $l $i)
  end.

(* l:   any number of cons followed by nil or an abstract tail
   i:   fully simplified Z literal
   Returns a prefix of l or a few cons followed by a List.upto with a smaller index,
   eg (a :: b :: c :: l)[:5] --> a :: b :: c :: (l[:2]) *)
Ltac2 rec convertible_list_upto(i: constr)(l: constr): constr :=
  lazy_match! l with
  | nil => l
  | @cons ?tp ?h ?t =>
      lazy_match! i with
      | Zpos _ => let j := eval cbv in (Z.pred $i) in
                  let r := convertible_list_upto j t in
                  '(@cons $tp $h $r)
      | _ => '(@nil $tp)
      end
  | _ => lazy_match! i with
         | Zpos _ => '(List.upto $i $l)
         | Z0 => '(@nil _)
         | Zneg _ => '(@nil _)
         end
  end.

(* l:   any number of cons followed by nil or an abstract tail
   i:   fully simplified Z literal
   Returns a suffix of l or a List.from with a smaller index *)
Ltac2 rec convertible_list_from i l :=
  lazy_match! l with
  | nil => l
  | @cons ?tp ?h ?t =>
      lazy_match! i with
      | Zpos _ => let j := eval cbv in (Z.pred $i) in convertible_list_from j t
      | _ => l
      end
  | _ => lazy_match! i with
         | Zpos _ => '(List.from $i $l)
         | Z0 => l
         | Zneg _ => l
         end
  end.

(* only works if l1 is made up of just cons and nil *)
Ltac2 rec prepend_concrete_list l1 l2 :=
  lazy_match! l1 with
  | cons ?h ?t => let r := prepend_concrete_list t l2 in '(cons $h $r)
  | nil => l2
  end.

Ltac2 is_concrete_enough(i: constr)(l: constr)(is_nonpos_concrete_enough: bool): bool :=
  lazy_match! l with
  | nil => is_Z_literal i
  | cons _ _ => is_Z_literal i
  | _ => lazy_match! i with
         | Z0 => is_nonpos_concrete_enough
         | Zneg _ => is_nonpos_concrete_enough
         | _ => false
         end
  end.

Ltac2 non_ring_expr_size(e: constr): int :=
  lazy_match! e with
  | Zneg _ => 2
  | _ => if is_Z_const e then 1 else 2
  end.

Ltac2 rec ring_expr_size(e: constr): int :=
  let r1 x :=
    let s := ring_expr_size x in Int.add 1 s in
  let r2 x y :=
    let s1 := ring_expr_size x in let s2 := ring_expr_size y in Int.add 1 (Int.add s1 s2) in
  lazy_match! e with
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

Ltac2 Type expr_kind := [ WordRingExpr | ZRingExpr | OtherExpr ].

Ltac2 expr_kind_eq k1 k2 :=
  match k1 with
  | WordRingExpr => match k2 with WordRingExpr => true | _ => false end
  | ZRingExpr    => match k2 with ZRingExpr    => true | _ => false end
  | OtherExpr    => match k2 with OtherExpr    => true | _ => false end
  end.

Ltac2 get_expr_kind(e: constr): expr_kind :=
  lazy_match! e with
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

(* To hide the ring_simplify proof when printing the proof term, and
   to provide a let so that the preprocessing of ring_simplify doesn't mess with
   the evar, while also making sure that the type as seen from the outside is a
   (_ = _) rather than a let. *)
Lemma ring_simplify_proof[A: Type](lhs rhs: A){pf: let x := rhs in lhs = x}: lhs = rhs.
Proof. exact pf. Qed.

Ltac2 ring_simplify_res_forcing_progress(e: constr): res :=
  let rhs := '(_) in
  res_rewrite '(@ring_simplify_proof _ $e $rhs
    (* to invoke ring_simplify, we need to switch to Ltac1 anyways, so we just do this
       whole line in Ltac1 *)
    ltac:(let x := fresh "x" in intro x; progress ring_simplify; subst x; reflexivity)).

Ltac2 ring_simplify_res_or_nothing_to_simpl(e: constr): res :=
  first_val [ ring_simplify_res_forcing_progress e
            | res_nothing_to_simpl e ].

Ltac2 local_ring_simplify(parent: expr_kind)(e: constr): res :=
  if expr_kind_eq (get_expr_kind e) parent then
    gfail "nothing to do here because parent will be ring_simplified too"
  else
    let r := ring_simplify_res_forcing_progress e in
    if Int.lt (ring_expr_size (new_term r)) (ring_expr_size e) then r
    else gfail "ring_simplify does not shrink the expression size".

Module List.
  Import List.ZIndexNotations. Local Open Scope zlist_scope.

  (* Given `e` of type `list A`, returns `xss` of type `list (list A)` such that
     `List.apps xss` is convertible to `e`, and as long as possible.
     (Side question: What would it take to prove such a spec?) *)
  Ltac2 rec reify_apps e :=
    lazy_match! e with
    | List.app ?xs ?ys => let r := reify_apps ys in '(cons $xs $r)
    | _ => '([|$e|])
    end.

  Goal forall l: list Z, True.
    intros.
    lazy_match! reify_apps '([|1; 2|] ++ ([|3|] ++ [|4|]) ++ (l ++ [|5|])) with
    | [|[|1; 2|]; [|3|] ++ [|4|]; l; [|5|]|] => ()
    end.
  Abort.

  (* Given (e1 :: .. :: eN :: non_concrete_tail), returns a pair containing
     (e1 :: .. :: eN :: acc) and non_concrete_tail.
     Note: Callees should not forget to consider the case where e is fully concrete. *)
  Ltac2 rec peel_off_concrete_part(e: constr)(acc: constr): constr * constr :=
    lazy_match! e with
    | cons ?x ?xs => let (c, nc) := peel_off_concrete_part xs acc in ('(cons $x $c), nc)
    | _ => (acc, e)
    end.

  Goal forall (b1 b2 b3: bool) (l: list bool), True.
    intros.
    let (c, nc) := peel_off_concrete_part '(b1 :: b2 :: b3 :: l) '(@nil bool) in
    lazy_match! c with
    | [|b1; b2; b3|] =>
        lazy_match! nc with
        | l => ()
        end
    end.
  Abort.

  (* Given `e` of type `list A`, returns `xss` of type `list (list A)` such that
     `List.apps xss` is convertible to `e`, and each argument to ++ becomes an
     element of the resulting list, and cons is only used for lists whose structure
     is fully concrete (i.e. (e1 :: e2 :: non_concrete_tail) is turned into two
     list elements, [|e1; e2|] and non_concrete_tail). *)
  Ltac2 rec reify_apps_and_cons(e: constr): constr :=
    lazy_match! e with
    | @cons ?tp ?x ?xs => let (c, nc) := peel_off_concrete_part e '(@nil $tp) in
                          let r := reify_apps_and_cons nc in '(cons $c $r)
    | List.app ?xs ?ys =>
        (* Note: no recursion into xs because that might not be convertible
           and we expect e to be already right-leaning in typical use cases *)
        let r := reify_apps_and_cons ys in '(cons $xs $r)
    | @nil ?tp => '(@nil (list $tp))
    | _ => '([|$e|])
    end.

  Goal forall (l1 l2 l3: list Z) (a b c: Z), True.
    intros.
    let r := reify_apps_and_cons
               '([|a; b|] ++ [|c|] ++ l1 ++ a :: b :: l2 ++ [|a; b|] ++ c :: l3) in
    lazy_match! r with
    | [| [|a; b|]; [|c|]; l1; [|a; b|]; l2; [|a; b|]; [|c|]; l3 |] => ()
    end.
    let r := reify_apps_and_cons '(l2 ++ [|a; b|]) in
    lazy_match! r with
    | [| l2; [|a; b|] |] => ()
    end.
  Abort.

  Section ZList_TODO_MOVE.
    Context [A: Type].

    Lemma upto_nil: forall i, (@nil A)[:i] = nil.
    Proof. intros. unfold List.upto. apply List.firstn_nil. Qed.

    Lemma from_nil: forall i, (@nil A)[i:] = nil.
    Proof. intros. unfold List.from. apply List.skipn_nil. Qed.

    Lemma repeatz_singleton_l: forall (x: A) n,
        0 <= n ->
        [|x|] ++ List.repeatz x n = List.repeatz x (1 + n).
    Proof.
      intros. unfold List.repeatz. rewrite Z2Nat.inj_add. 3: assumption. 2: discriminate.
      rewrite List.repeat_app. reflexivity.
    Qed.

    Lemma repeatz_singleton_r: forall (x: A) n,
        0 <= n ->
        List.repeatz x n ++ [|x|] = List.repeatz x (n + 1).
    Proof.
      intros. unfold List.repeatz. rewrite Z2Nat.inj_add. 2: assumption. 2: discriminate.
      rewrite List.repeat_app. reflexivity.
    Qed.
  End ZList_TODO_MOVE.

  Section WithA.
    Context [A: Type].

    (* Same as List.concat, but does not result in a trailing `++ nil` when unfolded *)
    Fixpoint cbn_concat(xss: list (list A)): list A :=
      match xss with
      | nil => nil
      | ys :: nil => ys
      | h :: t => h ++ cbn_concat t
      end.

    Lemma cbn_concat_spec: forall (xss: list (list A)), cbn_concat xss = List.concat xss.
    Proof.
      induction xss. 1: reflexivity.
      simpl. rewrite <- IHxss.
      destruct xss; try reflexivity.
      simpl. symmetry. apply List.app_nil_r.
    Qed.

    Definition cbn_app: list (list A) -> list (list A) -> list (list A) :=
      Eval unfold List.app in @List.app (list A).

    Lemma cbn_app_spec: cbn_app = @List.app (list A).
    Proof. reflexivity. Qed.

    Lemma reassoc_app: forall (xss yss: list (list A)) (xs ys zs: list A),
        cbn_concat xss = xs ->
        cbn_concat yss = ys ->
        cbn_concat (cbn_app xss yss) = zs ->
        List.app xs ys = zs.
    Proof.
      intros. subst. rewrite 3cbn_concat_spec. change cbn_app with (@List.app (list A)).
      symmetry. apply List.concat_app.
    Qed.

    Lemma reassoc_app_mergeable_in_middle:
      forall (xss yss: list (list A)) (last_xs first_ys simpler xs ys zs: list A),
        cbn_concat (cbn_app xss (cons last_xs nil)) = xs ->
        cbn_concat (cons first_ys yss) = ys ->
        List.app last_xs first_ys = simpler ->
        cbn_concat (cbn_app xss (cons simpler yss)) = zs ->
        List.app xs ys = zs.
    Proof.
      intros. subst. rewrite ?cbn_concat_spec, ?cbn_app_spec.
      repeat (rewrite ?List.concat_app; simpl; rewrite <- List.app_assoc).
      reflexivity.
    Qed.

    Definition cbn_firstn: nat -> list (list A) -> list (list A) :=
      Eval unfold List.firstn in @List.firstn (list A).

    Lemma cbn_firstn_spec: cbn_firstn = @List.firstn (list A).
    Proof. reflexivity. Qed.

    Definition cbn_dropRight(n: nat)(ls: list (list A)): list (list A) :=
      Eval unfold List.length, Nat.sub, List.firstn in
        List.firstn (Nat.sub (List.length ls) n) ls.

    Lemma cbn_dropRight_spec(n: nat)(ls: list (list A)):
        cbn_dropRight n ls = List.firstn (Nat.sub (List.length ls) n) ls.
    Proof. reflexivity. Qed.

    Definition cbn_takeRight(n: nat)(ls: list (list A)): list (list A) :=
      Eval unfold List.length, Nat.sub, List.skipn in
        List.skipn (Nat.sub (List.length ls) n) ls.

    Lemma cbn_takeRight_spec(n: nat)(ls: list (list A)):
        cbn_takeRight n ls = List.skipn (Nat.sub (List.length ls) n) ls.
    Proof. reflexivity. Qed.

    Definition cbn_skipn: nat -> list (list A) -> list (list A) :=
      Eval unfold List.skipn in @List.skipn (list A).

    Lemma cbn_skipn_spec: cbn_skipn = @List.skipn (list A).
    Proof. reflexivity. Qed.

    Fixpoint cbn_len_sum(xss: list (list A)): Z :=
      match xss with
      | nil => 0
      | h :: t => len h + cbn_len_sum t
      end.

    Lemma cbn_len_sum_nonneg: forall xss, 0 <= cbn_len_sum xss.
    Proof. induction xss; simpl; lia. Qed.

    Lemma cbn_len_sum_app: forall xss yss,
        cbn_len_sum (xss ++ yss) = cbn_len_sum xss + cbn_len_sum yss.
    Proof. intros. induction xss; intros; cbn; lia. Qed.

    Lemma cbn_len_sum_spec: forall xss, cbn_len_sum xss = len (List.concat xss).
    Proof. induction xss; simpl; rewrite ?List.app_length; lia. Qed.

    Lemma upto_apps0: forall n i (xs: list A) (xss: list (list A))
                            (ys: list A) (yss: list (list A)),
        i <= cbn_len_sum (cbn_firstn n xss) ->
        cbn_firstn n xss = yss ->
        cbn_concat xss = xs ->
        cbn_concat yss = ys ->
        List.upto i xs = List.upto i ys.
    Proof.
      intros. subst. rewrite 2cbn_concat_spec. revert i xss H.
      induction n; intros; simpl in *.
      - rewrite 2List.upto_beginning; trivial.
      - destruct xss. 1: reflexivity.
        simpl in *.
        rewrite 2List.upto_app. f_equal. apply IHn. lia.
    Qed.

    Lemma upto_apps_drop_r: forall n i (xs: list A) (xss: list (list A))
                            (ys: list A) (yss: list (list A)),
        i <= cbn_len_sum (cbn_dropRight n xss) ->
        cbn_dropRight n xss = yss ->
        cbn_concat xss = xs ->
        cbn_concat yss = ys ->
        List.upto i xs = List.upto i ys.
    Proof. unfold cbn_dropRight. intros. eapply upto_apps0; eassumption. Qed.

    (* Example: If we know that i points somewhere into xs2 or xs3, we can
                pull some listlets (xs0 and xs1) out of the upto on the left:
       (xs0 ++ xs1 ++ xs2 ++ xs3 ++ xs4)[:i] =
       xs0 ++ xs1 ++ (xs2 ++ xs3)[:i - len xs0 - len xs1] *)
    Lemma upto_apps_pullout_l: forall n i j (xs xs2: list A) (xss xss1 xss2: list (list A))
                                      (ys: list A) (yss: list (list A)),
        cbn_len_sum (cbn_firstn n xss) <= i ->
        cbn_firstn n xss = xss1 ->
        cbn_skipn n xss = xss2 ->
        i - cbn_len_sum (cbn_firstn n xss) = j ->
        cbn_concat xss = xs ->
        cbn_concat xss2 = xs2 ->
        cbn_app xss1 (cons (List.upto j xs2) nil) = yss ->
        cbn_concat yss = ys ->
        List.upto i xs = ys.
    Proof.
      induction n; intros; subst.
      - simpl. f_equal. lia.
      - destruct xss.
        + simpl. f_equal. lia.
        + rewrite ?cbn_concat_spec. simpl in *.
          pose proof (cbn_len_sum_nonneg (cbn_firstn n xss)).
          rewrite List.upto_app_pushdown_r by lia.
          f_equal. rewrite <-?cbn_concat_spec.
          eapply IHn; try reflexivity. 1: lia.
          f_equal. f_equal. f_equal. f_equal. lia.
    Qed.

    (* Example: If we know that i points somewhere into xs2 or xs3, we can
                discard some listlets on the right (x4),
                and pull some (xs0 and xs1) out of the upto on the left:
       (xs0 ++ xs1 ++ xs2 ++ xs3 ++ xs4)[:i] =
       xs0 ++ xs1 ++ (xs2 ++ xs3)[:i - len xs0 - len xs1] *)
    Lemma upto_apps: forall nL nR i j (xs xs2 xs2': list A) (xss xss1 xss2: list (list A))
                            (ys: list A) (yss: list (list A)),
        cbn_len_sum (cbn_firstn nL xss) <= i ->
        i <= cbn_len_sum (cbn_dropRight nR xss) ->
        cbn_firstn nL xss = xss1 ->
        i - cbn_len_sum xss1 = j ->
        cbn_dropRight nR (cbn_skipn nL xss) = xss2 ->
        cbn_concat xss = xs ->
        cbn_concat xss2 = xs2 ->
        List.upto j xs2 = xs2' ->
        cbn_app xss1 (cons xs2' nil) = yss ->
        cbn_concat yss = ys ->
        List.upto i xs = ys.
    Proof.
      intros * H H0 H1 H2 H3 H4 H5 xs2'Def H6 H7. subst xs2'.
      (* discard special case: *)
      assert (length xss < nL + nR \/ nL + nR <= length xss)%nat as CL by lia.
      destruct CL as [CL | CL]. {
        rewrite ?cbn_firstn_spec in *.
        rewrite ?cbn_dropRight_spec in *.
        rewrite ?cbn_skipn_spec in *.
        pose proof H3 as P.
        apply (f_equal (@length _)) in P.
        rewrite List.firstn_length, List.skipn_length in P.
        assert (length xss2 = 0)%nat as L0 by lia.
        destruct xss2 > [clear L0 | simpl in L0; exfalso; lia].
        simpl in H5. subst xs2.
        rewrite cbn_app_spec in H6. rewrite List.upto_nil in H6.
        subst yss.
        rewrite cbn_concat_spec in H7. rewrite List.concat_app in H7. simpl in H7.
        rewrite List.app_nil_r in H7.
        clear P.
        subst j xs ys.
        assert (length xss - nR <= nL)%nat by lia.
        assert (i = cbn_len_sum (List.firstn nL xss)). {
          pose proof (List.firstn_firstn xss (length xss - nR) nL) as B.
          assert (Init.Nat.min (length xss - nR) nL = length xss - nR)%nat as E by lia.
          rewrite E in B; clear E.
          rewrite <- B in H0.
          rewrite H1 in *.
          rewrite <- (List.firstn_skipn (length xss - nR) xss1) in H|-*.
          rewrite cbn_len_sum_app in H|-*.
          remember (cbn_len_sum (List.firstn (length xss - nR) xss1)) as len1.
          pose proof (cbn_len_sum_nonneg (List.skipn (length xss - nR) xss1)).
          lia.
        }
        subst i xss1.
        rewrite cbn_concat_spec.
        clear.
        revert nL. induction xss; intros; simpl.
        - rewrite List.upto_nil. rewrite List.firstn_nil. reflexivity.
        - destruct nL; simpl.
          + reflexivity.
          + pose proof (cbn_len_sum_nonneg (List.firstn nL xss)).
            rewrite List.upto_app_pushdown_r by lia. f_equal.
            rewrite <-IHxss. f_equal. lia.
      }
      (* main proof: *)
      subst.
      eapply upto_apps_pullout_l with (n := nL); try reflexivity. 1: assumption.
      f_equal. f_equal. f_equal.
      remember (cbn_skipn nL xss) as ll.
      eapply upto_apps_drop_r; try reflexivity.
      enough (cbn_len_sum (cbn_dropRight nR xss) =
                cbn_len_sum (cbn_firstn nL xss) + cbn_len_sum (cbn_dropRight nR ll)) by lia.
      subst ll.
      rewrite ?cbn_dropRight_spec, cbn_firstn_spec, cbn_skipn_spec.
      rewrite List.firstn_skipn_comm.
      rewrite List.length_skipn.
      replace (nL + (length xss - nL - nR))%nat with (length xss - nR)%nat by lia.
      rewrite <- cbn_len_sum_app.
      f_equal.
      pose proof (List.firstn_skipn nL (List.firstn (length xss - nR) xss)) as B.
      rewrite List.firstn_firstn in B.
      rewrite Nat.min_l in B by lia.
      symmetry. exact B.
    Qed.

    (* Special case of upto_apps, allowing reuse of proofs already computed for upto_apps.
       Example: If we know that i points to exactly between xs2 and xs3, we can
                discard some listlets on the right (xs4),
                and also drop the upto
       (xs0 ++ xs1 ++ xs2 ++ xs3 ++ xs4)[:i] = xs0 ++ xs1 ++ xs2 *)
    Lemma upto_apps_at_boundary: forall nL nR i (xs xs1: list A) (xss xss1: list (list A)),
        (nL + nR = length xss)%nat ->
        cbn_len_sum (cbn_firstn nL xss) <= i ->
        i <= cbn_len_sum (cbn_dropRight nR xss) ->
        cbn_firstn nL xss = xss1 ->
        cbn_concat xss = xs ->
        cbn_concat xss1 = xs1 ->
        List.upto i xs = xs1.
    Proof.
      intros. subst.
      eapply upto_apps; try eassumption; try reflexivity.
      rewrite cbn_app_spec, 3cbn_concat_spec.
      rewrite List.concat_app. simpl. rewrite List.app_nil_r.
      rewrite <- (List.app_nil_r (List.concat (cbn_firstn nL xss))) at 2.
      f_equal.
      replace (cbn_dropRight nR (cbn_skipn nL xss)) with (@nil (list A)).
      - simpl. apply List.upto_nil.
      - rewrite cbn_skipn_spec, cbn_dropRight_spec.
        symmetry. rewrite List.length_skipn.
        eapply List.firstn_eq_O. lia.
    Qed.

    Lemma from_apps_drop_l: forall n i j (xs xs2 xs2': list A) (xss xss2: list (list A)),
        cbn_len_sum (cbn_firstn n xss) <= i ->
        i - cbn_len_sum (cbn_firstn n xss) = j ->
        cbn_skipn n xss = xss2 ->
        cbn_concat xss = xs ->
        cbn_concat xss2 = xs2 ->
        List.from j xs2 = xs2' ->
        List.from i xs = xs2'.
    Proof.
      intros. subst. rewrite 2cbn_concat_spec. revert i xss H.
      induction n; intros; simpl in *.
      - f_equal. lia.
      - destruct xss.
        + f_equal. simpl. lia.
        + simpl in *.
          rewrite List.from_app. rewrite IHn by lia.
          pose proof (cbn_len_sum_nonneg (cbn_firstn n xss)).
          rewrite List.from_pastend by lia.
          rewrite List.app_nil_l.
          f_equal.
          lia.
    Qed.

    (* Example: If we know that i points somewhere into xs1 or xs2, we can
                pull some listlets (xs3 and xs4) out of the from on the right:
       (xs1 ++ xs2 ++ xs3 ++ xs4)[i:] = (xs1 ++ xs2)[:i] ++ xs3 ++ xs4 *)
    Lemma from_apps_pullout_r': forall n i (xs xs1 xs1' xs2: list A)
                                      (xss xss1 xss2: list (list A)),
        i <= cbn_len_sum (cbn_firstn n xss) ->
        cbn_firstn n xss = xss1 ->
        cbn_skipn n xss = xss2 ->
        cbn_concat xss = xs ->
        cbn_concat xss1 = xs1 ->
        cbn_concat xss2 = xs2 ->
        List.from i xs1 = xs1' ->
        List.from i xs = List.app xs1' xs2.
    Proof.
      intros; subst.
      rewrite ?cbn_concat_spec.
      rewrite <- (List.firstn_skipn n xss) at 1. rewrite List.concat_app.
      rewrite cbn_firstn_spec, cbn_skipn_spec.
      apply List.from_app_pushdown_l.
      rewrite cbn_len_sum_spec in H.
      exact H.
    Qed.

    Lemma from_apps_pullout_r: forall nR i (xs xs1 xs1' xs2: list A)
                                      (xss xss1 xss2: list (list A)),
        i <= cbn_len_sum (cbn_dropRight nR xss) ->
        cbn_dropRight nR xss = xss1 ->
        cbn_takeRight nR xss = xss2 ->
        cbn_concat xss = xs ->
        cbn_concat xss1 = xs1 ->
        cbn_concat xss2 = xs2 ->
        List.from i xs1 = xs1' ->
        List.from i xs = List.app xs1' xs2.
    Proof.
      intros. subst. eapply from_apps_pullout_r';
        rewrite ?cbn_len_sum_spec, ?cbn_firstn_spec, ?cbn_skipn_spec,
                ?cbn_takeRight_spec, ?cbn_dropRight_spec in *;
        try eassumption;
        try reflexivity.
    Qed.

    (* Example: If we know that i points somewhere into xs1 or xs2, we can
                discard some listlets on the left (xs0)
                and pull some (xs3 and xs4) out of the from on the right:
       (xs0 ++ xs1 ++ xs2 ++ xs3 ++ xs4)[i:] =
       (xs1 ++ xs2)[i - len xs0 :] ++ xs3 ++ xs4 *)
    Lemma from_apps: forall nL nR i j (xs xs2 xs2' xs3: list A)
                            (xss xss2 xss3: list (list A)),
        cbn_len_sum (cbn_firstn nL xss) <= i ->
        i <= cbn_len_sum (cbn_dropRight nR xss) ->
        i - cbn_len_sum (cbn_firstn nL xss) = j ->
        cbn_skipn nL (cbn_dropRight nR xss) = xss2 ->
        cbn_takeRight nR xss = xss3 ->
        cbn_concat xss = xs ->
        cbn_concat xss2 = xs2 ->
        cbn_concat xss3 = xs3 ->
        List.from j xs2 = xs2' ->
        List.from i xs = List.app xs2' xs3.
    Proof.
      intros. subst xs2'.
      (* discard special case: *)
      assert (length xss < nL + nR \/ nL + nR <= length xss)%nat as CL by lia.
      destruct CL as [CL | CL]. {
        rewrite ?cbn_firstn_spec in *.
        rewrite ?cbn_dropRight_spec in *.
        rewrite ?cbn_skipn_spec in *.
        pose proof H2 as P.
        apply (f_equal (@length _)) in P.
        rewrite List.skipn_length, List.firstn_length in P.
        assert (length xss2 = 0)%nat as L0 by lia.
        destruct xss2 > [clear L0 | simpl in L0; exfalso; lia].
        simpl in H5. subst xs2.
        rewrite cbn_takeRight_spec in H3.
        rewrite List.from_nil. rewrite List.app_nil_l.
        subst xs3.
        rewrite cbn_concat_spec in *.
        clear P.
        subst j xs xss3.
        assert (length xss - nR <= nL)%nat by lia.
        assert (i = cbn_len_sum (List.firstn (length xss - nR) xss)). {
          rewrite <- (List.firstn_skipn (length xss - nR) xss) in H.
          rewrite List.firstn_app in H.
          rewrite List.firstn_all2 in H by (rewrite List.firstn_length; lia).
          rewrite cbn_len_sum_app in H.
          rewrite ?cbn_len_sum_spec in *.
          lia.
        }
        subst i.
        rewrite cbn_len_sum_spec.
        clear. generalize (length xss - nR)%nat as n. clear nR.
        induction xss; intros; simpl.
        - rewrite List.from_nil. rewrite List.skipn_nil. reflexivity.
        - destruct n; simpl.
          + reflexivity.
          + rewrite <-IHxss. rewrite List.len_app. rewrite <- List.from_from by lia.
            rewrite List.from_app_pushdown_l by lia. f_equal.
            rewrite List.from_pastend by lia. reflexivity.
      }
      (* main proof: *)
      subst.
      eapply from_apps_pullout_r'. 6,4,2: reflexivity. 3: reflexivity.
      2: rewrite cbn_takeRight_spec, cbn_skipn_spec; reflexivity.
      { rewrite cbn_firstn_spec, cbn_len_sum_spec, cbn_dropRight_spec in *.
        assumption. }
      eapply from_apps_drop_l with (n := nL); try reflexivity.
      { rewrite cbn_firstn_spec. rewrite List.firstn_firstn.
        replace (Init.Nat.min nL (length xss - nR)) with nL by lia.
        assumption. }
      rewrite ?cbn_dropRight_spec, cbn_firstn_spec, cbn_skipn_spec.
      rewrite List.firstn_firstn.
      replace (Init.Nat.min nL (length xss - nR)) with nL by lia.
      reflexivity.
    Qed.

    (* Special case of from_apps, allowing reuse of proofs already computed for from_apps.
       Example: If we know that i points to exactly between xs1 and xs2, we can
                discard some listlets on the left (xs0 and xs1),
                and also drop the from
       (xs0 ++ xs1 ++ xs2 ++ xs3 ++ xs4)[i:] = xs2 ++ xs3 ++ xs4 *)
    Lemma from_apps_at_boundary: forall nL nR i (xs xs2: list A) (xss xss2: list (list A)),
        (nL + nR = length xss)%nat ->
        cbn_len_sum (cbn_firstn nL xss) <= i ->
        i <= cbn_len_sum (cbn_dropRight nR xss) ->
        cbn_skipn nL xss = xss2 ->
        cbn_concat xss = xs ->
        cbn_concat xss2 = xs2 ->
        List.from i xs = xs2.
    Proof.
      intros. subst. rewrite <- (List.app_nil_l (cbn_concat (cbn_skipn nL xss))).
      eapply from_apps; try eassumption; try reflexivity;
        rewrite ?cbn_concat_spec, ?cbn_takeRight_spec, ?cbn_skipn_spec, ?cbn_skipn_spec,
                ?cbn_dropRight_spec, ?cbn_len_sum_spec, ?cbn_firstn_spec;
        replace (length xss - nR)%nat with nL by lia.
      1: reflexivity.
      rewrite List.skipn_all2.
      - simpl. apply List.from_nil.
      - rewrite List.firstn_length. lia.
    Qed.

    Lemma push_down_from_repeatz: forall (i: Z) (a: A) (n j: Z),
        0 <= i <= n ->
        n - i = j ->
        List.from i (List.repeatz a n) = List.repeatz a j.
    Proof.
      intros. subst. unfold List.repeatz, List.from.
      replace (Z.to_nat n) with (Z.to_nat i + Z.to_nat (n - i))%nat by lia.
      rewrite List.repeat_app. rewrite List.skipn_app.
      rewrite List.repeat_length. rewrite Nat.sub_diag. rewrite List.skipn_O.
      rewrite List.skipn_all. 1: reflexivity.
      rewrite List.repeat_length. reflexivity.
    Qed.

    Lemma push_down_upto_repeatz: forall (i: Z) (a: A) (n: Z),
        0 <= i <= n ->
        List.upto i (List.repeatz a n) = List.repeatz a i.
    Proof.
      intros. subst. unfold List.repeatz, List.upto.
      replace (Z.to_nat n) with (Z.to_nat i + Z.to_nat (n - i))%nat by lia.
      rewrite List.repeat_app. rewrite List.firstn_app.
      rewrite List.repeat_length. rewrite Nat.sub_diag. rewrite List.firstn_O.
      rewrite List.app_nil_r.
      apply List.firstn_all2.
      rewrite List.repeat_length. reflexivity.
    Qed.
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

(* Sometimes, `gfirst [ t1 | t2 ]` is not quite what we want because if both t1 and t2
   fail, it swallows the error of t2 and just returns `Tactic_failure (None)`.
   We want a fallback/orelse/try-catch/single-success plus/|/try-else.
   Experimental syntax: `try t1 else t2`. *)

(* Like orelse, but t2 ignores the exception of t1 *)
Ltac2 try_else t1 t2 := orelse t1 (fun _ => t2 ()).

(* if-then-else also uses tactic(5) *)
Ltac2 Notation "try" t1(thunk(tactic(5))) "else" t2(thunk(tactic(5))) := try_else t1 t2.

Ltac2 Notation "try" t1(thunk(tactic(5))) := try0 t1.

Goal True.
  try fail "nope".
  try fail "ooh" else pose 1.
  try (pose 2; fail) else pose 3.
  try () else pose 1; pose 2.
  let r := try '(1%nat + 1%Z) else '(tt) in pose $r.
  Fail let r := try '(1%nat + 1%Z) else 2 in pose $r.
  Fail try fail "msg1" else fail "msg2". (* msg2 *)
  Fail first [ fail "msg1" | fail "msg2" ]. (* Tactic_failure (None) *)
Abort.

(* gen_stmt: ltac function taking a nat and returning a Prop
   tac: tactic to prove stmt, takes a dummy unit
   lower: min n to try
   upper: max n to try
   Returns the biggest possible n and the associated proof term *)
Ltac2 max_n_st(gen_stmt: constr -> constr)(tac: unit -> unit)
              (lower: constr)(upper: constr): (constr * constr) :=
  let rec loop n :=
    let stmt := gen_stmt n in
    try (n, '(ltac2:(tac ()) : $stmt))
    else if Constr.equal n lower then
           gfail "stmt does not hold for any n within the bounds"
         else
           lazy_match! n with
           | S ?m => loop m
           | _ => anomaly "expected a nat above %t, got %t" lower n
           end in
  loop upper.

Goal forall (b: nat), b = 12%nat -> (3 * 3 < b)%nat.
  intros.
  let tac := (fun _ =>
    lazy_match! goal with
    | [ |- ?g ] => () (* printf "goal: %t" g *)
    end;
    cbn; lia) in
  let (_, pf) := max_n_st (fun n => '(($n * $n < b)%nat)) tac '2%nat '7%nat in
  pose $pf as A.
  exact A.
Succeed Qed. Abort.

Ltac2 rec list_length_as_nat(l: constr): constr :=
  lazy_match! l with
  | nil => '(0%nat)
  | cons _ ?tail => let r := list_length_as_nat tail in '((S $r))
  end.

Ltac2 panic_if_failure(f: unit -> 'a): 'a :=
  match Control.case f with
  | Val p => let (r, _) := p in r
  | Err e => Control.throw e
  end.

(* overridden further below to just bottom_up_simpl *)
Ltac2 mutable bottom_up_simpl_recurse(e: constr): res := Control.throw Assertion_failure.

(* returns a proof whose LHS is (List.upto i l) and an RHS where the upto has been
   pushed down as far as nicely possible *)
Ltac2 rec push_down_upto(force_progress: bool)(treat_app: bool)
                        (tp: constr)(i: constr)(l: constr): res :=
  let nop := fun (_: unit) =>
               if force_progress then gfail "no progress"
               else res_nothing_to_simpl '(@List.upto $tp $i $l) in
  match! l with
  | _ => res_rewrite '(List.upto_beginning $l $i ltac2:(bottom_up_simpl_sidecond_hook ()))
  | _ => res_rewrite '(List.upto_pastend $l $i ltac2:(bottom_up_simpl_sidecond_hook ()))
  | List.app _ _ =>
      if treat_app then
        let xss := List.reify_apps l in
        let (nL, nL_pf) := max_n_st (* might fail *)
          (fun n => '(List.cbn_len_sum (List.cbn_firstn $n $xss) <= $i))
          (fun _ => cbn [List.cbn_len_sum List.cbn_firstn];
                         bottom_up_simpl_sidecond_hook ())
          '0%nat
          (list_length_as_nat xss) in
        let (nR, nR_pf) := max_n_st (* might fail *)
          (fun n => '($i <= List.cbn_len_sum (List.cbn_dropRight $n $xss)))
          (fun _ => cbn [List.cbn_len_sum List.cbn_dropRight];
                         bottom_up_simpl_sidecond_hook ())
          '0%nat
          (list_length_as_nat xss) in
        if Constr.equal nL '0%nat && Constr.equal nR '0%nat then nop () else
        match Control.case (fun _ => '(eq_refl: Nat.add $nL $nR = length $xss)) with
        | Val p => let (pf, _) := p in
          res_rewrite '(List.upto_apps_at_boundary $nL $nR $i _ _ $xss _ $pf $nL_pf $nR_pf
              ltac2:(cbn [List.cbn_firstn]; reflexivity)
              ltac2:(cbn [List.cbn_concat]; reflexivity)
              ltac2:(cbn [List.cbn_concat]; reflexivity))
        | Err _ =>
          res_rewrite '(List.upto_apps $nL $nR $i _ $l _ _ $xss _ _ _ _ $nL_pf $nR_pf
              ltac2:(cbn [List.cbn_firstn]; reflexivity)
              ltac2:(cbn [List.cbn_len_sum];
                     lazy_match! goal with
                     | [ |- ?diff = _ ] =>
                         let res := bottom_up_simpl_recurse diff in
                         let pf := eq_proof res in
                         exact $pf
                     end)
              ltac2:(cbn [List.cbn_dropRight List.cbn_skipn]; reflexivity)
              ltac2:(cbn [List.cbn_concat]; reflexivity)
              ltac2:(cbn [List.cbn_concat]; reflexivity)
              ltac2:(lazy_match! goal with
                     | [ |- List.upto ?j ?xs2 = _] =>
                         let res_rec := push_down_upto false false tp j xs2 in
                         let pf := eq_proof res_rec in
                         exact $pf
                     end)
              ltac2:(cbn [List.cbn_app]; reflexivity)
              ltac2:(cbn [List.cbn_concat]; reflexivity))
        end
      else gfail "try next match branch"
  | List.from ?j ?l =>
      let n := i in (* sized slice of size n: l[j:][:n] *)
      let r_sum := ring_simplify_res_or_nothing_to_simpl '(Z.add $j $n) in
      let sum := new_term r_sum in
      if Int.lt (ring_expr_size sum) (ring_expr_size n) then
        let pf_sum := eq_proof r_sum in
        res_rewrite '(sized_slice_to_indexed_slice $l $j $n $sum
                              ltac2:(bottom_up_simpl_sidecond_hook ()) $pf_sum)
      else gfail "ring_simplify does not shrink the expression size"
  | List.upto ?j ?ll =>
      let r1 := res_rewrite '(List.upto_upto_subsume $j $i $ll
                                      ltac2:(bottom_up_simpl_sidecond_hook ())) in
      let r2 := push_down_upto false true tp i ll in
      chain_res r1 r2
  | List.repeatz ?x ?n =>
      res_rewrite '(List.push_down_upto_repeatz $i $x $n
                      ltac2:(bottom_up_simpl_sidecond_hook ())) (* might fail! *)
  | _ => if is_concrete_enough i l true then
           let l' := convertible_list_upto i l in res_convertible l'
         else nop ()
  end.

(* returns a proof whose LHS is (List.from i l) and an RHS where the from has been
   pushed down as far as nicely possible. *)
Ltac2 rec push_down_from(force_progress: bool)(treat_app: bool)
                        (tp: constr)(i: constr)(l: constr): res :=
  (*non-lazy*)match! l with
  | _ => res_rewrite '(List.from_beginning $l $i ltac2:(bottom_up_simpl_sidecond_hook ()))
  | _ => res_rewrite '(List.from_pastend $l $i ltac2:(bottom_up_simpl_sidecond_hook ()))
  | List.app _ _ =>
      if treat_app then
        let xss := List.reify_apps l in
        let (nL, nL_pf) := max_n_st (* might fail *)
          (fun n => '(List.cbn_len_sum (List.cbn_firstn $n $xss) <= $i))
          (fun _ => cbn [List.cbn_len_sum List.cbn_firstn];
                         bottom_up_simpl_sidecond_hook ())
          '0%nat
          (list_length_as_nat xss) in
        let (nR, nR_pf) := max_n_st (* might fail *)
          (fun n => '($i <= List.cbn_len_sum (List.cbn_dropRight $n $xss)))
          (fun _ => cbn [List.cbn_len_sum List.cbn_dropRight];
                         bottom_up_simpl_sidecond_hook ())
          '0%nat
          (list_length_as_nat xss) in
        match Control.case (fun _ => '(eq_refl: Nat.add $nL $nR = length $xss)) with
        | Val p => let (pf, _) := p in
          res_rewrite '(List.from_apps_at_boundary $nL $nR $i _ _ $xss _ $pf $nL_pf $nR_pf
              ltac2:(cbn [List.cbn_skipn]; reflexivity)
              ltac2:(cbn [List.cbn_concat]; reflexivity)
              ltac2:(cbn [List.cbn_concat]; reflexivity))
        | Err _ =>
            lazy_match! nL with
            | O => lazy_match! nR with
                   | O => gfail "fall-through to last default case at end of match"
                   | S _ => res_rewrite '(List.from_apps_pullout_r $nR $i _ _ _ _ $xss _ _
                                          $nR_pf
                                          ltac2:(cbn[List.cbn_dropRight]; reflexivity)
                                          ltac2:(cbn[List.cbn_takeRight]; reflexivity)
                                          ltac2:(cbn[List.cbn_concat]; reflexivity)
                                          ltac2:(cbn[List.cbn_concat]; reflexivity)
                                          ltac2:(cbn[List.cbn_concat]; reflexivity)
                        ltac2:(lazy_match! goal with
                               | [ |- List.from _ ?xs1 = _] =>
                                   let res_rec := push_down_from false false tp i xs1 in
                                   let pf := eq_proof res_rec in
                                   exact $pf
                               end))
                   end
            | S _ => lazy_match! nR with
                     | O => res_rewrite '(List.from_apps_drop_l $nL $i _ _ _ _ $xss _
                              $nL_pf
                              ltac2:(cbn [List.cbn_len_sum List.cbn_firstn];
                                     lazy_match! goal with
                                     | [ |- ?diff = _ ] =>
                                         let res := bottom_up_simpl_recurse diff in
                                         let pf := eq_proof res in
                                         exact $pf
                                     end)
                               ltac2:(cbn[List.cbn_skipn]; reflexivity)
                               ltac2:(cbn[List.cbn_concat]; reflexivity)
                               ltac2:(cbn[List.cbn_concat]; reflexivity)
                               ltac2:(
                                 lazy_match! goal with
                                 | [ |- List.from ?j ?xs2 = _] =>
                                     let res_rec := push_down_from false false tp j xs2 in
                                     let pf := eq_proof res_rec in
                                     exact $pf
                                 end))
                     | S _ => res_rewrite '(List.from_apps $nL $nR $i _ _ _ _ _ $xss _ _
                              $nL_pf $nR_pf
                              ltac2:(cbn [List.cbn_len_sum List.cbn_firstn];
                                     lazy_match! goal with
                                     | [ |- ?diff = _ ] =>
                                         let res := bottom_up_simpl_recurse diff in
                                         let pf := eq_proof res in
                                         exact $pf
                                     end)
                               ltac2:(cbn[List.cbn_skipn List.cbn_dropRight]; reflexivity)
                               ltac2:(cbn[List.cbn_takeRight]; reflexivity)
                               ltac2:(cbn[List.cbn_concat]; reflexivity)
                               ltac2:(cbn[List.cbn_concat]; reflexivity)
                               ltac2:(cbn[List.cbn_concat]; reflexivity)
                               ltac2:(
                                 lazy_match! goal with
                                 | [ |- List.from ?j ?xs2 = _] =>
                                     let res_rec := push_down_from false false tp j xs2 in
                                     let pf := eq_proof res_rec in
                                     exact $pf
                                 end))
                     end
            end
        end
      else gfail "try next match branch"
  | List.upto ?j ?l =>
      (* l[:j][i:] = l[i:j] (notations expanding to the same term)  *)
      (*      = l[i:][:j-i] (indexed_slice_to_sized_slice)          *)
      let r_diff := ring_simplify_res_or_nothing_to_simpl '(Z.sub $j $i) in
      let diff := new_term r_diff in
      if Int.lt (ring_expr_size diff) (ring_expr_size j) then
        let pf_diff := eq_proof r_diff in
        res_rewrite '(indexed_slice_to_sized_slice $l $i $j $diff
                              ltac2:(bottom_up_simpl_sidecond_hook ()) $pf_diff)
      else gfail "ring_simplify does not shrink the expression size"
  | List.from ?j ?ll =>
      let r1 := res_rewrite '(List.from_from $ll $j $i
                                      ltac2:(bottom_up_simpl_sidecond_hook ())
                                      ltac2:(bottom_up_simpl_sidecond_hook ())) in
      let r2 := push_down_from false true tp '($j + $i) ll in
      chain_res r1 r2
  | List.repeatz ?x ?n =>
      res_rewrite '(List.push_down_from_repeatz $i $x $n _
                      ltac2:(bottom_up_simpl_sidecond_hook ()) (* <- might fail! *)
                      ltac2:(lazy_match! goal with
                             | [ |- ?diff = _ ] =>
                                 let res := bottom_up_simpl_recurse diff in
                                 let pf := eq_proof res in
                                 exact $pf
                             end))
  | _ => if is_concrete_enough i l true then
           let l' := convertible_list_from i l in res_convertible l'
         else if force_progress
              then gfail "no progress"
              else res_nothing_to_simpl '(@List.from $tp $i $l)
  end.

Section PushDownGet.
  Import List.ZIndexNotations. Local Open Scope zlist_scope.
  Context [A: Type] {inh: inhabited A}.

  Local Set Default Proof Mode "Classic".

  Lemma push_down_get_from: forall (l: list A) n i r,
      0 <= i < len l /\ 0 <= n < len l - i ->
      l[i + n] = r ->
      l[i:][n] = r.
  Proof.
    unfold List.get, List.from. intros.
    rewrite List.nth_skipn.
    destruct_one_match_hyp; destruct_one_match; try (exfalso; lia).
    rewrite <- H0. f_equal. lia.
  Qed.

  Lemma push_down_get_upto: forall (l: list A) n i r,
      0 <= n < i ->
      l[n] = r ->
      l[:i][n] = r.
  Proof.
    unfold List.get, List.upto. intros.
    rewrite List.nth_firstn by lia. assumption.
  Qed.

  Lemma push_down_get_head: forall a (l: list A) n,
      n = 0 ->
      (cons a l)[n] = a.
  Proof. intros. subst. reflexivity. Qed.

  Lemma push_down_get_tail: forall a (l: list A) n r,
      0 < n ->
      l[n - 1] = r ->
      (cons a l)[n] = r.
  Proof.
    unfold List.get. intros.
    destruct_one_match; destruct_one_match_hyp; try (exfalso; lia).
    replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia.
    simpl. assumption.
  Qed.

  Lemma push_down_get_app_l: forall (l1 l2: list A) n r,
      0 <= n < len l1 ->
      l1[n] = r ->
      (l1 ++ l2)[n] = r.
  Proof.
    unfold List.get. intros. rewrite List.app_nth1 by lia. assumption.
  Qed.

  Lemma push_down_get_app_r: forall (l1 l2: list A) n r,
      len l1 <= n ->
      l2[n - len l1] = r ->
      (l1 ++ l2)[n] = r.
  Proof.
    unfold List.get. intros. rewrite List.app_nth2 by lia.
    destruct_one_match; destruct_one_match_hyp; try (exfalso; lia).
    rewrite <- H0. f_equal. lia.
  Qed.

  Lemma push_down_get_set_same: forall (l: list A) i n x,
      0 <= i < len l ->
      n = i ->
      l[i := x][n] = x.
  Proof.
    intros. subst. unfold List.get, List.set, List.upto.
    destruct_one_match. 1: exfalso; lia.
    replace (Z.to_nat i) with (length (List.firstn (Z.to_nat i) l)) at 1.
    1: apply List.nth_middle.
    rewrite List.firstn_length. lia.
  Qed.

  Lemma push_down_get_set_diff: forall (l: list A) i n x r,
      0 <= i < len l ->
      n <> i ->
      l[n] = r ->
      l[i := x][n] = r.
  Proof.
    intros. subst. unfold List.get, List.set, List.upto.
    destruct_one_match. 1: reflexivity.
    assert (n < i \/ i < n) as C by lia.
    destruct C as [C | C].
    - rewrite List.app_nth1.
      + apply List.nth_firstn. lia.
      + rewrite List.firstn_length. lia.
    - rewrite List.app_assoc. rewrite List.app_nth2.
      + unfold List.from. rewrite List.nth_skipn. f_equal.
        rewrite List.app_length. rewrite List.firstn_length. simpl. lia.
      + rewrite List.app_length. rewrite List.firstn_length. simpl. lia.
  Qed.

  Lemma push_down_get_repeatz: forall (x: A) (c n: Z),
      0 <= n < c ->
      (List.repeatz x c)[n] = x.
  Proof.
    intros. unfold List.repeatz, List.get. rewrite List.nth_repeat by lia.
    destruct_one_match. 1: exfalso; lia. reflexivity.
  Qed.
End PushDownGet.

Ltac2 rec push_down_get(inh: constr)(l0: constr)(n: constr): res :=
  let with_sidecond_pf := fun (c: constr) (k: constr -> res) =>
    match Control.case (fun _ => '(ltac2:(bottom_up_simpl_sidecond_hook ()): $c)) with
    | Val p => let (s, _) := p in k s
    | Err _ => res_nothing_to_simpl '(@List.get _ $inh $l0 $n)
    end in
  let with_sidecond_pf2 := fun (c1: constr) (k1: constr -> res)
                               (c2: constr) (k2: constr -> res) =>
    match Control.case (fun _ => '(ltac2:(bottom_up_simpl_sidecond_hook ()): $c1)) with
    | Val p => let (s, _) := p in k1 s
    | Err _ =>
        match Control.case (fun _ => '(ltac2:(bottom_up_simpl_sidecond_hook ()): $c2)) with
        | Val p => let (s, _) := p in k2 s
        | Err _ => res_nothing_to_simpl '(@List.get _ $inh $l0 $n)
        end
    end in
  lazy_match! l0 with
  | List.from ?i ?l => with_sidecond_pf
      '(0 <= $i < Z.of_nat (List.length $l) /\ 0 <= $n < Z.of_nat (List.length $l) - $i)
      (fun s =>
         let res := push_down_get inh l '($i + $n) in
         let rhs := new_term res in
         let pf := eq_proof res in
         res_rewrite '(@push_down_get_from _ $inh $l $n $i $rhs $s $pf))
  | List.upto ?i ?l => with_sidecond_pf '(0 <= $n < $i) (fun s =>
      let res := push_down_get inh l n in
      let rhs := new_term res in
      let pf := eq_proof res in
      res_rewrite '(@push_down_get_upto _ $inh $l $n $i $rhs $s $pf))
  | cons ?h ?t => with_sidecond_pf2
      '($n = 0) (fun s => res_rewrite '(@push_down_get_head _ $inh $h $t $n $s))
      '(0 < $n) (fun s => let res := push_down_get inh t '($n - 1) in
                          let rhs := new_term res in
                          let pf := eq_proof res in
                          res_rewrite '(@push_down_get_tail _ $inh $h $t $n $rhs $s $pf))
  | List.app ?l1 ?l2 => with_sidecond_pf2
      '(0 <= $n < Z.of_nat (length $l1)) (fun s =>
         let res := push_down_get inh l1 n in
         let rhs := new_term res in
         let pf := eq_proof res in
         res_rewrite '(@push_down_get_app_l _ $inh $l1 $l2 $n $rhs $s $pf))
      '(Z.of_nat (length $l1) <= $n) (fun s =>
         let res := push_down_get inh l2 '($n - Z.of_nat (length $l1)) in
         let rhs := new_term res in
         let pf := eq_proof res in
         res_rewrite '(@push_down_get_app_r _ $inh $l1 $l2 $n $rhs $s $pf))
  | List.set ?l ?i ?x => with_sidecond_pf '(0 <= $i < Z.of_nat (length $l)) (fun b =>
      with_sidecond_pf2
        '($n = $i) (fun s => res_rewrite '(@push_down_get_set_same _ $inh $l $i $n $x $b $s))
        '($n <> $i) (fun s =>
            let res := push_down_get inh l n in
            let rhs := new_term res in
            let pf := eq_proof res in
            res_rewrite '(@push_down_get_set_diff _ $inh $l $i $n $x $rhs $b $s $pf)))
  | List.repeatz ?x ?c => with_sidecond_pf '(0 <= $n < $c) (fun s =>
      res_rewrite '(@push_down_get_repeatz _ $inh $x $c $n $s))
  | _ => res_nothing_to_simpl '(@List.get _ $inh $l0 $n)
  end.

(* We view the push_down_get procedure as computing a new index
   At the end of the toplevel call, if the index changed, we ring_simplify it once. *)
Ltac2 rec push_down_get_top(inh: constr)(l0: constr)(n: constr): res :=
  panic_if_failure (fun _ =>
  let res := push_down_get inh l0 n in
  if did_something res then
    let rhs := new_term res in
    lazy_match! rhs with
    | @List.get ?tp2 ?inh2 ?l2 ?i2 =>
        let resi := ring_simplify_res_or_nothing_to_simpl i2 in
        let resiLifted := lift_res1 rhs '(@List.get $tp2 $inh2 $l2) resi in
        chain_res res resiLifted
    | _ => res
    end
  else res).

Ltac2 rec is_concrete_list(e: constr): bool :=
  lazy_match! e with
  | nil => true
  | cons _ ?tl => is_concrete_list tl
  | _ => false
  end.

Ltac2 rec constr_list_length(e: constr): int :=
  lazy_match! e with
  | nil => 0
  | cons _ ?tl => Int.add 1 (constr_list_length tl)
  end.

Ltac2 rec unsnoc_constr_list(e: constr): constr * constr :=
  lazy_match! e with
  | cons ?x (@nil ?tp) => ('(@nil $tp), x)
  | cons ?h ?tl => let (l, last) := unsnoc_constr_list tl in
                   ('(cons $h $l), last)
  end.

Ltac2 uncons_constr_list(e: constr): constr * constr :=
  lazy_match! e with
  | cons ?h ?tl => (h, tl)
  end.

Ltac2 local_zlist_simpl(e: constr): res :=
  match! e with
  | @List.upto ?tp ?i ?l => push_down_upto true true tp i l
  | @List.from ?tp ?i ?l => push_down_from true true tp i l
  | @List.get _ ?inh ?l ?i =>
      if is_concrete_enough i l false
      then res_convertible (convertible_list_get inh l i)
      else push_down_get_top inh l i
  | @List.repeatz ?tp _ Z0 => res_convertible '(@nil $tp)
  | List.app ?xs nil => res_rewrite '(List.app_nil_r $xs)
  | List.app nil ?xs => res_convertible xs
  | List.app (cons ?x nil) (List.repeatz ?x ?n) =>
      res_rewrite '(List.repeatz_singleton_l $x $n ltac2:(bottom_up_simpl_sidecond_hook ()))
  | List.app (List.repeatz ?x ?n) (cons ?x nil) =>
      res_rewrite '(List.repeatz_singleton_r $x $n ltac2:(bottom_up_simpl_sidecond_hook ()))
  | List.app ?xs ?ys =>
      if is_concrete_list xs && is_concrete_list ys then
        (* Note: (is_concrete_list ys) is not necessary for prepend_concrete_list
           to work, but we want to use cons only for list literals, ie. we don't
           want lists like (e1 :: e2 :: non_concrete_tail) *)
        res_convertible (prepend_concrete_list xs ys)
      (* TODO also check if xs and ys are adjacent slices of the same base list *)
      else
        let xss := List.reify_apps_and_cons xs in
        let yss := List.reify_apps_and_cons ys in
        if Int.lt 2 (Int.add (constr_list_length xss) (constr_list_length yss)) then
          let (xss', last_xs) := unsnoc_constr_list xss in
          let (first_ys, yss') := uncons_constr_list yss in
          let res := bottom_up_simpl_recurse '(List.app $last_xs $first_ys) in
          let combined := new_term res in
          let pf := eq_proof res in
          if Int.equal 1 (constr_list_length (List.reify_apps_and_cons combined)) then
            res_rewrite '(List.reassoc_app_mergeable_in_middle $xss' $yss'
                            $last_xs $first_ys $combined $xs $ys _ eq_refl eq_refl $pf
                            ltac2:(cbn[List.cbn_concat List.cbn_app]; reflexivity))
          else
            lazy_match! xss' with
            | nil => gfail "nothing to simplify" (* already a right-leaning ++ *)
            | cons _ _ => (* reassociate ((xss1 ++ .. ++ xssN) ++ (yss1 ++ .. ++ yssN))
                             into (xss1 ++ .. ++ xssN ++ yss1 ++ .. ++ yssN) *)
                res_rewrite '(List.reassoc_app $xss $yss $xs $ys _ eq_refl eq_refl
                                ltac2:(cbn [List.cbn_concat List.cbn_app]; reflexivity))
            end
        else (* xss and yss both consist of only one listlet *)
          gfail "nothing to simplify"
  | @cons ?tp ?x ?xs =>
      if is_concrete_list xs then gfail "nothing to simplify" else
        lazy_match! xs with
        | List.app ?xs1 ?xs2 =>
            if is_concrete_list xs1
            then res_convertible '(List.app (cons $x $xs1) $xs2)
            else res_convertible '(List.app (cons $x nil) $xs)
        | _ => res_convertible '(List.app (cons $x nil) $xs)
        end
  end.

Ltac2 is_unary_Z_op(op: constr): bool :=
  lazy_match! op with
  | Z.of_nat => true
  | Z.to_nat => true
  | Z.succ => true
  | Z.pred => true
  | Z.opp => true
  | Z.log2 => true
  | Z.log2_up => true
  | _ => false
  end.

Ltac2 is_unary_nat_op(op: constr): bool :=
  lazy_match! op with
  | Nat.succ => true
  | Nat.pred => true
  | _ => false
  end.

Ltac2 is_binary_Z_op(op: constr): bool :=
  lazy_match! op with
  | Z.add => true
  | Z.sub => true
  | Z.mul => true
  | Z.div => true
  | Z.modulo => true
  | Z.quot => true
  | Z.rem => true
  | Z.pow => true
  | Z.shiftl => true
  | Z.shiftr => true
  | Z.land => true
  | Z.lor => true
  | Z.lxor => true
  | Z.ldiff => true
  | Z.clearbit => true
  | Z.setbit => true
  | Z.min => true
  | Z.max => true
  | _ => false
  end.

Ltac2 is_binary_nat_op(op: constr): bool :=
  lazy_match! op with
  | Nat.add => true
  | Nat.sub => true
  | Nat.mul => true
  | Nat.div => true
  | Nat.min => true
  | Nat.max => true
  | _ => false
  end.

Ltac2 local_ground_number_simpl(e: constr): res :=
  lazy_match! e with
  | ?f ?x ?y =>
      if Constr.is_const f then
        if is_binary_Z_op f then
          lazy_match! e with
          | Z.pow 2 _ => gfail "not simplifying powers of 2"
          | _ => if is_Z_const x && is_Z_const y
                 then res_convertible (eval cbv in $e)
                 else gfail "not constant"
          end
        else if is_binary_nat_op f && is_nat_const x && is_nat_const y
             then res_convertible (eval cbv in $e)
             else gfail "not constant"
      else gfail "not constant"
  | ?f ?x =>
      if Constr.is_const f &&
           (is_unary_Z_op f && is_Z_const x || is_unary_nat_op f && is_nat_const x)
      then res_convertible (eval cbv in $e)
      else gfail "not constant"
  end.

Goal forall (a b c: Z), a + b - 2 * a = c -> -a + b = c.
Proof.
  intros.
  lazy_match! Constr.type 'H with
  | ?e = _ =>
      let r := local_ring_simplify OtherExpr e in
      let n := new_term r in
      let pf := eq_proof r in
      eassert ($n = c) as H' by (etransitivity > [symmetry; exact $pf | exact H])
  end.
  exact H'.
Succeed Qed. Abort.

Goal forall (a b: Z), True.
Proof.
  intros.
  Fail let e := '(a + b) in let r := local_ring_simplify OtherExpr e in ().
  (* nothing to simplify (progress fails) *)
Abort.

Ltac2 mutable rec is_substitutable_rhs(rhs: constr): bool :=
  Constr.is_var rhs ||
  Constr.is_const rhs ||
  is_Z_const rhs ||
  lazy_match! rhs with
  | word.of_Z ?x => is_substitutable_rhs x
  | word.unsigned ?x => is_substitutable_rhs x
  | _ => false
  end.

(* After following a series of `var1 = var2` equations, we arrive at an equation
   of the form `var = rhs` with `rhs` not a var, but potentially small enough
   to be substituted. This function tells if `rhs` is indeed "small enough". *)
Ltac2 mutable is_small_terminal_rhs(rhs: constr): bool :=
  neg (Constr.is_var rhs) && is_substitutable_rhs rhs.

Ltac2 constr_to_var_ref(c: constr): Std.reference option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var id => Some (Std.VarRef id)
  | _ => None
  end.

Ltac2 rec unfold_to_const(seen: constr list)(e: constr): res :=
  let exploit_eq := fun (new: constr)(r: res) =>
    if List.exist (Constr.equal new) seen then Control.zero Not_applicable else
    if is_small_terminal_rhs new then r else
    chain_res r (unfold_to_const (new :: seen) new) in
  match constr_to_var_ref e with
  | Some ref =>
      (* Beware: Ltac2's Std.eval_cbv does not match Ltac1's `eval cbv in`!
         https://github.com/coq/coq/issues/14303
         Ltac2 silently does nothing if r is not unfoldable. *)
      let e' := Std.eval_cbv_delta [ref] e in
      if Constr.equal e e' then
        match! goal with
        | [ h: ?lhs = ?rhs |- _ ] =>
            if Constr.equal lhs e
            then exploit_eq rhs (res_rewrite (Control.hyp h))
            else if Constr.equal rhs e
            then exploit_eq lhs (res_rewrite (let h := Control.hyp h in constr:(eq_sym $h)))
            else Control.zero Not_applicable
        end
      else exploit_eq e' (res_convertible e')
  | None => Control.zero Not_applicable
  end.

Ltac2 local_follow_eqs_until_const_val(e: constr): res :=
  unfold_to_const [] e.

Ltac2 local_nonring_nonground_Z_simpl e :=
  lazy_match! e with
  | Z.div ?x 1 => res_rewrite '(Z.div_1_r $x)
  | Z.div ?x ?d =>
      let x_eq_prod_pf := cancel_div_rec d x in
      res_rewrite '(cancel_div_done $d $x _
                            ltac2:(bottom_up_simpl_sidecond_hook ()) $x_eq_prod_pf)
  end.

(* Note: we use '(...) most of the time, but when we rely on typeclass search,
   (eg to find a word.ok), we have to use constr:(...), because '(...) does not
   run typeclass search, and instead just creates and shelves an evar. *)

Ltac2 rec push_down_unsigned(w: constr): res :=
  lazy_match! w with
  | ?f1 ?a0 =>
      lazy_match! f1 with
      | @word.of_Z ?width ?word =>
          first_val
            [ res_rewrite constr:(@word.unsigned_of_Z_nowrap $width $word _ $a0
                                    ltac2:(bottom_up_simpl_sidecond_hook ()))
            | res_rewrite constr:(@word.unsigned_of_Z_modwrap $width $word _ $a0) ]
      | @word.opp ?width ?word =>
          let r_a0 := push_down_unsigned a0 in
          let pf0 := eq_proof r_a0 in
          lazy_match! new_term r_a0 with
          | 0 => res_rewrite constr:(word.unsigned_opp_0 $a0 $pf0)
          | _ => first_val [ res_rewrite constr:(word.unsigned_opp_eq_nowrap $pf0
                                             ltac2:(bottom_up_simpl_sidecond_hook ()))
                           | res_nothing_to_simpl constr:(word.unsigned $w) ]
          end
      | ?f2 ?a1 =>
          lazy_match! f2 with
          | word.add => push_down_unsigned_app2 w 'word.unsigned_add_eq_nowrap a1 a0
          | word.sub => push_down_unsigned_app2 w 'word.unsigned_sub_eq_nowrap a1 a0
          | word.mul => push_down_unsigned_app2 w 'word.unsigned_mul_eq_nowrap a1 a0
          | _ => res_nothing_to_simpl constr:(word.unsigned $w)
          end
      | _ => res_nothing_to_simpl constr:(word.unsigned $w)
      end
  | _ => res_nothing_to_simpl constr:(word.unsigned $w)
  end
with push_down_unsigned_app2(w: constr)(lem: constr)(a1: constr)(a0: constr): res :=
  let pf0 := eq_proof (push_down_unsigned a0) in
  let pf1 := eq_proof (push_down_unsigned a1) in
  first_val
    [ res_rewrite constr:($lem _ _ _ _ _ _ _ $pf1 $pf0 ltac2:(bottom_up_simpl_sidecond_hook ()))
    | res_nothing_to_simpl constr:(word.unsigned $w) ].

Ltac2 local_word_simpl(e: constr): res :=
  lazy_match! e with
  | word.unsigned ?w => push_down_unsigned w
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
      res_rewrite constr:(@word.of_Z_mod $width $word _ $z)
  | @word.of_Z ?width ?word (word.unsigned ?w) =>
      res_rewrite constr:(@word.of_Z_unsigned $width $word _ $w)
  end.

(* Nodes like eg (List.length (cons a (cons b (app (cons c xs) ys)))) can
   require an arbitrary number of simplification steps at the same node.

   ---> but that's more of a "push down List.length" algorithm, because once
   we have (len (cons c xs) + len ys), we need to recurse not at the current
   node, but down into the args of + !
Ltac2 saturate_local_simpl parent_kind e :=
  let r := local_simpl_hook parent_kind e in
  lazy_match! r SimplAgain with
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

Section PushDownLen.
  Import List.ZIndexNotations. Local Open Scope zlist_scope.
  Context [A: Type].

  Lemma push_down_len_from: forall (l: list A) i n r,
      len l = n ->
      0 <= i <= n ->
      n - i = r ->
      len l[i:] = r.
  Proof. intros. subst. eapply List.len_from. assumption. Qed.

  Lemma push_down_len_from_pastend: forall (l: list A) i n,
      len l = n ->
      n <= i ->
      len l[i:] = 0.
  Proof. intros. subst. rewrite List.from_pastend by assumption. reflexivity. Qed.

  Lemma push_down_len_from_negative: forall (l: list A) i n,
      len l = n ->
      i <= 0 ->
      len l[i:] = n.
  Proof.
    intros. subst. unfold List.from. replace (Z.to_nat i) with O by lia. reflexivity.
  Qed.

  Lemma push_down_len_upto: forall (l: list A) i n,
      len l = n ->
      0 <= i <= n ->
      len l[:i] = i.
  Proof. intros. subst. eapply List.len_upto. assumption. Qed.

  Lemma push_down_len_upto_pastend: forall (l: list A) i n,
      len l = n ->
      n <= i ->
      len l[:i] = n.
  Proof. intros. subst. rewrite List.upto_pastend by assumption. reflexivity. Qed.

  Lemma push_down_len_upto_negative: forall (l: list A) i n,
      len l = n ->
      i <= 0 ->
      len l[:i] = 0.
  Proof.
    intros. subst. unfold List.upto. replace (Z.to_nat i) with O by lia. reflexivity.
  Qed.

  Lemma push_down_len_cons: forall a (l: list A) n,
      1 + len l = n ->
      len (cons a l) = n.
  Proof. intros. subst. rewrite List.length_cons. lia. Qed.

  Lemma push_down_len_app: forall (l1 l2: list A) n1 n2 n,
      len l1 = n1 ->
      len l2 = n2 ->
      n1 + n2 = n ->
      len (l1 ++ l2) = n.
  Proof. intros. subst. eapply List.len_app. Qed.

  Lemma push_down_len_set: forall (l: list A) i n x,
      len l = n ->
      0 <= i < n ->
      len l[i := x] = n.
  Proof. intros. subst. eapply List.len_set. assumption. Qed.

  Lemma push_down_len_repeatz: forall (x: A) (n: Z),
      0 <= n ->
      len (List.repeatz x n) = n.
  Proof. intros. subst. eapply List.len_repeatz. assumption. Qed.

  Lemma push_down_len_repeatz_max: forall (x: A) (n: Z),
      len (List.repeatz x n) = Z.max n 0.
  Proof.
    intros. assert (n < 0 \/ 0 <= n) as C by lia. destruct C.
    - unfold List.repeatz. replace (Z.to_nat n) with O by lia. simpl. lia.
    - replace (Z.max n 0) with n by lia. eapply List.len_repeatz. assumption.
  Qed.
End PushDownLen.

Ltac2 rec concrete_list_length_err(l: constr): constr option :=
  lazy_match! l with
  | nil => Some 'O
  | cons _ ?t =>
      match concrete_list_length_err t with
      | Some r => Some '(S $r)
      | None => None
      end
  | _ => None
  end.

Ltac2 rec push_down_len(x: constr): res :=
  lazy_match! x with
  | List.from ?i ?l =>
      let r_len_l := push_down_len l in
      let len_l := new_term r_len_l in
      let pf_len_l := eq_proof r_len_l in
      first_val
        [ (* Case: index i is within bounds *)
          let sidecond := '(ltac2:(bottom_up_simpl_sidecond_hook ()): 0 <= $i <= $len_l) in
          let r_diff := ring_simplify_res_or_nothing_to_simpl '(Z.sub $len_l $i) in
          let diff := new_term r_diff in
          let pf_diff := eq_proof r_diff in
          res_rewrite
            '(push_down_len_from $l $i $len_l $diff $pf_len_l $sidecond $pf_diff)
        | (* Case: index i is too big *)
          let sidecond := '(ltac2:(bottom_up_simpl_sidecond_hook ()): $len_l <= $i) in
          res_rewrite '(push_down_len_from_pastend $l $i $len_l $pf_len_l $sidecond)
        | (* Case: index i is too small *)
          let sidecond := '(ltac2:(bottom_up_simpl_sidecond_hook ()): $i <= 0) in
          res_rewrite '(push_down_len_from_negative $l $i $len_l $pf_len_l $sidecond)
        | (* Case: unknown whether index is is within bounds, so the List.from remains *)
          res_nothing_to_simpl '(Z.of_nat (List.length $x)) ]
  | @List.upto ?tp ?i ?l =>
      let r_len_l := push_down_len l in
      let len_l := new_term r_len_l in
      let pf_len_l := eq_proof r_len_l in
      first_val
        [ (* Case: index i is within bounds *)
          let sidecond := '(ltac2:(bottom_up_simpl_sidecond_hook ()): 0 <= $i <= $len_l) in
          res_rewrite '(push_down_len_upto $l $i $len_l $pf_len_l $sidecond)
        | (* Case: index i is too big *)
          let sidecond := '(ltac2:(bottom_up_simpl_sidecond_hook ()): $len_l <= $i) in
          res_rewrite '(push_down_len_upto_pastend $i $len_l $pf_len_l $sidecond)
        | (* Case: index i is too small *)
          let sidecond := '(ltac2:(bottom_up_simpl_sidecond_hook ()): $i <= 0) in
          res_rewrite '(push_down_len_upto_negative $l $i $len_l $pf_len_l $sidecond)
        | (* Case: unknown whether index is is within bounds, so the List.upto remains *)
          res_nothing_to_simpl '(Z.of_nat (List.length $x)) ]
  | nil => res_convertible 'Z0
  | cons ?h ?t =>
      match concrete_list_length_err t with
      | Some n => let z := eval cbv in (Z.of_nat (S $n)) in res_convertible z
      | None =>
          let r_len_t := push_down_len t in
          let len_t := new_term r_len_t in
          let pf_len_t := eq_proof r_len_t in
          let r_oneplus := ring_simplify_res_or_nothing_to_simpl '(Z.add 1 $len_t) in
          let oneplus := new_term r_oneplus in
          let pf_oneplus := eq_proof r_oneplus in
          res_rewrite '(push_down_len_cons $h $t $oneplus $pf_oneplus)
      end
  | @List.app ?tp ?l1 ?l2 =>
      let r_len_l1 := push_down_len l1 in
      let r_len_l2 := push_down_len l2 in
      let len_l1 := new_term r_len_l1 in
      let len_l2 := new_term r_len_l2 in
      let r_sum_lens := ring_simplify_res_or_nothing_to_simpl '(Z.add $len_l1 $len_l2) in
      let sum_lens := new_term r_sum_lens in
      let pf_len_l1 := eq_proof r_len_l1 in
      let pf_len_l2 := eq_proof r_len_l2 in
      let pf_sum_lens := eq_proof r_sum_lens in
      res_rewrite '(push_down_len_app $l1 $l2 $len_l1 $len_l2 $sum_lens
                                      $pf_len_l1 $pf_len_l2 $pf_sum_lens)
  | @List.set ?tp ?l ?i ?x =>
      let r_len_l := push_down_len l in
      let len_l := new_term r_len_l in
      let pf_len_l := eq_proof r_len_l in
      let g := '(0 <= $i < $len_l) in
      first_val
        [ let s := '(ltac2:(bottom_up_simpl_sidecond_hook ()) : $g) in
          res_rewrite '(push_down_len_set $l $i $len_l $x $pf_len_l $s)
        | (* TODO Should we fail here (and in more places)? *)
          res_nothing_to_simpl '(Z.of_nat (List.length $x)) ]
  | List.repeatz ?a ?n =>
      first_val
        [ (* Case: n is provably nonnegative *)
          let sidecond := '(ltac2:(bottom_up_simpl_sidecond_hook ()): 0 <= $n) in
          res_rewrite '(push_down_len_repeatz $a $n $sidecond)
        | (* Case: n might be negative *)
          res_rewrite '(push_down_len_repeatz_max $a $n) ]
  | _ => res_nothing_to_simpl '(Z.of_nat (List.length $x))
  end.

Ltac2 push_down_len_top(e: constr): res :=
  lazy_match! e with
  | Z.of_nat (List.length ?l) => push_down_len l
  end.

Ltac2 mutable local_simpl_hook(parent_kind: expr_kind)(e: constr): res :=
  first_val
    [ local_follow_eqs_until_const_val e
    | local_zlist_simpl e
    | local_ring_simplify parent_kind e
    | local_ground_number_simpl e
    | push_down_len_top e
    | local_word_simpl e (* <-- not strictly local, might do a whole traversal *)
    | local_nonring_nonground_Z_simpl e
    | res_nothing_to_simpl e ].

Ltac2 rec bottom_up_simpl(parent_kind: expr_kind)(e: constr): res :=
  let current_kind := get_expr_kind e in
  let r_rec :=
    match current_kind with
    | OtherExpr =>
        lazy_match! e with
        | ?f ?x => lift_res_app e
                     (bottom_up_simpl OtherExpr f)
                     (bottom_up_simpl OtherExpr x)
        | match ?b with
          | true => ?thn
          | false => ?els
          end => lift_res_if e (bottom_up_simpl OtherExpr b)
                               (bottom_up_simpl OtherExpr thn)
                               (bottom_up_simpl OtherExpr els)
        | ?p -> ?q => lift_res_impl e (bottom_up_simpl OtherExpr p)
                                      (bottom_up_simpl OtherExpr q)
        | _ => res_nothing_to_simpl e
        end
    | _ => (* head of app is a known function symbol that doesn't need to be simplified *)
        lazy_match! e with
        | ?f ?x ?y => lift_res2 e f
                        (bottom_up_simpl current_kind x)
                        (bottom_up_simpl current_kind y)
        | ?f ?x => lift_res1 e f (bottom_up_simpl current_kind x)
        | _ => res_nothing_to_simpl e
        end
    end in
  let r_loc := local_simpl_hook parent_kind (new_term r_rec) in
  chain_res r_rec r_loc.

Ltac2 Set bottom_up_simpl_recurse := fun e => bottom_up_simpl OtherExpr e.

(* Consider `word.unsigned (foo (a + 0) ^+ x ^- foo a ^+ y)`:
   The argument of word.unsigned needs a first full bottom-up traversal to simplify
   it into `x ^+ y`, and after that, another push-down-word.unsigned traversal to
   obtain `word.unsigned x + word.unsigned y` (if no overflow).

   On the other hand, if you start pushing down len too early, not a problem,
   because list operations don't cancel like word.sub does.

   Therefore, pushing down len could be integrated into bottom_up_simpl, whereas
   pushing down word.unsigned runs *after* it in local_simpl_hook *)

Definition protect_conclusion(P: Prop) := P.
(* protect_conclusion is needed because if P2 is an implication,
   `apply ... in ...` creates subgoals for everything on the left of a -> in P2 *)
Lemma rew_Prop_hyp: forall (P1 P2: Prop) (pf: P1 = P2), P1 -> protect_conclusion P2.
Proof. intros. subst. assumption. Qed.

Lemma rew_Prop_goal: forall (P1 P2: Prop) (pf: P1 = P2), P2 -> P1.
Proof. intros. subst. assumption. Qed.

Definition forbidden(P: Prop) := P.

Ltac2 Type exn ::= [ Nothing_to_simplify ].

Ltac2 Type exn ::= [ Undo ].

(* run t and undo its effects (except for its print output), but if it fails,
   turn the failure into an uncatchable panic *)
Ltac2 undo(t: unit -> unit): unit :=
  match Control.case (fun _ => t (); Control.zero Undo) with
  | Val _ => Control.throw Assertion_failure
  | Err e => match e with
             | Undo => ()
             | _ => Control.throw e
             end
  end.

Ltac pre_log_simpl_hook := idtac.

Ltac2 log_simpl_inactive(t1: constr)(t2: constr) := undo (fun _ =>
  assert ($t1 = $t2) >
  [ repeat (lazy_match! goal with
            | [h: forbidden _ |- _] => Std.clear [h]
            end);
    ltac1:(pre_log_simpl_hook; log_sidecond)
  | ]).

Ltac2 log_simpl(t1: constr)(t2: constr) := ().

Ltac2 fail_if_no_progress () := Control.zero Nothing_to_simplify.
Ltac2 silent_if_no_progress () := ().
Ltac2 bottom_up_simpl_in_hyp_of_type(no_progress: unit -> unit)(h: ident)(t: constr): unit :=
  lazy_match! Constr.type t with
  | Prop =>
      change (forbidden $t) in $h; (* don't use h to simplify itself *)
      let r := bottom_up_simpl OtherExpr t in
      change $t in $h;
      if did_something r then
        let pf := eq_proof r in
        let t' := new_term r in
        log_simpl t t';
        eapply (rew_Prop_hyp $t $t' $pf) in $h;
        change $t' in $h
      else no_progress ()
  | _ => no_progress ()
  end.

Ltac2 bottom_up_simpl_in_hyp(h: ident): unit :=
  let t := Constr.type (Control.hyp h) in
  bottom_up_simpl_in_hyp_of_type fail_if_no_progress h t.

Ltac2 bottom_up_simpl_in_letbound_var(x: ident)(b: constr)(_t: constr): unit :=
  let r := bottom_up_simpl OtherExpr b in
  if did_something r then
    (* Note: will fail if x appears in the type of other expressions in a
       way that would lead to ill-typed terms, or if x appears on the rhs
       of another let-bound var, because `rewrite` doesn't affect the rhs
       of let-bound vars, so the clear will fail. *)
    (try (
      let e := Fresh.in_goal @e in
      let b' := new_term r in
      let pf := eq_proof r in
      let x_as_constr := Control.hyp x in
      let y := Fresh.in_goal x in
      pose ($y := $b');
      let y_as_constr := Control.hyp y in
      (* Note: we feed pf into the proof engine before doing anything like
         `rewrite` or `replace`, because these might rename variables in such
         a way that pf doesn't typecheck any more! *)
      (assert ($x_as_constr = $y_as_constr) as $e
          by exact $pf); (* `subst x y` is done by conversion *)
      let e_as_constr := Control.hyp e in
      rewrite $e_as_constr in *;
      move $y after $x;
      clear $x $e;
      Std.rename [(y, x)]))
  else ().

(* foreach_hyp/var already focus, and bottom_up_simpl_in_hyp only makes sense
   when already focused, but if we do `all: bottom_up_simpl_in_goal ()`, we
   have to focus explicitly. *)
Ltac2 bottom_up_simpl_in_goal0(no_progress: unit -> unit) := Control.enter (fun _ =>
  let t := Control.goal () in
  lazy_match! Constr.type t with
  | Prop =>
      let r := bottom_up_simpl OtherExpr t in
      if did_something r then
        let pf := eq_proof r in
        let t' := new_term r in
        log_simpl t t';
        eapply (rew_Prop_goal $t $t' $pf)
      else no_progress ()
  | _ => fail "not a Prop"
  end).

Ltac2 bottom_up_simpl_in_goal () := bottom_up_simpl_in_goal0 fail_if_no_progress.
Ltac2 bottom_up_simpl_in_goal_nop_ok () := bottom_up_simpl_in_goal0 silent_if_no_progress.

Ltac2 bottom_up_simpl_in_hyps () :=
  foreach_hyp (bottom_up_simpl_in_hyp_of_type silent_if_no_progress).

Ltac2 bottom_up_simpl_in_vars () :=
  foreach_var bottom_up_simpl_in_letbound_var.

Ltac2 bottom_up_simpl_in_hyps_and_vars () :=
  bottom_up_simpl_in_hyps (); bottom_up_simpl_in_vars ().

Ltac2 bottom_up_simpl_in_all () :=
  bottom_up_simpl_in_hyps (); bottom_up_simpl_in_vars ();
  bottom_up_simpl_in_goal_nop_ok ().

Ltac _bottom_up_simpl_in_hyp :=
  ltac2:(h1 |- bottom_up_simpl_in_hyp (Option.get (Ltac1.to_ident h1))).
Tactic Notation "bottom_up_simpl_in_hyp" ident(h) := _bottom_up_simpl_in_hyp h.

Ltac _bottom_up_simpl_in_hyp_of_type :=
  ltac2:(h1 t1 |- bottom_up_simpl_in_hyp_of_type silent_if_no_progress
                    (Option.get (Ltac1.to_ident h1))
                    (Option.get (Ltac1.to_constr t1))).
Tactic Notation "bottom_up_simpl_in_hyp_of_type" ident(h) constr(t) :=
  _bottom_up_simpl_in_hyp_of_type h t.

Ltac bottom_up_simpl_in_goal := ltac2:(bottom_up_simpl_in_goal ()).
Ltac bottom_up_simpl_in_goal_nop_ok := ltac2:(bottom_up_simpl_in_goal_nop_ok ()).

Ltac bottom_up_simpl_in_hyps := ltac2:(bottom_up_simpl_in_hyps ()).

Ltac bottom_up_simpl_in_vars := ltac2:(bottom_up_simpl_in_vars ()).

Ltac bottom_up_simpl_in_hyps_and_vars := ltac2:(bottom_up_simpl_in_hyps_and_vars ()).

Ltac bottom_up_simpl_in_all := ltac2:(bottom_up_simpl_in_all ()).

Local Hint Mode Word.Interface.word - : typeclass_instances.

Section Tests.
  Goal forall a: Z, a = a + 0 -> a = a + 0 -> True.
    intros ? e_nosimpl e.
    foreach_hyp (fun h t => if Ident.equal h @e_nosimpl then ()
                            else bottom_up_simpl_in_hyp_of_type silent_if_no_progress h t).
    constructor.
  Succeed Qed. Abort.

  Context {word: word.word 32} {word_ok: word.ok word}.

  Add Ring wring : (Properties.word.ring_theory (word := word))
      ((* too expensive: preprocess [autorewrite with rew_word_morphism], *)
       morphism (Properties.word.ring_morph (word := word)),
       constants [Properties.word_cst]).

  Hypothesis P: Z -> Prop.
  Hypothesis Q: list Z -> Prop.

  Import ZList.List.ZIndexNotations. Local Open Scope zlist_scope.
  Import bedrock2.WordNotations. Local Open Scope word_scope.

  Ltac2 refl0 () :=
    lazy_match! goal with
    | [ |- ?x = ?x ] => reflexivity
    end.
  Ltac2 Notation refl := refl0 ().

  (* For debugging: hides lia proofs, so the output of `Show Proof` is more readable
  Ltac2 Set bottom_up_simpl_sidecond_hook := fun _ =>
      lazy_match! goal with
      | [ |- ?g ] => eapply (@xlia $g)
      end;
      lia. *)

  Goal forall (n b: Z) (bs: list Z),
      Q (List.repeatz b (n - n) ++ bs[2/4:] ++
           List.repeatz b (word.unsigned (word.of_Z 0))) = Q bs.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (byte_of_Z: Z -> Byte.byte) (b: word) (bs: list Byte.byte),
      List.repeatz (byte_of_Z \[b]) \[/[0]] ++ bs[\[/[0]]:] = bs.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall a, 0 <= a < 2 ^ 32 -> let w := \[/[a]] in w = a.
  Proof. intros. bottom_up_simpl_in_vars (). subst w. refl. Succeed Qed. Abort.

  Goal forall a, 0 <= a < 2 ^ 32 -> let x := [|a|][0] in let w := \[/[a]] in w = x.
  Proof. intros. bottom_up_simpl_in_vars (). subst x w. refl. Succeed Qed. Abort.

  Goal forall a,
      0 <= a < 2 ^ 32 -> let w := 1 + \[/[a]] in let y := w in w = 0 -> y = 1 + \[/[a]].
  Proof.
    intros.
    (* Note: w can only be simplified if we `subst y` before, because
       replacing old w by new w in y's body can't be done by replace/rewrite *)
    bottom_up_simpl_in_vars ().
    subst w y.
    refl.
  Succeed Qed. Abort.

  (* don't loop infinitely on circular equalities between vars *)
  Goal forall (w1 w2 w3: word),
      w1 = /[1] ->
      w1 = w2 ->
      w2 = w3 ->
      w3 = w1 ->
      w2 = /[1].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (hprop: Type),
       let PS := fun (dummy: hprop) => Z in
       forall (mk: forall p, PS p -> Prop) (uintptr: Z -> hprop) x y,
       mk (uintptr x) y ->
       x = 0 ->
       True.
  Proof.
    intros.
    Fail bottom_up_simpl_in_hyps ().
    (* as excepted, but not experienced until now,
       dependent types break bottom_up_simpl! *)
    pose proof (f_equal uintptr H0) as A.
    pose proof (@f_equal hprop (Z -> Prop) mk (uintptr x) (uintptr 0) A).
    epose proof (@f_equal _ _ _ (uintptr x) (uintptr 0) A).
    Fail epose proof (@f_equal _ _ mk (uintptr x) (uintptr 0) A).
    pose proof (@f_equal _ _ (mk: hprop -> Z -> Prop) (uintptr x) (uintptr 0) A).
  Abort.

  Goal forall a b, /[\[a ^+ b]] = a ^+ b.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall w z, z = \[w] -> /[z] = w.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  (* don't turn the hypothesis `a = 1` into `1 = 1` *)
  Goal forall (a: Z), a = 1 -> a = 1.
  Proof. intros. bottom_up_simpl_in_hyps (). assumption. Succeed Qed. Abort.

  Goal forall a: word, P (word.unsigned (a ^+ word.of_Z 8 ^- a) / 4) -> P 2.
  Proof.
    intros. bottom_up_simpl_in_hyp @H. exact H.
  Qed.

  Goal forall (P: Prop) (found: word),
      found = /[0] ->
      found = /[1] -> P.
  Proof.
    intros * H. bottom_up_simpl_in_goal ().
    lazy_match! goal with
    | [ |- /[0] = /[1] -> P0 ] => ()
    end.
  Abort.

  Goal forall (P: Prop) (found: word),
      (found = /[1] -> P) ->
      found = /[0] ->
      /[0] = /[1] -> P.
  Proof. intros p found A B. bottom_up_simpl_in_hyps (). assumption. Succeed Qed. Abort.

  Goal forall (b: bool) (a e: word),
      (if b then /[\[a]] else e) = (if b then /[\[a]] else e).
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall a b: Z, (a + a, a + 1) = (2 * a, 1 + b) -> (2 * a, a + 1) = (2 * a, 1 + b).
  Proof.
    (* should not do simplifications that only reorder / don't decrease the size *)
    intros. bottom_up_simpl_in_hyp @H.
    exact H.
  Succeed Qed. Abort.

  Goal forall a b c: Z, a + a + a = b -> a + a + a = c -> b = c.
  Proof.
    intros. bottom_up_simpl_in_hyps (). Std.transitivity '(3 * a).
    - rewrite <- H. refl.
    - rewrite <- H0. refl.
  Succeed Qed. Abort.

  Goal forall mtvec_base: Z,
      (word.add (word.add (word.mul (word.of_Z 4) (word.of_Z mtvec_base)) (word.of_Z 144))
         (word.of_Z (4 * Z.of_nat (S (Z.to_nat (word.unsigned (word.sub (word.add
            (word.mul (word.of_Z 4) (word.of_Z (Z.of_nat 29))) (word.add
               (word.mul (word.of_Z 4) (word.of_Z mtvec_base)) (word.of_Z 28)))
                  (word.add (word.mul (word.of_Z 4) (word.of_Z mtvec_base))
                     (word.of_Z 144))) / 4)))))) = /[4] ^* /[mtvec_base] ^+ /[148].
  Proof.
    intros. bottom_up_simpl_in_goal (). refl.
  Qed.

  Goal forall (stack_hi: Z) (f: word -> Z),
      f (word.add (word.of_Z stack_hi) (word.of_Z (-128))) =
      f (word.sub (word.of_Z stack_hi) (word.of_Z 128)).
  Proof.
    intros. bottom_up_simpl_in_goal (). refl.
  Qed.

  Goal forall (T: Type) (l res: list T) (a b c: T),
      res = [|a; b; c|] ++ l ->
      a :: b :: c :: l = res.
  Proof. intros. bottom_up_simpl_in_goal (). subst res. refl. Succeed Qed. Abort.

  Goal forall (a b: Z),
      0 <= a + b < 2 ^ 32 ->
      word.unsigned (word.of_Z (a + b)) - b = a.
  Proof.
    intros. bottom_up_simpl_in_goal (). refl.
  Succeed Qed. Abort.

  Goal forall (foo: Z -> word) (a: Z) (x y: word),
       word.unsigned x + word.unsigned y < 2 ^ 32 ->
       word.unsigned (foo (a + 0) ^+ x ^- foo a ^+ y) = word.unsigned x + word.unsigned y.
  Proof.
    intros. bottom_up_simpl_in_goal (). refl.
  Succeed Qed. Abort.

  Goal forall (z: Z), word.of_Z (word.unsigned (word.of_Z z)) = word.of_Z z.
  Proof.
    intros. bottom_up_simpl_in_goal (). refl.
  Succeed Qed. Abort.

  Goal forall (i j k count d: Z),
      d <> 0 ->
      (d * j - i * d + k * d * count) / d - count * k = j - i.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (A: Type) (xs ys: list A) i j,
      0 <= i <= 3 + j + i ->
      xs[i : 3 + i + j] = ys ->
      xs[i:][: j + 3] = ys.
  Proof. intros. bottom_up_simpl_in_hyps (). assumption. Succeed Qed. Abort.

  Goal forall (A: Type) (xs ys: list A) i j,
      0 <= i <= j ->
      xs[i:][: j - i] = ys ->
      xs[i : j] = ys.
  Proof. intros. bottom_up_simpl_in_hyps (). assumption. Succeed Qed. Abort.

  Goal forall (A: Type) (xs ys: list A),
      len (xs ++ ys) = len xs + len ys.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (A: Type) (xs ys: list A) (x: A) (i: Z),
      0 <= i < len ys ->
      len (xs ++ ys ++ xs) = 2 * len xs + len ys.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (A: Type) (xs ys: list A) (x: A) (i: Z) (j: Z),
      0 <= i < len ys ->
      0 <= j < i ->
      len (ys[j := x][i := x]) = len ys.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (A: Type) (xs ys: list A) (x: A) (i: Z),
      0 <= i < len ys ->
      len (xs ++ ys[i := x] ++ xs) = 2 * len xs + len ys.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (A: Type) (xs1 xs2 xs3 xs4 xs5 xs6: list A),
      (xs1 ++ xs2) ++ (xs3 ++ xs4 ++ xs5) ++ xs6 = xs1 ++ xs2 ++ xs3 ++ xs4 ++ xs5 ++ xs6.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (A: Type) (l1 l2: list A) (i: Z),
      len l1 = i ->
      (l1 ++ l2)[:i] = l1.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (A: Type) (l1 l2: list A) (i: Z),
      len l1 = i ->
      (l1 ++ l2)[0:][:i] = l1.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (A: Type) (l1 l2: list A) (i: Z),
      0 <= i <= len l1 ->
      (l1 ++ l2)[:i] = l1[:i].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (A: Type) (l1 l2 l3: list A) (i k: Z),
      len l1 + len l2 = i ->
      0 <= k < len l3 ->
      (l1 ++ l2 ++ l3[:k])[i:] = l3[:k].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (l0 l1 l2 l3 l4 l5: list bool),
      l0 ++ ((l1 ++ l2) ++ (l3 ++ l4)) ++ l5 = l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (l1 l2 l3 res: list Z) (a b c: Z),
      res = [|a; b; c|] ++ l1 ++ [|a; b|] ++ l2 ++ [|a; b; c|] ++ l3 ->
      [|a; b|] ++ [|c|] ++ l1 ++ (a :: b :: l2 ++ [|a; b|]) ++ c :: l3 = res.
  Proof. intros. bottom_up_simpl_in_goal (). subst res. refl. Succeed Qed. Abort.

  Goal forall (b1 b2 b3 b4 b5: bool),
      [|b1; b2; b3|] ++ [|b4; b5|] = [|b1; b2; b3; b4; b5|].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Ltac2 Set bottom_up_simpl_sidecond_hook := fun _ =>
    (* Note/TODO: full-fledged bottom_up_simpl_in_goal for sideconditions is a bit overkill,
       we only need push_down_len *)
      bottom_up_simpl_in_goal_nop_ok ();
      lazy_match! goal with
      | [ |- ?g ] => eapply (@xlia $g)
      end;
      lia.

  Goal forall (T: Type) (l: list T) (a b c: T),
      2 <= len l ->
      (a :: b :: c :: l)[:5] = a :: b :: c :: l[:2].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (l0 l1 l2 l3: list bool) (b1 b2 b3 b4 b5: bool),
      (l0 ++ l1 ++ [|b1; b2; b3|]) ++ (([|b4; b5|] ++ l2) ++ l3) =
      l0 ++ l1 ++ [|b1; b2; b3; b4; b5|] ++ l2 ++ l3.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (A: Type) (l res: list A) (x y z: A),
      res = [|x; y; z|] ++ l ->
      ([|x; y|] ++ l)[:2] ++ ([|x; y; z|] ++ l)[2:] = res.
  Proof. intros. bottom_up_simpl_in_goal (). subst res. refl. Succeed Qed. Abort.

  Goal forall (b1 b2: bool) (l res: list bool),
      res = [|b1; b2|] ++ l ->
      b1 :: b2 :: l = res.
  Proof. intros. bottom_up_simpl_in_goal (). subst res. refl. Succeed Qed. Abort.

  Goal forall (b1 b2: bool) (l res: list bool),
      res = [|b1; b2|] ++ l ->
      b1 :: ([|b2|] ++ l) = res.
  Proof. intros. bottom_up_simpl_in_goal (). subst res. refl. Succeed Qed. Abort.

  Goal forall (b1 b2: bool) (l res: list bool),
      res = [|b1; b2|] ++ l ->
      (b1 :: [|b2|]) ++ l = res.
  Proof. intros. bottom_up_simpl_in_goal_nop_ok (). subst res. refl. Succeed Qed. Abort.

  Goal forall (b1 b2: bool) (l res: list bool),
      res = [|b1; b2|] ++ l ->
      [|b1|] ++ (b2 :: l) = res.
  Proof. intros. bottom_up_simpl_in_goal (). subst res. refl. Succeed Qed. Abort.

  Hypothesis (sort: list Z -> list Z).

  Goal forall l1 l2 x (i: word),
      len (sort l1) + 1 = \[i] + 1 ->
      (sort l1 ++ x :: l2)[:\[i] + 1] = sort l1 ++ [|x|].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (A: Type) (l1 l2 l3: list A) (i k: Z),
      len l1 + len l2 <= i < len l1 + len l2 + k ->
      0 <= k < len l3 ->
      (l1 ++ l2 ++ l3[:k])[i:] = l3[i - len l1 - len l2 : k].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (A: Type) (l1 l2 l3: list A) (i: Z),
      len l1 + len l2 = i ->
      (l1 ++ l2 ++ l3)[i:] = l3.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (s1: list Z),
      0 < len s1 ->
      s1[0] = (s1 ++ [|0|])[0].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (l1 l2 l3: list Z) (i j k: Z),
      len l1 <= i < len l1 + j - k ->
      0 <= j <= len l2 ->
      0 <= k < j ->
      0 <= i - len l1 < j - k ->
      (l1 ++ l2[:j][k:] ++ l3[k:])[i] = l2[k + i - len l1].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  (* if we only know enough index constraints to push down the get operation partially,
     we still do that: *)
  Goal forall (l: list Z) (i j k: Z),
      0 <= i < j ->
      l[k:][:j][i] = l[k:][i].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  (* make sure ring_simplify is run on the newly computed index *)
  Goal forall (l: list Z) (i j: Z),
      0 <= i + j < len l ->
      0 <= i - j < len l - i - j ->
      l[i + j:][i - j] = l[2 * i].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  (* from, i points into ys *)
  Goal forall (xs ys zs: list bool) i,
      len xs <= i <= len xs + len ys ->
      ((xs ++ ys) ++ zs)[i:] = ys[i - len xs:] ++ zs.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  (* from, i points into ys *)
  Goal forall (xs ys zs: list bool) i,
      len xs <= i <= len xs + len ys ->
      (xs ++ (ys ++ zs))[i:] = ys[i - len xs:] ++ zs.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  (* from, i points somewhere into (ys1 ++ ys2).
     This example shows why only looking at one app node at a time is not enough:
     By only looking at the app node between ys1 and ys2, we can't do anything,
     because we don't know whether i points into the left or right part, so we
     miss the opportunity to take the zs out. *)
  Goal forall (ys1 ys2 zs: list bool) i,
      0 <= i <= len ys1 + len ys2 ->
      (ys1 ++ (ys2 ++ zs))[i:] = (ys1 ++ ys2)[i:] ++ zs.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  (* from, i points somewhere into (ys1 ++ ys2) *)
  Goal forall (xs ys1 ys2 zs: list bool) i,
      len xs <= i <= len xs + len ys1 + len ys2 ->
      (xs ++ (ys1 ++ (ys2 ++ zs)))[i:] = (ys1 ++ ys2)[i - len xs:] ++ zs.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  (* make sure the new index (len xs + j - len xs) gets simplified *)
  Goal forall (xs ys1 ys2 zs: list bool) j,
      0 <= j <= len ys1 + len ys2 ->
      (xs ++ (ys1 ++ (ys2 ++ zs)))[len xs + j:] = (ys1 ++ ys2)[j:] ++ zs.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  (* upto, i points into xs *)
  Goal forall (xs ys zs: list bool) i,
      0 <= i < len xs ->
      ((xs ++ ys) ++ zs)[:i] = xs[:i].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  (* upto, i points into xs *)
  Goal forall (xs ys zs: list bool) i,
      0 <= i < len xs ->
      (xs ++ (ys ++ zs))[:i] = xs[:i].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  (* upto, i points into xs2 *)
  Goal forall (xs1 xs2 ys zs: list bool) i,
      len xs1 <= i < len xs1 + len xs2 ->
      (xs1 ++ (xs2 ++ (ys ++ zs)))[:i] = (xs1 ++ xs2)[:i].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  (* upto, i points somewhere into (ys1 ++ ys2) *)
  Goal forall (xs0 xs1 ys1 ys2 zs: list bool) i expected,
      len xs0 + len xs1 <= i <= len xs0 + len xs1 + len ys1 + len ys2 ->
      expected = xs0 ++ xs1 ++ (ys1 ++ ys2)[:i - len xs0 - len xs1] ->
      (xs0 ++ (xs1 ++ (ys1 ++ (ys2 ++ zs))))[:i] = expected.
  Proof. intros. bottom_up_simpl_in_goal (). subst expected. refl. Abort.

  (* push_down_from might have to chop off several lists at the start of a series of ++ *)
  Goal forall (xs ys zs: list bool) (i j: Z),
      0 <= i <= len xs ->
      0 <= j <= len ys ->
      (ys[:j] ++ (ys[j:] ++ (zs ++ xs)))[len ys:] = zs ++ xs.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (xs0 xs1 xs2 xs3 xs4: list bool) i k,
      0 <= k <= len xs2 ->
      len xs0 + len xs1 <= i <= len xs0 + len xs1 + k ->
      (xs0 ++ xs1 ++ xs2[:k] ++ xs3 ++ xs4)[:i] = xs0 ++ xs1 ++ xs2[:i - len xs0 - len xs1].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (s2: list Z),
      0 < len s2 ->
      (s2 ++ [|0|])[1 :] = s2[1:] ++ [|0|].
  Proof. intros. try bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (s2: list Z),
      0 < len s2 ->
      (s2 ++ [|0|])[1 :][:len s2] = s2[1:] ++ [|0|].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (s2: list Z) (p2'' p2: Z),
      p2 = p2'' + 1 ->
      0 < len s2 ->
      (s2 ++ [|0|])[p2 - p2'' :][:len s2] = s2[1:] ++ [|0|].
  Proof. intros. bottom_up_simpl_in_goal (). f_equal. f_equal. lia. Succeed Qed. Abort.

  Goal forall (A: Type) (xs1 xs2 xs3 xs4 xs5 xs6: list A) i j k s,
      0 <= j <= len xs3 ->
      s = len xs1 + len xs2 + len xs3 - j ->
      s <= i <= s + k ->
      k <= len xs4 ->
      ((xs1 ++ xs2) ++ (xs3[j:] ++ xs4[:k] ++ xs5) ++ xs6)[:i] =
      (xs1 ++ xs2 ++ xs3[j:] ++ xs4[:k])[:i].
  Proof.
    intros. bottom_up_simpl_in_goal ().
    (* Note: The rhs gets simplified into something longer:
       xs1 ++ xs2 ++ xs3[j:] ++ xs4[:i - len xs1 - len xs2 - len x3 + j]
       but "clearer" in the sense that it's now obvious that the upto points into xs4 *)
    refl.
  Succeed Qed. Abort.

  Goal forall (A: Type) (l1 l2: list A) (x: A) (i: Z),
      len l1 = i ->
      (l1 ++ [|x|] ++ l2)[:i + 1] = l1 ++ [|x|].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (A: Type) (l1 l2: list A) (x: A) (i: Z),
      len l1 = i ->
      (l1 ++ x :: l2)[:i + 1] = l1 ++ [|x|].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (z i n: Z),
      0 <= i <= n ->
      (List.repeatz z n)[:i] = List.repeatz z i.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (z i n: Z),
      0 <= i <= n ->
      (List.repeatz z n)[i:] = List.repeatz z (n - i).
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (z i n: Z),
      0 <= i <= n ->
      (List.repeatz z n)[n - i:] = List.repeatz z i.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (l: list bool) i j,
      len l <= i ->
      j <= 0 ->
      (l[i:], l[j:], l[:i], l[:j]) = (nil, l, l, nil).
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (b: bool) l n i j,
      0 <= n <= i ->
      j <= 0 ->
      l = List.repeatz b n ->
      (l[i:], l[j:], l[:i], l[:j]) = (nil, l, l, nil).
  Proof. intros. subst l. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (B: Type) (b: B) (bs: list B),
      (bs ++ [|b|]) ++ ([|b|] ++ bs) = bs ++ [|b; b|] ++ bs.
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (B: Type) (b: B) (bs: list B) (i: Z),
      0 <= i ->
      List.repeatz b i ++ [|b|] = List.repeatz b (i + 1).
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.

  Goal forall (B: Type) (b: B) (bs: list B) (i: Z),
      0 <= i ->
      List.repeatz b i ++ [|b|] ++ bs[i + 1:] = List.repeatz b (i + 1) ++ bs[i + 1:].
  Proof. intros. bottom_up_simpl_in_goal (). refl. Succeed Qed. Abort.


  (** ** Not supported yet: *)

  Goal forall b (bs: list Z) (a i: word),
      0 <= \[i] < len bs ->
      (List.repeatz \[b] \[i] ++ bs[\[i]:])[\[a ^+ i ^- a] / 1] = bs[\[i]].
  Proof.
    intros.
    (* TODO should work in just one step: *)
    bottom_up_simpl_in_goal ().
    bottom_up_simpl_in_goal ().
    refl.
  Succeed Qed. Abort.

  Goal forall a b z, z = \[a ^+ b] -> /[z] = a ^+ b.
  Proof. intros. Abort.

  Goal forall (l0 l1 l2 l3 l4: list Z) (i j: Z),
      0 <= i + j < len l2 ->
      (l0 ++ l1 ++ l2[:i + j]) ++ ((l2[j + i:] ++ l3) ++ l4) = l0 ++ l1 ++ l2 ++ l3 ++ l4.
  Proof. intros. bottom_up_simpl_in_goal (). Fail refl. Abort.

  Goal forall (z1 z2: Z) (y: word),
      word.of_Z (z1 + z2) ^- word.of_Z z1 = y ->
      word.of_Z z2 = y.
  Proof.
    intros.
    bottom_up_simpl_in_hyps ().
    ltac1:(ring_simplify in H).
    (* TODO push_down_of_Z? *)
    (* only simplifies with preprocess [autorewrite with rew_word_morphism] *)
    ltac1:(autorewrite with rew_word_morphism in H).
    ltac1:(ring_simplify in H).
    exact H.
  Succeed Qed. Abort.

  Context (f: Z -> Z).

  Goal forall x y z1 z2: Z, x = f (z1 + z2) + y - f (z2 + z1) -> x = y.
  Proof.
    intros.
    (* no effect: *)
    ltac1:(ring_simplify (z1 + z2) in H).
    ltac1:(ring_simplify (z2 + z1) in H).
    (* has effect: *)
    ltac1:(ring_simplify (z1 + z2) (z2 + z1) in H).
    ltac1:(ring_simplify in H).
    assumption.
  Succeed Qed. Abort.

End Tests.
