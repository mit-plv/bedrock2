Require Import Coq.Strings.String Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
From bedrock2 Require Import NotationsInConstr ProgramLogic Map.Separation Array Scalars TailRecursion.

Require bedrock2.Examples.Demos.
Definition bsearch := @Demos.bsearch _ Demos.BinarySearch.StringNames.Inst.

From coqutil Require Import Datatypes.List Word.Interface Map.Interface. (* coercions word and rep *)
From bedrock2 Require Import Semantics BasicC64Semantics.

From coqutil Require Import Z.div_mod_to_equations.
From coqutil.Tactics Require Import syntactic_unify.
From coqutil.Tactics Require Import rdelta.

Require Import bedrock2.TODO_absint.

Strategy -1000 [word parameters]. (* TODO where should this go? *)

Module absint_test.
  Fixpoint goal (x : word) (n : nat) : Prop
    := match n with
       | O => True
       | S n' => let x := word.add x x in goal x n'
       end.
  Goal forall x X, 1 <= X < 2^60 -> unsigned.absint_eq (word.unsigned x) X -> goal x 7.
  Proof.
    cbv beta iota delta [goal].
    intros.

    let e := match goal with x := _ |- _ => x end in
    let e := constr:(word.ndn (word.xor (word.or (word.and (word.sub (word.mul (word.slu (word.sru e (word.of_Z 16)) (word.of_Z 3)) x) x) x) x) x) x) in
    let H := unsigned.zify_expr e in
    idtac H.
    exact I.
  Qed.


  Goal forall x y, 0 <= x < 5 -> 10 <= y < 20 -> True.
  Proof.
    intros.

    set (a := x+y).
    set (b := y+x).
    set (c := a*b+7).

    let e := constr:(a + y mod 2 * (b*(x*y/4)) + c) in
    let H := rbounded e in
    cbn in *.

    let e := constr:(a*c + b) in
    let H := rbounded e in
    idtac H;
    cbn in *.
    exact I.
  Qed.
End absint_test.

(* custom rewrite tactic to work around COQBUG(4885) *)
Ltac set_evars := repeat match goal with |- context[?e] => is_evar e; set e end.
Ltac subst_evars := repeat match goal with x := ?e |- _ => is_evar e; subst x end.
Ltac _ureplace_in_by pat hyp tac :=
  multimatch goal with
  | H: context [?lhs] |- _ =>
    assert_succeeds (idtac;
                     let pat := open_constr:(pat) in (* uconstr -> open_constr *)
                     let pat := lazymatch pat with ?pat => pat end in (* strip casts if any *)
                     syntactic_unify lhs pat);
    let T := type of lhs in
    let rhs := open_constr:(_:T) in
    let rhs := lazymatch rhs with ?rhs => rhs end in (* strip cast *)
    replace lhs with rhs in H by tac
  end.
Tactic Notation "ureplace" uconstr(pat) "in" hyp(hyp) "by" tactic3(tac) := _ureplace_in_by pat hyp tac.

Ltac _ureplace_by pat tac :=
  let g := fresh in
  let H := fresh in
  lazymatch goal with |- ?G => remember G as g eqn:H end;
  ureplace pat in H by tac;
  subst g.
Tactic Notation "ureplace" uconstr(pat) "by" tactic3(tac) := _ureplace_by pat tac.

Local Infix "^+" := word.add  (at level 50, left associativity).
Local Infix "^-" := word.sub  (at level 50, left associativity).
Local Infix "^<<" := word.slu  (at level 37, left associativity).
Local Infix "^>>" := word.sru  (at level 37, left associativity).
Local Notation "/_" := word.of_Z.
Local Notation "\_" := word.unsigned.
Local Open Scope Z_scope.
Lemma word__add_sub x y : (x^+y^-x) = y.
Proof.
  apply Properties.word.unsigned_inj.
  rewrite word.unsigned_sub, word.unsigned_add.
  unfold word.wrap.
  rewrite Zminus_mod_idemp_l, Z.add_simpl_l.
  apply Properties.word.wrap_unsigned.
Qed.

  From coqutil Require Import Z.div_mod_to_equations.

Monomorphic Definition word__monomorphic_ring_theory := Properties.word.ring_theory.
Add Ring word_ring : word__monomorphic_ring_theory.

Import HList List.
Instance spec_of_bsearch : spec_of "bsearch"%string := fun functions =>
  forall left right target xs R t m,
    sep (array scalar (word.of_Z 8) left xs) R m ->
    \_ (right ^- left) = 8*Z.of_nat (Datatypes.length xs) ->
    WeakestPrecondition.call functions
      "bsearch"%string t m (left::right::target::nil)%list
      (fun t' m' rets => t=t' /\ sep (array scalar (word.of_Z 8) left xs) R m' /\ exists i, rets = (i::nil)%list /\
      ((*sorted*)False -> True)
      ).

From coqutil.Tactics Require Import letexists rdelta.
From coqutil.Macros Require Import symmetry.
Import PrimitivePair.

Local Instance mapok: map.ok mem := SortedListWord.ok (Naive.word 64 eq_refl) _.
Local Instance wordok: coqutil.Word.Interface.word.ok word := coqutil.Word.Naive.ok _ _.
Local Instance byteok: coqutil.Word.Interface.word.ok byte := coqutil.Word.Naive.ok _ _.

Set Printing Depth 99999999.
Require Import AdmitAxiom.

Local Unset Simplex. (* COQBUG(9615) *)

Lemma swap_swap_ok : program_logic_goal_for_function! bsearch.
Proof.
  repeat straightline.

  refine (
    tailrec (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _ HList.polymorphic_list.nil)) ("left"::"right"::"target"::nil)%list%string
        (fun l xs R t m left right target => PrimitivePair.pair.mk
                                               (sep (array scalar (word.of_Z 8) left xs) R m /\
                                                \_ (right ^- left) = 8*Z.of_nat (Datatypes.length xs) /\
                                                List.length xs = l)
        (fun        T M LEFT RIGHT TARGET => T = t /\ sep (array scalar (word.of_Z 8) left xs) R M))
        lt _ _ _ _ _ _ _);
    cbn [reconstruct map.putmany_of_list HList.tuple.to_list
         HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
  1,2,3,5: case proof_admitted.
  repeat straightline.
  2: case proof_admitted.
  clear H2. subst br. subst v0.
  seprewrite @array_address_inbounds;
    [ ..|(* if expression *) exact eq_refl|letexists; split; [repeat straightline|]]. (* determines element *)
  1, 2 : case proof_admitted.
  (* split if cases *) split; repeat straightline. (* code is processed, loop-go-again goals left behind *)
  2: case proof_admitted.
  repeat letexists.
  split; [repeat straightline|].
  repeat letexists. repeat split.
  1,2,3,4,5 : case proof_admitted.
  destruct H5.
  all : clear -H6.
  subst x7. subst x8.
  repeat match goal with x := _ |- _ => subst x end.
  all : clear -H6.
  Info 3 SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6; [|case proof_admitted..].
  destruct x.
  all: case proof_admitted.
  Grab Existential Variables.
  all : case proof_admitted.
Qed. (* Error: No such section variable or assumption: H6. *)

Local Set Simplex.