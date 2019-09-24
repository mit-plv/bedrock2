Require Import Coq.Strings.String Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Z.PushPullMod.
From bedrock2 Require Import NotationsInConstr ProgramLogic Map.Separation Array Scalars TailRecursion.

Require bedrock2.Examples.Demos.
Definition bsearch := @Demos.bsearch _ Demos.BinarySearch.StringNames.Inst.

From coqutil Require Import Datatypes.List Word.Interface Map.Interface. (* coercions word and rep *)
From bedrock2 Require Import Semantics BasicC64Semantics.

From coqutil Require Import Z.div_mod_to_equations Z.div_to_equations.
From coqutil.Tactics Require Import syntactic_unify.
From coqutil.Tactics Require Import rdelta.

Require Import bedrock2.AbsintWordToZ.
Strategy -1000 [word parameters]. (* TODO where should this go? *)

Local Infix "^+" := word.add  (at level 50, left associativity).
Local Infix "^-" := word.sub  (at level 50, left associativity).
Local Infix "^<<" := word.slu  (at level 37, left associativity).
Local Infix "^>>" := word.sru  (at level 37, left associativity).
Local Notation "/_" := word.of_Z.      (* smaller angle: squeeze a Z into a word *)
Local Notation "\_" := word.unsigned.  (* supposed to be a denotation bracket;
                                          or bigger angle: let a word fly into the large Z space *)
Local Open Scope Z_scope.

From coqutil Require Import Z.div_mod_to_equations.
From bedrock2 Require Import Semantics BasicC64Semantics.

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

From coqutil.Tactics Require Import eabstract letexists rdelta.
From coqutil.Macros Require Import symmetry.
Import PrimitivePair.

Lemma mix_eq_into_mod{lhs rhs m: Z}(E: lhs mod m = rhs)(a: Z):
    a mod m = (a - lhs + rhs) mod m.
Proof.
  intros. rewrite <- E. Z.mod_equality.
Qed.

Lemma mix_eq_into_unsigned{lhs: word}{rhs: Z}(E: word.unsigned lhs = rhs)(w: word):
  word.unsigned w = word.unsigned (word.add w (word.sub (word.of_Z rhs) lhs)).
Proof.
  intros.
  rewrite <- E.
  rewrite word.of_Z_unsigned.
  f_equal.
  ring.
Qed.

Lemma computable_bounds{lo v hi: Z}(H: andb (Z.leb lo v) (Z.ltb v hi) = true): lo <= v < hi.
Proof.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply Z.leb_le in H1.
  apply Z.ltb_lt in H2.
  auto.
Qed.

Lemma computable_le{lo v: Z}(H: Z.leb lo v = true): lo <= v.
Proof. apply Z.leb_le. assumption. Qed.

Lemma computable_lt{lo v: Z}(H: Z.ltb lo v = true): lo < v.
Proof. apply Z.ltb_lt. assumption. Qed.

Ltac count_summands e :=
  lazymatch e with
  | Z.add ?a ?b => let m := count_summands a in
                   let n := count_summands b in
                   let r := eval cbv in (m + n) in r
  | Z.sub ?a ?b => let m := count_summands a in
                   let n := count_summands b in
                   let r := eval cbv in (m + n) in r
  | _ => Z.one
  end.

Goal False.
  let a := constr:((1 - 3) + (3 + 2 + 8)) in
  let n := count_summands a in set (x := n).
Abort.

Ltac rhs_fewer_summands E :=
   match type of E with
   | ?a mod ?x = ?b mod ?x =>
     let m := count_summands a in
     let n := count_summands b in
     let b := eval cbv in (Z.ltb n m) in
     lazymatch b with
     | true => idtac
     | false => fail "lhs has" m "summands, rhs has" n
     end
   end.

(* If we have "(... + a ... - b ...) mod m" and an equation "E: a - b = somethingSimpler",
   this tactic will replace "a - b" by "somethingSimpler", even though "a - b" does not
   appear as such. In a sense, it does rewriting where the matching is not syntactic, but
   according to the "ring" tactic on Z.
   And note that "a - b" is just an example lhs, it can be any ring expression over Z. *)
Ltac mix_eq_into_mod :=
  match goal with
  | E: ?lhs mod ?m = ?rhs |- context[?e mod ?m] =>
    let F := named_pose_proof (mix_eq_into_mod E e) in
    match type of F with
    | _ = ?R mod m => ring_simplify R in F
    end;
    rhs_fewer_summands F;
    rewrite F;
    clear F;
    (* removing the modulo, so let's remember its bounds: *)
    let B := named_pose_proof (Z.mod_pos_bound lhs m eq_refl) in
    rewrite E in B (* TODO prevent duplicate *)
  end.

Ltac lia2 := PreOmega.zify; rewrite ?Z2Nat.id in *; Z.div_mod_to_equations; blia.

Ltac lia3 :=
  idtac; (* for evaluation order when passing lia3 as an arg to other tactics *)
  lazymatch goal with
  | |- context[_ mod _] => fail "mod found, applying lia could be too expensive"
  | |- _ => lia2
  end.

Ltac cond_hyps_factor :=
    repeat match goal with
           | [ H : ?x -> _, H' : ?x -> _ |- _ ] =>
                pose proof (fun u : x => conj (H u) (H' u)); clear H H' end.

Ltac lia4 := PreOmega.zify; rewrite ?Z2Nat.id in *; Z.div_to_equations; cond_hyps_factor; blia.

Module Z.
  Lemma mod_mul_l: forall (a b: Z), (b * a) mod b = 0.
  Proof.
    intros. assert (b = 0 \/ b <> 0) as C by blia. destruct C as [C | C].
    - subst. apply Zmod_0_r.
    - rewrite Z.mul_comm. apply Z.mod_mul. assumption.
  Qed.
  Lemma mod_mul_r: forall (a b: Z), (a * b) mod b = 0.
  Proof.
    intros. rewrite Z.mul_comm. apply mod_mul_l.
  Qed.
End Z.

Ltac Zsimp e parentIsZ simplifier :=
  first
  [ (* try to simplify child expression *)
    lazymatch e with
    | Z.add ?a ?b => first [ Zsimp a true simplifier | Zsimp b true simplifier ]
    | Z.mul ?a ?b => first [ Zsimp a true simplifier | Zsimp b true simplifier ]
    | Z.sub ?a ?b => first [ Zsimp a true simplifier | Zsimp b true simplifier ]
    | Z.opp ?a    =>         Zsimp a true simplifier
    | ?f ?a               => first [ Zsimp f false simplifier | Zsimp a false simplifier ]
    end
  | (* If we're here, no child expression could be simplified. *)
    lazymatch parentIsZ with false => idtac end;
    lazymatch e with
    | Z.add _ _ => idtac
    | Z.mul _ _ => idtac
    | Z.sub _ _ => idtac
    | Z.opp _   => idtac
    end;
    progress (simplifier e)
  ].

Ltac Zsimp_goal :=
  repeat match goal with
         | |- ?G => Zsimp G false ltac:(fun e => ring_simplify e)
         end.

Ltac is_lia P :=
  lazymatch P with
  | @eq Z _ _ => idtac
  | not (@eq Z _ _) => idtac
  | (_ < _)%Z => idtac
  | (_ <= _)%Z => idtac
  | (_ <= _ < _)%Z => idtac
  | @eq nat _ _ => idtac
  | not (@eq nat _ _) => idtac
  | (_ < _)%nat => idtac
  | (_ <= _)%nat => idtac
  | (_ <= _ < _)%nat => idtac
  | _ => fail "The term" P "is not LIA"
  end.

Ltac cleanup_for_ZModArith :=
  repeat match goal with
         | a := _ |- _ => subst a
         | H: ?T |- _ => tryif is_lia T then fail else clear H
         end.

Ltac ZModArith_step lia_tac :=
  match goal with
  (* TODO delete this first line because it's already on the last line,
     it's just here to demo how "robust" the heuristics are which decide when
     it's safe to try lia *)
  | |- _ => solve [lia_tac]
  | |- _ => exact eq_refl
  | |- _ => progress Z.push_pull_mod
  | |- context[?a mod ?m] =>
    rewrite (Z.mod_small a m) by
        first [apply computable_bounds; reflexivity | assumption | lia_tac]
  | |- _ => mix_eq_into_mod
  | |- _ => progress Zsimp_goal
  | |- _ => apply Z.mod_mul_l
  | |- _ => apply Z.mod_mul_r
  | |- _ => solve [lia_tac]
  end.

(* TODO improve *)
Ltac simpl_list_length_exprs :=
  rewrite ?List.length_skipn, ?List.firstn_length.

Hint Rewrite word.unsigned_of_Z word.signed_of_Z word.of_Z_unsigned word.unsigned_add word.unsigned_sub word.unsigned_opp word.unsigned_or word.unsigned_and word.unsigned_xor word.unsigned_not word.unsigned_ndn word.unsigned_mul word.signed_mulhss word.signed_mulhsu word.unsigned_mulhuu word.unsigned_divu word.signed_divs word.unsigned_modu word.signed_mods word.unsigned_slu word.unsigned_sru word.signed_srs word.unsigned_eqb word.unsigned_ltu word.signed_lts
       using solve[reflexivity || trivial]
  : word_laws.

Ltac wordOps_to_ZModArith :=
  repeat first
         [ progress (autorewrite with word_laws in *; cbv [word.wrap] in *)
         | rewrite Z.shiftr_div_pow2 by (apply computable_le; reflexivity)
         | rewrite Z.shiftl_mul_pow2 by (apply computable_le; reflexivity) ].

Ltac unsigned_sidecond :=
  lazymatch goal with
  | |- ?G => tryif is_lia G then idtac else fail "this tactic does not solve this kind of goal"
  end;
  cleanup_for_ZModArith;
  simpl_list_length_exprs;
  wordOps_to_ZModArith;
  repeat ZModArith_step ltac:(lia4).

Set Ltac Profiling.

Local Unset Simplex. (* COQBUG(9615) *)
Lemma bsearch_ok : program_logic_goal_for_function! bsearch.
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

  { repeat straightline. }
  { exact lt_wf. }
  { eauto. }
  { repeat straightline.
    2: solve [auto]. (* exiting loop *)
    (* loop body *)
    rename H2 into length_rep. subst br. subst v0.
    seprewrite @array_address_inbounds;
       [ ..|(* if expression *) exact eq_refl|letexists; split; [repeat straightline|]]. (* determines element *)
    { unsigned_sidecond. }
    { unsigned_sidecond. }
    (* split if cases *) split; repeat straightline. (* code is processed, loop-go-again goals left behind *)
    { repeat letexists. split; [repeat straightline|].
      repeat letexists; repeat split; repeat straightline.
      { SeparationLogic.ecancel_assumption. }
      { unsigned_sidecond. }
      { unsigned_sidecond. }
      SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      { unsigned_sidecond. }
      { unsigned_sidecond. }
      { unsigned_sidecond. }
      { SeparationLogic.ecancel_assumption. } }
    (* second branch of the if, very similar goals... *)
    { repeat letexists. split. 1: solve [repeat straightline].
      repeat letexists; repeat split; repeat straightline.
      { SeparationLogic.ecancel_assumption. }
      { unsigned_sidecond. }
      { unsigned_sidecond. }
      subst x8. SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      { unsigned_sidecond. }
      { unsigned_sidecond. }
      { unsigned_sidecond. }
      { SeparationLogic.ecancel_assumption. } } }
  repeat straightline.
  repeat apply conj; auto; []. (* postcondition *)
  letexists. split.
  { exact eq_refl. }
  { auto. }

  Unshelve.
  all: exact (word.of_Z 0).

  all:fail "remaining subgoals".
Qed.
(* Print Assumptions bsearch_ok. *)
(* SortedListString.string_strict_order *)
(* reconstruct_enforce *)
(* SortedListMap *)

Local Set Simplex.

Goal False. idtac "End of binary search profiling.". Abort.
