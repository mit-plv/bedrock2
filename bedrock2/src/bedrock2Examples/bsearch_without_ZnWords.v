Require Import Coq.Strings.String Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import bedrock2.ZnWords.
From bedrock2 Require Import NotationsCustomEntry ProgramLogic Map.Separation Array Scalars Loops.

Require Import egg.Loader.
Require Import Coq.Logic.PropExtensionality.

Require bedrock2Examples.Demos.
Definition bsearch := Demos.bsearch.

From coqutil Require Import Datatypes.List Word.Interface Map.Interface. (* coercions word and rep *)
Require Import coqutil.Word.Properties.

Local Open Scope Z_scope.

Module word.
  Section WithWord.
    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Local Hint Mode word.word - : typeclass_instances.

    Add Ring wring: (@word.ring_theory width word word_ok).

    Lemma add_0_l: forall x, word.add (word.of_Z 0) x = x.
    Proof. intros. ring. Qed.
    Lemma add_0_r: forall x, word.add x (word.of_Z 0) = x.
    Proof. intros. ring. Qed.
    Lemma mul_0_l: forall x, word.mul (word.of_Z 0) x = word.of_Z 0.
    Proof. intros. ring. Qed.
    Lemma mul_0_r: forall x, word.mul x (word.of_Z 0) = word.of_Z 0.
    Proof. intros. ring. Qed.
    Lemma mul_1_l: forall x, word.mul (word.of_Z 1) x = x.
    Proof. intros. ring. Qed.
    Lemma mul_1_r: forall x, word.mul x (word.of_Z 1) = x.
    Proof. intros. ring. Qed.

    Lemma add_comm: forall a b, word.add a b = word.add b a.
    Proof. intros. ring. Qed.
    Lemma add_to_left_assoc: forall a b c,
        word.add a (word.add b c) = word.add (word.add a b) c.
    Proof. intros. ring. Qed.
    Lemma add_to_right_assoc: forall a b c,
        word.add (word.add a b) c = word.add a (word.add b c).
    Proof. intros. ring. Qed.
    Lemma add_opp: forall a, word.add a (word.opp a) = word.of_Z 0.
    Proof. intros. ring. Qed.
    Lemma sub_def: forall a b, word.sub a b = word.add a (word.opp b).
    Proof. intros. ring. Qed.

    Lemma unsigned_slu_to_mul_pow2: forall (x: word) a,
        0 <= a < width ->
        word.unsigned (word.slu x (word.of_Z a)) = (word.unsigned x * 2 ^ a) mod 2 ^ width.
    Proof.
      intros. rewrite word.unsigned_slu_shamtZ by assumption. unfold word.wrap.
      rewrite Z.shiftl_mul_pow2. 2: apply H. reflexivity.
    Qed.

    Lemma unsigned_sru_to_div_pow2: forall (x: word) a,
        0 <= a < width ->
        word.unsigned (word.sru x (word.of_Z a)) = word.unsigned x / 2 ^ a.
    Proof.
      intros. rewrite word.unsigned_sru_shamtZ by assumption.
      rewrite Z.shiftr_div_pow2. 2: apply H. reflexivity.
    Qed.

    Lemma unsigned_nonneg: forall x: word, 0 <= word.unsigned x.
    Proof. intros. apply word.unsigned_range. Qed.
  End WithWord.
End word.

Lemma neq_sym{A: Type}: forall (x y: A), x <> y -> y <> x. Proof. congruence. Qed.
Lemma eq_same_True: forall (A: Type) (a: A), (a = a) = True.
Proof. intros. apply propositional_extensionality; split; intros; auto. Qed.

Module Z.
  Lemma div_mul_lt: forall x d1 d2,
      0 < x ->
      0 < d1 ->
      d1 < d2 ->
      x / d2 * d1 < x.
  Proof. intros. Z.to_euclidean_division_equations. Lia.nia. Qed.

  Lemma lt_from_le_and_neq: forall x y,
      x <= y -> x <> y -> x < y.
  Proof. intros. Lia.lia. Qed.

  Lemma mul_nonneg : forall e1 e2 : Z, 0 <= e1 -> 0 <= e2 -> 0 <= e1 * e2.
  Proof. intros. Lia.nia. Qed.

  Lemma div_nonneg : forall a b : Z, 0 <= a -> 0 < b -> 0 <= a / b.
  Proof. intros. apply Z.div_pos; assumption. Qed.

  Lemma forget_mod_in_lt_l : forall a b m : Z,
      0 <= a ->
      0 < m ->
      a < b ->
      a mod m < b.
  Proof.
    intros. eapply Z.le_lt_trans. 1: eapply Z.mod_le. all: assumption.
  Qed.

  Lemma remove_inner_mod: forall n m a : Z,
      0 < n ->
      0 < m ->
      (n | m) ->
      (a mod m) mod n = a mod n.
  Proof. intros. symmetry. apply Znumtheory.Zmod_div_mod; assumption. Qed.
End Z.

From bedrock2 Require Import Semantics BasicC64Semantics.

From coqutil.Tactics Require Import syntactic_unify.
From coqutil.Tactics Require Import rdelta.

Require Import bedrock2.AbsintWordToZ.
Strategy -1000 [word]. (* TODO where should this go? *)

Declare Scope word_scope.

Local Infix "^+" := word.add  (at level 50, left associativity) : word_scope.
Local Infix "^-" := word.sub  (at level 50, left associativity) : word_scope.
Local Infix "^<<" := word.slu  (at level 37, left associativity) : word_scope.
Local Infix "^>>" := word.sru  (at level 37, left associativity) : word_scope.
Local Notation "/_" := word.of_Z       (* smaller angle: squeeze a Z into a word *)
 : word_scope.
Local Notation "\_" := word.unsigned   (* supposed to be a denotation bracket;
                                          or bigger angle: let a word fly into the large Z space *)
 : word_scope.

Local Open Scope word_scope.

From bedrock2 Require Import Semantics BasicC64Semantics.

Import HList List.
#[export] Instance spec_of_bsearch : spec_of "bsearch"%string := fun functions =>
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

Lemma eq_eq_sym: forall {A: Type} (x y: A), (x = y) = (y = x).
Proof.
  intros. apply propositional_extensionality. split; intros; congruence.
Qed.

Ltac consts :=
  lazymatch goal with
  | |- ?a <= ?b < ?c => requireZcstExpr a; requireZcstExpr b; requireZcstExpr c;
                        eapply computable_bounds
  | |- ?a <= ?b => requireZcstExpr a; requireZcstExpr b;
                   eapply computable_le
  | |- ?a < ?b => requireZcstExpr a; requireZcstExpr b;
                  eapply computable_lt
  | |- ?a <> ?b => requireZcstExpr a; requireZcstExpr b; unfold not; discriminate 1
  end;
  reflexivity.

Lemma eight_divides_2_64: (2 ^ 3 | 2 ^ 64).
Proof. unfold Z.divide. exists (2 ^ 61). reflexivity. Qed.

Ltac pose_const_sideconds :=
  assert (0 <= 8 < 2 ^ 64) as C1 by consts;
  assert (0 <= 3 < 64) as C2 by consts;
  assert (0 <= 4 < 64) as C3 by consts;
  assert (0 <= 2 ^ 3) as C4 by consts;
  assert (0 < 2 ^ 4) as C5 by consts;
  assert (0 < 2 ^ 64) as C6 by consts;
  assert (0 < 2 ^ 3) as C7 by consts;
  assert (2 ^ 3 < 2 ^ 4) as C8 by consts;
  assert (2 ^ 3 = 8) as C9 by reflexivity;
  pose proof eight_divides_2_64 as C10.

Ltac pose_lib_lemmas :=
  (* word *)
  pose proof word.add_0_l as wadd_0_l;
  pose proof word.add_0_r as wadd_0_r;
  pose proof word.add_comm as wadd_comm;
  pose proof word.add_to_left_assoc as wadd_to_left_assoc;
  pose proof word.add_to_right_assoc as wadd_to_right_assoc;
  pose proof word.add_opp as wadd_opp;
  pose proof word.sub_def as wsub_def;
  pose proof word.unsigned_of_Z_nowrap as wunsigned_of_Z_nowrap;
  pose proof (word.unsigned_nonneg: forall x : word,
                 trigger! ((word.unsigned x)) (0 <= word.unsigned x))
    as wunsigned_nonneg;
  pose proof word.unsigned_sru_to_div_pow2 as wunsigned_sru_to_div_pow2;
  pose proof word.unsigned_slu_to_mul_pow2 as wunsigned_slu_to_mul_pow2;
  (* Z *)
  pose proof Z.forget_mod_in_lt_l as Z_forget_mod_in_lt_l;
  pose proof (Z.mul_nonneg: forall e1 e2 : Z,
                 trigger! ((e1 * e2)) (0 <= e1 -> 0 <= e2 -> 0 <= e1 * e2))
    as Z_mul_nonneg;
  pose proof (Z.div_nonneg: forall a b : Z,
                 trigger! ((a / b)) (0 <= a -> 0 < b -> 0 <= a / b))
    as Z_div_nonneg;
  pose proof Z.div_mul_lt as Z_div_mul_lt;
  pose proof Z.lt_from_le_and_neq as Z_lt_from_le_and_neq;
  pose proof Z.remove_inner_mod as Z_remove_inner_mod;
  pose proof Z_mod_mult as Z__mod_mult;
  (* misc *)
  pose proof @eq_eq_sym as H_eq_eq_sym;
  pose proof eq_same_True as H_eq_same_True.

(* will have to stop using fully applied sep *)
Ltac desep :=
  repeat match goal with
         | H: sep _ _ _ |- _ => clear H
         | x := context[@sep] |- _ => subst x
         end.

Ltac write_goal :=
  desep; pose_const_sideconds; pose_lib_lemmas; egg_simpl_goal.

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
    rename H2 into length_rep. subst br.
    seprewrite @array_address_inbounds;
       [ ..|(* if expression *) exact eq_refl|letexists; split; [repeat straightline|]]. (* determines element *)

    { write_goal.

      subst mid.
      rewrite word.unsigned_of_Z_nowrap by consts.
      rewrite <- length_rep.
      rewrite word.word_sub_add_l_same_l.
      rewrite word.unsigned_slu_to_mul_pow2 by consts.
      rewrite word.unsigned_sru_to_div_pow2 by consts.

      eapply Z.le_lt_trans. 1: eapply Z.mod_le.
      { eapply Ztac.mul_le. 2: consts.
        eapply Z.div_pos. 2: consts.
        eapply word.unsigned_nonneg.}
      { consts. }
      eapply Z.div_mul_lt. 2,3: consts.
      eapply Z.lt_from_le_and_neq.
      1: apply word.unsigned_nonneg.
      apply neq_sym.
      apply H4. }

    { write_goal.
      subst mid.
      rewrite wunsigned_of_Z_nowrap by exact C1.
      rewrite wsub_def.
      rewrite wadd_comm.
      rewrite wadd_to_left_assoc.
      rewrite (wadd_comm (word.opp x1) x1).
      rewrite wadd_opp.
      rewrite wadd_0_l.
      rewrite wunsigned_slu_to_mul_pow2 by exact C2.
      rewrite <- C9.
      rewrite Z_remove_inner_mod. 2: exact C7. 2: exact C6. 2: exact C10.
      rewrite Z__mod_mult.
      reflexivity. }

    (* split if cases *) split; repeat straightline. (* code is processed, loop-go-again goals left behind *)
    { repeat letexists. split; [repeat straightline|].
      1:split.
      2:split.
      { SeparationLogic.ecancel_assumption. }
      { ZnWordsL. }
      { cleanup_for_ZModArith. reflexivity. }
      split; repeat straightline.
      2:split; repeat straightline.
      2: SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      { ZnWordsL. }
      { ZnWords. }
      { ZnWords. }
      { trivial. }
      { SeparationLogic.ecancel_assumption. } }
    (* second branch of the if, very similar goals... *)
    { repeat letexists. split.
      1:split.
      2:split.
      { SeparationLogic.ecancel_assumption. }
      { ZnWordsL. }
      { cleanup_for_ZModArith. reflexivity. }
      split.
      { ZnWordsL. }
      repeat straightline; split; trivial.
      subst x5. SeparationLogic.seprewrite_in (symmetry! @array_address_inbounds) H6.
      { ZnWords. }
      { ZnWords. }
      { ZnWords. }
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
