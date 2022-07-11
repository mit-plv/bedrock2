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
    Lemma add_rot: forall a m b, word.add (word.add a m) b = word.add (word.add b a) m.
    Proof. intros. ring. Qed.
    Lemma add_join: forall a m b, word.add (word.add a m) b = word.add m (word.add a b).
    Proof. intros. ring. Qed.
    Lemma add_to_left_assoc: forall a b c,
        word.add a (word.add b c) = word.add (word.add a b) c.
    Proof. intros. ring. Qed.
    Lemma add_to_right_assoc: forall a b c,
        word.add (word.add a b) c = word.add a (word.add b c).
    Proof. intros. ring. Qed.
    Lemma add_opp: forall a, word.add a (word.opp a) = word.of_Z 0.
    Proof. intros. ring. Qed.
    Lemma add_opp_l_distant: forall a m, word.add (word.opp a) (word.add m a) = m.
    Proof. intros. ring. Qed.
    Lemma add_opp_r_distant: forall a m, word.add a (word.add m (word.opp a)) = m.
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

    Lemma unsigned_upper: forall x: word, word.unsigned x < 2 ^ width.
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

  Lemma euclidean_decomp: forall a b, a = a / b * b + a mod b.
  Proof.
    intros.
    etransitivity. 1: eapply (Z_div_mod_eq_full a b). f_equal.
    apply Z.mul_comm.
  Qed.

  (* TODO generalize coqutil.Z.ZLib.Z.div_mul_undo_le *)
  Lemma div_mul_undo_le: forall a b, 0 < b -> a / b * b <= a.
  Proof.
    intros.
    pose proof (Zmod_eq_full a b) as P.
    pose proof (Z.mod_pos_bound a b) as Q.
    Lia.lia.
  Qed.

  Lemma add_rot: forall a m b, Z.add (Z.add a m) b = Z.add (Z.add b a) m.
  Proof. intros. ring. Qed.
  Lemma add_join: forall a m b, Z.add (Z.add a m) b = Z.add m (Z.add a b).
  Proof. intros. ring. Qed.

  Lemma add_opp_l_distant: forall a m, Z.add (Z.opp a) (Z.add m a) = m.
  Proof. intros. ring. Qed.
  Lemma add_opp_r_distant: forall a m, Z.add a (Z.add m (Z.opp a)) = m.
  Proof. intros. ring. Qed.

  Lemma factor_add_mul_11: forall a, a + a = a * 2.
  Proof. intros. Lia.lia. Qed.
  Lemma factor_add_mul_1q: forall a q, a + a * q = a * (1 + q).
  Proof. intros. Lia.lia. Qed.
  Lemma factor_add_mul_q1: forall a q, a * q + a = a * (q + 1).
  Proof. intros. Lia.lia. Qed.
  Lemma factor_add_mul_qq: forall a p q, a * p + a * q = a * (p + q).
  Proof. intros. Lia.lia. Qed.

  (* Lemma factor_sub_mul_11: forall a, a - a = a * 2. already Z.sub_diag *)
  Lemma factor_sub_mul_1q: forall a q, a - a * q = a * (1 - q).
  Proof. intros. Lia.lia. Qed.
  Lemma factor_sub_mul_q1: forall a q, a * q - a = a * (q - 1).
  Proof. intros. Lia.lia. Qed.
  Lemma factor_sub_mul_qq: forall a p q, a * p - a * q = a * (p - q).
  Proof. intros. Lia.lia. Qed.

End Z.

Lemma Z_cancel_mul_ll: forall f a b,
    f <> 0 ->
    (f * a = f * b) = (a = b).
Proof.
  intros. apply propositional_extensionality. split; intros; Lia.nia.
Qed.

Lemma and_True_l: forall P, and True P = P.
Proof.
  intros. apply propositional_extensionality. split; intros; intuition idtac.
Qed.

Lemma and_True_r: forall P, and P True = P.
Proof.
  intros. apply propositional_extensionality. split; intros; intuition idtac.
Qed.

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

Inductive worth_considering_status: Set := is_worth_considering.

Definition consider{T: Type}(x: T) := is_worth_considering.

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
  pose proof (word.add_join: forall a m b,
       trigger! ((word.add a b)) (word.add (word.add a m) b = word.add m (word.add a b)))
       as wadd_join;
  pose proof (word.add_rot: forall a m b,
       trigger! ((word.add b a)) (word.add (word.add a m) b = word.add (word.add b a) m))
       as wadd_rot;
  pose proof word.add_to_left_assoc as wadd_to_left_assoc;
  pose proof word.add_to_right_assoc as wadd_to_right_assoc;
  pose proof word.add_opp as wadd_opp;
  pose proof word.add_opp_l_distant as wadd_opp_l_distant;
  pose proof word.add_opp_r_distant as wadd_opp_r_distant;
  pose proof word.sub_def as wsub_def;
  pose proof word.unsigned_of_Z_nowrap as wunsigned_of_Z_nowrap;
  pose proof (word.unsigned_nonneg: forall x : word,
                 trigger! ((word.unsigned x)) (0 <= word.unsigned x))
    as wunsigned_nonneg;
  pose proof (word.unsigned_upper: forall x : word,
                 trigger! ((word.unsigned x)) (word.unsigned x < 2 ^ 64))
                   (* ^ TODO make width-generic *)
    as wunsigned_upper;
  pose proof word.unsigned_sru_to_div_pow2 as wunsigned_sru_to_div_pow2;
  pose proof word.unsigned_slu_to_mul_pow2 as wunsigned_slu_to_mul_pow2;
  (* Z *)
  pose proof Z.forget_mod_in_lt_l as Z_forget_mod_in_lt_l;
  pose proof (Z.mul_nonneg: forall e1 e2 : Z,
                 trigger! ((e1 * e2)) (0 <= e1 -> 0 <= e2 -> 0 <= e1 * e2))
    as z_mul_nonneg;
  pose proof (Z.div_nonneg: forall a b : Z,
                 trigger! ((a / b)) (0 <= a -> 0 < b -> 0 <= a / b))
    as z_div_nonneg;
  pose proof Z.div_mul_lt as z_div_mul_lt;
  pose proof Z.lt_from_le_and_neq as z_lt_from_le_and_neq;
  pose proof Z.remove_inner_mod as z_remove_inner_mod;
  pose proof Z_mod_mult as z_mod_mult;
  (* misc *)
  pose proof @eq_eq_sym as H_eq_eq_sym;
  pose proof eq_same_True as H_eq_same_True;
  pose proof and_True_l as and_True_l;
  pose proof and_True_r as and_True_r.

(* will have to stop using fully applied sep *)
Ltac desep :=
  repeat match goal with
         | H: sep _ _ _ |- _ => clear H
         | x := context[@sep] |- _ => subst x
         end.

Ltac preproc :=
  desep; pose_const_sideconds; pose_lib_lemmas.

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

    { (*
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
      apply H4. *)

      preproc.
      egg_simpl_goal 3.
      all: cbv beta; try assumption; try exact I.
      all: egg_simpl_goal 3.
      all: cbv beta; try assumption; try exact I.
      all: egg_simpl_goal 3.
      all: cbv beta; try assumption; try exact I.
      all: egg_simpl_goal 3.
      all: cbv beta; try assumption; try exact I. }

    { preproc.
      (*
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
      rewrite z_remove_inner_mod. 2: exact C7. 2: exact C6. 2: exact C10.
      rewrite z_mod_mult.
      reflexivity.
      *)

      egg_simpl_goal 3.
      all: cbv beta; try assumption; try exact I. }

    (* split if cases *) split; repeat straightline. (* code is processed, loop-go-again goals left behind *)
    { repeat letexists. split; [repeat straightline|].
      1:split.
      2:split.
      { SeparationLogic.ecancel_assumption. }
      {

        pose proof @length_skipn as L_length_skipn;
        pose proof @List.firstn_length as L_firstn_length;
        pose proof @List.app_length as L_app_length;
        pose proof @length_cons as L_length_cons;
        pose proof @length_nil as L_length_nil.

        repeat match goal with
               | x := _ |- _ => clear x || subst x
               end.

        preproc.
        clear H2.

  pose proof word.unsigned_sub as wunsigned_sub; unfold word.wrap in wunsigned_sub.
  pose proof word.unsigned_add as wunsigned_add; unfold word.wrap in wunsigned_add.
  pose proof Zplus_mod_idemp_r as z_plus_mod_idemp_r.
  pose proof Zplus_mod_idemp_l as z_plus_mod_idemp_l.
  assert (z_add_add_mod_idemp: forall a b c n : Z,
             (a + b mod n + c) mod n = (a + b + c) mod n). {
    clear. intros. rewrite (Z.add_comm a (b mod n)).
    rewrite <- Z.add_assoc. rewrite Zplus_mod_idemp_l. f_equal. ring.
  }
  assert (z_add_sub_mod_idemp: forall a b c n : Z,
             (a + b mod n - c) mod n = (a + b - c) mod n). {
    clear. intros. replace (a + b mod n - c) with (a - c + b mod n) by ring.
    rewrite Zplus_mod_idemp_r. f_equal. ring.
  }
  assert (z_sub_add_mod_idemp: forall a b c n : Z,
             (a - b mod n + c) mod n = (a - b + c) mod n). {
    clear. intros. replace (a - b mod n + c) with (a + c - b mod n) by ring.
    rewrite Zminus_mod_idemp_r. f_equal. ring.
  }
  assert (z_sub_sub_mod_idemp: forall a b c n : Z,
             (a - b mod n - c) mod n = (a - b - c) mod n). {
    clear. intros. replace (a - b mod n - c) with (a - c - b mod n) by ring.
    rewrite Zminus_mod_idemp_r. f_equal. ring.
  }
  pose proof Zminus_mod_idemp_r as z_minus_mod_idemp_r.
  pose proof Zminus_mod_idemp_l as z_minus_mod_idemp_l.
  assert (z_plus_mod_idemp_r_bw : forall a b n,
             trigger! ((b mod n)) ((a + b) mod n = (a + b mod n) mod n))
    by (symmetry; apply Zplus_mod_idemp_r).
  assert (z_plus_mod_idemp_l_bw : forall a b n,
             trigger! ((a mod n)) ((a + b) mod n = (a mod n + b) mod n))
    by (symmetry; apply Zplus_mod_idemp_l).
  assert (z_minus_mod_idemp_r_bw : forall a b n,
             trigger! ((b mod n)) ((a - b) mod n = (a - b mod n) mod n))
    by (symmetry; apply Zminus_mod_idemp_r).
  assert (z_minus_mod_idemp_l_bw : forall a b n,
             trigger! ((a mod n)) ((a - b) mod n = (a mod n - b) mod n))
    by (symmetry; apply Zminus_mod_idemp_l).

  pose proof Z.add_0_l as z_add_0_l;
  pose proof (Z.add_join: forall a m b,
       trigger! ((Z.add a b)) (Z.add (Z.add a m) b = Z.add m (Z.add a b))) as z_add_join;
  pose proof (Z.add_rot: forall a m b,
       trigger! ((Z.add b a)) (Z.add (Z.add a m) b = Z.add (Z.add b a) m))
       as z_add_rot;
  pose proof Z.add_assoc as z_add_to_left_assoc;
  pose proof Z.add_assoc as z_add_to_right_assoc; symmetry in z_add_to_right_assoc;
  pose proof Z.add_opp_diag_r as z_add_opp;
  pose proof Z.add_opp_r as z_sub_def; symmetry in z_sub_def.

  pose proof Z.add_opp_l_distant as z_add_opp_l_distant.
  pose proof Z.add_opp_r_distant as z_add_opp_r_distant.

  (* shortcuts to not depend on sub_def, which requires too high ffn: *)
  pose proof Z.sub_add_distr as z_sub_add_to_left_assoc;
  pose proof Z.sub_add_distr as z_sub_sub_to_right_assoc;
    symmetry in z_sub_sub_to_right_assoc;
  pose proof Z.sub_sub_distr as z_sub_sub_to_left_assoc;
  pose proof Z.sub_sub_distr as z_sub_add_to_right_assoc;
    symmetry in z_sub_add_to_right_assoc;
  pose proof Z.add_sub_assoc as z_add_sub_to_left_assoc;
  pose proof Z.add_sub_assoc as z_add_sub_to_right_assoc;
    symmetry in z_add_sub_to_right_assoc.

  pose proof Z.mul_0_l as z_mul_0_l;
  pose proof Z.mul_comm as z_mul_comm;
  pose proof Z.mul_assoc as z_mul_to_left_assoc;
  pose proof Z.mul_assoc as z_mul_to_right_assoc; symmetry in z_mul_to_right_assoc.

  pose proof Z.mul_add_distr_l as z_mul_add_distr_l.
  pose proof Z.mul_opp_r as z_mul_opp_r.

  pose proof Nat2Z.inj_sub_max as Nat2Z_inj_sub_max.
  pose proof (Nat2Z.inj_succ: forall n: nat, Z.of_nat (S n) = Z.of_nat n + 1) as
    Nat2Z_inj_succ.
  pose proof ZifyInst.of_nat_to_nat_eq as z_of_nat_to_nat.
  pose proof Z.mul_max_distr_nonneg_l as z_mul_max_distr_nonneg_l;
    symmetry in z_mul_max_distr_nonneg_l.
  pose proof Z.mul_min_distr_nonpos_l as z_mul_max_distr_nonpos_l;
    symmetry in z_mul_max_distr_nonpos_l.

  pose proof Zmod_eq as z_mod_eq.

  pose proof Z.opp_add_distr as z_opp_add_distr.
  pose proof Z.add_opp_r as z_sub_def_bw.
  pose proof word.unsigned_sub as wunsigned_sub_bw;
    unfold word.wrap in wunsigned_sub_bw; symmetry in wunsigned_sub_bw.
  pose proof word.unsigned_add as wunsigned_add_bw;
    unfold word.wrap in wunsigned_add_bw; symmetry in wunsigned_add_bw.

  pose proof Z.mul_sub_distr_l as z_mul_sub_distr_l.
  pose proof Z.mod_small as z_mod_small.
  assert (z_mod_small_precond: forall a b,
           trigger! ((a mod b)) (is_worth_considering = consider (0 <= a < b)))
    by reflexivity.

  pose proof Z_mod_plus_full as z_mod_plus_full.

  pose proof Zmult_mod_distr_l as z_mult_mod_distr_l.
  pose proof Zmult_mod_distr_r as z_mult_mod_distr_r.

  pose proof Z.mul_1_r as z_mul_1_r.
  assert (8 <> 0) as C11 by consts.
  assert (2 ^ 64 = 2 ^ 64 / 8 * 8) as C12 by reflexivity.
  assert (2 ^ 64 / 8 * 2 ^ 4 = 2 * 2 ^ 64) as C13 by reflexivity.
  assert (0 < 2) as C14 by reflexivity.
  assert (2 ^ 4 = 8 * 2) by reflexivity.

  assert (z_div_lt_to_mul: forall a b d, 0 < d -> (a / d < b) = (a < b * d)). {
    clear. intros. apply propositional_extensionality.
    Z.to_euclidean_division_equations.
    split; intros; Lia.nia.
  }
  assert (z_forget_mul_in_lt: forall a b f,
    trigger! ((a < f * b)) (0 < f -> 0 < b -> a < b -> a < f * b)). {
    clear. unfold with_trigger. intros. eapply Z.lt_le_trans. 1: eassumption.
    replace b with (1 * b) at 1 by Lia.lia.
    pose proof Z.mul_le_mono_pos_r as P. specialize P with (1 := H0).
    specialize (P 1 f). eapply P. Lia.lia.
  }

  assert (forall a b: Z, trigger! ((a mod b)) (a = (a / b) * b + a mod b)) as
    z_euclidean_decomp_mod_trigger by apply Z.euclidean_decomp.
  assert (forall a b: Z, trigger! ((a / b)) (a = (a / b) * b + a mod b)) as
    z_euclidean_decomp_div_trigger by apply Z.euclidean_decomp.

  assert (z_mod_lower: forall a b,
             trigger! ((a mod b)) (0 < b -> 0 <= a mod b)). {
    unfold with_trigger. eapply Z.mod_pos_bound.
  }
  assert (z_mod_upper: forall a b,
             trigger! ((a mod b)) (0 < b -> a mod b < b)). {
    unfold with_trigger. eapply Z.mod_pos_bound.
  }

  pose proof Zred_factor2 as z_factor_1_plus.
  pose proof Z.mul_add_distr_l as z_mul_add_distr_l_bw; symmetry in z_mul_add_distr_l_bw.
  pose proof Z.mul_opp_r as z_mul_opp_r_bw; symmetry in z_mul_opp_r_bw.
  pose proof Z_div_mult_full as z_div_mult_full.
  pose proof Zdiv_mult_cancel_l as z_div_mult_cancel_l.

  pose proof Z.factor_add_mul_11 as z_factor_add_mul_11;
  pose proof Z.factor_add_mul_1q as z_factor_add_mul_1q;
  pose proof Z.factor_add_mul_q1 as z_factor_add_mul_q1;
  pose proof Z.factor_add_mul_qq as z_factor_add_mul_qq;
  pose proof Z.factor_sub_mul_1q as z_factor_sub_mul_1q;
  pose proof Z.factor_sub_mul_q1 as z_factor_sub_mul_q1;
  pose proof Z.factor_sub_mul_qq as z_factor_sub_mul_qq.

  pose proof Z_cancel_mul_ll as z_cancel_mul_ll.

  (* stated in a convoluted way because each quantified variable must appear in conclusion *)
  assert (and_proj_l: forall P Q, and P Q -> and P Q = P). {
    clear. intros. apply propositional_extensionality. intuition idtac.
  }
  assert (and_proj_r: forall P Q, and P Q -> and P Q = Q). {
    clear. intros. apply propositional_extensionality. intuition idtac.
  }
  assert (z_neq_mul: forall n m, (n * m <> 0) = (n <> 0 /\ m <> 0)). {
    intros. symmetry. apply propositional_extensionality. eapply Z.neq_mul_0.
  }
  assert (z_mod_neq_0: forall n m, n mod m <> 0 -> n <> 0). {
    clear. intros. intro C. subst. apply H. apply Zmod_0_l.
  }
  assert (z_unfold_times_2: forall x, x * 2 = x + x). {
    clear. intros. Lia.lia.
  }
  (* not really helpful because where it looked useful, the (d * x) that was created
     contained a division in x, but that doesn't simplify away with the (d *...)
  assert (z_bounds_div: forall x b d,
             0 < d ->
             (d | b) ->
             (0 <= x < b / d) = (0 <= d * x < b)). {
    clear. intros.
    pose proof (Z.mul_lt_mono_pos_r d x (b / d) H) as P.
    apply propositional_extensionality. split; intros [? ?]; split; try Lia.lia.
    - eapply proj1 in P. specialize (P H2).
      rewrite Z.mul_comm. eapply Z.lt_le_trans. 1: exact P.
      apply Z.div_mul_undo_le. assumption.
    - unfold Z.divide in H0. destruct H0 as [z H0]. subst b.
      eapply proj2 in P. eapply P.
      rewrite Z.mul_comm. rewrite Z.div_mul by Lia.lia. assumption.
  }
  *)

  assert (z_mul_lt_to_lt_div: forall x b d,
             0 < d ->
             (d | b) ->
             (d * x < b) = (x < b / d)). {
    clear. intros.
    pose proof (Z.mul_lt_mono_pos_r d x (b / d) H) as P.
    apply propositional_extensionality. split; intros.
    - unfold Z.divide in H0. destruct H0 as [z H0]. subst b.
      eapply proj2 in P. eapply P.
      rewrite Z.mul_comm. rewrite Z.div_mul by Lia.lia. assumption.
    - eapply proj1 in P. specialize (P H1).
      rewrite Z.mul_comm. eapply Z.lt_le_trans. 1: exact P.
      apply Z.div_mul_undo_le. assumption.
  }

  set (halflen := (8 * Z.of_nat v / 2 ^ 4)).

Tactic Notation "egg_step" int(n) :=
  let G := lazymatch goal with |- ?x => x end in
  egg_simpl_goal n;
  [ try assumption; assert (is_worth_considering = consider G) by reflexivity  ..
  | cbv beta; try exact I].

all: egg_step 2.
all: egg_step 2.
all: egg_step 2.
all: egg_step 2.
all: egg_step 3.

rewrite z_mod_small.

  2: {
    subst halflen.
    all: egg_step 3.

    replace (Z.of_nat v - (Z.of_nat v / 2 + 1)) with
      (Z.of_nat v - Z.of_nat v / 2 - 1).
    2: {
    all: egg_step 3.
    }

rewrite (Z.euclidean_decomp (Z.of_nat v) 2) at 1 3.

replace (Z.of_nat v / 2 * 2 + Z.of_nat v mod 2 - Z.of_nat v / 2 - 1)
with (Z.of_nat v mod 2 + Z.of_nat v / 2 - 1). 2: {
    all: egg_step 2.
}

    move length_rep at bottom.
    move H3 at bottom.
    move H4 at bottom.
    rewrite H3 in length_rep.
    pose proof (wunsigned_upper (x2 ^- x1)) as U. unfold with_trigger in U.
    rewrite length_rep in U.
    rewrite z_mul_lt_to_lt_div in U by assumption.
    pose proof (z_mod_upper (Z.of_nat v) 2) as MU. unfold with_trigger in MU.
    specialize (MU eq_refl).

assert (z_div_upper_bound: forall x b d,
           trigger! ((x / d)) (0 < d -> x < b -> x / d < b / d + 1)). {
  clear. unfold with_trigger. intros. Z.to_euclidean_division_equations. Lia.nia.
}
pose proof z_div_upper_bound as A.
unfold with_trigger in A.
specialize A with (1 := C14) (2 := U).

assert (Z.of_nat v <> 0) as Nz. {
  egg_step 2.
}

(* could do bounds propagation like in AbsintWordToZ.v, but lower bound would
   not be strong enough:

  0 <= Z.of_nat v mod 2 + Z.of_nat v / 2 - 1 < 2 ^ 64 / 8
               0                  0       -1

  need case distinction: Z.of_nat v can't be 0. If it is 1:

  0 <= Z.of_nat v mod 2 + Z.of_nat v / 2 - 1 < 2 ^ 64 / 8
               1                  0       -1
  ok

  If Z.of_nat v >= 2:
  0 <= Z.of_nat v mod 2 + Z.of_nat v / 2 - 1 < 2 ^ 64 / 8
               0                  1       -1
  ok

  so how does ZnWords do it?
*)
split.
{
  clear -Nz. Z.to_euclidean_division_equations.
  assert_succeeds Lia.lia.
  clear H1 H2 H3.
  specialize (H (ltac:(Lia.lia))).
  specialize (H0 (ltac:(Lia.lia))).
  remember (Z.of_nat v) as x.
  Zify.zify.
  rewrite <- Heqx in cstr. clear Heqx v. subst x.
  assert (0 < 2 * q + r) as G0 by Lia.lia. clear Nz cstr.


  Lia.lia.
}
ZnWords.
}

    all: egg_step 2.
  ZnWords.
}

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
Time Qed. (* 1.637 secs *)
