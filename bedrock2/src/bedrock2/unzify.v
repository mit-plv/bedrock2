(* Z-ify word expressions in an undoable (unzify) way *)

Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Z.Lia.
Require Import coqutil.Tactics.foreach_hyp.
Local Open Scope Z_scope.

(* returns the name of the newly added or already existing hyp *)
Ltac unique_pose_proof_name pf :=
  let t := type of pf in
  lazymatch goal with
  | H: t |- _ => H
  | |- _ => let H := fresh in
            let __ := match constr:(Set) with
                      | _ => pose proof pf as H
                      end in H
  end.

Module Import word.
  Section WithWord.
    Context {width} {word : word.word width} {word_ok : word.ok word}.

    Lemma modulus_nonzero: 2 ^ width <> 0. (* TODO move next to word.modulus_pos *)
    Proof. eapply Z.pow_nonzero. 2: eapply word.width_nonneg. cbv. discriminate. Qed.

    Lemma unsigned_range_eq{z}{x: word}: word.unsigned x = z -> 0 <= z < 2 ^ width.
    Proof. intros. subst. eapply word.unsigned_range. Qed.

    (* The RHSs of the conclusions of the lemmas below are modulos expressed without
       using modulo.
       After using the equations, we have to eapply unsigned_range_eq in them to
       make sure we have the bounds of the modulo. *)

    Lemma unsigned_add_eq_wrap_for_lia: forall (a b: word) (ua ub: Z),
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        word.unsigned (word.add a b) = ua + ub - 2 ^ width * ((ua + ub) / 2 ^ width).
    Proof.
      intros. subst.
      rewrite word.unsigned_add. unfold word.wrap.
      eapply Z.mod_eq. eapply modulus_nonzero.
    Qed.

    Lemma unsigned_sub_eq_wrap_for_lia: forall (a b: word) (ua ub: Z),
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        word.unsigned (word.sub a b) = ua - ub - 2 ^ width * ((ua - ub) / 2 ^ width).
    Proof.
      intros. subst.
      rewrite word.unsigned_sub. unfold word.wrap.
      eapply Z.mod_eq. eapply modulus_nonzero.
    Qed.

    Lemma unsigned_mul_eq_wrap_for_lia: forall (a b: word) (ua ub: Z),
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        word.unsigned (word.mul a b) = ua * ub - 2 ^ width * ((ua * ub) / 2 ^ width).
    Proof.
      intros. subst.
      rewrite word.unsigned_mul. unfold word.wrap.
      eapply Z.mod_eq. eapply modulus_nonzero.
    Qed.

    Lemma unsigned_slu_shamtZ_eq_wrap_for_lia: forall (x: word) (ux a: Z),
        0 <= a < width ->
        word.unsigned x = ux ->
        word.unsigned (word.slu x (word.of_Z a)) =
          ux * 2 ^ a - 2 ^ width * (ux / 2 ^ (width - a)).
    Proof.
      intros. subst. rewrite word.unsigned_slu_shamtZ by assumption.
      unfold word.wrap. rewrite Z.shiftl_mul_pow2 by apply H.
      rewrite Z.mod_eq by apply modulus_nonzero.
      replace (2 ^ width) with (2 ^ (width - a) * 2 ^ a) at 2.
      2: {
        rewrite <-Z.pow_add_r. 1: f_equal. all: lia.
      }
      rewrite Z.div_mul_cancel_r.
      1: reflexivity.
      all: apply Z.pow_nonzero; lia.
    Qed.

    Lemma unsigned_sru_shamtZ_eq_wrap_for_lia: forall (x: word) (ux a: Z),
        0 <= a < width ->
        word.unsigned x = ux ->
        word.unsigned (word.sru x (word.of_Z a)) = ux / 2 ^ a.
    Proof.
      intros. subst. rewrite word.unsigned_sru_shamtZ by assumption.
      rewrite Z.shiftr_div_pow2 by apply H. reflexivity.
    Qed.

    (* TODO list of further lemmas to be used:

    Lemma unsigned_inj': forall x y: word, x <> y -> word.unsigned x <> word.unsigned y.
    *)

  End WithWord.
End word.

Section EmbedNatInZ.
  Lemma Z_of_nat_range_eq{z}{x: nat}: Z.of_nat x = z -> 0 <= z.
  Proof. intros. subst. apply Nat2Z.is_nonneg. Qed.

  Lemma Z_of_nat_add_eq: forall (a b: nat) (az bz: Z),
      Z.of_nat a = az ->
      Z.of_nat b = bz ->
      Z.of_nat (Nat.add a b) = az + bz.
  Proof. intros. subst. apply Nat2Z.inj_add. Qed.

  Lemma Z_of_nat_sub_eq: forall (a b: nat) (az bz: Z),
      Z.of_nat a = az ->
      Z.of_nat b = bz ->
      Z.of_nat (Nat.sub a b) = az - bz. (* TODO needs Z.max 0 *)
  Abort.

  Lemma Z_of_nat_mul_eq: forall (a b: nat) (az bz: Z),
      Z.of_nat a = az ->
      Z.of_nat b = bz ->
      Z.of_nat (Nat.mul a b) = az * bz.
  Proof. intros. subst. apply Nat2Z.inj_mul. Qed.

  (* Not using eq_refl to make sure it is not taken as "no change was made" *)
  Lemma Z_of_nat_const n z: Z.of_nat n = z -> Z.of_nat n = z.
  Proof. exact id. Qed.
End EmbedNatInZ.

Ltac zify_unsigned wok e :=
  lazymatch e with
  | ?f ?x ?y =>
      lazymatch f with
      | @word.add _ _ => zify_unsigned_app2 wok (@unsigned_add_eq_wrap_for_lia _ _ wok) x y
      | @word.sub _ _ => zify_unsigned_app2 wok (@unsigned_sub_eq_wrap_for_lia _ _ wok) x y
      | @word.mul _ _ => zify_unsigned_app2 wok (@unsigned_mul_eq_wrap_for_lia _ _ wok) x y
      | _ => constr:(@eq_refl _ (word.unsigned e))
      end
  | _ => constr:(@eq_refl _ (word.unsigned e))
  end
with zify_unsigned_app2 wok lem x y :=
  let px := zify_unsigned wok x in
  let py := zify_unsigned wok y in
  unique_pose_proof_name (lem _ _ _ _ px py).

Ltac zify_of_nat e :=
  lazymatch isnatcst e with
  | false =>
      lazymatch e with
      | ?f ?x ?y =>
          lazymatch f with
          | Nat.add => zify_of_nat_app2 Z_of_nat_add_eq x y
          | Nat.mul => zify_of_nat_app2 Z_of_nat_mul_eq x y
          | _ => constr:(@eq_refl Z (Z.of_nat e))
          end
      | _ => constr:(@eq_refl Z (Z.of_nat e))
      end
  | true => let z := eval cbv in (Z.of_nat e) in constr:(Z_of_nat_const e z eq_refl)
  end
with zify_of_nat_app2 lem x y :=
  let px := zify_of_nat x in
  let py := zify_of_nat y in
  unique_pose_proof_name (lem _ _ _ _ px py).

Lemma f_equal_impl: forall P P' Q Q': Prop, P = P' -> Q = Q' -> (P -> Q) = (P' -> Q').
Proof. congruence. Qed.

Ltac zify_term wok e :=
  (*
  let __ := match constr:(Set) with
            | _ => idtac "zify_term" e "{"
            end in
  let res :=
  *)
  lazymatch e with
  | ?f1 ?a0 =>
      lazymatch f1 with
      | Logic.not => zify_app1 wok e f1 a0
      | @word.unsigned _ _ => zify_unsigned wok a0
      | Z.of_nat => zify_of_nat a0
      | ?f2 ?a1 =>
          lazymatch f2 with
          | Logic.and => zify_app2 wok e f2 a1 a0
          | Logic.or  => zify_app2 wok e f2 a1 a0
          | Logic.eq  => zify_app2 wok e f2 a1 a0
          | Z.add     => zify_app2 wok e f2 a1 a0
          | Z.sub     => zify_app2 wok e f2 a1 a0
          | Z.mul     => zify_app2 wok e f2 a1 a0
          | _ => constr:(@eq_refl _ e)
          end
      | _ => constr:(@eq_refl _ e)
      end
  | ?P -> ?Q => zify_impl wok e P Q
  | _ => constr:(@eq_refl _ e)
  end
  (*
  in let __ := match constr:(Set) with _ => idtac "} =" res end in res
  *)
with zify_app1 wok e f x :=
  let px := zify_term wok x in
  lazymatch px with
  | eq_refl => constr:(@eq_refl _ e)
  | _ => constr:(f_equal f px)
  end
with zify_app2 wok e f x y :=
  let px := zify_term wok x in
  let py := zify_term wok y in
  lazymatch px with
  | eq_refl =>
      lazymatch py with
      | eq_refl => constr:(@eq_refl _ e)
      | _ => constr:(f_equal2 f px py)
      end
  | _ => constr:(f_equal2 f px py)
  end
with zify_impl wok e x y :=
  let px := zify_term wok x in
  let py := zify_term wok y in
  lazymatch px with
  | eq_refl =>
      lazymatch py with
      | eq_refl => constr:(@eq_refl _ e)
      | _ => constr:(f_equal_impl px py)
      end
  | _ => constr:(f_equal_impl px py)
  end.

Lemma rew_Prop_hyp: forall (P1 P2: Prop) (pf: P1 = P2), P1 -> P2.
Proof. intros. subst. assumption. Qed.

Lemma rew_Prop_goal: forall (P1 P2: Prop) (pf: P1 = P2), P2 -> P1.
Proof. intros. subst. assumption. Qed.

Inductive zified_hyps_start_here: Prop := mk_zified_hyps_start_here.

(* TODO detection of word equal and not equal should also take place under
   logical connectives, but using equality and functional extensionality,
   or using <-> in f_equal-like (morphism) lemmas? *)
Ltac zify_hyp wok h0 tp0 :=
  lazymatch tp0 with
  | @eq (@word.rep _ _) _ _ =>
      let h := constr:(f_equal word.unsigned h0) in
      let tp := type of h in
      let pf := zify_term wok tp in
      let hf := fresh h0 "Z" in pose proof (rew_Prop_hyp _ _ pf h) as hf
  | not (@eq (@word.rep _ _) _ _) =>
      let h := constr:(word.unsigned_inj' _ _ h0) in
      let tp := type of h in
      let pf := zify_term wok tp in
      let hf := fresh h0 "Z" in pose proof (rew_Prop_hyp _ _ pf h) as hf
  | _ =>
      let pf := zify_term wok tp0 in
      lazymatch pf with
      | eq_refl => idtac
      | _ => let hf := fresh h0 "Z" in pose proof (rew_Prop_hyp _ _ pf h0) as hf
      end
  end.

Ltac hyp_is_evar_free h tp :=
  tryif has_evar tp then fail "hypothesis" h "is not evar-free" else idtac.

Ltac hyps_are_evar_free := foreach_hyp hyp_is_evar_free.

Ltac goal_is_evar_free :=
  lazymatch goal with
  | |- ?G => tryif has_evar G then fail "the goal is not evar-free" else idtac
  end.

Ltac assert_no_evars := hyps_are_evar_free; goal_is_evar_free.

Goal (forall a: nat, a = a) -> forall b: nat, exists c, c = b.
Proof.
  intros.
  assert_succeeds (idtac; assert_no_evars).
  eexists.
  assert_fails (idtac; goal_is_evar_free).
  assert_succeeds (idtac; hyps_are_evar_free).
  match goal with
  | |- ?x = _ => specialize (H x)
  end.
  assert_fails (idtac; hyps_are_evar_free).
  assert_fails (idtac; assert_no_evars).
Abort.

Ltac get_word_instance :=
  lazymatch goal with
  | inst: word.word _ |- _ => inst
  | _: context[@word.unsigned ?wi ?inst] |- _ => inst
  | _: context[@word.signed ?wi ?inst] |- _ => inst
  | |- context[@word.unsigned ?wi ?inst] => inst
  | |- context[@word.signed ?wi ?inst] => inst
  end.

Ltac get_word_ok :=
  let wo := get_word_instance in
  lazymatch constr:(_ : word.ok wo) with
  | ?wok => wok
  end.

Ltac zify_goal :=
  lazymatch goal with
  | |- @eq (@word.rep _ _) _ _ => eapply word.unsigned_inj
  | |- _ <> _ => intro
  | |- _ => idtac
  end;
  (* if there are evars in the goal, the preprocessing might affect the
     evars or their evarcontexts in tricky ways that no one wants to
     debug, so we should fail here.
     TODO but maybe it would be handy to use this tactic even when there
     are evars, especially for contradictory goals? *)
  assert_no_evars;
  lazymatch goal with
  | |- ?G =>
      is_lia G;
      let wok := get_word_ok in
      let pf := zify_term wok G in
      eapply (rew_Prop_goal _ _ pf)
  end.

Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".

(* Same signatures as in https://ocaml.org/p/batteries/3.6.0/doc/BatList/index.html *)
(* TODO: upstream to Coq *)
Module List.
  Ltac2 rec take_while(p: 'a -> bool)(xs: 'a list) :=
    match xs with
    | [] => []
    | h :: t => if p h then h :: take_while p t else []
    end.

  Ltac2 rec drop_while(p: 'a -> bool)(xs: 'a list) :=
    match xs with
    | [] => []
    | h :: t => if p h then drop_while p t else xs
    end.

  (* same as (take_while p xs, drop_while p xs) but done in one pass *)
  Ltac2 rec span(p: 'a -> bool)(xs: 'a list) :=
    match xs with
    | [] => ([], [])
    | h :: t => if p h then let (tk, dr) := span p t in (h :: tk, dr) else ([], xs)
    end.
End List.

Ltac2 apply_range_bounding_lemma_in_eqs () :=
  match List.drop_while
          (fun p => let (h, rhs, tp) := p in
                    Bool.neg (Constr.equal tp 'zified_hyps_start_here))
          (Control.hyps ())
  with
  | marker :: hs =>
      List.iter (fun p => let (h, rhs, tp) := p in
                          lazy_match! tp with
                          | word.unsigned _ = _ => eapply word.unsigned_range_eq in $h
                          | Z.of_nat _ = _ => eapply Z_of_nat_range_eq in $h
                          | _ => ()
                          end) hs
  | [] => Control.throw_invalid_argument "No zified_hyps_start_here marker found"
  end.

Ltac apply_range_bounding_lemma_in_eqs := ltac2:(apply_range_bounding_lemma_in_eqs ()).

Ltac zify_hyps :=
  pose proof mk_zified_hyps_start_here;
  let wok := get_word_ok in
  foreach_hyp (zify_hyp wok);
  apply_range_bounding_lemma_in_eqs.

(* TODO: matching should look into rhs (:= and =) of variables to detect patterns like
   (word.unsigned x) with H: x = word.add a b *)

(* TODO: also pose the right unsigned_range lemmas to get full Euclidean equations *)

(* TODO: Z division/modulo also needs to be turned into Euclidean equations *)

(* structure:
   rzify recurses into logical connectives, =, <> and word operations, posing a
   zified hypothesis for each interesting hypothesis.
   Goal is not yet zified, but each goal will be zified using the same rewrites,
   so that the goal's subterms match the terms appearing in the zified hypotheses. *)

Ltac unzify :=
  lazymatch goal with
  | H: zified_hyps_start_here |- _ =>
      repeat lazymatch goal with
        | A: ?T |- _ => lazymatch T with
                        | zified_hyps_start_here => fail (* done *)
                        | _ => clear A
                        end
        end;
      clear H
  | |- _ => fail "no zified_hyps_start_here marker found"
  end.

Goal forall (a b: nat), Z.of_nat (a + b) = Z.of_nat (a + 0) + Z.of_nat (0 + b).
Proof.
  intros.
  zify.
  xlia zchecker.
Abort.

Section Tests.
  Context {word: word.word 32} {word_ok: word.ok word}.
  Local Hint Mode Word.Interface.word - : typeclass_instances.

  Goal forall (left0 right : word) (xs : list word),
    word.unsigned (word.sub right left0) = 8 * Z.of_nat (Datatypes.length xs + 0) ->
    forall (x : list word) (x1 x2 : word),
    word.unsigned (word.sub x2 x1) = 8 * Z.of_nat (Datatypes.length x) ->
    word.sub x2 x1 <> word.of_Z 0 ->
    word.unsigned
      (word.sub x2
         (word.add
            (word.add x1 (word.slu (word.sru (word.sub x2 x1) (word.of_Z 4)) (word.of_Z 3)))
            (word.of_Z 8))) =
    8 *
    Z.of_nat
      (Datatypes.length x -
       S (Z.to_nat (word.unsigned (word.sub (word.add x1 (word.slu (word.sru (word.sub x2 x1)
           (word.of_Z 4)) (word.of_Z 3))) x1) / word.unsigned (word.of_Z 8)))).
  Proof.
    intros.
    (* Require Import bedrock2.ZnWords. Time ZnWords. *)
    zify_hyps.
    zify_goal.
    unzify.
  Abort.
End Tests.
