(* Z-ify word expressions in an undoable (unzify) way *)

Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Local Open Scope Z_scope.

Module Import word.
  Section WithWord.
    Context {width} {word : word.word width} {word_ok : word.ok word}.

    Lemma modulus_nonzero: 2 ^ width <> 0.
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

Lemma f_equal_impl: forall P P' Q Q': Prop, P = P' -> Q = Q' -> (P -> Q) = (P' -> Q').
Proof. congruence. Qed.

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
  constr:(lem _ _ _ _ px py).

Ltac zify_term wok e :=
  lazymatch e with
  | ?f ?x ?y =>
      lazymatch f with
      | Logic.and => zify_app2 wok e f x y
      | Logic.or => zify_app2 wok e f x y
      | Logic.eq => zify_app2 wok e f x y
      | _ => constr:(@eq_refl _ e)
      end
  | ?f ?x =>
      lazymatch f with
      | Logic.not => zify_app1 wok e f x
      | @word.unsigned _ _ => zify_unsigned wok x
      | _ => constr:(@eq_refl _ e)
      end
  | ?P -> ?Q => zify_impl wok e P Q
  | _ => constr:(@eq_refl _ e)
  end
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

(*
Ltac zify_hyp wok h tp :=
  let pf := zify_term wok e in
  lazymatch pf with
  | eq_refl => idtac
  | _ => lazymatch type of pf
*)

(* TODO: need to pose unsigned ... for lia equations, not only return,
   so that we can pose modulo bounds later and save redundant proofs *)

(* TODO: matching should look into rhs (:= and =) of variables to detect patterns like
   (word.unsigned x) with H: x = word.add a b *)

(* TODO: also pose the right unsigned_range lemmas to get full Euclidean equations *)

(* TODO: Z division/modulo also needs to be turned into Euclidean equations *)

(* structure:
   rzify recurses into logical connectives, =, <> and word operations, posing a
   zified hypothesis for each interesting hypothesis.
   Goal is not yet zified, but each goal will be zified using the same rewrites,
   so that the goal's subterms match the terms appearing in the zified hypotheses. *)

Inductive zified_hyps_start_here: Prop := mk_zified_hyps_start_here.

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

Require Import Ltac2.Ltac2.

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

Ltac2 apply_unsigned_range_in_eqs () :=
  match List.drop_while
          (fun p => let (h, rhs, tp) := p in
                    Bool.neg (Constr.equal tp 'zified_hyps_start_here))
          (Control.hyps ())
  with
  | marker :: hs =>
      List.iter (fun p => let (h, rhs, tp) := p in eapply word.unsigned_range_eq in $h) hs
  | [] => Control.throw_invalid_argument "No zified_hyps_start_here marker found"
  end.

Ltac apply_unsigned_range_in_eqs := ltac2:(apply_unsigned_range_in_eqs ()).

Set Default Proof Mode "Classic".

(*
Goal forall a b: Z, a = b -> zified_hyps_start_here -> 1 = 1 -> b = a -> True.
  intros.
  apply_unsigned_range_in_eqs.
*)
