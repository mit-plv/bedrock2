(* Z-ify word expressions in an undoable (unzify) way *)

Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Z.Lia.
Require Import coqutil.Datatypes.ZList.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.foreach_hyp.
Require Import coqutil.Tactics.ident_ops.
Local Open Scope Z_scope.

(* returns the name of the newly added or already existing hyp *)
Ltac unique_pose_proof_name newname pf :=
  let t := type of pf in
  lazymatch goal with
  | H: t |- _ => H
  | |- _ => let __ := match constr:(Set) with
                      | _ => pose proof pf as newname
                      end in newname
  end.

Module Import word.
  Section WithWord.
    Context {width} {word : word.word width} {word_ok : word.ok word}.

    Lemma unsigned_range_eq{z}{x: word}: word.unsigned x = z -> 0 <= z < 2 ^ width.
    Proof. intros. subst. eapply word.unsigned_range. Qed.

    (* The RHSs of the conclusions of the lemmas below are modulos expressed without
       using modulo.
       After using the equations, we have to eapply unsigned_range_eq in them to
       make sure we have the bounds of the modulo. *)

    Lemma unsigned_of_Z_eq_wrap_for_lia: forall (z z': Z),
        z = z' ->
        word.unsigned (word.of_Z (word := word) z) = z' - 2 ^ width * (z' / 2 ^ width).
    Proof.
      intros. subst z'.
      rewrite word.unsigned_of_Z. unfold word.wrap.
      eapply Z.mod_eq. eapply word.modulus_nonzero.
    Qed.

    Lemma unsigned_add_eq_wrap_for_lia: forall (a b: word) (ua ub: Z),
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        word.unsigned (word.add a b) = ua + ub - 2 ^ width * ((ua + ub) / 2 ^ width).
    Proof.
      intros. subst.
      rewrite word.unsigned_add. unfold word.wrap.
      eapply Z.mod_eq. eapply word.modulus_nonzero.
    Qed.

    Lemma unsigned_sub_eq_wrap_for_lia: forall (a b: word) (ua ub: Z),
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        word.unsigned (word.sub a b) = ua - ub - 2 ^ width * ((ua - ub) / 2 ^ width).
    Proof.
      intros. subst.
      rewrite word.unsigned_sub. unfold word.wrap.
      eapply Z.mod_eq. eapply word.modulus_nonzero.
    Qed.

    Lemma unsigned_mul_eq_wrap_for_lia: forall (a b: word) (ua ub: Z),
        word.unsigned a = ua ->
        word.unsigned b = ub ->
        word.unsigned (word.mul a b) = ua * ub - 2 ^ width * ((ua * ub) / 2 ^ width).
    Proof.
      intros. subst.
      rewrite word.unsigned_mul. unfold word.wrap.
      eapply Z.mod_eq. eapply word.modulus_nonzero.
    Qed.

    Lemma unsigned_slu_shamtZ_eq_wrap_for_lia: forall (x: word) (ux a: Z),
        ((0 <=? a) && (a <? width))%bool = true ->
        word.unsigned x = ux ->
        word.unsigned (word.slu x (word.of_Z a)) =
          ux * 2 ^ a - 2 ^ width * (ux / 2 ^ (width - a)).
    Proof.
      intros. subst. rewrite word.unsigned_slu_shamtZ by lia.
      unfold word.wrap. rewrite Z.shiftl_mul_pow2 by lia.
      rewrite Z.mod_eq by apply word.modulus_nonzero.
      replace (2 ^ width) with (2 ^ (width - a) * 2 ^ a) at 2.
      2: {
        rewrite <-Z.pow_add_r. 1: f_equal. all: lia.
      }
      rewrite Z.div_mul_cancel_r.
      1: reflexivity.
      all: apply Z.pow_nonzero; lia.
    Qed.

    Lemma unsigned_sru_shamtZ_eq_wrap_for_lia: forall (x: word) (ux a: Z),
        ((0 <=? a) && (a <? width))%bool = true ->
        word.unsigned x = ux ->
        word.unsigned (word.sru x (word.of_Z a)) = ux / 2 ^ a.
    Proof.
      intros. subst. rewrite word.unsigned_sru_shamtZ by lia.
      rewrite Z.shiftr_div_pow2 by lia. reflexivity.
    Qed.

  End WithWord.
End word.

Section EmbedNatInZ.
  Lemma Z_of_nat_range_eq[z][x: nat]: Z.of_nat x = z -> 0 <= z.
  Proof. intros. subst. apply Nat2Z.is_nonneg. Qed.

  Lemma Z_of_nat_to_nat_eq_cases: forall [z z': Z],
      z = z' ->
      0 < z' /\ Z.of_nat (Z.to_nat z) = z' \/ z' <= 0 /\ Z.of_nat (Z.to_nat z) = 0.
  Proof. lia. Qed.

  Lemma Z_of_nat_S_eq: forall [a: nat] [az: Z],
      Z.of_nat a = az ->
      Z.of_nat (S a) = 1 + az.
  Proof. lia. Qed.

  Lemma Z_of_nat_add_eq: forall [a b: nat] [az bz: Z],
      Z.of_nat a = az ->
      Z.of_nat b = bz ->
      Z.of_nat (Nat.add a b) = az + bz.
  Proof. intros. subst. apply Nat2Z.inj_add. Qed.

  Lemma Z_of_nat_sub_eq_cases: forall [a b: nat] [az bz: Z],
      Z.of_nat a = az ->
      Z.of_nat b = bz ->
      bz < az /\ Z.of_nat (Nat.sub a b) = az - bz \/ Z.of_nat (Nat.sub a b) = 0.
  Proof. lia. Qed.

  Lemma Z_of_nat_mul_eq: forall [a b: nat] [az bz: Z],
      Z.of_nat a = az ->
      Z.of_nat b = bz ->
      Z.of_nat (Nat.mul a b) = az * bz.
  Proof. intros. subst. apply Nat2Z.inj_mul. Qed.

  (* Not using eq_refl to make sure it is not taken as "no change was made" *)
  Lemma Z_of_nat_const n z: Z.of_nat n = z -> Z.of_nat n = z.
  Proof. exact id. Qed.
End EmbedNatInZ.

Section ListLen.
  Context [A: Type].
  Lemma list_len_app_eq: forall [x y: list A] [lx ly: Z],
      Z.of_nat (length x) = lx ->
      Z.of_nat (length y) = ly ->
      Z.of_nat (length (x ++ y)) = lx + ly.
  Proof. intros. subst. rewrite List.app_length. lia. Qed.

  Lemma list_len_repeatz_cases: forall (a: A) [n n': Z],
      n = n' ->
      0 <= n' /\ Z.of_nat (length (List.repeatz a n)) = n' \/
      n' < 0  /\ Z.of_nat (length (List.repeatz a n)) = 0.
  Proof.
    intros. subst. unfold List.repeatz. rewrite List.repeat_length. lia.
  Qed.
End ListLen.

Section ZOps.
  Lemma Z_min_spec_eq: forall [x y x' y': Z],
      x = x' ->
      y = y' ->
      x' < y' /\ Z.min x y = x' \/ y' <= x' /\ Z.min x y = y'.
  Proof. intros. subst. eapply Z.min_spec. Qed.

  Lemma Z_max_spec_eq: forall [x y x' y': Z],
      x = x' ->
      y = y' ->
      x' < y' /\ Z.max x y = y' \/ y' <= x' /\ Z.max x y = x'.
  Proof. intros. subst. eapply Z.max_spec. Qed.
End ZOps.

Lemma f_equal_impl: forall P P' Q Q': Prop, P = P' -> Q = Q' -> (P -> Q) = (P' -> Q').
Proof. congruence. Qed.

(* Called when e has no simplification opportunities.
   We pose an eq_refl proof so that it will later be turned into `0 <= e < 2 ^ width`,
   but we don't return the name of that hyp, but an eq_refl instead, because we want
   to detect "no simplifications made" by matching for eq_refl. *)
Ltac zify_unsigned_nop e :=
  let pf := constr:(@eq_refl _ (word.unsigned e)) in
  let n := fresh "__Zrange_0" in
  let __ := unique_pose_proof_name n pf in pf.

Ltac zify_of_nat_nop e :=
  let pf := constr:(@eq_refl Z (Z.of_nat e)) in
  let n := fresh "__Zrange_0" in
  let __ := unique_pose_proof_name n pf in pf.

Ltac zify_len_nop e :=
  let pf := constr:(@eq_refl Z (Z.of_nat (List.length e))) in
  let n := fresh "__Zrange_0" in
  let __ := unique_pose_proof_name n pf in pf.

Ltac zify_nop e := constr:(@eq_refl _ e).

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
      | Z.of_nat => zify_of_nat wok a0
      | Z.opp => zify_app1 wok e f1 a0
      | ?f2 ?a1 =>
          lazymatch f2 with
          | Logic.and => zify_app2 wok e f2 a1 a0
          | Logic.or  => zify_app2 wok e f2 a1 a0
          | Logic.eq  => zify_app2 wok e f2 a1 a0
          | Z.add     => zify_app2 wok e f2 a1 a0
          | Z.sub     => zify_app2 wok e f2 a1 a0
          | Z.mul     => zify_app2 wok e f2 a1 a0
          (* TODO: also pose Euclidean division equations for div and mod *)
          | Z.div     => zify_app2 wok e f2 a1 a0
          | Z.modulo  => zify_app2 wok e f2 a1 a0
          | Z.le      => zify_app2 wok e f2 a1 a0
          | Z.lt      => zify_app2 wok e f2 a1 a0
          | Z.ge      => zify_app2 wok e f2 a1 a0
          | Z.gt      => zify_app2 wok e f2 a1 a0
          | Z.min     => let pa0 := zify_term wok a0 in
                         let pa1 := zify_term wok a1 in
                         let n := fresh "__Zspecmin_0" in
                         let __ := unique_pose_proof_name n (Z_min_spec_eq pa1 pa0) in
                         zify_nop e
          | Z.max     => let pa0 := zify_term wok a0 in
                         let pa1 := zify_term wok a1 in
                         let n := fresh "__Zspecmax_0" in
                         let __ := unique_pose_proof_name n (Z_max_spec_eq pa1 pa0) in
                         zify_nop e
          | _ => zify_nop e
          end
      | _ => zify_nop e
      end
  | ?P -> ?Q => zify_impl wok e P Q
  | _ => zify_nop e
  end
  (*
  in let __ := match constr:(Set) with _ => idtac "} =" res end in res
  *)
with zify_app1 wok e f x :=
  let px := zify_term wok x in
  lazymatch px with
  | eq_refl => zify_nop e
  | _ => constr:(f_equal f px)
  end
with zify_app2 wok e f x y :=
  let px := zify_term wok x in
  let py := zify_term wok y in
  lazymatch px with
  | eq_refl =>
      lazymatch py with
      | eq_refl => zify_nop e
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
      | eq_refl => zify_nop e
      | _ => constr:(f_equal_impl px py)
      end
  | _ => constr:(f_equal_impl px py)
  end
with zify_unsigned wok e :=
  lazymatch e with
  | ?f1 ?a0 =>
      lazymatch f1 with
      | @word.of_Z _ _ =>
          let p_a0 := zify_term wok a0 in
          let n := fresh "__Zrange_0" in
          unique_pose_proof_name n (@unsigned_of_Z_eq_wrap_for_lia _ _ wok _ _ p_a0)
      | ?f2 ?a1 =>
          lazymatch f2 with
          | @word.add _ _ => zify_unsigned_app2 wok
                               (@unsigned_add_eq_wrap_for_lia _ _ wok) a1 a0
          | @word.sub _ _ => zify_unsigned_app2 wok
                               (@unsigned_sub_eq_wrap_for_lia _ _ wok) a1 a0
          | @word.mul _ _ => zify_unsigned_app2 wok
                               (@unsigned_mul_eq_wrap_for_lia _ _ wok) a1 a0
          | @word.slu _ _ => zify_unsigned_shift wok e
                               (@unsigned_slu_shamtZ_eq_wrap_for_lia _ _ wok) a1 a0
          | @word.sru _ _ => zify_unsigned_shift wok e
                               (@unsigned_sru_shamtZ_eq_wrap_for_lia _ _ wok) a1 a0
          | _ => zify_unsigned_nop e
          end
      | _ => zify_unsigned_nop e
      end
  | _ => (* Note: If e is a let-bound variable whose rhs is eg (word.add foo bar), we
            don't see through this var definition, so do we miss zification opportunities?
            No, because before zifying this e, we already zified all let-bound vars, and
            for let-bound vars of type word, we add an equation of the form
            `word.unsigned thevar = ...`, so just returning eq_refl here is sufficient! *)
      zify_unsigned_nop e
  end
with zify_unsigned_app2 wok lem x y :=
  let px := zify_unsigned wok x in
  let py := zify_unsigned wok y in
  let n := fresh "__Zrange_0" in
  unique_pose_proof_name n (lem _ _ _ _ px py)
with zify_unsigned_shift wok e lem x y :=
  lazymatch y with
  | word.of_Z ?a' =>
      let a := rdelta a' in
      lazymatch isZcst a with
      | true =>
          let width := lazymatch type of wok with @word.ok ?wi _ => wi end in
          lazymatch match constr:(Set) with
                    | _ => constr:(eq_refl: ((0 <=? a) && (a <? width))%bool = true)
                    | _ => tt
                    end
          with
          | tt => zify_unsigned_nop e
          | ?pa =>
              let px := zify_unsigned wok x in
              let n := fresh "__Zrange_0" in
              unique_pose_proof_name n (lem _ _ a pa px)
          end
      | false => zify_unsigned_nop e
      end
  | _ => zify_unsigned_nop e
  end
(* TODO not all proofs posed in zify_of_nat need to be posed, because eg
   0 <= Z.of_nat x + Z.of_nat y
   already follows from the
   0 <= Z.of_nat x and 0 <= Z.of_nat y
   that the subterm's processing posed *)
with zify_of_nat wok e :=
  lazymatch isnatcst e with
  | false =>
      lazymatch e with
      | ?f1 ?a0 =>
          lazymatch f1 with
          | Z.to_nat =>
              let p_a0 := zify_term wok a0 in
              let n := fresh "__Zcases_0" in
              let __ := unique_pose_proof_name n (Z_of_nat_to_nat_eq_cases p_a0) in
              zify_of_nat_nop e
          | S =>
              let p_a0 := zify_of_nat wok a0 in
              let n := fresh "__Zrange_0" in
              unique_pose_proof_name n (Z_of_nat_S_eq p_a0)
          | @List.length _ => zify_len wok a0
          | ?f2 ?a1 =>
              lazymatch f2 with
              | Nat.add => zify_of_nat_app2 wok Z_of_nat_add_eq a1 a0
              | Nat.mul => zify_of_nat_app2 wok Z_of_nat_mul_eq a1 a0
              | Nat.sub =>
                  let p0 := zify_of_nat wok a0 in
                  let p1 := zify_of_nat wok a1 in
                  let nc := fresh "__Zcases_0" in
                  let __ := unique_pose_proof_name nc (Z_of_nat_sub_eq_cases p1 p0) in
                  zify_of_nat_nop e
              | _ => zify_of_nat_nop e
              end
          | _ => zify_of_nat_nop e
          end
      | _ => zify_of_nat_nop e
      end
  | true => let z := eval cbv in (Z.of_nat e) in constr:(Z_of_nat_const e z eq_refl)
  end
with zify_of_nat_app2 wok lem x y :=
  let px := zify_of_nat wok x in
  let py := zify_of_nat wok y in
  let n := fresh "__Zrange_0" in
  unique_pose_proof_name n (lem _ _ _ _ px py)
with zify_len wok l :=
  lazymatch l with
  | ?f1 ?a0 =>
      lazymatch f1 with
      | ?f2 ?a1 =>
          lazymatch f2 with
          | @List.app _ =>
              let pa0 := zify_len wok a0 in
              let pa1 := zify_len wok a1 in
              constr:(list_len_app_eq pa1 pa0)
          | @List.repeatz _ =>
              let pa0 := zify_term wok a0 in
              let n := fresh "__Zcases_0" in
              let __ := unique_pose_proof_name n (list_len_repeatz_cases a1 pa0) in
              zify_len_nop l
          | _ => zify_len_nop l
          end
      | _ => zify_len_nop l
      end
  | _ => zify_len_nop l
  end.

Ltac zify_letbound_var wok x body tp :=
  lazymatch tp with
  | @word.rep _ _ =>
      let pf := zify_unsigned wok body in
      let n := fresh "__Zdef_" x in pose proof (pf : word.unsigned x = _) as n
  | nat =>
      let pf := zify_of_nat wok body in
      let n := fresh "__Zdef_" x in pose proof (pf : Z.of_nat x = _) as n
  | _ =>
      let pf := zify_term wok body in
      let n := fresh "__Zdef_" x in pose proof (pf : x = _) as n
  end.

Lemma rew_Prop_hyp: forall (P1 P2: Prop) (pf: P1 = P2), P1 -> P2.
Proof. intros. subst. assumption. Qed.

Lemma rew_Prop_goal: forall (P1 P2: Prop) (pf: P1 = P2), P2 -> P1.
Proof. intros. subst. assumption. Qed.

(* TODO detection of word equal and not equal should also take place under
   logical connectives, but using equality and functional extensionality,
   or using <-> in f_equal-like (morphism) lemmas? *)
Ltac zify_hyp_pf wok h0 tp0 :=
  lazymatch tp0 with
  | @eq (@word.rep _ _) _ _ =>
      let h := constr:(f_equal word.unsigned h0) in
      let tp := type of h in
      let pf := zify_term wok tp in
      constr:(rew_Prop_hyp _ _ pf h)
  | not (@eq (@word.rep _ _) _ _) =>
      let h := constr:(word.unsigned_inj' _ _ h0) in
      let tp := type of h in
      let pf := zify_term wok tp in
      constr:(rew_Prop_hyp _ _ pf h)
  | _ =>
      let pf := zify_term wok tp0 in
      lazymatch pf with
      | eq_refl => h0
      | _ => constr:(rew_Prop_hyp _ _ pf h0)
      end
  end.

(* if zification did something and created a new hyp hnew of type tnew,
   return (@Some tnew hnew), else return (@None tp) *)
Ltac zify_hyp_option wok h tp :=
  let pf := zify_hyp_pf wok h tp in
  lazymatch pf with
  | h => constr:(@None tp)
  | _ => let hf := fresh "__Z_" h in
         let __ := match constr:(Set) with
                   | _ => pose proof pf as hf
                   end in
         constr:(Some hf)
  end.

Ltac zify_hyp wok h tp :=
  (* __pure hyps were already zified when they were purified,
     and __Z hyps also don't need to be zified *)
  tryif ident_starts_with __pure h then idtac
  else tryif ident_starts_with __Z h then idtac
  else let __ := zify_hyp_option wok h tp in idtac.

Ltac get_word_instance :=
  lazymatch goal with
  | inst: word.word _ |- _ => inst
  | _: context[@word.unsigned ?wi ?inst] |- _ => inst
  | _: context[@word.signed ?wi ?inst] |- _ => inst
  | |- context[@word.unsigned ?wi ?inst] => inst
  | |- context[@word.signed ?wi ?inst] => inst
  | |- _ => fail "no word instance found"
  end.

Ltac get_word_ok :=
  let wo := get_word_instance in
  lazymatch constr:(_ : word.ok wo) with
  | ?wok => wok
  end.

(* Sometimes we might want to use our recursive zify without any words, but just
   for Z and nat, so we use this fake word.ok as the wok argument, which will work
   just fine as long as there are no word operations. *)
Inductive no_word_ok_found: Prop := mk_no_word_ok_found.

Ltac get_word_ok_or_dummy :=
  match constr:(Set) with
  | _ => get_word_ok
  | _ => constr:(mk_no_word_ok_found)
  end.

Ltac clear_if_dup h :=
  let tp := type of h in
  lazymatch goal with
  | _: tp, _: tp |- _ => clear h
  | |- _ => idtac
  end.

Ltac clear_Z_hyp_if_derivable h :=
  let tp := type of h in
  try (clear h; assert_succeeds (idtac; assert tp by xlia zchecker)).

Ltac apply_range_bounding_lemma_in_hyp h tp :=
  tryif ident_starts_with __Zrange_ h then
    lazymatch tp with
    | word.unsigned _ = _ => eapply word.unsigned_range_eq in h; clear_Z_hyp_if_derivable h
    | Z.of_nat _ = _ => eapply Z_of_nat_range_eq in h; clear_Z_hyp_if_derivable h
    | _ => idtac
    end
  else idtac.

Ltac apply_range_bounding_lemma_in_eqs :=
  foreach_hyp_upwards apply_range_bounding_lemma_in_hyp.

Ltac zify_goal :=
  lazymatch goal with
  | |- @eq (@word.rep _ _) _ _ => eapply word.unsigned_inj
  | |- _ <> _ => intro
  | |- _ => idtac
  end;
  lazymatch goal with
  | |- ?G =>
      is_lia G;
      let wok := get_word_ok_or_dummy in
      let pf := zify_term wok G in
      eapply (rew_Prop_goal _ _ pf)
  end;
  apply_range_bounding_lemma_in_eqs.

Ltac zify_hyps :=
  let wok := get_word_ok_or_dummy in
  foreach_var (zify_letbound_var wok);
  foreach_hyp (zify_hyp wok);
  apply_range_bounding_lemma_in_eqs.

(* structure:
   rzify recurses into logical connectives, =, <> and word operations, posing a
   zified hypothesis for each interesting hypothesis.
   Goal is not yet zified, but each goal will be zified using the same rewrites,
   so that the goal's subterms match the terms appearing in the zified hypotheses. *)

Ltac clear_hyp_if_zified h tp :=
  tryif ident_starts_with __Z h then clear h else idtac.

Ltac unzify := foreach_hyp clear_hyp_if_zified.

Require Import bedrock2.WordNotations. Local Open Scope word_scope.

Section Tests.
  Local Set Ltac Backtrace.

  Goal forall (a b: nat), Z.of_nat (a + b) = Z.of_nat (a + 0) + Z.of_nat (0 + b).
  Proof.
    intros.

    zify_hyps.

    zify_goal.
    xlia zchecker.
  Abort.

  Context {word: word.word 32} {word_ok: word.ok word}.
  Local Hint Mode Word.Interface.word - : typeclass_instances.

  Ltac rzify_lia := zify_hyps; zify_goal; xlia zchecker.

  Goal forall (a b: word) (z: Z), \[a ^+ b] < z -> let c := b ^+ a in \[c] < z.
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b: nat) (z: Z),
      Z.of_nat (Nat.add a b) < z ->
      let c := Nat.add b a in
      Z.of_nat c < z.
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b: word) (z: Z), \[a ^+ b] < z -> let c := \[b ^+ a] in c < z.
  Proof. intros. rzify_lia. Qed.

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
    Import coqutil.Tactics.Tactics.
    forget (\[x1 ^+ (x2 ^- x1) ^>> /[4] ^<< /[3] ^- x1] / \[/[8]]) as X1.
    Z.to_euclidean_division_equations.
    lia.
  Qed.

End Tests.
