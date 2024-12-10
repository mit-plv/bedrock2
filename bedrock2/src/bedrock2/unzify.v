(* Z-ify word expressions in an undoable (unzify) way *)

From Coq Require Import ZArith Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Z.Lia.
Require Import coqutil.Datatypes.ZList.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.foreach_hyp.
Require Import coqutil.Tactics.ident_ops.
Require Import bedrock2.WordPushDownLemmas.
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

Ltac is_nat_arith2 f :=
  lazymatch f with
  | Nat.add => constr:(true)
  | Nat.sub => constr:(true)
  | Nat.mul => constr:(true)
  | Nat.pow => constr:(true)
  | _ => constr:(false)
  end.

Ltac is_Z_arith2 f :=
  lazymatch f with
  | Z.add => constr:(true)
  | Z.sub => constr:(true)
  | Z.mul => constr:(true)
  | Z.pow => constr:(true)
  | _ => constr:(false)
  end.

Ltac is_const_nat_expr t :=
  lazymatch t with
  | O => constr:(true)
  | S ?p => is_const_nat_expr p
  | Z.to_nat ?x => is_const_Z_expr x
  | ?f ?x ?y =>
      lazymatch is_nat_arith2 f with
      | true => lazymatch is_const_nat_expr x with
                | true => is_const_nat_expr y
                | false => constr:(false)
                end
      | false => constr:(false)
      end
  | _ => constr:(false)
  end
with is_const_positive_expr t :=
  lazymatch t with
  | xO ?p => is_const_positive_expr p
  | xI ?p => is_const_positive_expr p
  | xH => constr:(true)
  | _ => constr:(false)
  end
with is_const_Z_expr t :=
  lazymatch t with
  | Z0 => constr:(true)
  | Z.pos ?p => is_const_positive_expr p
  | Z.neg ?p => is_const_positive_expr p
  | Z.of_nat ?n => is_const_nat_expr n
  | Z.opp ?x => is_const_Z_expr x
  | ?f ?x ?y =>
      lazymatch is_Z_arith2 f with
      | true => lazymatch is_const_Z_expr x with
                | true => is_const_Z_expr y
                | false => constr:(false)
                end
      | false => constr:(false)
      end
  | _ => constr:(false)
  end.

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

  Lemma list_len_nil: Z.of_nat (length (@nil A)) = 0.
  Proof. reflexivity. Qed.

  Lemma list_len_cons: forall (x: A) [l: list A] [ll: Z],
      Z.of_nat (length l) = ll ->
      Z.of_nat (length (cons x l)) = 1 + ll.
  Proof. intros. subst. rewrite List.length_cons. lia. Qed.

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

  Lemma list_len_from_cases: forall [i i': Z] [l: list A] [ll: Z],
      i = i' ->
      Z.of_nat (length l) = ll ->
      i' < 0        /\ Z.of_nat (length (List.from i l)) = ll      \/
      0 <= i' <= ll /\ Z.of_nat (length (List.from i l)) = ll - i' \/
      ll <= i'      /\ Z.of_nat (length (List.from i l)) = 0.
  Proof. intros. unfold List.from. rewrite List.length_skipn. lia. Qed.

  Lemma list_len_upto_cases: forall [i i': Z] [l: list A] [ll: Z],
      i = i' ->
      Z.of_nat (length l) = ll ->
      i' < 0        /\ Z.of_nat (length (List.upto i l)) = 0  \/
      0 <= i' <= ll /\ Z.of_nat (length (List.upto i l)) = i' \/
      ll <= i'      /\ Z.of_nat (length (List.upto i l)) = ll.
  Proof. intros. unfold List.upto. rewrite List.firstn_length. lia. Qed.
End ListLen.

(* Section does not reject trailing non-maximally-inserted implicit argument,
   while it would be rejected outside section, so we fix the Arguments manually: *)
Arguments list_len_nil : clear implicits.

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

  Lemma zify_Z_if: forall (c crhs: bool) (a b a' b': Z),
      c = crhs ->
      a = a' ->
      b = b' ->
      crhs = true /\ (if c then a else b) = a' \/
      crhs = false /\ (if c then a else b) = b'.
  Proof. intros. subst a' b' crhs. destruct c; intuition. Qed.

  Lemma Z_div_mod_comp: forall a b,
      match Z.compare b 0 with
      | Eq => False
      | _ => True
      end ->
      a mod b = a - b * (a / b).
  Proof.
    intros.
    assert (b <> 0) as NE. {
      intro C; subst. rewrite Z.compare_refl in H. exact H.
    }
    apply (Z.div_mod a) in NE.
    lia.
  Qed.

  Lemma Z_mod_pos_bound_comp: forall a b,
      match Z.compare 0 b with
      | Lt => True
      | _ => False
      end ->
      0 <= a mod b < b.
  Proof.
    intros. apply Z.mod_pos_bound.
    destruct_one_match_hyp; try contradiction.
    eapply (proj1 (Z.compare_lt_iff _ _)).
    assumption.
  Qed.

  Lemma Z_mod_neg_bound_comp: forall a b,
      match Z.compare b 0 with
      | Lt => True
      | _ => False
      end ->
      b < a mod b <= 0.
  Proof.
    intros. apply Z.mod_neg_bound.
    destruct_one_match_hyp; try contradiction.
    eapply (proj1 (Z.compare_lt_iff _ _)).
    assumption.
  Qed.
End ZOps.

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

Ltac zify_prop_nop e := constr:(iff_refl e).

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
      | @word.unsigned _ _ => zify_unsigned wok a0
      | @word.signed _ _ =>
          let p := zify_unsigned wok a0 in
          let n := fresh "__Zrange_0" in
          unique_pose_proof_name n (word.signed_eq_unsigned_wrap_for_lia _ _ p)
      | Z.of_nat => zify_of_nat wok a0
      | Z.opp => zify_app1 wok e f1 a0
      | ?f2 ?a1 =>
          lazymatch f2 with
          | Z.add     => zify_app2 wok e f2 a1 a0
          | Z.sub     => zify_app2 wok e f2 a1 a0
          | Z.mul     => zify_app2 wok e f2 a1 a0
          | Z.div     => zify_div_mod_expr wok e f2 a1 a0
          | Z.modulo  => zify_div_mod_expr wok e f2 a1 a0
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
  | match ?c in bool return Z with
    | true => ?a
    | false => ?b
    end =>
      lazymatch zify_lia_bool wok c with
      | tt => zify_nop e
      | ?pc => let pa := zify_term wok a in
               let pb := zify_term wok b in
               let n := fresh "__Zspecif_0" in
               let __ := unique_pose_proof_name n (zify_Z_if c _ a b _ _ pc pa pb) in
               zify_nop e
      end
  | _ => zify_nop e
  end
  (*
  in let __ := match constr:(Set) with _ => idtac "} =" res end in res
  *)
with zify_div_mod_expr wok e f x m :=
  let p := zify_app2 wok e f x m in
  lazymatch type of p with
  | _ = f ?x' ?m' =>
      lazymatch is_const_Z_expr m' with
      | true => (* only pose div/mod equations if the modulus is a constant, because
                   otherwise it results in non-linear equations *)
          let c := eval cbv in (Z.compare 0 m') in
          lazymatch c with
          | Eq => let n := fresh "__Zdivmod_0" in
                  let lem := lazymatch f with
                             | Z.modulo => Z.mod_0_r_ext
                             | Z.div => Z.div_0_r_ext
                             end in
                  let __ := unique_pose_proof_name n (lem x' m' eq_refl) in p
          | _ => let n1 := fresh "__Zdivmod_0" in
                 let __ := unique_pose_proof_name n1 (Z_div_mod_comp x' m' I) in
                 let n2 := fresh "__Zmodbound_0" in
                 let lem := lazymatch c with
                            | Lt => Z_mod_pos_bound_comp
                            | Gt => Z_mod_neg_bound_comp
                            end in
                  let __ := unique_pose_proof_name n2 (lem x' m' I) in p
          end
      | false => p
      end
  end
with zify_lia_bool wok c0 :=
  let c := rdelta_var c0 in
  match goal with
  | |- _ => let pc := zify_bool wok c in
            let __ := lazymatch type of pc with | _ = ?rhs => is_lia_bool rhs end in pc
  | h: c = ?rhs |- _ =>
      let __ := match constr:(Set) with _ => is_lia_bool rhs end in h
  | _ => constr:(tt)
  end
with zify_bool wok b :=
  lazymatch b with
  | ?f1 ?a0 =>
      lazymatch f1 with
      | negb => zify_bool_app1 wok b f1 a0
      | ?f2 ?a1 =>
          lazymatch f2 with
          | andb => zify_bool_app2 wok b f2 a1 a0
          | orb => zify_bool_app2 wok b f2 a1 a0
          | Z.ltb     => zify_app2 wok b f2 a1 a0
          | Z.leb     => zify_app2 wok b f2 a1 a0
          | @word.ltu _ _ => zify_u_u_bool wok b (@word.unsigned_ltu_eq _ _ wok) a1 a0
          | @word.eqb _ _ => zify_u_u_bool wok b (@word.unsigned_eqb_eq _ _ wok) a1 a0
          | _ => zify_nop b
          end
      | _ => zify_nop b
      end
  | _ => zify_nop b
  end
with zify_bool_app1 wok e f x :=
  let px := zify_bool wok x in
  lazymatch px with
  | eq_refl => zify_nop e
  | _ => constr:(f_equal f px)
  end
with zify_bool_app2 wok e f x y :=
  let px := zify_bool wok x in
  let py := zify_bool wok y in
  lazymatch px with
  | eq_refl =>
      lazymatch py with
      | eq_refl => zify_nop e
      | _ => constr:(f_equal2 f px py)
      end
  | _ => constr:(f_equal2 f px py)
  end
with zify_u_u_bool wok e lem x y :=
  let px := zify_unsigned wok x in
  let py := zify_unsigned wok y in
  constr:(lem _ _ _ _ px py)
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
with zify_unsigned wok e :=
  lazymatch e with
  | ?f1 ?a0 =>
      lazymatch f1 with
      | @word.of_Z _ _ =>
          let p_a0 := zify_term wok a0 in
          let n := fresh "__Zrange_0" in
          unique_pose_proof_name n (@word.unsigned_of_Z_eq_wrap_for_lia _ _ wok _ _ p_a0)
      | @word.opp _ _ =>
          let p_a0 := zify_unsigned wok a0 in
          let n := fresh "__Zspecopp_0" in
          let __ := unique_pose_proof_name n (word.unsigned_opp_eq_for_lia p_a0) in
          zify_unsigned_nop e
      | ?f2 ?a1 =>
          lazymatch f2 with
          | @word.add _ _ => zify_unsigned_app2 wok
                               (@word.unsigned_add_eq_wrap_for_lia _ _ wok) a1 a0
          | @word.sub _ _ => zify_unsigned_app2 wok
                               (@word.unsigned_sub_eq_wrap_for_lia _ _ wok) a1 a0
          | @word.mul _ _ => zify_unsigned_app2 wok
                               (@word.unsigned_mul_eq_wrap_for_lia _ _ wok) a1 a0
          | @word.slu _ _ => zify_unsigned_shift wok e
                               (@word.unsigned_slu_shamtZ_eq_wrap_for_lia _ _ wok) a1 a0
          | @word.sru _ _ => zify_unsigned_shift wok e
                               (@word.unsigned_sru_shamtZ_eq_wrap_for_lia _ _ wok) a1 a0
          | _ => zify_unsigned_nop e
          end
      | _ => zify_unsigned_nop e
      end
  | match ?c with
    | true => ?a
    | false => ?b
    end =>
      lazymatch zify_lia_bool wok c with
      | tt => zify_unsigned_nop e
      | ?pc =>
          let pa := zify_unsigned wok a in
          let pb := zify_unsigned wok b in
          let n := fresh "__Zspecif_0" in
          let __ := unique_pose_proof_name n (word.unsigned_if_eq_for_lia c _ a b _ _ pc pa pb) in
          zify_unsigned_nop e
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
          | @List.cons _ =>
              let pl := zify_len wok a0 in
              constr:(list_len_cons a1 pl)
          | @List.repeatz _ =>
              let pa0 := zify_term wok a0 in
              let n := fresh "__Zcases_0" in
              let __ := unique_pose_proof_name n (list_len_repeatz_cases a1 pa0) in
              zify_len_nop l
          | @List.from _ =>
              let pi := zify_term wok a1 in
              let pl := zify_len wok a0 in
              let n := fresh "__Zcases_0" in
              let __ := unique_pose_proof_name n (list_len_from_cases pi pl) in
              zify_len_nop l
          | @List.upto _ =>
              let pi := zify_term wok a1 in
              let pl := zify_len wok a0 in
              let n := fresh "__Zcases_0" in
              let __ := unique_pose_proof_name n (list_len_upto_cases pi pl) in
              zify_len_nop l
          | _ => zify_len_nop l
          end
      | @List.nil => constr:(list_len_nil a0)

      | _ => zify_len_nop l
      end
  | _ => zify_len_nop l
  end.

Ltac zify_letbound_var wok x body tp :=
  lazymatch tp with
  | @word.rep _ _ =>
      let pf := zify_unsigned wok body in
      let n := fresh "__Zdef_" x in
      let __ := unique_pose_proof_name n (pf : word.unsigned x = _) in
      idtac
  | nat =>
      let pf := zify_of_nat wok body in
      let n := fresh "__Zdef_" x in
      let __ := unique_pose_proof_name n (pf : Z.of_nat x = _) in
      idtac
  | Z => (* xlia zchecker requires that := is turned into =, so we pose a proof
            even if it's just eq_refl *)
      let pf := zify_term wok body in
      let n := fresh "__Zdef_" x in
      let __ := unique_pose_proof_name n (pf : x = _) in
      idtac
  | _ => (* only pose proof if it's more interesting than eq_refl *)
      let pf := zify_term wok body in
      lazymatch pf with
      | eq_refl => idtac
      | _ => let n := fresh "__Zdef_" x in
             let __ := unique_pose_proof_name n (pf : x = _) in
             idtac
      end
  end.

Lemma zify_Prop_if: forall (c c': bool) (P Q P' Q': Prop),
    c = c' ->
    P <-> P' ->
    Q <-> Q' ->
    (if c then P else Q) <-> c' = true /\ P' \/ c' = false /\ Q'.
Proof. intros. split; subst c'; destruct c; intuition discriminate. Qed.

Lemma and_cong: forall (P P' Q Q': Prop),
    P <-> P' ->
    Q <-> Q' ->
    P /\ Q <-> P' /\ Q'.
Proof. intuition. Qed.

Lemma or_cong: forall (P P' Q Q': Prop),
    P <-> P' ->
    Q <-> Q' ->
    P \/ Q <-> P' \/ Q'.
Proof. intuition. Qed.

Lemma impl_cong: forall (P P' Q Q': Prop),
    P <-> P' ->
    Q <-> Q' ->
    (P -> Q) <-> (P' -> Q').
Proof. intuition. Qed.

Lemma not_cong: forall (P P': Prop),
    P <-> P' ->
    (~ P) <-> (~ P').
Proof. intuition. Qed.

Lemma f_equal2_prop: forall [A B: Type] (f: A -> B -> Prop) (a a': A) (b b': B),
    a = a' ->
    b = b' ->
    (f a b) <-> (f a' b').
Proof. intros. subst. reflexivity. Qed.

Lemma unsigned_eq_cong{width}{word: word.word width}{word_ok: word.ok word}:
  forall (x y: word) (ux uy: Z),
    word.unsigned x = ux ->
    word.unsigned y = uy ->
    (x = y) <-> (ux = uy).
Proof. intros. subst. split; intros; subst; auto using word.unsigned_inj. Qed.

Lemma of_nat_eq_cong: forall (a b: nat) (az bz: Z),
    Z.of_nat a = az ->
    Z.of_nat b = bz ->
    (a = b) <-> (az = bz).
Proof. intros. subst. split; intros; subst; auto using Nat2Z.inj. Qed.

Lemma bool_eq_cong: forall (a b a' b': bool),
    a = a' ->
    b = b' ->
    (a = b) <-> (a' = b').
Proof. intros. subst. reflexivity. Qed.

(* Z.of_nat and word.unsigned are embeddings (injections), so their cong lemmas are iffs,
   but len is an abstraction, so its cong lemma only holds in one direction.
   For simplicity, we don't use it right now, but here it is for completeness: *)
Lemma len_eq_cong[A: Type]: forall (xs ys: list A) (lxs lys: Z),
    Z.of_nat (List.length xs) = lxs ->
    Z.of_nat (List.length ys) = lys ->
    (xs = ys) -> (lxs = lys).
Proof. intros. subst. reflexivity. Qed.

Ltac zify_prop wok e :=
  lazymatch e with
  | @eq ?tp ?x ?y =>
      lazymatch tp with
      | @word.rep _ _ =>
          let px := zify_unsigned wok x in
          let py := zify_unsigned wok y in
          (* note: even if px and py are just eq_refl, we still want to transform the
             equality on words into an equality on Zs, and could do so using f_equal2,
             but for uniformity, we can also use unsigned_eq_cong *)
          constr:(unsigned_eq_cong _ _ _ _ px py)
      | nat =>
          let px := zify_of_nat wok x in
          let py := zify_of_nat wok y in
          constr:(of_nat_eq_cong _ _ _ _ px py)
      | bool =>
          let px := zify_bool wok x in
          let py := zify_bool wok y in
          constr:(bool_eq_cong _ _ _ _ px py)
      | _ => zify_prop_app2_terms wok e (@eq tp) x y
      end
  | ?p /\ ?q => zify_prop_app2_props wok e and_cong p q
  | ?p \/ ?q => zify_prop_app2_props wok e or_cong p q
  | ?p -> ?q => zify_prop_app2_props wok e impl_cong p q
  | not ?p =>
      let pp := zify_prop wok p in
      lazymatch pp with
      | iff_refl _ => zify_prop_nop e
      | _ => constr:(not_cong _ _ pp)
      end
  | match ?c with
    | true => ?a
    | false => ?b
    end =>
      let pc := zify_bool wok c in
      let pa := zify_prop wok a in
      let pb := zify_prop wok b in
      constr:(zify_Prop_if _ _ _ _ _ _ pc pa pb)
  | Z.le ?x ?y => zify_prop_app2_terms wok e Z.le x y
  | Z.lt ?x ?y => zify_prop_app2_terms wok e Z.lt x y
  | Z.ge ?x ?y => zify_prop_app2_terms wok e Z.ge x y
  | Z.gt ?x ?y => zify_prop_app2_terms wok e Z.gt x y
  | _ => zify_prop_nop e
  end
with zify_prop_app2_terms wok e f x y :=
  let px := zify_term wok x in
  let py := zify_term wok y in
  lazymatch px with
  | eq_refl =>
      lazymatch py with
      | eq_refl => zify_prop_nop e
      | _ => constr:(f_equal2_prop f _ _ _ _ px py)
      end
  | _ => constr:(f_equal2_prop f _ _ _ _ px py)
  end
with zify_prop_app2_props wok e lem x y :=
  let px := zify_prop wok x in
  let py := zify_prop wok y in
  lazymatch px with
  | iff_refl _ =>
      lazymatch py with
      | iff_refl _ => zify_prop_nop e
      | _ => constr:(lem _ _ _ _ px py)
      end
  | _ => constr:(lem _ _ _ _ px py)
  end.

Lemma iff_to_fw_impl(P1 P2: Prop): (P1 <-> P2) -> (P1 -> P2).
Proof. exact (@proj1 _ _). Qed.

Lemma iff_to_bw_impl(P1 P2: Prop): (P1 <-> P2) -> (P2 -> P1).
Proof. exact (@proj2 _ _). Qed.

Ltac zify_hyp_pf wok h tp :=
  lazymatch type of tp with
  | Prop =>
      let pf := zify_prop wok tp in
      lazymatch pf with
      | iff_refl _ => h
      | _ => constr:(iff_to_fw_impl _ _ pf h)
      end
  | _ => h
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

Ltac do_clear_Z_hyp_if_derivable h :=
  let tp := type of h in
  try (clear h; assert_succeeds (idtac; assert tp by xlia zchecker)).

Ltac don't_clear_Z_hyp_if_derivable h := idtac.

Ltac apply_range_bounding_lemma_in_hyp maybe_clear_Z_hyp_if_derivable wok h tp :=
  tryif ident_starts_with __Zrange_ h then
    lazymatch tp with
    | word.unsigned _ = _ =>
        eapply (@word.unsigned_range_eq _ _ wok) in h;
        maybe_clear_Z_hyp_if_derivable h
    | word.signed _ = _ =>
        eapply (@word.signed_range_eq_for_lia _ _ wok) in h;
        maybe_clear_Z_hyp_if_derivable h
    | Z.of_nat _ = _ =>
        eapply Z_of_nat_range_eq in h;
        maybe_clear_Z_hyp_if_derivable h
    | _ => idtac
    end
  else idtac.

Ltac zify_goal :=
  let g := lazymatch goal with |- ?g => g end in
  let wok := get_word_ok_or_dummy in
  let pf := zify_prop wok g in
  eapply (iff_to_bw_impl _ _ pf);
  (* the result of zify_goal is very short-lived (only one xlia call), so
     we don't waste time on clearing derivable Z hyps seems *)
  foreach_hyp_upwards (apply_range_bounding_lemma_in_hyp don't_clear_Z_hyp_if_derivable wok).

Ltac zify_one_hyp h :=
  let tp := type of h in
  let wok := get_word_ok_or_dummy in
  let __ := zify_hyp_option wok h tp in idtac.

Ltac zify_hyps :=
  let wok := get_word_ok_or_dummy in
  foreach_var (zify_letbound_var wok);
  foreach_hyp (zify_hyp wok);
  (* the results of zify_hyps is often used many times, and might also be seen by the
     user while debugging, so clearing derivable Z hyps seems worthwhile *)
  foreach_hyp_upwards (apply_range_bounding_lemma_in_hyp do_clear_Z_hyp_if_derivable wok).

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

  Ltac rzify_lia := zify_hyps; zify_goal; xlia zchecker.

  Goal forall (x y: Z), 0 <= x < y -> y < 2 ^ 32 -> x mod 2 ^ 32 < y mod 2 ^ 32.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (x y: Z), y < x <= 0 -> - 2 ^ 32 < y -> y mod - 2 ^ 32 < x mod - 2 ^ 32.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (x y: Z), x + y / (5 - 7 + 2) = x.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (x y: Z), x + y mod (5 - 7 + 2) = y + x.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b: nat), Z.of_nat (a + b) = Z.of_nat (a + 0) + Z.of_nat (0 + b).
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Context {word: word.word 32} {word_ok: word.ok word}.
  Local Hint Mode Word.Interface.word - : typeclass_instances.

  Goal forall (a b: word),
      word.signed (a ^+ b) = word.signed (b ^+ a).
  Proof. intros. zify_goal. xlia zchecker. Succeed Qed. Abort.

  Goal forall (a b c: word),
      word.signed (a ^+ b ^- c) = word.signed (word.opp c ^+ b ^+ a).
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b c: word),
      word.signed (a ^+ b ^- c) = word.signed (word.of_Z 0 ^- c ^+ b ^+ a).
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b: word) (z: Z), \[a ^+ b] < z -> let c := b ^+ a in \[c] < z.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b: nat) (z: Z),
      Z.of_nat (Nat.add a b) < z ->
      let c := Nat.add b a in
      Z.of_nat c < z.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b: word) (z: Z), \[a ^+ b] < z -> let c := \[b ^+ a] in c < z.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b r: word),
      \[r] = Z.min \[b] \[a] ->
      \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b: word),
      a <> b ->
      \[a ^- b] <> 0.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b c: word),
      b <> a /\ c <> b /\ c <> a ->
      a ^- b <> word.of_Z 0 /\ b ^- c <> word.of_Z 0.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b x y: word),
      (if word.ltu a b then word.ltu x y = true else word.ltu x y = false) ->
      \[a] < \[b] ->
      \[x] < \[y].
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b: Z),
      let r := if Z.ltb a b then a else b in
      a < b /\ r = a \/ b <= a /\ r = b.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b: Z),
      let c := Z.ltb a b in
      let r := if c then a else b in
      a < b /\ r = a \/ b <= a /\ r = b.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b: Z),
      let c := Z.ltb a b in
      let r := if c then a else word.unsigned (word.of_Z b) in
      a < b /\ r = a \/ b <= a /\ r + 2 ^ 32 * (b / 2 ^ 32) = b.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b: word),
      let c := Z.ltb \[b ^+ a ^- b] \[b] in
      let r := if c then a else b in
      \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b: word),
      let r := if word.ltu (b ^+ a ^- b) b then a else b in
      \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b: word),
      let c := word.ltu a b in
      let r := if c then a else b in
      \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  (* same tests as above but with = instead of := *)

  Goal forall (a b r: Z),
      r = (if Z.ltb a b then a else b) ->
      a < b /\ r = a \/ b <= a /\ r = b.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b r: Z) c,
      c = Z.ltb a b ->
      r = (if c then a else b) ->
      a < b /\ r = a \/ b <= a /\ r = b.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b r: Z) c,
      c = Z.ltb a b ->
      r = (if c then a else word.unsigned (word.of_Z b)) ->
      a < b /\ r = a \/ b <= a /\ r + 2 ^ 32 * (b / 2 ^ 32) = b.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b r: word) c,
      c = Z.ltb \[b ^+ a ^- b] \[b] ->
      r = (if c then a else b) ->
      \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b r: word),
      r = (if word.ltu (b ^+ a ^- b) b then a else b) ->
      \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (a b r: word) c,
      c = word.ltu a b ->
      r = (if c then a else b) ->
      \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (w: word) (in1 in2: Z),
      0 <= in1 < 10 ->
      0 <= in2 < 20 ->
      \[w] = \[if Z.ltb in1 in2 then /[in1] else /[in2]] ->
      \[w] < 20.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (w: word) (in1 in2 in3 in4: Z),
      0 <= in1 < 10 ->
      0 <= in2 < 20 ->
      0 <= in3 < 30 ->
      0 <= in4 < 40 ->
      \[w] = \[if Z.ltb in1 in2
               then if Z.ltb in3 in4 then /[in1] else /[in2]
               else if Z.ltb in1 in3 then /[in3] else /[in4]] ->
      \[w] < 40.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (in0 in1: Z),
      /[in0] <> /[in1] ->
      (negb (word.eqb /[in0] /[in1]))%bool = true.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (in0 in1 in2: Z),
      /[in0] <> /[in2] ->
      /[in1] <> /[in2] ->
      (negb (word.eqb /[in0] /[in2]) && negb (word.eqb /[in1] /[in2]))%bool = true.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (A: Type) (s1: list A),
      (Z.of_nat (List.length (List.from 1 s1)) + 1) * 1 <=
      (Z.of_nat (List.length s1) + 1) * 1.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (A: Type) (i a: Z) (s1: list A),
      Z.of_nat (List.length (List.upto i s1)) + a <=
      Z.of_nat (List.length s1) + a.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  Goal forall (A: Type) (x y z: A) (l: list A),
      Z.of_nat (List.length (l ++ l)) + Z.of_nat (List.length (x :: y :: l)) +
        Z.of_nat (List.length (x :: y :: z :: nil)) =
      3 * Z.of_nat (List.length l) + 5.
  Proof. intros. rzify_lia. Succeed Qed. Abort.

  (* If we use equalities on bool for opaque conditions, lia doesn't recognize that
     the values of a and b are correlated through c: *)
  Goal forall (a b: Z) (c: bool),
      c = true /\ a = 1 \/ c = false /\ a = 2 ->
      c = true /\ b = 2 \/ c = false /\ b = 4 ->
      2 * a = b.
  Proof. intros. Fail lia. destruct c; lia. Succeed Qed. Abort.

  (* On the other hand, if we turn the equalities on bool into equalities on Z,
     lia does recognize the correlation.
     But if we implement this transformation, lia would do case distinctions even
     for things it doesn't understand, and maybe that's too many case distinctions. *)
  Goal forall (a b: Z) (c: bool),
      Z.b2z c = 1 /\ a = 1 \/ Z.b2z c = 0 /\ a = 2 ->
      Z.b2z c = 1 /\ b = 2 \/ Z.b2z c = 0 /\ b = 4 ->
      2 * a = b.
  Proof. intros. lia. Succeed Qed. Abort.

  (* No lia content in condition c, but the goal to be proven holds
     no matter whether c is true or false. Currently, we don't
     add a definition for the value of the if: *)
  Goal forall (c: bool) (w: word) (in1 in2: Z),
      0 <= in1 < 10 ->
      0 <= in2 < 20 ->
      \[w] = \[if c then /[in1] else /[in2]] ->
      \[w] < 20.
  Proof.
    intros. zify_hyps. zify_goal. Fail xlia zchecker.
  Abort.

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
  Succeed Qed. Abort.

  (* not supported yet: *)
  Goal forall (a: word),
      \[a] < 2 ^ 32 ->
      word.divu (/[2] ^* a) /[2] = a.
  Abort.

End Tests.
