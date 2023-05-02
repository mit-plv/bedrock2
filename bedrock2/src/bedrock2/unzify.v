(* Z-ify word expressions in an undoable (unzify) way *)

Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Z.Lia.
Require Import coqutil.Datatypes.ZList.
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

  Lemma zify_Z_if: forall (c crhs: bool) (a b a' b': Z),
      c = crhs ->
      a = a' ->
      b = b' ->
      crhs = true /\ (if c then a else b) = a' \/
      crhs = false /\ (if c then a else b) = b'.
  Proof. intros. subst a' b' crhs. destruct c; intuition. Qed.
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
      | Z.of_nat => zify_of_nat wok a0
      | Z.opp => zify_app1 wok e f1 a0
      | ?f2 ?a1 =>
          lazymatch f2 with
          | Z.add     => zify_app2 wok e f2 a1 a0
          | Z.sub     => zify_app2 wok e f2 a1 a0
          | Z.mul     => zify_app2 wok e f2 a1 a0
          (* TODO: also pose Euclidean division equations for div and mod *)
          | Z.div     => zify_app2 wok e f2 a1 a0
          | Z.modulo  => zify_app2 wok e f2 a1 a0
          | Z.ltb     => zify_app2 wok e f2 a1 a0
          | Z.leb     => zify_app2 wok e f2 a1 a0
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
          | @word.ltu _ _ => zify_u_u_bool wok e (@word.unsigned_ltu_eq _ _ wok) a1 a0
          | @word.eqb _ _ => zify_u_u_bool wok e (@word.unsigned_eqb_eq _ _ wok) a1 a0
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
with zify_lia_bool wok c0 :=
  let c := rdelta_var c0 in
  match goal with
  | |- _ => let pc := zify_term wok c in
            let __ := lazymatch type of pc with | _ = ?rhs => is_lia_bool rhs end in pc
  | h: c = ?rhs |- _ =>
      let __ := match constr:(Set) with _ => is_lia_bool rhs end in h
  | _ => constr:(tt)
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
      let pc := zify_term wok c in
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

Ltac clear_Z_hyp_if_derivable h :=
  let tp := type of h in
  try (clear h; assert_succeeds (idtac; assert tp by xlia zchecker)).

Ltac apply_range_bounding_lemma_in_hyp wok h tp :=
  tryif ident_starts_with __Zrange_ h then
    lazymatch tp with
    | word.unsigned _ = _ =>
        eapply (@word.unsigned_range_eq _ _ wok) in h; clear_Z_hyp_if_derivable h
    | Z.of_nat _ = _ => eapply Z_of_nat_range_eq in h; clear_Z_hyp_if_derivable h
    | _ => idtac
    end
  else idtac.

Ltac apply_range_bounding_lemma_in_eqs wok :=
  foreach_hyp_upwards (apply_range_bounding_lemma_in_hyp wok).

Ltac zify_goal :=
  let g := lazymatch goal with |- ?g => g end in
  let wok := get_word_ok_or_dummy in
  let pf := zify_prop wok g in
  eapply (iff_to_bw_impl _ _ pf);
  apply_range_bounding_lemma_in_eqs wok.

Ltac zify_hyps :=
  let wok := get_word_ok_or_dummy in
  foreach_var (zify_letbound_var wok);
  foreach_hyp (zify_hyp wok);
  apply_range_bounding_lemma_in_eqs wok.

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
  Proof. intros. try rzify_lia. Qed.

  Goal forall (a b: nat) (z: Z),
      Z.of_nat (Nat.add a b) < z ->
      let c := Nat.add b a in
      Z.of_nat c < z.
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b: word) (z: Z), \[a ^+ b] < z -> let c := \[b ^+ a] in c < z.
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b r: word),
      \[r] = Z.min \[b] \[a] ->
      \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b.
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b: word),
      a <> b ->
      \[a ^- b] <> 0.
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b c: word),
      b <> a /\ c <> b /\ c <> a ->
      a ^- b <> word.of_Z 0 /\ b ^- c <> word.of_Z 0.
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b x y: word),
      (if word.ltu a b then word.ltu x y = true else word.ltu x y = false) ->
      \[a] < \[b] ->
      \[x] < \[y].
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b: Z),
      let r := if Z.ltb a b then a else b in
      a < b /\ r = a \/ b <= a /\ r = b.
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b: Z),
      let c := Z.ltb a b in
      let r := if c then a else b in
      a < b /\ r = a \/ b <= a /\ r = b.
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b: Z),
      let c := Z.ltb a b in
      let r := if c then a else word.unsigned (word.of_Z b) in
      a < b /\ r = a \/ b <= a /\ r + 2 ^ 32 * (b / 2 ^ 32) = b.
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b: word),
      let c := Z.ltb \[b ^+ a ^- b] \[b] in
      let r := if c then a else b in
      \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b.
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b: word),
      let r := if word.ltu (b ^+ a ^- b) b then a else b in
      \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b.
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b: word),
      let c := word.ltu a b in
      let r := if c then a else b in
      \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b.
  Proof. intros. rzify_lia. Qed.

  (* same tests as above but with = instead of := *)

  Goal forall (a b r: Z),
      r = (if Z.ltb a b then a else b) ->
      a < b /\ r = a \/ b <= a /\ r = b.
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b r: Z) c,
      c = Z.ltb a b ->
      r = (if c then a else b) ->
      a < b /\ r = a \/ b <= a /\ r = b.
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b r: Z) c,
      c = Z.ltb a b ->
      r = (if c then a else word.unsigned (word.of_Z b)) ->
      a < b /\ r = a \/ b <= a /\ r + 2 ^ 32 * (b / 2 ^ 32) = b.
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b r: word) c,
      c = Z.ltb \[b ^+ a ^- b] \[b] ->
      r = (if c then a else b) ->
      \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b.
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b r: word),
      r = (if word.ltu (b ^+ a ^- b) b then a else b) ->
      \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b.
  Proof. intros. rzify_lia. Qed.

  Goal forall (a b r: word) c,
      c = word.ltu a b ->
      r = (if c then a else b) ->
      \[a] < \[b] /\ r = a \/ \[b] <= \[a] /\ r = b.
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
