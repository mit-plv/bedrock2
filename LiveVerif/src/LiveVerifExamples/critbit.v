(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.onesize_malloc.
Require Import coqutil.Datatypes.PropSet.

(* some parts of this file are based on tree_set.v (binary search trees) *)

Inductive tree_skeleton: Set :=
| Leaf
| Node(leftChild rightChild: tree_skeleton).

Definition tree_skeleton_lt(sk1 sk2: tree_skeleton): Prop :=
  match sk2 with
  | Node leftChild rightChild => sk1 = leftChild \/ sk1 = rightChild
  | Leaf => False
  end.

Lemma tree_skeleton_lt_wf: well_founded tree_skeleton_lt.
Proof.
  unfold well_founded. intros sk2.
  induction sk2; eapply Acc_intro; intros sk1 Lt; unfold tree_skeleton_lt in Lt.
  - contradiction.
  - destruct Lt; subst; assumption.
Qed.


#[local] Hint Resolve tree_skeleton_lt_wf: wf_of_type.

Lemma tree_skeleton_lt_l: forall sk1 sk2,
    safe_implication True (tree_skeleton_lt sk1 (Node sk1 sk2)).
Proof. unfold safe_implication, tree_skeleton_lt. intros. auto. Qed.

Lemma tree_skeleton_lt_r: forall sk1 sk2,
    safe_implication True (tree_skeleton_lt sk2 (Node sk1 sk2)).
Proof. unfold safe_implication, tree_skeleton_lt. intros. auto. Qed.

#[local] Hint Resolve tree_skeleton_lt_l tree_skeleton_lt_r : safe_implication.

Load LiveVerif.

Context {consts: malloc_constants}.

Context {word_map: map.map word word}.
Context {word_map_ok: map.ok word_map}.

Definition prefix_bits (n: Z) (w: word) :=
  if n =? 32 then w else word.and (word.not (/[-1] ^<< /[n])) w.

Lemma testbit_1 : forall i : Z, Z.testbit 1 i = (i =? 0).
Proof.
  intros. unfold Z.testbit. destruct i; reflexivity.
Qed.

Ltac unfold_bits_step :=
  match goal with
  | |- context[ ?X mod 2 ^ 32 ] =>
      let Hb := fresh "Hb" in assert (Hb: 0 <= X < 2 ^ 32); [ lia | ];
                              rewrite (Z.mod_small X (2 ^ 32) Hb); clear Hb
  | H: context[ ?X mod 2 ^ 32 ] |- _ =>
      let Hb := fresh "Hb" in assert (Hb: 0 <= X < 2 ^ 32); [ ZnWords | ];
                              rewrite (Z.mod_small X (2 ^ 32) Hb) in H; clear Hb
  | _ => rewrite word.unsigned_and in *
  | _ => rewrite word.unsigned_or in *
  | _ => rewrite word.unsigned_not in *
  | _ => rewrite word.unsigned_slu; [ | ZnWords ]
  | _ => rewrite word.unsigned_sru; [ | ZnWords ]
  | H: context[ \[word.slu _ _] ] |- _ => rewrite word.unsigned_slu in H; [ | ZnWords ]
  | H: context[ \[word.sru _ _] ] |- _ => rewrite word.unsigned_sru in H; [ | ZnWords ]
  | _ => rewrite word.unsigned_of_Z in *
  | _ => rewrite <- Z.land_ones; [ | lia ]
  | _ => rewrite Z.testbit_ones; [ | lia ]
  | _ => rewrite Z.land_spec in *
  | _ => rewrite Z.lor_spec in *
  | _ => rewrite bitblast.Z.shiftl_spec' in *
  | _ => rewrite bitblast.Z.shiftr_spec' in *
  | _ => rewrite bitblast.Z.lnot_spec' in *
  | _ => rewrite Z.bits_0 in *
  | _ => rewrite bitblast.Z.testbit_minus1' in *
  | _ => rewrite testbit_1 in *
  | H: context[ word.wrap ] |- _ => unfold word.wrap in H
  | _ => unfold word.wrap
  end.

Ltac unfold_bits := repeat unfold_bits_step.

Lemma prefix_bits_is_modulo : forall (n: Z) (w: word),
    0 <= n <= 32 -> prefix_bits n w = /[\[w] mod (2^n)].
Proof.
  (* maybe we could use the bitblast tactic here? *)
  intros. apply word.unsigned_inj. apply Z.bits_inj. unfold Z.eqf.
  intros. assert (n = 32 \/ n < 32).
  lia. destruct H0; unfold prefix_bits;
    [ assert (Hc: n =? 32 = true); [ lia | ] | assert (Hc: n =? 32 = false); [ lia | ] ];
    rewrite Hc; unfold_bits; (replace (\[w]) with (\[w] mod 2 ^ 32); [ | ZnWords ]);
    unfold_bits; destruct (Z.testbit \[w] n0); lia.
  (* invoking unfold_bits for a second time because that adds the information
     that testbit \[w] is non-zero only for indices 0 to 31 *)
Qed.

Record prefix: Type := {
    length: Z;
    bits: word
  }.

Definition is_prefix (p1 p2: prefix) :=
  p1.(length) <= p2.(length) /\ prefix_bits p1.(length) p1.(bits) = prefix_bits p1.(length) p2.(bits).

Definition canonic_bits (p: prefix) := prefix_bits p.(length) p.(bits).

Definition is_canonic (p: prefix) := canonic_bits p = p.(bits).

Definition bit_at (n: Z) := /[1] ^<< /[n].

Definition append_0 (p: prefix) :=
  {| length := p.(length) + 1;
     bits := canonic_bits p |}.

Definition append_1 (p: prefix) :=
  {| length := p.(length) + 1;
     bits := word.or (canonic_bits p) (bit_at p.(length)) |}.

Definition full_prefix (k: word) := {| length := 32; bits := k |}.

Definition is_prefix_key (p: prefix) (k: word) := is_prefix p (full_prefix k).

Ltac f_apply f H :=
  match type of H with
  | ?lhs = ?rhs =>
      let h := fresh "H" in assert (h: f lhs = f rhs); [ rewrite H; reflexivity | ];
                            cbv beta in h; clear H; rename h into H
  end.

Ltac prove_is_prefix_append_x :=
  intros;
  unfold is_prefix; unfold append_0; unfold append_1; unfold bit_at;
  unfold canonic_bits; unfold prefix_bits;
  split; simpl; [ lia | ];
  replace (length _ =? 32) with false; [ | lia ];
  apply word.unsigned_inj; apply Z.bits_inj; unfold Z.eqf;
  intros; unfold_bits; destruct (Z.testbit \[bits _]); lia.

Lemma is_prefix_append_0 : forall p, 0 <= length p < 32 -> is_prefix p (append_0 p).
Proof.
  prove_is_prefix_append_x.
Qed.

Lemma is_prefix_append_1 : forall p, 0 <= length p < 32 -> is_prefix p (append_1 p).
Proof.
  prove_is_prefix_append_x.
Qed.

Lemma is_prefix_trans : forall p1 p2 p3,
    0 <= length p1 <= 32 -> 0 <= length p2 <= 32 -> 0 <= length p3 <= 32 ->
    is_prefix p1 p2 -> is_prefix p2 p3 -> is_prefix p1 p3.
Proof.
  intros. unfold is_prefix in *. split. lia. destruct H2. destruct H3.
  rewrite prefix_bits_is_modulo in *; try lia.
  rewrite prefix_bits_is_modulo in *; try lia.
  f_equal.
  Ltac extract_equality H :=
    let Hres := fresh "H" in
    eassert (Hres: \[ ?[a] ] = \[ ?[b] ]);
    [ apply f_equal; exact H | ];
    repeat rewrite word.unsigned_of_Z in Hres; unfold word.wrap in Hres;
    rewrite (Zmod_small _ (2 ^ 32)) in Hres;
    (* infinite loop if I use repeat rewrite here?! *)
    rewrite (Zmod_small _ (2 ^ 32)) in Hres;
    clear H; rename Hres into H.
  extract_equality H4.
  extract_equality H5.
  f_apply (fun n => n mod (2 ^ length p1)) H5.
  replace (length p2) with (length p1 + (length p2 - length p1)) in H5; [ | lia].
  rewrite Z.pow_add_r in H5. rewrite Z.rem_mul_r in H5. rewrite Z.rem_mul_r in H5.
  rewrite Z.mul_comm in H5. rewrite Z_mod_plus_full in H5.
  rewrite Z.mul_comm in H5. rewrite Z_mod_plus_full in H5.
  repeat rewrite Zmod_mod in H5. congruence.
  all: try lia.
  all: match goal with | |- context[?a mod ?b] => assert (0 <= a mod b < b);
    [ apply Z_mod_lt; lia | ]; assert (b <= 2 ^ 32); [ apply Z.pow_le_mono_r; lia | ]
       end; lia.
Qed.

Lemma is_prefix_key_trans : forall p1 p2 k,
    0 <= length p1 <= 32 -> 0 <= length p2 <= 32 ->
    is_prefix p1 p2 -> is_prefix_key p2 k -> is_prefix_key p1 k.
Proof.
  intros. unfold is_prefix_key in *. eapply is_prefix_trans. all: cycle 3.
  eassumption. assumption. 3: simpl. all: lia.
Qed.

(* no need to use word (record) for ghost: might use positive *)
Fixpoint cbt' (sk: tree_skeleton) (p: prefix) (c: word_map) (a: word): mem -> Prop :=
  match sk with
    | Leaf => ex1 (fun k: word => ex1 (fun v: word =>
        <{ * emp (a <> /[0])
           * freeable 12 a
           * <{ + uintptr /[-1] (* uint 32 (2 ^ 32 - 1) *)
                + uintptr k
                + uintptr v }> a
           * emp (p = full_prefix k)
           * emp (c = map.singleton k v) }>))
  | Node skL skR => ex1 (fun aL: word => ex1 (fun pL: prefix => ex1 (fun cL: word_map =>
     ex1 (fun aR: word => ex1 (fun pR: prefix => ex1 (fun cR: word_map
          =>
          <{ * emp (a <> /[0])
             * freeable 12 a
             * <{ + uintptr /[p.(length)] (* uint 32 p.(length) *)
                  + uintptr aL
                  + uintptr aR }> a
             * cbt' skL pL cL aL
             * cbt' skR pR cR aR
             * emp (0 <= p.(length) <= 31)
             * emp (is_canonic p)
             * emp (is_prefix (append_0 p) pL)
             * emp (is_prefix (append_1 p) pR)
             * emp (map.split c cL cR) }>))))))
  end.

Definition nncbt (c: word_map) (a: word): mem -> Prop :=
  ex1 (fun sk: tree_skeleton => ex1 (fun p: prefix => cbt' sk p c a)).

(* in full generality, a CBT can be represented as a pointer which is either
   - NULL for an empty CBT, or
   - pointing to the CBT root node *)
Definition cbt (c: word_map) (a: word): mem -> Prop :=
  or1 (nncbt c a) (emp (c = map.empty /\ a = /[0])).


#[export] Instance spec_of_cbt_init: fnspec :=                              .**/

uintptr_t cbt_init( ) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := R m;
  ensures t' m' res := t' = t /\
                       <{ * cbt map.empty res
                          * R }> m' #**/                                   /**.
Derive cbt_init SuchThat (fun_correct! cbt_init) As cbt_init_ok.                .**/
{                                                                          /**. .**/
  return NULL;                                                             /**. .**/
}                                                                          /**.
unfold cbt. exists (map.empty). exists m. step. apply map.split_empty_l.
step. step. right. unfold emp. tauto. tauto.
Qed.

Lemma purify_cbt' :
  forall sk p c a, purify (cbt' sk p c a) (a <> /[0] /\ 0 <= length p <= 32).
Proof.
  unfold purify. intros. destruct sk; simpl cbt' in *; steps; subst p; simpl; steps.
Qed.

Lemma purify_wand : forall (P Q: mem -> Prop), purify (wand P Q) True.
Proof. unfold purify. auto. Qed.

#[local] Hint Extern 1 (cannot_purify (cbt' _ _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (cbt' _ _ _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (cbt _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (wand _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (nncbt _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (freeable _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (or1 _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (sep _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify (uint _ _ _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (cannot_purify _)
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (PredicateSize_not_found (wand _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (PredicateSize_not_found (or1 _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (PredicateSize_not_found (nncbt _))
      => constructor : suppressed_warnings.
#[local] Hint Extern 1 (PredicateSize_not_found (sep allocator))
      => constructor : suppressed_warnings.

#[local] Hint Unfold cbt : heapletwise_always_unfold.
#[local] Hint Unfold nncbt : heapletwise_always_unfold.

Hint Resolve purify_cbt' : purify.
Hint Resolve purify_wand : purify.
Print HintDb purify.

Lemma cbt_key_has_prefix : forall (sk: tree_skeleton) (p: prefix) (c: word_map) (a: word) (m: mem) (k: word),
    cbt' sk p c a m -> map.get c k <> None -> is_prefix_key p k.
Proof.
  induction sk.
  - intros. unfold cbt' in H. steps. subst c. unfold map.singleton in *. subst p.
    assert (k = k0 \/ k <> k0). step. destruct H. subst k0. unfold is_prefix_key.
    unfold is_prefix. step. rewrite map.get_put_diff in H0.
    rewrite map.get_empty in H0. congruence. assumption.
  - intros. simpl in H. steps. apply split_du in H11. unfold map.split in H11.
    destruct H11. destruct (map.get c k) eqn:E; [ | tauto ]. clear H0.
    subst c. epose proof (map.putmany_spec cL cR k). destruct H.
    destruct H as [v [H H']]. clear IHsk1. pose proof H5.
    eapply IHsk2 with (k:=k) in H5.
    eapply is_prefix_key_trans. lia. 3: eassumption. assumption.
    eapply is_prefix_trans. lia. 4: eassumption. simpl. lia. lia.
    eapply is_prefix_append_1. lia. rewrite H. discriminate.
    clear IHsk2. eapply IHsk1 with (k:=k) in H4.
    eapply is_prefix_key_trans. lia. 3: eassumption. lia.
    eapply is_prefix_trans. lia. 4: eassumption.
    simpl. lia. lia. eapply is_prefix_append_0. lia. destruct H.
    rewrite E in H0. rewrite <- H0. discriminate.
Qed.

#[export] Instance spec_of_dummy: fnspec := .**/
uintptr_t dummy( ) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := True;
                  ensures t' m' res := True #**/ /**. About spec_of_dummy.

Check .**/ void dummy( ) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := True;
                  ensures t' m' := True #**/ /**.

Check spec_of_dummy : Semantics.env -> Prop.
Print spec_of_dummy.

(* observation: if A and B both can't be purified, purify_rec fails on sep A B, but
not on sep A P or sep P B, where P can be purified *)


Require Import bedrock2.PurifySep.

Lemma wand_trans : forall (P Q R : mem -> Prop),
    impl1 <{ * wand P Q * wand Q R }> (wand P R).
Proof.
  (* Set Printing Coercions. *)
  unfold impl1. intros. unfold wand in *. intros. steps. unfold "|=" in *.
  rewrite mmap.du_assoc in H0. rewrite mmap.du_comm in H0.
  rewrite mmap.du_assoc in H0. remember (m1 \*/ m0). destruct m.
  eapply H3. rewrite split_du. eassumption. eapply H2. rewrite split_du.
  symmetry. rewrite mmap.du_comm. eassumption. assumption. discriminate.
Qed.

Lemma wand_ex_r : forall {A: Type} (P : mem -> Prop) (Q: A -> mem -> Prop),
    impl1 (ex1 (fun x => wand P (Q x))) (wand P (ex1 Q)).
Proof.
  unfold impl1. intros. destruct H. unfold wand. intros. apply H in H0.
  eexists. auto.
Qed.

Lemma wand_emp_iff_impl : forall (P Q : mem -> Prop),
    (wand P Q map.empty) <-> (impl1 P Q).
Proof.
  intros. unfold wand. split; intros.
  - unfold impl1. intros. eapply H.
    apply map.split_empty_l. reflexivity. assumption.
  - apply H. rewrite map.split_empty_l in H0. congruence.
Qed.

Lemma wand_same_emp : forall P : mem -> Prop, wand P P map.empty.
Proof.
  unfold wand. intros. apply map.split_empty_l in H. congruence.
Qed.

Lemma or1_intro_l : forall P Q : mem -> Prop, impl1 P (or1 P Q).
Proof.
  unfold impl1. unfold or1. auto.
Qed.

Lemma or1_intro_r : forall P Q : mem -> Prop, impl1 Q (or1 P Q).
Proof.
  unfold impl1. unfold or1. auto.
Qed.

Lemma to_with_mem : forall (P : mem -> Prop) (m : mem), P m -> with_mem m P.
Proof.
  auto.
Qed.

Ltac hyps_to_with_mem := repeat match goal with
  | H: ?P ?m |- _ => apply to_with_mem in H
  end.

Lemma or1_sep : forall P Q R : mem -> Prop,
  iff1 (sep (or1 P Q) R) (or1 (sep P R) (sep Q R)).
Proof.
  intros. split; steps; lazymatch goal with H: context[ or1 ] |- _ => destruct H end;
    steps; hyps_to_with_mem;
    [ left | right | eapply (or1_intro_l _ Q m0) in H0
    | eapply (or1_intro_r P _ m0) in H0];
    steps; hyps_to_with_mem; steps.
Qed.

Lemma or1_seps : forall (P Q : mem -> Prop) (Ps : list (mem -> Prop)),
  iff1 (seps (cons (or1 P Q) Ps)) (or1 (seps (cons P Ps)) (seps (cons Q Ps))).
Proof.
  intros. simpl. destruct Ps; [ | apply or1_sep]; apply iff1_refl.
Qed.

Lemma du_def_split : forall (m m1 : mem) (mm: mmap mem),
    mm \*/ m1 = m -> exists m2 : mem, mm = m2 /\ map.split m m2 m1.
Proof.
  intros. pose proof H. unfold "\*/" in H0. destruct mm eqn:E. exists m0.
  split. reflexivity. apply split_du. assumption. discriminate.
Qed.


Lemma append_0_prefix : forall (p : prefix) (k : word),
    0 <= length p <= 31 -> is_prefix_key (append_0 p) k ->
    word.and (k ^>> /[length p]) /[1] = /[0].
Proof.
Admitted.
  (*
  (*
  intros p k. unfold is_prefix_key. unfold is_prefix.
  unfold full_prefix. simpl. unfold canonic_bits. unfold prefix_bits.  *)
  intros. unfold is_prefix_key in *. unfold is_prefix in *. simpl in *.
  unfold canonic_bits in *. unfold prefix_bits in *.
  destruct (length p + 1 =? 32) eqn:E. destruct (length p =? 32) eqn:E2.
  lia. apply word.unsigned_inj. ZnWords_pre. apply Z.bits_inj. unfold Z.eqf. destruct H0.
  subst k. intros. unfold_bits. lia. destruct (length p =? 32) eqn:E2. lia.
  apply word.unsigned_inj. apply Z.bits_inj. unfold Z.eqf. destruct H0.
  intros. f_apply (fun x => Z.testbit \[x] (n + length p)) H1. unfold_bits.
  rewrite Z.land_spec.
  apply word.unsigned_inj. apply Z.bits_inj. unfold Z.eqf. destruct H.
  intros. f_apply (fun x => \[x]) H0. unfold_bits.
  rewrite Z.land_spec in
  destruct (Z.testbit 0 n). f_apply (fun x => \[x]) H0. unfold_bits.
  unfold_bits. destruct
   *)

Lemma append_1_prefix : forall (p : prefix) (k : word),
    0 <= length p <= 31 -> is_prefix_key (append_1 p) k ->
    word.and (k ^>> /[length p]) /[1] = /[1].
Proof.
Admitted.

Lemma manual_du_on_sep : forall (m m1 m2: mem) (P Q : mem -> Prop),
    P m1 -> Q m2 -> mmap.du m1 m2 = m -> sep P Q m.
Proof.
  steps. change (P m1) with (m1 |= P) in H.
  change (Q m2) with (m2 |= Q) in H0. steps.
Qed.

Lemma map_get_putmany_not_left : forall (m1 m2 : word_map) (k : word),
    map.get m1 k = None -> map.get (map.putmany m1 m2) k = map.get m2 k.
Proof.
  intros. destruct (map.get m2 k) eqn:E. erewrite map.get_putmany_right. reflexivity.
  assumption. erewrite map.get_putmany_left; assumption.
Qed.

Local Hint Extern 1 (PredicateSize (cbt' ?sk)) => exact 12 : typeclass_instances.

#[export] Instance spec_of_cbt_best_leaf: fnspec :=                             .**/


uintptr_t cbt_best_leaf(uintptr_t tp, uintptr_t k) /**#
  ghost_args := (sk: tree_skeleton) (pr: prefix) (c: word_map) (R: mem -> Prop);
  requires t m := <{ * cbt' sk pr c tp
                     * R }> m;
  ensures t' m' res := t' = t /\ ex1 (fun k' => ex1 (fun v' =>
                  let leaf := cbt' Leaf (full_prefix k') (map.singleton k' v') res in
                        <{ * leaf
                           * wand leaf (cbt' sk pr c tp)
                           * emp (k <> k' -> map.get c k = None)
                           * emp (k = k' -> map.get c k = Some v')
                           * R }> )) m' #**/     /**.
Derive cbt_best_leaf SuchThat (fun_correct! cbt_best_leaf) As cbt_best_leaf_ok.  .**/
{                                                                            /**. .**/
  uintptr_t p = tp;                                                          /**.

  (* setting up the loop invariant *)
  move H0 at bottom. rewrite <- Def0 in H0.
  move m0 at bottom. remember c as c'. remember sk as sk'. remember pr as pr'.
  prove (m0 |= sep (cbt' sk' pr' c' p) (wand (cbt' sk' pr' c' p) (cbt' sk pr c tp))).
  { subst sk'. subst pr'. subst c'. subst tp. prove (mmap.Def m0 = mmap.Def m0).
    unfold "|=". steps. unfold canceling. steps. simpl. subst m2.
    apply wand_emp_iff_impl. eapply impl1_refl. }
  prove (map.get c' k = map.get c k). subst c. reflexivity.
  rewrite Heqc'. rewrite Heqsk'. rewrite Heqpr'. (* rewriting inside ready *)
  clear H0 Heqc' Heqsk' Heqpr' Def0.
  loop invariant above p.                                            .**/
  while (load(p) != -1) /* decreases sk' */ { /*?.
  subst v.
  instantiate (3:=(match sk' with | Leaf => ?[ME1] | _ => ?[ME2] end)).
  destruct sk'; cycle 1. simpl cbt' in *. steps.
  .**/
  (* without "== 1", not supported in one of the tactics *)
    if (((k >> load(p)) & 1) == 1) /* split */ {                           /**. .**/
      p = load(p + 8);                                                       /**. .**/
    }                                                                        /**.
  unfold canceling. unfold seps. step. step. step. eapply wand_trans.
  apply sep_comm. step. step. unfold canceling. step. step. step. unfold seps.
  unfold wand. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step.
  change (cbt' sk'2 pR cR p m4) with (m4 |= cbt' sk'2 pR cR p) in H15.
  step. step. step. step. step. step. step. step. step. step.
  rewrite split_du. assumption. step. step. step. step.
  rewrite <- H4. clear H4 H5.
  apply split_du in H14. unfold map.split in H14. destruct H14.
  subst c'. symmetry. apply map_get_putmany_not_left.
  destruct (map.get cL k) eqn:E; [ exfalso | trivial ].
  apply cbt_key_has_prefix with (k:=k) in H7.
  eapply is_prefix_key_trans in H11. 4: eassumption. apply append_0_prefix in H11.
  rewrite H in H11. ZnWords. step. unfold append_0. simpl. step. step.
  congruence. step. step. .**/
    else {                                                                   /**. .**/
      p = load(p + 4);                                                       /**. .**/
    }                                                                        /**.
  (* the proof here in the else branch is almost exactly the same as in
     the then branch, except that we unfold wand a bit later and instead
     apply the wand_ex_r lemma before the unfolding *)
  unfold canceling. unfold seps. step. step. step. eapply wand_trans.
  unfold seps. apply sep_comm. step. step. unfold canceling. step. step. step.
  unfold seps. apply wand_ex_r. step. apply wand_ex_r. step. apply wand_ex_r.
  step. apply wand_ex_r. step. apply wand_ex_r. step. apply wand_ex_r. step.
  unfold wand. intros. step. step. step. step. step. step. step.
  change (cbt' sk'1 pL cL p m4) with (m4 |= cbt' sk'1 pL cL p) in H15. step. step.
  step. step. step. step. step. step. step. step. step. rewrite <- split_du in H14.
  assumption. step. step. step. step. rewrite <- H4. clear H4 H5.
  apply split_du in H14. unfold map.split in H14. destruct H14. subst c'.
  symmetry. apply map.get_putmany_left.
  destruct (map.get cR k) eqn:E; [ exfalso | trivial ]. (*
  apply map.invert_get_putmany_None in H1. step. assumption. step.
  destruct (map.get c' k) eqn:E; [ exfalso | trivial ]. apply split_du in H14.
  apply map.get_split with (k:=k) in H14. destruct H14; step. congruence.
  rewrite H4p0 in E. *) apply cbt_key_has_prefix with (k:=k) in H8.
  eapply is_prefix_key_trans in H12. 4: eassumption. apply append_1_prefix in H12.
  congruence. step. unfold append_1. simpl. step. step. congruence. step. .**/
  }                                                                          /**.
  simpl cbt' in *. steps. .**/
  return p;                                                                  /**. .**/
} /**. unfold full_prefix. step. step. step. step. step. reflexivity.
  subst pr'. subst c'. step. rewrite <- H4. unfold map.singleton. step. step.
  rewrite map.get_put_diff. apply map.get_empty. assumption. step. step. subst k0.
  rewrite map.get_put_same. steps. steps.
Qed.

(*
(* comment-out rationale: while properties of a tree-subtree pair probably can be
   extracted from a T1 --* T2 wand (T1 here is a subtree T2) (like here below,
   it seems painful to
   prove such a lemma; it seems easier to assert the properties we need in the
   postcondition of cbt_find_best, where they should be easier to prove *)
Lemma subtree_content : forall (tp tp' : word) (sk sk' : tree_skeleton)
                               (pr pr' : prefix) (c c' : word_map) (k : word) (m : mem),
  sep (cbt' sk' pr' c' tp') (wand (cbt' sk' pr' c' tp') (cbt' sk pr c tp)) m ->
  is_prefix_key pr' k -> map.get c k = map.get c' k.
Proof.
  induction sk.
  - intros. destruct sk'. pose proof H. apply wand_mp in H. simpl in H. apply to_with_mem in H1.
    steps. unfold "|=" in H1. unfold sep in H1. fwd. destruct sk'.
    + simpl in H1p1. repeat destruct_ex1_step. repeat split_sep_step.
      repeat destruct_emp_step. subst pr'.
apply split_du in D. rewrite <- manual_du_on_sep in H1.
Admitted.
*)

Lemma map_singleton_inj : forall (k1 k2 v1 v2 : word),
    map.singleton k1 v1 = map.singleton k2 v2 -> k1 = k2 /\ v1 = v2.
Proof.
  intros. unfold map.singleton in *. assert (k1 = k2).
  assert (k1 = k2 \/ k1 <> k2). step. destruct H0; [ trivial | exfalso ].
  f_apply (fun m: word_map => map.get m k2) H. rewrite map.get_put_same in H.
  rewrite map.get_put_diff in H. rewrite map.get_empty in H. discriminate.
  auto. subst k1. steps. f_apply (fun m: word_map => map.get m k2) H.
  repeat rewrite map.get_put_same in H. congruence.
Qed.

#[export] Instance spec_of_cbt_lookup: fnspec :=                                .**/
uintptr_t cbt_lookup(uintptr_t tp, uintptr_t k, uintptr_t val_out) /**#
  ghost_args := (c: word_map) (val_out_orig: word) (R: mem -> Prop);
  requires t m := <{ * cbt c tp
                     * uintptr val_out_orig val_out
                     * R }> m;
  ensures t' m' res := t' = t
           /\ <{ * emp (res = /[match map.get c k with | Some _ => 1 | None => 0 end])
                 * cbt c tp
                 * uintptr (match map.get c k with
                            | Some v => v
                            | None => val_out_orig
                            end) val_out
                 * R }> m'         #**/                                     /**.
Derive cbt_lookup SuchThat (fun_correct! cbt_lookup) As cbt_lookup_ok.           .**/
{                                                                           /**. .**/
  if (tp == NULL) /* split */ {                                             /**. .**/
    return 0;                                                               /**. .**/
  }                                                                         /**.
  destruct H0. steps. apply purify_cbt' in H0. steps. apply purify_emp in H0.
  steps. subst c. rewrite map.get_empty. step. subst tp. steps. destruct H0.
  steps. apply purify_cbt' in H. steps. apply purify_emp in H. steps. subst c.
  rewrite map.get_empty. steps. .**/
  else {                                                                    /**.
  destruct H0; [ | exfalso ]; hyps_to_with_mem; repeat heapletwise_step; fwd;
  [ | contradiction ]. .**/
    uintptr_t n = cbt_best_leaf(tp, k);                                     /*?.
  steps. unfold enable_frame_trick.enable_frame_trick. steps. .**/
    uintptr_t k' = load(n + 4);                                             /*?.
  simpl in H1. step. step. step. step. step. step. step.
  apply map_singleton_inj in H12. fwd. subst k0. steps. .**/
    if (k' == k) /* split */ {                                              /**. .**/
      store(val_out, load(n + 8));                                          /**. .**/
      return 1;                                                             /**. .**/
    }                                                                       /**.
  destruct (map.get c k); [ trivial | exfalso ]. assert (None = Some v).
  auto. discriminate.
  unfold canceling. step. step. step. apply or1_seps. left. simpl. step.
  step. step. step. instantiate (2:=sk). instantiate (1:=p). step.
  clear D H0 m0. clear m2 H3 m3.
  assert ((m11 \*/ (m1 \*/ (m5 \*/ m7))) \*/ m4 = m11 \*/ (((m1 \*/ m4) \*/ m5) \*/ m7)).
  rewrite mmap.du_assoc. f_equal. rewrite (mmap.du_assoc _ _ m4).
  rewrite (mmap.du_comm _ m4). repeat rewrite mmap.du_assoc. reflexivity.
  remember (m1 \*/ m4 \*/ m5) as m0. destruct m0; cycle 1. rewrite D0 in H0.
  simpl in H0. discriminate. rewrite H0. clear H0. assert (cbt' sk p c tp m0).
  remember (m1 \*/ m4) as m2. destruct m2; [ | discriminate ].
  symmetry in Heqm0.
  eassert (<{ * ?[P] * (wand ?P ?[Q]) }> m0). eapply manual_du_on_sep. 3: eassumption.
  2: eassumption. unfold cbt'. steps. symmetry in Heqm2. steps. apply wand_mp in H0.
  assumption. hyps_to_with_mem. step. step. step. step. step. step.
  symmetry in H9. apply H6 in H9. rewrite H9. steps. steps.  .**/
    else {                                                                 /**. .**/
      return 0;                                                            /**. .**/
    }                                                                      /**.
  assert (map.get c k = None). apply H4. congruence. steps. unfold canceling.
  step. step. step. apply or1_seps. left. simpl. step. step. step. step.
  instantiate (2:=sk). instantiate (1:=p). step. clear D H0 H3 m0 m2 m3 m.
  assert ((m1 \*/ (m5 \*/ (m7 \*/ m9))) \*/ m4 = (m4 \*/ m1 \*/ m5) \*/ (m7 \*/ m9)).
  rewrite mmap.du_comm. repeat rewrite mmap.du_assoc. reflexivity.
  remember (m4 \*/ m1 \*/ m5) as m0. rewrite H0. destruct m0; cycle 1.
  rewrite D0 in H0. simpl in H0. discriminate. clear H0. assert (cbt' sk p c tp m).
  remember (m4 \*/ m1). destruct m0; [ | discriminate ].
  symmetry in Heqm0.
  eassert (<{ * ?[P] * (wand ?P ?[Q]) }> m). eapply manual_du_on_sep.
  3: eassumption. 2: eassumption. unfold cbt'. symmetry in Heqm1. steps.
  apply wand_mp in H0. assumption. hyps_to_with_mem. steps.
  apply not_eq_sym in H9. apply H4 in H9. rewrite H9. steps. steps.
 .**/
  }                                                                        /**. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_cbt_alloc_leaf: fnspec :=                            .**/

uintptr_t cbt_alloc_leaf(uintptr_t k, uintptr_t v) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * allocator * R }> m;
  ensures t' m' res := t' = t
           /\ <{ * (if \[res] =? 0 then
                     allocator_failed_below 12
                   else
                     <{ * allocator
                        * cbt (map.singleton k v) res }>)
                 * R }> m' #**/                                            /**.
Derive cbt_alloc_leaf SuchThat (fun_correct! cbt_alloc_leaf) As cbt_alloc_leaf_ok. .**/
{                                                                          /**. .**/
  uintptr_t p = malloc(12);                                                /**. .**/
  if (p == NULL) /* split */ {                                             /**. .**/
    return NULL;                                                           /**. .**/
  }                                                                        /**.
  assert (\[/[0]] = 0). step. rewrite H3. simpl (_ =? _) in *.
  cbv iota in *. steps. .**/
  else {                                                                   /**.
  assert (\[p] =? 0 = false). steps. rewrite H3 in H2. unfold "|=" in H2. .**/
    store(p, -1);                                                          /**. .**/
    store(p + 4, k);                                                       /**. .**/
    store(p + 8, v);                                                       /**. .**/
    return p;                                                              /**. .**/
  }                                                                        /**.
  replace (\[p] =? 0) with (false) by steps. step. step. unfold canceling.
  step. step. step. apply or1_seps. left. simpl. step. step. step.
  instantiate (2:=Leaf). simpl cbt'. step. step. step. step. step.
  assert (m7 \*/ (m10 \*/ (m8 \*/ (((m4 \*/ m0) \*/ m1) \*/ m2))) =
  (m7 \*/ m10 \*/ m8) \*/ (((m4 \*/ m0) \*/ m1) \*/ m2)).
  repeat rewrite mmap.du_assoc. reflexivity. remember (m7 \*/ m10 \*/ m8) as m11.
  destruct m11; cycle 1. rewrite D0 in H10. simpl in H10. discriminate.
  rewrite H10. step. step. step.
  instantiate (2:=k). instantiate (1:=v). clear H5 H7.
  assert (<{ + uintptr /[-1]
                          + uintptr k
                          + uintptr v }> p m). symmetry in Heqm11. unfold sepapps.
  simpl. unfold sepapp. steps. clear H2 H8 H11. unfold canceling. step. step.
  step. unfold seps. remember ((m4 \*/ m0) \*/ m2) as m12. destruct m12; cycle 1.
  simpl in D0. discriminate. eapply manual_du_on_sep. 3: eassumption. assumption.
  symmetry in Heqm12. step. step. step. step. step. step. unfold canceling.
  step. step. step. simpl. eapply proj2. rewrite <- (sep_emp_l _ R).
  remember (m4 \*/ m0) as m11. destruct m11; cycle 1. simpl in D0. discriminate.
  eapply manual_du_on_sep. 3: eassumption. instantiate (1:=True). symmetry in Heqm0.
  unfold anyval in H6. destruct H6. apply array_0_is_emp in H2. unfold emp in H2. fwd.
  unfold anyval in H9. destruct H9. apply array_0_is_emp in H2. unfold emp in H2. fwd.
  apply split_du in Heqm0. unfold map.split in Heqm0. fwd. subst m6. unfold emp.
  split. apply map.empty_putmany. step. step. step. step. step. step. step. step.
  step. step. step. step. .**/
}                                                                          /**.
Qed.

(* whether like this or in some other way, it would be nice to have some
   automated reasoning about maps *)
(*
Ltac reason_map := repeat lazymatch goal with
  (*
  | H: context[ map.get map.empty ?k ] |- _ => rewrite map.get_empty in H
  | H: context[ map.get (map.put _ ?k _) ?k ] |- _ => rewrite map.get_put_same in H *)
  | H: context[ map.get (map.singleton ?k _) ?k ] |- _ =>
    unfold map.singleton in H; rewrite map.get_put_same in H
  | |- context[ map.get (map.singleton ?k _) ?k ] =>
    unfold map.singleton; rewrite map.get_put_same
  end.
*)

Lemma map_get_singleton_same : forall (k v : word),
    map.get (map.singleton k v) k = Some v.
Proof.
  intros. unfold map.singleton. apply map.get_put_same.
Qed.

Lemma map_get_singleton_diff : forall (k k' v : word),
    k' <> k -> map.get (map.singleton k v) k' = None.
Proof.
  intros. unfold map.singleton. rewrite map.get_put_diff. apply map.get_empty.
  assumption.
Qed.

Ltac destruct_split H :=
  try apply split_du in H; unfold map.split in H; destruct H.

Ltac eq_neq_cases k1 k2 :=
  let H := fresh "H" in assert (H: k1 = k2 \/ k1 <> k2); [ step | ]; destruct H.

Lemma cbt_nonempty : forall sk pr c tp m,
  cbt' sk pr c tp m -> exists k v, map.get c k = Some v.
Proof.
  induction sk; intros; simpl in H.
  - steps. subst c. instantiate (2:=k). reason_map. reflexivity.
  - repeat heapletwise_step. apply IHsk2 in H4. cleanup_step. steps.
    destruct_split H10. subst c. apply map.get_putmany_right. eassumption.
Qed.

Lemma putmany_singleton_left_small : forall (c1 c2 : word_map) k v,
  map.putmany c1 c2 = map.singleton k v ->
  c1 = map.empty \/ exists v', c1 = map.singleton k v'.
Proof.
  intros. destruct (map.get c1 k) eqn:E.
  - right. exists r. apply map.map_ext. intros. eq_neq_cases k k0. subst k0.
    rewrite map_get_singleton_same. assumption. rewrite map_get_singleton_diff.
    f_apply (fun c : word_map => map.get c k0) H. rewrite map_get_singleton_diff in H.
    apply map.invert_get_putmany_None in H. destruct H. assumption. congruence.
    congruence.
  - left. apply map.map_ext. intros. eq_neq_cases k k0. subst k0.
    rewrite map.get_empty. assumption. rewrite map.get_empty.
    f_apply (fun c : word_map => map.get c k0) H. rewrite map_get_singleton_diff in H.
    apply map.invert_get_putmany_None in H. tauto. congruence.
Qed.

Lemma putmany_singleton_right_small : forall (c1 c2 : word_map) k v,
   map.putmany c1 c2 = map.singleton k v -> c2 = map.empty \/ c2 = map.singleton k v.
Proof.
  intros. destruct (map.get c2 k) eqn:E; [ right | left ]; apply map.map_ext;
  intros; eq_neq_cases k k0.
  - subst k0. rewrite map_get_singleton_same. rewrite E.
    eapply map.get_putmany_right in E. rewrite H in E.
    rewrite map_get_singleton_same in E. congruence.
  - eapply map.get_putmany_right in E. rewrite H in E. rewrite map_get_singleton_diff.
    f_apply (fun c : word_map => map.get c k0) H. rewrite map_get_singleton_same in E.
    rewrite map_get_singleton_diff in H. apply map.invert_get_putmany_None in H.
    tauto. congruence. congruence.
  - subst k0. rewrite map.get_empty. assumption.
  - f_apply (fun c : word_map => map.get c k0) H. rewrite map_get_singleton_diff in H.
    apply map.invert_get_putmany_None in H. rewrite map.get_empty. tauto. congruence.
Qed.

Lemma cbt_singleton_is_leaf : forall sk pr k v tp m,
    cbt' sk pr (map.singleton k v) tp m -> sk = Leaf.
Proof.
  destruct sk.
  - intros. reflexivity.
  - intros. exfalso. simpl in *. steps. destruct_split H10. symmetry in H.
    pose proof H. apply putmany_singleton_left_small in H. destruct H.
    apply cbt_nonempty in H3. cleanup_step. subst cL. rewrite map.get_empty in H3.
    discriminate. cleanup_step. apply putmany_singleton_right_small in H10.
    destruct H10. apply cbt_nonempty in H4. cleanup_step. subst cR.
    rewrite map.get_empty in H4. discriminate. unfold map.disjoint in H9.
    specialize (H9 k v' v). subst cL. subst cR.
    repeat rewrite map_get_singleton_same in H9. auto.
Qed.

#[export] Instance spec_of_cbt_insert: fnspec :=                                .**/

uintptr_t cbt_insert(uintptr_t tp, uintptr_t k, uintptr_t v) /**#
  ghost_args := (c: word_map) (R: mem -> Prop);
  requires t m := <{ * allocator
                     * cbt c tp
                     * R }> m;
  ensures t' m' res := t' = t
           /\ <{ * (if \[res] =? 0 then
                     <{ * allocator_failed_below 12
                        * cbt c tp }>
                    else
                     <{ * allocator
                        * cbt (map.put c k v) res }>)
                 * R }> m'        #**/                                     /**.
Derive cbt_insert SuchThat (fun_correct! cbt_insert) As cbt_insert_ok.          .**/
{                                                                          /**. .**/
  if (tp == NULL) /* split */ {                                            /**. .**/
    (* a direct `return cbt_alloc_leaf(k, v);` gives a type error
       (the assignment_rhs type vs the expr type) *)
    uintptr_t res = cbt_alloc_leaf(k, v);                                  /**. .**/
    return res;                                                            /**. .**/
  }                                                                        /**.
  destruct H2. step. step. apply purify_cbt' in H2. tauto. step. step.
  destruct (\[res] =? 0) eqn:E. steps. subst tp. steps. steps.
  unfold "|=" in H1. unfold canceling. steps. apply or1_seps.
  right. simpl. assert (mmap.Def m1 = mmap.Def m1). step. step. step. step.
  step. step. step. step. step. step. step. step. step. step.
  unfold "|=" in H1. step. destruct H4; cycle 1. step. step. step.
  f_apply (fun c : word_map => map.get c k) H1p0.
  rewrite map_get_singleton_same in *. rewrite map.get_empty in *.
  discriminate. step. step. step. unfold canceling. step. step. step.
  apply or1_seps. left. simpl. step. step. step. instantiate (2:=Leaf).
  instantiate (1:=full_prefix k). simpl cbt'. step. step. step. step.
  step. step. pose proof (cbt_singleton_is_leaf _ _ _ _ _ _ H1). subst sk.
  simpl (cbt' Leaf) in H1. unfold "|=" in H1. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step.
  instantiate (2:=k). instantiate (1:= v). step. step. step. subst c.
  reflexivity. repeat rewrite mmap.du_empty_l. step. step.
  apply map_singleton_inj in H7. steps. steps.

  }
(* TODO: implement & prove *)
Abort.

End LiveVerif. Comments .**/ //.
