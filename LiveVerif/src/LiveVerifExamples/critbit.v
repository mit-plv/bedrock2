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
  | _ => rewrite word.unsigned_xor in *
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
  | _ => rewrite Z.lxor_spec in *
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
#[local] Hint Extern 1 (cannot_purify allocator)
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

Local Hint Extern 1 (PredicateSize (cbt' ?sk)) => exact 12 : typeclass_instances.

Lemma cbt_expose_fields (sk: tree_skeleton) (p: prefix) (c: word_map) (a: word):
  impl1 (cbt' sk p c a) (ex1 (fun w1 => ex1 (fun w2 => ex1 (fun w3 =>
    <{ * freeable 12 a
       * <{ + uintptr w1
            + uintptr w2
            + uintptr w3 }> a
       * emp (a <> /[0])
       * match sk with
         | Leaf => <{ * emp (w1 = /[-1])
                      * emp (p = full_prefix w2)
                      * emp (c = map.singleton w2 w3) }>
         | Node skL skR => ex1 (fun pL: prefix => ex1 (fun cL: word_map =>
                           ex1 (fun pR: prefix => ex1 (fun cR: word_map =>
                         <{ * emp (w1 = /[p.(length)])
                            * cbt' skL pL cL w2
                            * cbt' skR pR cR w3
                            * emp (0 <= p.(length) <= 31)
                            * emp (is_canonic p)
                            * emp (is_prefix (append_0 p) pL)
                            * emp (is_prefix (append_1 p) pR)
                            * emp (map.split c cL cR) }>))))
         end
                                                              }> )))).
Proof.
  unfold impl1. intro m. intros. destruct sk; simpl cbt' in *.
  - steps.
  - steps. apply split_du. assumption.
Qed.

Lemma cbt_fields (sk: tree_skeleton) (p: prefix) (c: word_map) (a: word) :
  impl1 (cbt' sk p c a) (ex1 (fun w2 => ex1 (fun w3 => ex1 (fun R =>
       <{ * <{ + uintptr
       (match sk with
        | Leaf => /[-1]
        | Node _ _ => /[p.(length)]
        end)
        + uintptr w2 + uintptr w3 }> a * R }>)))).
Proof.
  unfold impl1. intros. destruct sk; simpl in *; steps.
Qed.

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

Lemma prefixes_of_same : forall (p1 p2 p3: prefix),
  length p1 <= length p2 -> is_prefix p1 p3 -> is_prefix p2 p3 -> is_prefix p1 p2.
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

(*
Lemma uintptr_footprint : forall a v m,
  uintptr v a m -> forall addr,
  map.get m addr <> None <-> 0 <= \[addr ^- a] < 4.


Lemma cbt_leaf_footprint : forall pr c lp m,
  cbt' Leaf pr c lp m -> forall addr,
  map.get m addr <> None <-> 0 <= \[addr ^- lp] < 12.
Proof.

  assert (malloc_block_size > 12). unfold malloc_block_size.
  intros. simpl in H. steps.
  assert (map.get m addr = None <-> map.get m1 addr = None).
  apply split_du in D. unfold map.split in D. destruct D. subst m.
  split; intros. apply map.invert_get_putmany_None in H. tauto.
  rewrite map.get_putmany_left. unfold freeable in H2.


Lemma determine_leaf_in_leaf : forall pr pr' c c' lp lp' m0 m1,
  map.disjoint m0 m1 ->
  cbt' Leaf pr' c' lp' m0 ->
  wand (cbt' Leaf pr' c' lp') (cbt' Leaf pr c lp) m1 ->
  (pr = pr' /\ c = c' /\ lp = lp').
Proof.
  intros. remember (map.putmany m0 m1) as m. assert (map.split m m0 m1).
  unfold map.split. tauto. apply split_du in H2.
  eapply manual_du_on_sep in H2; [ | eassumption | eassumption ].
  eapply wand_mp in H2. assert

(* same as with subtree_content lemma further up *)
Lemma leaf_value_write : forall sk pr k v v' c m m0 lp tp,
  map.disjoint m0 m ->
  cbt' Leaf (full_prefix k) (map.singleton k v) lp m0 ->
  wand (cbt' Leaf (full_prefix k) (map.singleton k v) lp) (cbt' sk pr c tp) m ->
  wand (cbt' Leaf (full_prefix k) (map.singleton k v') lp) (cbt' sk pr (map.put c k v') tp) m.
Proof.
  induction sk.
  - intros. unfold wand. intros. pose proof manual_du_on_sep.
    remember (map.putmany m0 m) as mm. assert (map.split mm m0 m). unfold map.split.
    tauto. apply split_du in H5. eapply H4 in H5. 2: eexact H0. 2: eexact H1.
    apply wand_mp in H5. simpl in H5. step. steps. subst c.

Inductive cbt_subtree :
  tree_skeleton -> prefix -> word_map -> word -> mem ->
  tree_skeleton -> prefix -> word_map -> word -> mem ->
  Prop :=
  | cbt_subtree_refl (sk' : tree_skeleton) (pr' : prefix) (c' : word_map) (tp' : word) (m' : mem) : cbt' sk' pr' c' tp' m' ->
      cbt_subtree sk' pr' c' tp' m' sk' pr' c' tp' m'
  | cbt_subtree_step (sk' : tree_skeleton) (pr' : prefix) (c' : word_map) (tp' : word) (m' : mem) (sk : tree_skeleton) (pr : prefix) (
*)

Lemma map_put_putmany_right : forall (m1 m2: word_map) (k v: word),
  map.put (map.putmany m1 m2) k v = map.putmany m1 (map.put m2 k v).
Proof.
  intros. apply map.map_ext. intros. assert (k0 = k \/ k0 <> k). step.
  destruct H. subst k0. rewrite map.get_put_same. erewrite map.get_putmany_right.
  reflexivity. rewrite map.get_put_same. reflexivity.
  rewrite map.get_put_diff; [ | assumption ]. destruct (map.get m2 k0) eqn:E.
  erewrite map.get_putmany_right; [ | eassumption ].
  erewrite map.get_putmany_right. reflexivity. rewrite map.get_put_diff.
  assumption. assumption. rewrite map.get_putmany_left; [ | assumption ].
  rewrite map.get_putmany_left; [ reflexivity | rewrite map.get_put_diff; assumption ].
Qed.

Lemma map_put_putmany_left : forall (m1 m2: word_map) (k v: word),
  map.get m2 k = None ->
  map.put (map.putmany m1 m2) k v = map.putmany (map.put m1 k v) m2.
Proof.
Admitted.

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

Lemma map_put_singleton_same : forall (k v v': word),
  map.put (map.singleton k v) k v' = map.singleton k v'.
Proof.
  intros. unfold map.singleton. apply map.put_put_same.
Qed.

Ltac destruct_split H :=
  try apply split_du in H; unfold map.split in H; destruct H.

Ltac eq_neq_cases k1 k2 :=
  let H := fresh "H" in assert (H: k1 = k2 \/ k1 <> k2); [ step | ]; destruct H.

#[export] Instance spec_of_cbt_update_or_best: fnspec :=                        .**/

uintptr_t cbt_update_or_best(uintptr_t tp, uintptr_t k, uintptr_t v) /**#
  ghost_args := (sk: tree_skeleton) (pr: prefix) (c: word_map) (R: mem -> Prop);
  requires t m := <{ * cbt' sk pr c tp
                     * R }> m;
  ensures t' m' res := t' = t /\ map.get c res <> None /\
                       (forall pr_q k_q,
                       0 <= length pr_q <= 32 ->
                       map.get c k_q <> None -> is_prefix_key pr_q k_q ->
                       is_prefix_key pr_q k -> is_prefix_key pr_q res) /\
                ((res = k /\ <{ * cbt' sk pr (map.put c k v) tp * R }> m')
            \/   (res <> k /\ <{ * cbt' sk pr c tp * R }> m')) #**/     /**.
Derive cbt_update_or_best SuchThat (fun_correct! cbt_update_or_best)
  As cbt_update_or_best_ok. .**/
{                                                                            /**. .**/
  uintptr_t p = tp;                                                          /**. (* .**/
  uintptr_t cb = 0;                                                          /**. *)

  (* setting up the loop precondition *)
  rewrite <- Def0 in H0.
  (* delete #(cb = ??). *)
  move t before tp.
  unfold ready. rewrite <- Def0. rewrite Def0 at 2.
  delete #(p = ??).
  move sk at bottom.
  move c after Scope1.
  move R after Scope1.
  move pr after Scope1.
  loop invariant above m.

  (* transform goal here *)
  lazymatch goal with
  | |- exec ?fs ?body ?t ?m ?l ?P =>
      lazymatch eval pattern sk, p, pr, c, R in P with
      | ?f sk p pr c R =>
          change (exec fs body t m l ((fun (g: word * prefix * word_map * (mem -> Prop)) (sk: tree_skeleton) =>
     (*let '(s1, s2, p1, p2, R) := g in f s1 s2 p1 p2 R) (s1, s2, p1, p2, R) (len s1)))*)
          let (g, R) := g in
          let (g, c) := g in
          let (p, pr) := g in
          f sk p pr c R) (p, pr, c, R) sk))
      end
  end.
  eapply wp_while_tailrec_use_functionpost with (e:=live_expr:(load(p) != -1)).
  { eauto with wf_of_type. }
  { package_heapletwise_context. }
  start_loop_body.
  subst v0.
  instantiate (3:=(match sk with | Leaf => ?[vLeaf] | _ => ?[vNode] end)).
  destruct sk; cycle 1. simpl cbt' in H3. steps. .**/
    if (((k >> load(p)) & 1) == 1) /* split */ {                             /**. .**/
      p = load(p + 8);                                                       /**. .**/
    }                                                                        /**.
  new_ghosts(p, pR, cR, <{ * R
                           * freeable 12 p'
                           * cbt' sk1 pL cL aL
                           * <{ + uintptr /[length pr]
                                + uintptr aL
                                + uintptr p }> p' }>). instantiate (1:=sk2).
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. unfold state_implication.
  (* ^^ step on state_implication clears c = cL \*/ cR (which we need) *)
  step. destruct H1. step. econstructor. eassumption. apply split_du in H12.
  unfold map.split in H12. destruct H12. subst c. step. step. step. step.
  destruct (map.get cR retv) eqn:E; [ | congruence ]. intro.
  eapply map.get_putmany_right in E. erewrite H1 in E. discriminate.
  step. step. destruct (map.get cR k_q) eqn:E. eapply HPp2. lia. erewrite E.
  congruence. assumption. assumption.
  destruct (map.get (map.putmany cL cR) k_q) eqn:E2; [ | congruence ].
  eapply map.get_putmany_left in E. erewrite E2 in E. rewrite E in H13.
  eapply cbt_key_has_prefix in H13. 2: eassumption.
  assert (length pr_q <= length pr \/ length pr < length pr_q). lia.
  eapply cbt_key_has_prefix in HPp1. 2: eassumption.
  destruct H16. eapply prefixes_of_same in H16. 2: eexact H14.
  eapply is_prefix_trans. lia. 4: eassumption. lia. simpl. lia.
  eapply is_prefix_trans. lia. 4: eassumption. simpl. lia. lia.
  eapply is_prefix_trans. lia. 3: eassumption. lia. simpl. lia.
  apply is_prefix_append_1. lia. eapply is_prefix_trans. lia. 4: eexact H13.
  lia. simpl. lia. eapply is_prefix_trans. lia. 4: eassumption. simpl. lia.
  lia. apply is_prefix_append_0. lia.
  assert (is_prefix (append_0 pr) pr_q). eapply prefixes_of_same. simpl. lia.
  2: eexact H14. eapply is_prefix_trans. simpl. lia. 3: eassumption. lia.
  simpl. lia. assumption. eapply is_prefix_trans in H15. 5: eassumption.
  apply append_0_prefix in H15. exfalso. ZnWords. lia. simpl. lia. lia.
  simpl. lia.
  simpl cbt'. destruct HPp3; [ left | right ]. steps. unfold map.split. step.
  apply map_put_putmany_right. apply map.disjoint_put_r; [ | assumption ].
  destruct (map.get cL k) eqn:E; [ exfalso | trivial ].
  assert (map.get cL k <> None). congruence. eapply cbt_key_has_prefix in H13.
  2: eassumption. eapply is_prefix_trans in H13. 5: eassumption.
  apply append_0_prefix in H13. ZnWords. lia. simpl. lia. lia. simpl. lia.
  steps. steps. unfold map.split. steps. .**/
    else {                                                                   /**. .**/
      p = load(p + 4);                                                       /**. .**/
    }                                                                        /**.
  new_ghosts(p, pL, cL, <{ * R
                           * freeable 12 p'
                           * cbt' sk2 pR cR aR
                           * <{ + uintptr /[length pr]
                                + uintptr p
                                + uintptr aR }> p' }>).
  apply split_du in H12. unfold map.split in H12. destruct H12. subst c.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. unfold state_implication. step.
  destruct H1. step. econstructor. eassumption. step. step. step. step.
  intro. apply map.invert_get_putmany_None in H1. tauto.
  eapply cbt_key_has_prefix in HPp1. 2: eassumption. step. step.
  destruct (map.get (map.putmany cL cR) k_q) eqn:E; [ | congruence ].
  destruct (map.get cR k_q) eqn:E2; cycle 1. rewrite map.get_putmany_left in E;
  [ | eassumption ]. eapply HPp2. lia. 2: eexact H14. congruence. assumption.
  assert (map.get cR k_q <> None). congruence. eapply cbt_key_has_prefix in H16.
  2: eassumption. assert (length pr_q <= length pr \/ length pr < length pr_q). lia.
  destruct H17. eapply prefixes_of_same in H17. 2: eexact H14.
  eapply is_prefix_trans. lia. 4: eassumption. lia. simpl. lia.
  eapply is_prefix_trans. lia. 4: eassumption. simpl. lia. lia.
  eapply is_prefix_trans. lia. 4: apply is_prefix_append_0. lia. simpl. lia.
  assumption. lia.
  eapply is_prefix_trans. lia. 4: eexact H16. lia. simpl. lia.
  eapply is_prefix_trans. lia. 4: eassumption. simpl. lia. lia.
  apply is_prefix_append_1. lia. assert (is_prefix (append_1 pr) pr_q).
  eapply prefixes_of_same. simpl. lia. 2: eexact H14. eapply is_prefix_trans.
  simpl. lia. 3: eassumption. lia. simpl. lia. assumption.
  eapply is_prefix_trans in H15. 5: eassumption. eapply append_1_prefix in H15.
  exfalso. ZnWords. lia. simpl. lia. lia. simpl. lia.
  simpl cbt'. destruct HPp3; [ left | right ]. steps. unfold map.split.
  assert (map.get cR k = None). (* step.
  apply map_put_putmany_left. *) destruct (map.get cR k) eqn:E;
  [ exfalso | trivial ]. assert (map.get cR k <> None). congruence.
  eapply cbt_key_has_prefix in H13. 2: eassumption. eapply is_prefix_trans in H13.
  5: eassumption. apply append_1_prefix in H13. congruence. lia. simpl. lia. lia.
  simpl. lia. step. apply map_put_putmany_left. assumption.
  apply map.disjoint_put_l. assumption. assumption.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. apply map.split_disjoint_putmany. assumption. step. step. .**/
  }                                                                         /**.
  simpl cbt' in H3. steps. .**/
  if (load(p + 4) == k) /* split */ {                                       /**. .**/
    store(p + 8, v);                                                        /**. .**/
    return k;                                                               /**. .**/
  }                                                                         /**.
  subst c. rewrite map_get_singleton_same. congruence. left. simpl cbt'.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. subst c. apply map_put_singleton_same.
  step. step. .**/
  else {                                                                    /**. .**/
    return load(p + 4);                                                     /**. .**/
  }                                                                         /**.
  subst c. rewrite map_get_singleton_same. congruence. subst c.
  eq_neq_cases k0 k_q. subst k0. assumption.
  rewrite map_get_singleton_diff in H8. contradiction. congruence.
  right. step. step. simpl cbt'. steps. .**/
}                                                                           /**.
Qed.

#[export] Instance spec_of_cbt_best_leaf: fnspec :=                             .**/

uintptr_t cbt_best_leaf(uintptr_t tp, uintptr_t k) /**#
  ghost_args := (sk: tree_skeleton) (pr: prefix) (c: word_map) (R: mem -> Prop);
  requires t m := <{ * cbt' sk pr c tp
                     * R }> m;
  ensures t' m' res := t' = t /\ ex1 (fun k' => ex1 (fun v' =>
     let leaf := cbt' Leaf (full_prefix k') (map.singleton k' v') res in
       <{ * leaf
          * wand leaf (cbt' sk pr c tp) (*
          * and1 (wand leaf (cbt' sk pr c tp))
            (fun m => forall v'', (* forall version of ex1? *)
               wand (cbt' Leaf (full_prefix k') (map.singleton k' v'') res)
                    (cbt' sk pr (map.put c k v'') tp) m) *)
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
    apply wand_emp_iff_impl. eapply impl1_refl. } (*
  unfold "|=" in H. step. unzify. unpurify. *)
  prove (map.get c' k = map.get c k). subst c. reflexivity.
  rewrite Heqc'. rewrite Heqsk'. rewrite Heqpr'. (* rewriting inside ready *)
  clear Heqc' Heqsk' Heqpr' Def0. (*
  prove (forall v'' lp,
    m0 |= <{ * cbt' Leaf (full_prefix k') (map.singleton k' v'') lp
  prove (forall k' v v' lp ma' mb' ma mb lp,
    ((map.split m2 ma' mb' /\
     cbt' Leaf (full_prefix k') (map.singleton k' v) lp ma' /\
     wand (cbt' Leaf (full_prefix k') (map.singleton k' v) lp)
          (cbt' sk' pr' c' p) mb') ->
    (wand (cbt' Leaf (full_prefix k') (map.singleton k' v') lp)
          (cbt' sk' pr' (map.put c' k v') mb'))) ->
    ((map.split
    (map.sp *)
  clear H0.
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
  destruct (map.get cR k) eqn:E; [ exfalso | trivial ].
  apply cbt_key_has_prefix with (k:=k) in H8.
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

Lemma cbt_nonempty : forall sk pr c tp m,
  cbt' sk pr c tp m -> exists k v, map.get c k = Some v.
Proof.
  induction sk; intros; simpl in H.
  - steps. subst c. instantiate (2:=k). rewrite map_get_singleton_same. reflexivity.
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

Inductive hidden (P : Type): Type := hide: P -> hidden P.

Lemma xor_0_l: forall w, word.xor /[-1] w = word.not w.
Proof.
  intros. apply word.unsigned_inj. unfold_bits. apply Z.bits_inj.
  unfold Z.eqf. intros. unfold_bits. destruct (Z.testbit \[w] n);
  destruct xorb eqn:E; unfold xorb in E; fwd; lia.
Qed.

#[export] Instance spec_of_critical_bit: fnspec :=                              .**/

uintptr_t critical_bit(uintptr_t k1, uintptr_t k2) /**#
  (* heaplet packaging doesn't work well then there's just one item in the heap *)
  ghost_args := (R1 R2: mem -> Prop);
  requires t m := <{ * R1 * R2 }> m /\ k1 <> k2;
  ensures t' m' res := t = t' /\ <{ * R1 * R2 }> m'
                /\ 0 <= \[res] < 32
                /\ prefix_bits \[res] k1 = prefix_bits \[res] k2
                /\ prefix_bits (\[res] + 1) k1 <> prefix_bits (\[res] + 1) k2 #**/  /**.
Derive critical_bit SuchThat (fun_correct! critical_bit) As critical_bit_ok.    .**/
{                                                                          /**. .**/
  uintptr_t i = 0;                                                         /**.
  prove (0 <= \[i] < 32).
  prove (word.and (word.not (/[-1] ^<< i)) k1 = word.and (word.not (/[-1] ^<< i)) k2).
  subst i. replace (word.not (/[-1] ^<< /[0])) with /[0]. apply word.unsigned_inj.
  unfold_bits. repeat rewrite Z.land_0_r. reflexivity. apply word.unsigned_inj.
  unfold_bits. simpl. reflexivity.
  delete #(i = /[0]).
  loop invariant above H.
  move i at bottom. .**/
  while (i < 31 && ((-1 ^ (-1 << (i + 1))) & k1) == ((-1 ^ (-1 << (i + 1))) & k2))
    /* decreases (32 - \[i]) */ {                                          /**. .**/
    i = i + 1;                                                             /**. .**/
  }                                                                        /**.
  subst i. replace (word.opp /[1]) with (/[-1]) in H5.
  rewrite xor_0_l in H5. assumption. ZnWords. .**/
  return i;                                                                /**. .**/
}                                                                          /**.
  unfold prefix_bits. assert (Hi: \[i] =? 32 = false). lia. rewrite Hi.
  replace /[\[i]] with i. assumption. ZnWords.
  unfold prefix_bits. destruct (\[i] + 1 =? 32) eqn:E. assumption.
  destruct H. exfalso. ZnWords. replace (word.opp /[1]) with (/[-1]) in H.
  rewrite xor_0_l in H. replace (/[\[i] + 1]) with (i ^+ /[1]).
  assumption. ZnWords. ZnWords.
Qed.

Definition empty_prefix := {| length := 0; bits := /[0] |}.

Lemma empty_is_prefix: forall pr, 0 <= length pr <= 32 -> is_prefix empty_prefix pr.
Proof.
  intros. unfold is_prefix. unfold empty_prefix. simpl. step. step.
  unfold prefix_bits. simpl.
Admitted.

Lemma is_prefix_key_extend_0: forall pr k,
  0 <= length pr < 32 -> is_prefix_key pr k ->
  word.and (k ^>> /[length pr]) /[1] = /[0] ->
  is_prefix_key (append_0 pr) k.
Proof.
Admitted.

Lemma is_prefix_key_extend_1: forall pr k,
  0 <= length pr < 32 -> is_prefix_key pr k ->
  word.and (k ^>> /[length pr]) /[1] = /[1] ->
  is_prefix_key (append_1 pr) k.
Proof.
Admitted.

Lemma clip_prefix_bits: forall n1 n2 w,
  0 <= n1 <= n2 -> n2 <= 32 -> prefix_bits n1 (prefix_bits n2 w) = prefix_bits n1 w.
Proof.
Admitted.

Lemma clip_prefix_bits_equality: forall n1 n2 wa wb,
  0 <= n1 <= n2 -> n2 <= 32 -> prefix_bits n2 wa = prefix_bits n2 wb ->
  prefix_bits n1 wa = prefix_bits n1 wb.
Proof.
Admitted.

Lemma map_get_putmany_not_None_iff: forall (m1 m2: word_map) (k: word),
  map.get (map.putmany m1 m2) k <> None <->
  (map.get m1 k <> None \/ map.get m2 k <> None).
Proof.
  intros. destruct (map.get m2 k) eqn:E.
  - erewrite map.get_putmany_right. 2: eassumption. split. right. tauto. congruence.
  - erewrite map.get_putmany_left. 2: eassumption. tauto.
Qed.

Lemma bits_equality_is_prefix_key_iff: forall pr k1 k2,
  prefix_bits (length pr) k1 = prefix_bits (length pr) k2 ->
  (is_prefix_key pr k1 <-> is_prefix_key pr k2).
Proof.
  intros. unfold is_prefix_key. unfold is_prefix. simpl. rewrite H. tauto.
Qed.

Lemma same_prefix_bits_equality: forall pr k1 k2,
  is_prefix_key pr k1 -> is_prefix_key pr k2 ->
  prefix_bits (length pr) k1 = prefix_bits (length pr) k2.
Proof.
  intros. unfold is_prefix_key in *. unfold is_prefix in *.
  simpl in *. fwd. congruence.
Qed.

Lemma eq_None_by_false {X : Type}: forall o: option X, ~(o <> None) -> o = None.
Proof.
  intros. destruct o. exfalso. apply H. congruence. congruence.
Qed.

Lemma map_get_singleton_not_None: forall k v k': word,
  map.get (map.singleton k v) k' <> None -> k = k'.
Proof.
  intros. eq_neq_cases k k'; [ trivial | exfalso ].
  rewrite map_get_singleton_diff in H; congruence.
Qed.

Lemma is_prefix_refl: forall pr, is_prefix pr pr.
Proof.
  intros. unfold is_prefix. step.
Qed.

Lemma is_prefix_key_refl: forall k, is_prefix_key (full_prefix k) k.
Proof.
  intros. unfold is_prefix_key. apply is_prefix_refl.
Qed.

Lemma is_prefix_key_extend_0_or_1: forall pr k,
  0 <= length pr < 32 -> is_prefix_key pr k ->
  (is_prefix_key (append_0 pr) k \/ is_prefix_key (append_1 pr) k).
Proof.
Admitted.

Lemma and_1_not_1_0: forall w, word.and w /[1] <> /[1] -> word.and w /[1] = /[0].
Proof.
Admitted.

#[export] Instance spec_of_cbt_insert_at: fnspec :=                             .**/

uintptr_t cbt_insert_at(uintptr_t tp, uintptr_t cb, uintptr_t k, uintptr_t v) /**#
  ghost_args := (sk: tree_skeleton) (total_pr: prefix) (pr: prefix) (c: word_map)
                (R: mem -> Prop);
  requires t m := <{ * allocator
                     * cbt' sk pr c tp
                     * R }> m
                  /\ 0 <= length total_pr
                  /\ is_prefix total_pr pr /\ is_prefix_key total_pr k
                  /\ 0 <= \[cb] < 32
                  /\ exists k',
                       (map.get c k' <> None
                         /\ prefix_bits \[cb] k' = prefix_bits \[cb] k)
                  /\ forall k',
                       (map.get c k' <> None ->
                         prefix_bits (\[cb] + 1) k' <> prefix_bits (\[cb] + 1) k);
  ensures t' m' res := t' = t
                       /\ if \[res] =? 0 then
                            <{ * allocator_failed_below 12
                               * cbt' sk pr c tp
                               * R
                               * (fun _ => True) }> m'
                          else
                            (* `id` is a hack to identify this occurrence when
                                rewriting *)
                            res = id tp /\
                            ex1 (fun sk' => ex1 (fun pr' =>
                              <{ * allocator
                                 * emp (is_prefix total_pr pr')
                                 * cbt' sk' pr' (map.put c k v) tp
                                 * R }>)) m' #**/ /**.
Derive cbt_insert_at SuchThat (fun_correct! cbt_insert_at) As cbt_insert_at_ok.  .**/
{                                                                           /**. .**/
  uintptr_t p = tp;                                                         /**.
  assert (Htpnn: tp <> /[0]). apply purify_cbt' in H2. tauto.
  move Htpnn after Scope1.
  rewrite <- Def0 in H2.
  move t before tp.
  unfold ready. rewrite <- Def0. rewrite Def0 at 2. replace (id p) with tp.
  delete #(p = ??).
  move sk at bottom. (*
  move c after Scope5.
  move R after Scope1.
  move p' after Scope1. *)
  move k' before Scope1.
  move p before Scope1.
  loop invariant above m.
  (*
  eapply exec.weaken; cycle 1. intros.
  lazymatch goal with
  | |- ?g => lazymatch eval pattern t'0, m'0, l' in g with
             | ?f t'0 m'0 l' =>
               instantiate (1:=fun t m l => (is_prefix focus_pr p') /\ f t m l) in H1
             end
  end.
  cbv beta in H1. tauto.
  *)

  (* transform goal here *)
  lazymatch goal with
  | |- exec ?fs ?body ?t ?m ?l ?P =>
      lazymatch eval pattern sk, p, pr, total_pr, c, R in P with
      | ?f sk p pr total_pr c R =>
          change (exec fs body t m l ((fun (g: word * prefix * prefix * word_map * (mem -> Prop)) (sk: tree_skeleton) =>
     (*let '(s1, s2, p1, p2, R) := g in f s1 s2 p1 p2 R) (s1, s2, p1, p2, R) (len s1)))*)
          let (g, R) := g in
          let (g, c) := g in
          let (g, total_pr) := g in
          let (p, pr) := g in
          f sk p pr total_pr c R) (p, pr, total_pr, c, R) sk))
      end
  end.
  eapply wp_while_tailrec_use_functionpost with (e:=live_expr:(load(p) < cb)).
  { eauto with wf_of_type. }
  { package_heapletwise_context. }
  start_loop_body.
  subst v0.
  repeat heapletwise_step.

  (* we want to progress on the goal with several steps that
  mess up our hypotheses -- so we create a copy of the context by splitting
  the current goal (?C) into (?A) and (?A -> ?C) *)
  eassert (imp: ?[A] -> ?[C]). 2: eapply imp. 2: clear imp. intro.
  apply cbt_fields in H11. step. step. step. step. step. step. step. step.
  apply hide in X.
  step. step. step. step. step. step. step.
  inversion X. eexact X0.

  steps.

  (* in this case (loop condition true), sk must be an internal node *)
  destruct sk; [ exfalso; ZnWords | ].

  pose proof H11 as Hprk'. eapply cbt_key_has_prefix in Hprk'. 2: eassumption.
  simpl cbt' in H11. repeat heapletwise_step.
  .**/
    if (((k >> load(p)) & 1) == 1) /* split */ {                            /**. .**/
      p = load(p + 8);                                                      /**. .**/
    }                                                                       /**.
  new_ghosts (p, pR, append_1 pr, cR,
      <{ * R
         * freeable 12 p'
         * <{ + uintptr /[length pr]
              + uintptr aL
              + uintptr p }> p'
         * cbt' sk1 pL cL aL }>).
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. simpl. step. step. step. step.
  apply is_prefix_key_extend_1. lia.
  eapply clip_prefix_bits_equality with (n1:=length pr) in H9.
  unfold is_prefix_key. unfold full_prefix. unfold is_prefix. simpl.
  rewrite <- H9. unfold is_prefix_key in Hprk'. unfold full_prefix in Hprk'.
  unfold is_prefix in Hprk'. simpl in Hprk'. assumption. step. step. step.
  step. step. step.
  destruct_split H19. subst c. apply map_get_putmany_not_None_iff in H8.
  destruct H8; [ exfalso | assumption ]. eapply cbt_key_has_prefix in H12.
  2: eassumption. eapply is_prefix_key_trans in H12. 4: eassumption.
  eapply clip_prefix_bits_equality in H9.
  rewrite bits_equality_is_prefix_key_iff in H12. 2: eassumption.
  apply append_0_prefix in H12. ZnWords. lia. simpl. lia. lia. simpl. lia. lia.
  step. step. step. step.
  apply H10. destruct_split H19. subst c. apply map_get_putmany_not_None_iff.
  tauto.
  step. step. step. step. unfold state_implication. clear D m.
  step. destruct H18.
  econstructor. eassumption. step. step. step. step. step.
  rewrite H18 in *. change (0 =? 0) with true in HPp1. cbv iota in HPp1.
  simpl cbt'. steps. apply split_du in H19. assumption. step.
  replace (\[retv] =? 0) with false in HPp1; [ | lia ]. step.
  step. step. step. step. step. step. step. step. step. step. step. step.
  replace (\[retv] =? 0) with false in HPp1 by ZnWords.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. 2: instantiate (2:=Node sk1 sk').
  2: simpl cbt'. 2: steps. step. destruct_split H19. subst c.
  unfold map.split. step. apply map_put_putmany_right.
  apply map.disjoint_put_r. apply eq_None_by_false. intro.
  eapply cbt_key_has_prefix in H12. 2: eassumption.
  eapply is_prefix_key_trans in H12. 4: eassumption.
  apply append_0_prefix in H12. ZnWords. lia. simpl. lia. lia. assumption. .**/
    else {                                                                    /**. .**/
      p = load(p + 4);                                                        /**. .**/
    }                                                                         /**.
  new_ghosts (p, pL, append_0 pr, cL,
      <{ * R
         * freeable 12 p'
         * <{ + uintptr /[length pr]
              + uintptr p
              + uintptr aR }> p'
         * cbt' sk2 pR cR aR }>).
  step. steps. simpl. steps. apply is_prefix_key_extend_0. lia.
  eapply clip_prefix_bits_equality with (n1:=length pr) in H9.
  rewrite bits_equality_is_prefix_key_iff. 2: symmetry. 2: eassumption.
  assumption. lia. lia. apply and_1_not_1_0. assumption. destruct_split H19.
  subst c. apply map_get_putmany_not_None_iff in H8. destruct H8;
  [ assumption | exfalso ]. eapply cbt_key_has_prefix in H13. 2: eassumption.
  eapply is_prefix_key_trans in H13. 4: eassumption.
  eapply clip_prefix_bits_equality in H9.
  eapply bits_equality_is_prefix_key_iff in H13. 2: symmetry. 2: eassumption.
  apply append_1_prefix in H13. congruence. lia. simpl. lia. lia. simpl. lia.
  lia. apply H10. destruct_split H19. subst c. apply map_get_putmany_not_None_iff.
  tauto. step. step. step. unfold state_implication. clear D m. step.
  destruct H18. econstructor. eassumption. step. step. step. step. step.
  replace (\[retv] =? 0) with true in * by lia. simpl cbt'. steps.
  apply split_du. assumption. replace (\[retv] =? 0) with false in * by lia.
  step. step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step.
  2: instantiate (2:=Node sk' sk2). 2: simpl cbt'. 2: steps. step.
  destruct_split H19. subst c.
  assert (map.get cR k = None).
  apply eq_None_by_false. intro. eapply cbt_key_has_prefix in H13.
  2: eassumption. eapply is_prefix_key_trans in H13. 4: eassumption.
  eapply append_1_prefix in H13. congruence. lia. simpl. lia. lia.
  unfold map.split. step.
  apply map_put_putmany_left. assumption. apply map.disjoint_put_l. assumption.
  replace (\[retv] =? 0) with false in * by lia. steps. .**/
  }                                                                          /**. .**/
  uintptr_t new_leaf = cbt_alloc_leaf(k, v);                                 /**. .**/
  if (new_leaf == NULL) /* split */ {                                        /**. .**/
    return NULL;                                                             /**.
  change (0 =? 0) with true in H1. cbv iota in H1. .**/
  }                                                                          /**. .**/
  else {                                                                     /**.
  replace (\[new_leaf] =? 0) with false in * by ZnWords. unfold "|=" in H1. .**/
    uintptr_t new_node = malloc(12);                                         /**. .**/
    if (new_node == NULL) /* split */ {                                      /**.
  change (0 =? 0) with true in *. cbv iota in *. .**/
      return NULL;                                                           /**. .**/
    }                                                                        /**. .**/
    else {                                                                   /**.
  replace (\[new_node] =? 0) with false in * by ZnWords. unfold "|=" in H1.
  apply cbt_expose_fields in H11. destruct H13; repeat step. .**/
      store(new_node, load(p));                                              /**. .**/
      store(new_node + 4, load(p + 4));                                      /**. .**/
      store(new_node + 8, load(p + 8));                                      /**. .**/
      store(p, cb);                                                          /**. .**/
      if (((k >> cb) & 1) == 1) /* split */ {                                /**. .**/
        store(p + 4, new_node);                                              /**. .**/
        store(p + 8, new_leaf);                                              /**. .**/
        return tp;                                                           /**. .**/
      }                                                                      /*?.
  step. step. step. step. step. steps. step. step. step. step.
  instantiate (2:=Node sk sk0). step. step. step.
  instantiate (1:={|length:=\[cb]; bits:=prefix_bits \[cb] k|}).
  enough (length total_pr <= \[cb]).
  unfold is_prefix. step. step. step. rewrite clip_prefix_bits.
  unfold is_prefix_key in H6. unfold is_prefix in H6. simpl in H6. step.
  assumption. lia. lia.
  assert (length total_pr <= 32). unfold is_prefix_key in H6.
  unfold full_prefix in H6. unfold is_prefix in H6. simpl in H6. lia.
  assert (Hcmp: length total_pr <= \[cb] \/ \[cb] + 1 <= length total_pr). lia.
  destruct Hcmp; [ assumption | exfalso ].
  apply H10 with k'. assumption.
  apply clip_prefix_bits_equality with (length total_pr). lia. lia.
  apply same_prefix_bits_equality. 2: assumption.
  enough (is_prefix_key pr k'). eapply is_prefix_key_trans in H28. 4: eassumption.
  assumption. lia. destruct sk; unfold "|=" in H18; steps. subst pr. simpl. lia.
  destruct sk; unfold "|=" in H18; steps. subst pr. subst c.
  apply map_get_singleton_not_None in H8. subst w2. apply is_prefix_key_refl.
  destruct_split H35. subst c. rewrite map_get_putmany_not_None_iff in H8.
  destruct H8. eapply cbt_key_has_prefix in H18. 2: eassumption.
  eapply is_prefix_trans. lia. 3: apply is_prefix_append_0. simpl. lia.
  simpl. lia. lia. eapply is_prefix_trans. 4: eassumption. simpl. lia. lia.
  simpl. lia. assumption.
  eapply cbt_key_has_prefix in H29. 2: eassumption.
  eapply is_prefix_trans. lia. 3: apply is_prefix_append_1. simpl. lia.
  simpl. lia. lia. eapply is_prefix_trans. 4: eassumption. simpl. lia. lia.
  simpl. lia. assumption.

  simpl cbt'. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. instantiate (2:=c). instantiate (3:=pr).
  destruct sk; simpl cbt'; unfold "|=" in H18; repeat heapletwise_step.
  step. eassert (Hsepapps:
    <{ + uintptr ?[I1] + uintptr ?[I2] + uintptr ?[I3] }> ?[P] = ?[S]).
  unfold sepapps. simpl. unfold sepapp. reflexivity.
  rewrite Hsepapps. clear Hsepapps. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step.
  unfold is_canonic. unfold canonic_bits. simpl. apply clip_prefix_bits.
  lia. lia. step. step.

  subst c. apply map_get_singleton_not_None in H8. subst w2. subst pr.
  specialize (H10 k').
  subst pr.
  assert (\[cb] + 1 <= length pr).

  unfold append_0. simpl. unfold is_prefix. simpl.
  unfold canonic_bits. simpl.
  step. ste

step. unfold full_prefix in H5. simpl in H5.

  simpl cbt'.
  step. step. step. step. step. step. step. step. step. step. step. step.
  eassert (Hsepapps:
    <{ + uintptr ?[L] + uintptr ?[X] + uintptr ?[X2] }> p = ?[S]).
  unfold sepapps. simpl. unfold sepapp. reflexivity.
  rewrite Hsepapps. clear Hsepapps. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step.
  step.
  admit.


uintptr_t new_leaf = cbt_alloc_leaf(k, v);
if (new_leaf == NULL) return tp;
uintptr_t new_node = malloc(12);
if (new_node == NULL) return tp;
store(new_node, load(p));
store(new_node + 4, load(p + 4));
store(new_node + 8, load(p + 8));
store(p, cb);
if (((k >> cb) & 1) == 1) {
  store(p + 4, new_node);
  store(p + 8, new_leaf);
}
else {
  store(p + 4, new_leaf);
  store(p + 8, new_node);
}
return tp;

}



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
  apply map_singleton_inj in H7. steps. steps. .**/
  else {                                                                   /**.
  destruct H2; cycle 1. step. step. step. contradiction. step. step. .**/
  uintptr_t best_k = cbt_update_or_best(tp, k, v);                         /**.
  unfold enable_frame_trick.enable_frame_trick.
  clear D H3 H1 H0 m m0 m2 m3. steps. .**/
    if (best_k == k) /* split */ {                                         /**.
  subst best_k. destruct H0p4; [ | tauto ]. step. unzify. .**/
      return tp;                                                           /**. .**/
    }                                                                      /**.
  assert (Htp: \[tp] =? 0 = false). step. rewrite Htp. step. step.
  unfold canceling. step. step. step. step. apply or1_seps. left. simpl.
  steps. steps. destruct H0p4; [ exfalso; tauto | ]. .**/
    else {                                                                 /*?.
  fwd. steps. .**/
      uintptr_t p = tp;                                                    /**. .**/
      uintptr_t cb = critical_bit(k, best_k);                              /**.
  instantiate (3:=emp True). steps.
  unfold enable_frame_trick.enable_frame_trick.
  clear m' m0 m2 m3 H1 H3 H4 D. steps.

  (* setting up the loop precondition *)
  (* setting up the loop precondition *)
  rewrite <- Def0 in H5.
  (* delete #(cb = ??). *)
  move t' before tp.
  unfold ready. rewrite <- Def0. rewrite Def0 at 2.
  delete #(p = ??).
  move sk at bottom. (*
  move c after Scope5.
  move R after Scope1.
  move p' after Scope1. *)
  loop invariant above H5.
  remember empty_prefix as focus_pr.
  prove (is_prefix focus_pr p'). subst focus_pr. apply empty_is_prefix.
  apply purify_cbt' in H5. lia.
  delete #(focus_pr = ??).
  move focus_pr after Scope6.
  (*
  eapply exec.weaken; cycle 1. intros.
  lazymatch goal with
  | |- ?g => lazymatch eval pattern t'0, m'0, l' in g with
             | ?f t'0 m'0 l' =>
               instantiate (1:=fun t m l => (is_prefix focus_pr p') /\ f t m l) in H1
             end
  end.
  cbv beta in H1. tauto.
  *)

  (* transform goal here *)
  lazymatch goal with
  | |- exec ?fs ?body ?t ?m ?l ?P =>
      lazymatch eval pattern sk, p, p' (*, focus_pr*), c, R in P with
      | ?f sk p p' (*focus_pr*) c R =>
          change (exec fs body t m l ((fun (g: word * prefix * prefix * word_map * (mem -> Prop)) (sk: tree_skeleton) =>
     (*let '(s1, s2, p1, p2, R) := g in f s1 s2 p1 p2 R) (s1, s2, p1, p2, R) (len s1)))*)
          let (g, R) := g in
          let (g, c) := g in
          let (g, _) := g in
          let (p, p') := g in
          f sk p p' (*focus_pr*) c R) (p, p', focus_pr, c, R) sk))
      end
  end.
  eapply wp_while_tailrec_use_functionpost with (e:=live_expr:(load(p) < cb)).
  { eauto with wf_of_type. }
  { package_heapletwise_context. }
  start_loop_body.
  subst v0.
  rewrite <- Def0 in H5.
  (* delete #(cb = ??). *)
  move t' before tp.
  unfold ready. rewrite <- Def0. rewrite Def0 at 2.
  delete #(p = ??).
  move sk at bottom. (*
  move c after Scope5.
  move R after Scope1.
  move p' after Scope1. *)
  loop invariant above H5.
  remember empty_prefix as focus_pr.
  prove (is_prefix focus_pr p'). subst focus_pr. apply empty_is_prefix.
  apply purify_cbt' in H5. lia.
  delete #(focus_pr = ??).
  move focus_pr after Scope6.
  (*
  eapply exec.weaken; cycle 1. intros.
  lazymatch goal with
  | |- ?g => lazymatch eval pattern t'0, m'0, l' in g with
             | ?f t'0 m'0 l' =>
               instantiate (1:=fun t m l => (is_prefix focus_pr p') /\ f t m l) in H1
             end
  end.
  cbv beta in H1. tauto.
  *)

  (* transform goal here *)
  lazymatch goal with
  | |- exec ?fs ?body ?t ?m ?l ?P =>
      lazymatch eval pattern sk, p, p' (*, focus_pr*), c, R in P with
      | ?f sk p p' (*focus_pr*) c R =>
          change (exec fs body t m l ((fun (g: word * prefix * prefix * word_map * (mem -> Prop)) (sk: tree_skeleton) =>
     (*let '(s1, s2, p1, p2, R) := g in f s1 s2 p1 p2 R) (s1, s2, p1, p2, R) (len s1)))*)
          let (g, R) := g in
          let (g, c) := g in
          let (g, _) := g in
          let (p, p') := g in
          f sk p p' (*focus_pr*) c R) (p, p', focus_pr, c, R) sk))
      end
  end.
  eapply wp_while_tailrec_use_functionpost with (e:=live_expr:(load(p) < cb)).
  { eauto with wf_of_type. }
  { package_heapletwise_context. }
  start_loop_body.
  subst v0.

(* TODO: verify the below implementation; implement critical_bit (a new function)  *)

// ghosts: prefix required for the currently focused tree + the usual ones
while (load(p) < cb) {
// while (load(p) >= 0 && (k & ((1 << load(p)) - 1)) == (block_k & ((1 << load(p)) - 1))) {
  if (((k >> load(p)) & 1) == 1) {
    p = load(p + 8);
  }
  else {
    p = load(p + 4);
  }
}
uintptr_t new_leaf = cbt_alloc_leaf(k, v);
if (new_leaf == NULL) return tp;
uintptr_t new_node = malloc(12);
if (new_node == NULL) return tp;
store(new_node, load(p));
store(new_node + 4, load(p + 4));
store(new_node + 8, load(p + 8));
store(p, cb);
if (((k >> cb) & 1) == 1) {
  store(p + 4, new_node);
  store(p + 8, new_leaf);
}
else {
  store(p + 4, new_leaf);
  store(p + 8, new_node);
}
return tp;

}
Abort.

End LiveVerif. Comments .**/ //.
