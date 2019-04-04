From Coq Require Import Strings.String Lists.List ZArith.BinInt.
From bedrock2 Require Import BasicC64Semantics ProgramLogic.
Require Import coqutil.Z.Lia.

Require Import bedrock2.Examples.ARPResponder.

Import Datatypes List ListNotations.
Local Open Scope string_scope. Local Open Scope list_scope. Local Open Scope Z_scope.
Require Import bedrock2.NotationsInConstr.
From coqutil.Word Require Import Interface.

From bedrock2 Require Import Array Scalars Separation.
From coqutil.Tactics Require Import letexists rdelta.
Local Notation bytes := (array scalar8 (word.of_Z 1)).

Lemma word__if_zero (t:bool) (H : word.unsigned (if t then word.of_Z 1 else word.of_Z 0) = 0) : t = false. Admitted.
Lemma word__if_nonzero (t:bool) (H : word.unsigned (if t then word.of_Z 1 else word.of_Z 0) <> 0) : t = true. Admitted.

Set Printing Width 90.
Ltac seplog_use_array_load1 H i :=
  let iNat := eval cbv in (Z.to_nat i) in
  unshelve SeparationLogic.seprewrite_in @array_index_nat_inbounds H;
    [exact iNat|exact (word.of_Z 0)|blia|];
  change ((word.unsigned (word.of_Z 1) * Z.of_nat iNat)%Z) with i in *.

Local Instance spec_of_arp : spec_of "arp" := fun functions =>
  forall t m packet ethbuf len R,
    (sep (array scalar8 (word.of_Z 1) ethbuf packet) R) m ->
    word.unsigned len = Z.of_nat (length packet) ->
  WeakestPrecondition.call functions "arp" t m [ethbuf; len] (fun T M rets => True).
Goal program_logic_goal_for_function! arp.
  repeat straightline.
  letexists; split; [solve[repeat straightline]|]; split; [|solve[repeat straightline]]; repeat straightline.
  eapply word__if_nonzero in H1.
  rewrite word.unsigned_ltu, word.unsigned_of_Z, Z.mod_small in H1 by admit.
  eapply Z.ltb_lt in H1.
  repeat (letexists || straightline).
  split.
  1: repeat (split || letexists || straightline).
  Ltac tload :=
  lazymatch goal with |- Memory.load Syntax.access_size.one ?m (word.add ?base (word.of_Z ?i)) = Some ?v =>
  lazymatch goal with H: _ m |- _ =>
    let iNat := eval cbv in (Z.to_nat i) in
    SeparationLogic.seprewrite_in @array_index_nat_inbounds H;
    [instantiate (1 := iNat); blia|instantiate (1 := word.of_Z 0) in H];
    eapply load_one_of_sep;
    change (word.of_Z (word.unsigned (word.of_Z 1) * Z.of_nat iNat)) with (word.of_Z i) in *;
    SeparationLogic.ecancel_assumption
  end end.

  all:try tload.
  1: subst v0; exact eq_refl.
  split; [|solve[repeat straightline]]; repeat straightline.

  letexists; split; [|split; [|solve[repeat straightline]]].
  1: solve [repeat (split || letexists || straightline || tload)].

  repeat straightline.

  lazymatch goal with |- WeakestPrecondition.store Syntax.access_size.one ?m ?a ?v ?post =>
  lazymatch goal with H: _ m |- _ =>
    let av := rdelta a in
    let i := lazymatch av with word.add ?base (word.of_Z ?i) => i end in
    let iNat := eval cbv in (Z.to_nat i) in
    pose i;
    SeparationLogic.seprewrite_in @array_index_nat_inbounds H;
    [instantiate (1 := iNat); blia|instantiate (1 := word.of_Z 0) in H];
    eapply store_one_of_sep;
    change (word.of_Z (word.unsigned (word.of_Z 1) * Z.of_nat iNat)) with (word.of_Z i) in *;
    [SeparationLogic.ecancel_assumption|]
  end end.

  straightline.
  straightline.
  straightline.
  straightline.
  straightline.
  straightline.

  assert (length_firstn_inbounds : forall {T} n (xs : list T), le n (length xs) -> length (firstn n xs) = n). {
    intros.
    rewrite firstn_length, PeanoNat.Nat.min_comm.
    destruct (Min.min_spec (length xs) n); blia.
  }

  unshelve erewrite (_:a = word.add ethbuf (word.of_Z (Z.of_nat (length (firstn 21 packet))))) in H4. {
    rewrite length_firstn_inbounds by blia.
    trivial. }

  assert (array_snoc : forall {T} rep size a vsa b (vb:T)
                              (H:b = word.add a (word.of_Z (word.unsigned size * Z.of_nat (length vsa)) )),
             Lift1Prop.iff1 (sep (array rep size a vsa) (rep b vb)) (array rep size a (vsa ++ cons vb nil))). {
    clear. intros. subst b.
    etransitivity; [|symmetry; eapply Array.array_append].
    cbn [array]; SeparationLogic.cancel. }
  SeparationLogic.seprewrite_in @array_snoc H4.
  { change (word.unsigned (word.of_Z 1)) with 1; rewrite Z.mul_1_l; trivial. }

  assert (array_append_merge : forall {T} rep size start (xs ys : list T) start' (H: start' = (word.add start (word.of_Z (word.unsigned size * Z.of_nat (length xs))))),
            Lift1Prop.iff1 (sep (array rep size start xs) (array rep size start' ys)) (array rep size start (xs ++ ys))). {
    clear; intros; subst start'; symmetry; eapply array_append. }
  SeparationLogic.seprewrite_in @array_append_merge H4. {
    change (word.unsigned (word.of_Z 1)) with 1; rewrite Z.mul_1_l.
    rewrite app_length; cbn [length].
    rewrite length_firstn_inbounds by blia.
    change (Z.of_nat (21 + 1)) with 22.
    admit. (* wring *) }
  move H4 at bottom.

  letexists; split.
  1: {
    repeat (split || letexists || straightline).

    lazymatch goal with |- Memory.load Syntax.access_size.one ?m (word.add ?base (word.of_Z ?i)) = Some ?v =>
    lazymatch goal with H: _ m |- _ =>
      let iNat := eval cbv in (Z.to_nat i) in
      SeparationLogic.seprewrite_in @array_index_nat_inbounds H;
      [instantiate (1 := iNat) |instantiate (1 := word.of_Z 0) in H;
      eapply load_one_of_sep;
      change (word.of_Z (word.unsigned (word.of_Z 1) * Z.of_nat iNat)) with (word.of_Z i) in *;
      SeparationLogic.ecancel_assumption ]
    end end.

    repeat rewrite ?app_length, ?length_firstn_inbounds by blia; cbn [length].
    assert (length_skipn_inbounds : forall {T} n (xs : list T), le n (length xs) -> length (skipn n xs) = (length xs - n)%nat). {
      clear -length_firstn_inbounds. intros.
      pose proof firstn_skipn n xs as HH; eapply (f_equal (@length _)) in HH; rewrite <-HH.
      rewrite app_length, length_firstn_inbounds; blia.
    }

    assert (length_tl_inbounds : forall {T} xs (H : le 1 (length xs)), length (@tl T xs) = (length xs - 1)%nat). {
      destruct xs; cbn [length tl]; blia.
    }

    rewrite length_tl_inbounds by (rewrite ?length_skipn_inbounds; blia).
    rewrite length_skipn_inbounds by blia.
    blia.
  }

  assert (skipn_app : forall n {T} (xs ys : list T), skipn n (xs ++ ys) = skipn n xs ++ skipn (n - length xs) ys). {
    (* reduce to UF_LIA *) admit. }
  remember (word.of_Z
          (word.unsigned
             (hd (word.of_Z 0)
                (skipn 22
                   ((firstn 21 packet ++ [word.of_Z (word.unsigned v2)]) ++
                    tl (skipn 21 packet)))))) as w.
  assert (skipn_all_exact : forall {T} (xs : list T), skipn (length xs) xs = nil). {
    clear; intros. induction xs; eauto. }
  assert (skipn_all : forall n {T} (xs : list T), le (length xs) n -> skipn n xs = nil). {
    admit. }
  rewrite !skipn_app in Heqw.
  rewrite skipn_all in Heqw by (rewrite length_firstn_inbounds ; blia).
  cbn [app] in Heqw.
  replace ((22 - length (firstn 21 packet ++ [word.of_Z (word.unsigned v2)]))%nat) with 0%nat in Heqw. 2: {
    rewrite app_length; cbn [length]; rewrite length_firstn_inbounds; blia.
  }
  assert (skipn_0_l : forall {T} (xs : list T), skipn 0 xs = xs).
  { reflexivity. }
  rewrite skipn_0_l in *.

  assert (tl_is_skipn1 : forall {T} (xs : list T), tl xs = skipn 1 xs). {
    destruct xs; reflexivity. }
  rewrite tl_is_skipn1 in Heqw.

  assert (skipn_skipn : forall n m {T} (xs : list T), skipn n (skipn m xs) = skipn (n + m) xs). {
    admit. }

  rewrite skipn_skipn in Heqw.
  change (1+21)%nat with 22%nat in *.
  subst w.
  subst v3.
  rewrite tl_is_skipn1 in *.
  rewrite skipn_skipn in H4.
  change (1+21)%nat with 22%nat in *.
  rewrite <-app_assoc in H4.

  assert (length_skipn_inbounds : forall {T} n (xs : list T), le n (length xs) -> length (skipn n xs) = (length xs - n)%nat). {
    clear -length_firstn_inbounds; intros.
    rewrite <-(firstn_skipn n xs) at 2.
    rewrite app_length.
    rewrite length_firstn_inbounds; blia.
  }

  assert (length ((firstn 21 packet ++ [word.of_Z (word.unsigned v2)] ++ skipn 22 packet)) = length packet). {
    rewrite ?app_length, ?length_firstn_inbounds, ?length_skipn_inbounds by blia.
    cbn [length]; blia.
  }

  lazymatch goal with |- WeakestPrecondition.store Syntax.access_size.one ?m ?a ?v ?post =>
  lazymatch goal with H: _ m |- _ =>
    let av := rdelta a in
    let i := lazymatch av with word.add ?base (word.of_Z ?i) => i end in
    let iNat := eval cbv in (Z.to_nat i) in
    pose i;
    let HH := fresh H in pose proof H as HH;
    SeparationLogic.seprewrite_in @array_index_nat_inbounds HH;
    [instantiate (1 := iNat); blia|instantiate (1 := word.of_Z 0) in HH];
    eapply store_one_of_sep;
    change (word.of_Z (word.unsigned (word.of_Z 1) * Z.of_nat iNat)) with (word.of_Z i) in *;
    [SeparationLogic.ecancel_assumption|]; clear HH
  end end.

  repeat straightline.

  rewrite ?firstn_app in H6.
  replace (firstn 32 (firstn 21 packet)) with (firstn 21 packet) in H6; cycle 1. {
    Fail rewrite (@firstn_all2 _ _) by (rewrite length_firstn_inbounds; blia).
    rewrite (@firstn_all2 _ 32) by (rewrite length_firstn_inbounds; blia).
    trivial.
  }
  Notation "a [ i ]" := (hd _ (skipn i a)) (at level 10, left associativity, format "a [ i ]").
  Notation "a [: i ]" := (firstn i a) (at level 10, left associativity, format "a [: i ]").
  Notation "a [ i :]" := (skipn i a) (at level 10, left associativity, format "a [ i :]").

  match type of H6 with
         | context [firstn ?n [?x]] => rewrite (@firstn_all2 _ n [x]) in H6
         end.
  2: cbn [length]; rewrite length_firstn_inbounds; blia.
  cbn [length] in H6.
  rewrite length_firstn_inbounds in H6 by blia.
  change (32 - 21 - 1)%nat with 10%nat in H6.

  rewrite !skipn_app in H6.

  rewrite (skipn_all 32%nat _ (firstn 21%nat _)) in H6 by (rewrite !length_firstn_inbounds ; blia).
  cbn [app] in H6.
  change (22 - 21)%nat with 1%nat in *.

  rewrite skipn_all in H6 by trivial.
  cbn [app] in H6.

  rewrite tl_is_skipn1 in H6.
  rewrite !skipn_app in H6.
  rewrite !length_firstn_inbounds in H6 by blia.
  rewrite !skipn_skipn in H6.
  change (1 + (32 - 21))%nat with 12%nat in H6.
  rewrite (skipn_all 12%nat) in H6 by (cbn [length]; blia).
  cbn [app length] in H6.

  rewrite (skipn_all (S _ - S _)%nat) in H6 by (cbn; blia).
  cbn [length] in *.

  change (1 - 0 + (32 - 21 - 1) + 22)%nat with 33%nat in H6.

  SeparationLogic.seprewrite_in @array_snoc H6. {
    rewrite app_length, length_firstn_inbounds by blia.
    cbn [length].
    rewrite length_firstn_inbounds by (rewrite length_skipn_inbounds ; blia).
    eapply f_equal.
    eapply f_equal.
    cbv.
    trivial.
  }

  repeat rewrite <-?app_assoc, <-?app_comm_cons in H6.

  assert (length_cons : forall {T} x xs, length (@cons T x xs) = S (length xs)). { reflexivity. }

  SeparationLogic.seprewrite_in @array_append_merge H6. {
    repeat rewrite ?length_cons, ?app_length, ?length_firstn_inbounds, ?length_skipn_inbounds by blia.
    repeat rewrite ?length_cons, ?app_length, ?length_firstn_inbounds, ?length_skipn_inbounds; [|blia..].
    replace (word.add (word.add ethbuf (word.of_Z 32)) (word.of_Z 1))
            with (word.add ethbuf (word.add (word.of_Z 32) (word.of_Z 1))) by admit.
    eapply f_equal; exact eq_refl. }

  repeat rewrite ?app_nil_l, <-?app_assoc, <-?app_comm_cons in H6.
Abort.
