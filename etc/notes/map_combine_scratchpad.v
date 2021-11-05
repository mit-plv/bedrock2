Require Import Rupicola.Lib.Loops.
Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Lib.Api. (* FIXME *)

Section Blargh.
  Context {A B: Type}.

  Open Scope Z_scope.

  Context from to
          (body: forall (acc: A) (tok: ExitToken.t) (idx: Z),
              from - 1 < idx < to ->
              (ExitToken.t * (ListArray.t A * ListArray.t  B)))
          (a0: (ListArray.t A * ListArray.t  B)).

  Context `{HasDefault A} `{HasDefault B}.
  Instance: HasDefault (A * B) := (default, default).


  Instance Convertible_Z_nat : Convertible Z nat := Z.to_nat.

  Lemma ranged_for_combine: forall n (lA: list A) (lB: list B) fA fB,
      (n <= length lA)%nat ->
      (n <= length lB)%nat ->
      length lA = length lB ->
    ranged_for_all
      0%Z (Z.of_nat n)
      (fun ab idx (H: _) => let '(a, b) := ab in
         let/d xa := ListArray.get a idx in
         let/d xb := ListArray.get b idx in
         let/d ya := fA xa xb in
         let/d yb := fB xa xb in
         let/d a := ListArray.put a idx ya in
         let/d b := ListArray.put b idx yb in
         (a, b))
      (lA, lB) =
    List.split
      (ranged_for_all
         0 (Z.of_nat n)
         (fun ab idx (H: _) =>
            let/d ab := ab in
            let/d xab := ListArray.get ab idx in
            let/d yab := (fA (fst xab) (snd xab), fB (fst xab) (snd xab)) in
            let/d ab := ListArray.put ab idx yab in
            ab)
         (combine lA lB)).
  Proof.
    induction n; simpl; intros.
    - rewrite !ranged_for_all_exit by lia.
      admit.
    - unfold ranged_for_all.
      replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
      erewrite !ranged_for_break_unfold_r_nstop.
      all: try reflexivity.
      all: try lia.
      unfold ranged_for_all in IHn.
      rewrite IHn by lia.
      set (ranged_for_break _ _ _ _ _).
      rewrite (surjective_pairing (split y)).
      pose proof split_nth y n default as Hfst.
      pose proof split_nth y n default as Hsnd.
      apply (f_equal fst) in Hfst.
      apply (f_equal snd) in Hsnd.
      simpl in Hfst, Hsnd.
      unfold ListArray.get, ListArray.put.
      unfold cast, Convertible_Z_nat.
      rewrite !Nat2Z.id.
      rewrite <- Hfst, <- Hsnd.
      unfold dlet.


      unfold dlet.
      
      2: {

      | rewrite <- IHn ].

        intros; destruct acc.
    induction lA; destruct lB; inversion 1; simpl.
    - admit.
    - unfold ranged_for_all in *.

      erewrite ranged_for_break_unfold_l.
      unfold ranged_for_break in *.


      
  .
  ranged_for
