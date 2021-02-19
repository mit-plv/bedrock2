From Coq Require Recdef.
Require Import Rupicola.Lib.Api.

Module Type ExitToken_sig.
  Axiom t : Set.
  Axiom new : bool -> t.
  Axiom get : t -> bool.
  Axiom set : t -> t.
End ExitToken_sig.

Module ExitToken <: ExitToken_sig.
  Definition t := bool.
  Definition new (b: bool) : t := b.
  Definition get (tok: t) : bool := tok.
  Definition set (tok: t) : t := true.
  Definition branch {A} (tok: t) (set unset: A) :=
    if tok then set else unset.
End ExitToken.

Open Scope Z_scope.
Open Scope list.

Section Gallina.
  Fixpoint z_range' z0 len :=
    match len with
    | O => []
    | S len => z0 :: z_range' (z0 + 1) len
    end.

  Lemma z_range'_snoc' z0 len :
    forall zs, z_range' z0 (S len) ++ zs =
          z_range' z0 len ++ [z0 + Z.of_nat len] ++ zs.
  Proof.
    induction len in z0 |- *.
    - rewrite Z.add_0_r; reflexivity.
    - remember (S len) as n; intros.
      simpl; rewrite IHlen; rewrite Heqn; cbn -[Z.of_nat].
      replace (z0 + Z.of_nat (S len)) with (z0 + 1 + Z.of_nat len) by lia.
      reflexivity.
  Qed.

  Lemma z_range'_snoc z0 len :
    z_range' z0 (S len) =
    z_range' z0 len ++ [z0 + Z.of_nat len].
  Proof.
    intros; pose proof z_range'_snoc' z0 len [] as H.
    rewrite !app_nil_r in H.
    assumption.
  Qed.

  Lemma z_range'_sound len :
    forall z0 z,
      List.In z (z_range' z0 len) ->
      z0 <= z < z0 + Z.of_nat len.
  Proof.
    induction len; cbn -[Z.of_nat].
    - inversion 1; subst; lia.
    - destruct 1 as [-> | H].
      + lia.
      + specialize (IHlen _ _ H). lia.
  Qed.

  Lemma z_range'_complete len :
    forall z0 z,
      z0 <= z < z0 + Z.of_nat len ->
      List.In z (z_range' z0 len).
  Proof.
    induction len; cbn -[Z.of_nat].
    - lia.
    - intros.
      destruct (Z.eq_dec z0 z);
        [left; eauto | right].
      apply IHlen.
      lia.
  Qed.

  Definition z_range from to :=
    z_range' from (Z.to_nat (to - from)).

  Lemma z_range_sound from to z:
    List.In z (z_range from to) ->
    from - 1 < z < to.
  Proof.
    unfold z_range; intros H%z_range'_sound; lia.
  Qed.

  Lemma z_range_complete from to z:
    from - 1 < z < to ->
    List.In z (z_range from to).
  Proof.
    unfold z_range; intros; apply z_range'_complete; lia.
  Qed.

  Lemma range_unique from to z :
    forall (h h': from - 1 < z < to), h = h'.
  Proof.
    destruct h, h'; f_equal;
      unfold Z.lt in *; eapply @Eqdep_dec.UIP_dec; decide equality.
  Qed.

  Lemma z_range_nil from to:
    from >= to ->
    z_range from to = [].
  Proof.
    intros; unfold z_range.
    replace (Z.to_nat (to - from)) with 0%nat by lia; reflexivity.
  Qed.

  Lemma z_range_cons from to:
    from < to ->
    z_range from to = from :: z_range (from + 1) to.
  Proof.
    unfold z_range; intros.
    replace (Z.to_nat (to - from)) with (S (Z.to_nat (to - (from + 1)))) by lia.
    reflexivity.
  Qed.

  Lemma z_range_snoc from to:
    from < to ->
    z_range from to = z_range from (to - 1) ++ [to - 1].
  Proof.
    unfold z_range; intros.
    replace (Z.to_nat (to - from)) with (S (Z.to_nat (to - (from + 1)))) by lia.
    rewrite z_range'_snoc.
    replace (to - (from + 1)) with (to - 1 - from) by lia.
    replace (from + Z.of_nat (Z.to_nat (to - 1 - from))) with (to - 1) by lia.
    reflexivity.
  Qed.

  Context {A: Type}.

  Section NoBreak.
    Context (from to: Z).
    Context (body: forall (idx: Z) (acc: A), from - 1 < idx < to -> A).

    Lemma iter'0 {idx tl P}:
      (forall z : Z, In z (idx :: tl) -> P z) ->
      (forall z : Z, In z tl -> P z).
    Proof. simpl; eauto. Qed.

    Fixpoint ranged_for_all' indexes :=
      match indexes return (forall z, List.In z indexes -> from - 1 < z < to) -> A -> A with
      | [] => fun _ acc => acc
      | idx :: tl =>
        fun pr acc =>
          let acc := body idx acc (pr _ (or_introl eq_refl)) in
          ranged_for_all' tl (iter'0 pr) acc
      end.

    Definition ranged_for_all :=
      ranged_for_all' (z_range from to) (z_range_sound from to).

    Lemma ranged_for_all_exit a0:
      from >= to -> ranged_for_all a0 = a0.
    Proof.
      unfold ranged_for_all; intros.
      generalize (z_range_sound from to).
      rewrite (z_range_nil from to H).
      reflexivity.
    Qed.
  End NoBreak.

  Section WithBreak.
    Context from to
            (body: forall (idx: Z) (acc: A), from - 1 < idx < to -> A).
    Context (stop: A -> bool).

    Fixpoint ranged_for_break' indexes :=
      match indexes return (forall z, List.In z indexes -> from - 1 < z < to) -> A -> A with
      | [] => fun _ acc => acc
      | idx :: tl =>
        fun pr acc =>
          if stop acc then acc
          else let acc := body idx acc (pr _ (or_introl eq_refl)) in
               ranged_for_break' tl (iter'0 pr) acc
      end.

    Lemma ranged_for_break'_stop_idempotent zs H a0:
      stop a0 = true ->
      ranged_for_break' zs H a0 = a0.
    Proof.
      destruct zs; simpl; intros h; try rewrite h; reflexivity.
    Qed.
  End WithBreak.

  Lemma ranged_for_break'_Proper :
    forall from from' to to' body body' stop stop' zs zs' a0 a0' H H',
      zs = zs' -> a0 = a0' ->
      (forall z a h h', body z a h = body' z a h') ->
      (forall a, stop a = stop' a) ->
      ranged_for_break' from to body stop zs H a0 =
      ranged_for_break' from' to' body' stop' zs' H' a0'.
  Proof.
    induction zs; intros * Hz Ha Hb Hs; subst; simpl in *.
    - reflexivity.
    - rewrite Hs; destruct stop'; try reflexivity.
      apply IHzs; f_equal; eauto.
  Qed.

  Lemma ranged_for_break'_app from to body stop:
    forall zs zs' a0 Hp H H',
      ranged_for_break' from to body stop (zs ++ zs') Hp a0 =
      ranged_for_break' from to body stop zs' H (ranged_for_break' from to body stop zs H' a0).
  Proof.
    induction zs; cbn; intros.
    - apply ranged_for_break'_Proper;
        intros; f_equal; apply range_unique || reflexivity.
    - erewrite IHzs.
      destruct stop eqn:?.
      + rewrite ranged_for_break'_stop_idempotent by assumption.
        reflexivity.
      + repeat f_equal.
        apply range_unique.
  Qed.

  Definition ranged_for_break from to body stop :=
    ranged_for_break' from to body stop (z_range from to) (z_range_sound from to).

  Lemma ranged_for_break_exit from to body stop a0:
    from >= to -> ranged_for_break from to body stop a0 = a0.
  Proof.
    unfold ranged_for_break; intros.
    generalize (z_range_sound from to).
    rewrite (z_range_nil from to H).
    reflexivity.
  Qed.

  Lemma ranged_for_break_Proper :
    forall from from' to to' body body' stop stop' a0 a0',
      a0 = a0' ->
      from = from' -> to = to' ->
      (forall z a h h', body z a h = body' z a h') ->
      (forall a, stop a = stop' a) ->
      ranged_for_break from to body stop a0 =
      ranged_for_break from' to' body' stop' a0'.
  Proof.
    intros; subst; unfold ranged_for_break;
      apply ranged_for_break'_Proper; eauto.
  Qed.

  Section Induction.
    Context (P: A -> Prop) (a0: A).

    Context (from to: Z).
    Context (body: forall (idx: Z) (acc: A), from - 1 < idx < to -> A).
    Context (stop: A -> bool).

    Context (H0: P a0).
    Context (Hbody: forall idx a1 Hle, P a1 -> P (body idx a1 Hle)).

    Lemma ranged_for_break'_ind' :
      forall zs H,
        P (ranged_for_break' from to body stop zs H a0).
    Proof.
      intros.
      revert zs H a0 H0.
      induction zs; cbn; eauto; [].
      intros; destruct (stop _); eauto.
    Qed.

    Lemma ranged_for_break_ind :
      P (ranged_for_break from to body stop a0).
    Proof. eapply ranged_for_break'_ind'. Qed.
  End Induction.
End Gallina.

Lemma ranged_for_break_unfold_l1 {from to}:
  from < to -> from - 1 < from < to.
Proof. lia. Qed.

Lemma ranged_for_break_unfold_l2 {from to z}:
  from + 1 - 1 < z < to -> from - 1 < z < to.
Proof. lia. Qed.

Lemma ranged_for_break_unfold_l {A} from to body stop (a0: A):
  ranged_for_break from to body stop a0 =
  match Z_lt_dec from to with
  | left Hlt =>
    if stop a0 then a0
    else let a0 := body from a0 (ranged_for_break_unfold_l1 Hlt) in
         ranged_for_break
           (from + 1) to
           (fun idx acc pr => body idx acc (ranged_for_break_unfold_l2 pr))
           stop a0
  | right _ => a0
  end.
Proof.
  destruct Z_lt_dec.
  - unfold ranged_for_break.
    generalize (z_range_sound from to) as Hrn.
    generalize (z_range_sound (from + 1) to) as Hrn1.
    rewrite (z_range_cons from to) by assumption.
    intros; simpl; destruct stop.
    + reflexivity.
    + apply ranged_for_break'_Proper;
        intros; f_equal; reflexivity || apply range_unique.
  - apply ranged_for_break_exit; lia.
Qed.

Lemma ranged_for_break_extend1 {from to}:
  forall idx, (from - 1 < idx < to)%Z -> (from - 1 < idx < to + 1)%Z.
Proof. lia. Qed.

Lemma ranged_for_break_unfold_r1 {from}:
  forall idx, (from - 1 < idx)%Z -> (from - 1 < idx < idx + 1)%Z.
Proof. lia. Qed.

Lemma ranged_for_break_unfold_r {A} from to body stop (a0: A) H:
  ranged_for_break from (to + 1) body stop a0 =
  let butlast :=
      ranged_for_break
        from to
        (fun (idx : Z) (acc : A) (pr : (from - 1 < idx < to)%Z) =>
           body idx acc (ranged_for_break_extend1 idx pr))
        stop a0 in
  if stop butlast then butlast
  else body to butlast H.
Proof.
  unfold ranged_for_break.
  generalize (z_range_sound from to) as Hin.
  generalize (z_range_sound from (to + 1)) as Hin1.

  rewrite z_range_snoc by lia. intros.
  erewrite ranged_for_break'_app; simpl.
  set (ranged_for_break' _ _ _ _ _ _ _) as fr.
  set (ranged_for_break' _ _ _ _ _ _ _) as fr1.
  assert (fr = fr1) as Hr.
  { subst fr fr1.
    apply ranged_for_break'_Proper;
      intros; f_equal; (lia || reflexivity || apply range_unique). }
  { rewrite Hr; destruct stop; try reflexivity.
    instantiate (1 := ?[h]).
    generalize (?h (to + 1 - 1) (or_introl eq_refl));
      replace (to + 1 - 1) with to by lia; intros.
    f_equal; apply range_unique. }
  Unshelve.
  { replace (to + 1 - 1) with to by lia.
    intros z ?%Hin; lia. }
  { simpl; destruct 1; lia. }
Qed.

Notation body_pointwise b b' :=
  (forall idx acc pr pr', b idx acc pr = b' idx acc pr').

Lemma ranged_for_break_unfold_r_nstop {A} from to body body1 stop (a0: A) H:
  body_pointwise body body1 ->
  stop (ranged_for_break from to body stop a0) = false ->
  ranged_for_break from (to + 1) body1 stop a0 =
  body1 to (ranged_for_break from to body stop a0) H.
Proof.
  intros Hb Hs.
  unshelve erewrite ranged_for_break_unfold_r; try lia.
  erewrite (ranged_for_break_Proper _ from _ to _ body _ stop _ a0); intros; eauto.
  cbv zeta; unshelve erewrite Hs by lia; f_equal; apply range_unique.
Qed.

Lemma ranged_for_break_monotonic {A} from to body to1 body1 stop (a0: A):
  to1 >= to ->
  body_pointwise body body1 ->
  stop (ranged_for_break from to body stop a0) = true ->
  ranged_for_break from to1 body1 stop a0 =
  ranged_for_break from to body stop a0.
Proof.
  intros Hgt Hb Hs.
  generalize (z_range_sound from to) as Hin.
  generalize (z_range_sound from to1) as Hin1.

  destruct (Z_le_gt_dec to1 from) as [?|Hgt'].
  { intros; rewrite !ranged_for_break_exit by lia; reflexivity. }

  revert body1 Hb;
    replace to1 with (to + Z.of_nat (Z.to_nat (to1 - to))) in * by lia;
    generalize (Z.to_nat (to1 - to)) as n;
    intros.

  induction n; cbn -[Z.of_nat].
  - (* split; [rewrite <- Hs; f_equal|]; *)
    apply ranged_for_break_Proper;
      rewrite ?Z.add_0_r; reflexivity || eauto.
  - revert body1 Hin1 Hb; rewrite Nat2Z.inj_succ;
      unfold Z.succ; rewrite Z.add_assoc; intros.

    destruct (Z_lt_le_dec (from - 1) (to + Z.of_nat n)).

    + unshelve erewrite ranged_for_break_unfold_r; try lia.
      erewrite IHn; cbv zeta; eauto; try rewrite Hs.
      * reflexivity.
      * auto using z_range_sound.
    + rewrite !ranged_for_break_exit;
        reflexivity || lia.
Qed.

Definition ranged_for_widen_bounds {from idx from' to} :
  from - 1 < idx < from' ->
  from' <= to ->
  from - 1 < idx < to.
Proof. lia. Qed.

(* Lemma ranged_for_break_continue_eqn {A} from to step body a0 *)
(*       (H: forall idx, _) H': *)
(*   @ranged_for_break A from (to + step) step body a0  = *)
(*   snd (body (ExitToken.new false) to *)
(*             (ranged_for_break from to step *)
(*                         (fun tok idx acc pr => *)
(*                            body tok idx acc (H idx pr)) *)
(*                         a0) *)
(*             H'). (* (ranged_for_widen_bounds _ _) *) *)
(* Proof. *)
(*   ' *)
(*     unfold ranged_for_break'. apply ranged_for_break'_ind. _ind. *)
(*   intros; unfold ranged_for_break. *)
(*   rewrite ranged_for_break'_equation with (to0 := to). *)
(*   rewrite ranged_for_break'_equation. *)
(*   destruct Z_lt_dec; (reflexivity || lia). *)
(* Qed. *)

Section WithTok.
  Context {A: Type}.

  Section Def.
    Context from to
            (body: forall (tok: ExitToken.t) (idx: Z) (acc: A),
                from - 1 < idx < to -> (ExitToken.t * A))
            (a0: A).

    Definition ranged_for' :=
      ranged_for_break
        from to
        (fun idx acc pr =>
           body (ExitToken.new false) idx (snd acc) pr)
        (fun tok_acc => ExitToken.get (fst tok_acc))
        (ExitToken.new false, a0).

    Definition ranged_for :=
      snd ranged_for'.

    Definition ranged_for_nobreak :=
      snd (ranged_for_all
             from to
             (fun idx acc pr =>
                body (ExitToken.new false) idx (snd acc) pr)
             (ExitToken.new false, a0)).
  End Def.

  Lemma ranged_for'_Proper :
    forall from from' to to' body body' a0 a0',
      a0 = a0' ->
      from = from' -> to = to' ->
      (forall tok z a h h', body tok z a h = body' tok z a h') ->
      ranged_for' from to body a0 =
      ranged_for' from' to' body' a0'.
  Proof.
    unfold ranged_for'; intros.
    apply ranged_for_break_Proper; eauto || congruence.
  Qed.

  Lemma ranged_for'_unfold_r from to body a0 H:
    let wbody tok idx acc pr :=
        body tok idx acc (ranged_for_break_extend1 idx pr) in
    ranged_for' from (to + 1) body a0 =
    let butlast := ranged_for' from to wbody a0 in
    if fst butlast then butlast
    else body (ExitToken.new false) to (snd butlast) H.
  Proof.
    unfold ranged_for'.
    erewrite ranged_for_break_unfold_r.
    reflexivity.
  Qed.

  Lemma ranged_for'_unfold_r_nstop from to body body' a0
        (H: from  - 1 < to < to + 1):
    (forall t, body_pointwise (body t) (body' t)) ->
    fst (ranged_for' from to body a0) = false ->
    ranged_for' from (to + 1) body' a0 =
    body' (ExitToken.new false) to (snd (ranged_for' from to body a0)) H.
  Proof.
    unfold ranged_for'; intros Hb Hc.
    erewrite ranged_for_break_unfold_r_nstop; eauto; cbv beta; eauto.
  Qed.

  Lemma ranged_for'_monotonic from to body a0 to' body':
    to' >= to ->
    (forall t, body_pointwise (body t) (body' t)) ->
    fst (ranged_for' from to body a0) = true ->
    ranged_for' from to' body' a0 =
    ranged_for' from to body a0.
  Proof.
    unfold ranged_for'; intros.
    erewrite ranged_for_break_monotonic; eauto; cbv beta; eauto.
  Qed.
End WithTok.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Context {A: Type}
          (from to: word).

  Section Generic.
    Context {to_Z: word -> Z}
            (to_Z_of_Z: forall l h w,
                to_Z l <= w <= to_Z h ->
                to_Z (word.of_Z w) = w).

    Context (body: forall (tok: ExitToken.t) (idx: word) (acc: A),
                to_Z from - 1 < to_Z idx < to_Z to ->
                (ExitToken.t * A)).

    Lemma ranged_for_w1 {idx}:
      to_Z from - 1 < idx < to_Z to ->
      to_Z from - 1 < to_Z (word.of_Z idx) < to_Z to.
    Proof. intros; erewrite (to_Z_of_Z from to); lia. Qed.

    Definition w_body tok idx acc pr :=
      body tok (word.of_Z idx) acc (ranged_for_w1 pr).

    Definition ranged_for_w (a0: A) : A :=
      ranged_for (to_Z from) (to_Z to) w_body a0.

    Lemma ranged_for_w_exit a0:
      to_Z from >= to_Z to -> ranged_for_w a0 = a0.
    Proof.
      intros; unfold ranged_for_w, ranged_for, ranged_for'.
      rewrite ranged_for_break_exit; eauto.
    Qed.

    Section Induction.
      Context (P: A -> Prop) (a0: A).
      Context (H0: P a0).
      Context (Hbody: forall tok idx a1 Hle, P a1 -> P (snd (body tok idx a1 Hle))).

      Lemma ranged_for_w_ind : P (ranged_for_w a0).
      Proof. unfold ranged_for_w, ranged_for, ranged_for'.
         apply ranged_for_break_ind; simpl; eauto. Qed.
    End Induction.
  End Generic.

  Section Unsigned.
    Lemma word_unsigned_of_Z_bracketed l h w:
      word.unsigned l <= w <= word.unsigned h ->
      word.unsigned (word.of_Z w) = w.
    Proof.
      pose proof word.unsigned_range l.
      pose proof word.unsigned_range h.
      intros; rewrite word.unsigned_of_Z, word.wrap_small; lia.
    Qed.

    Definition ranged_for_u :=
      ranged_for_w word_unsigned_of_Z_bracketed.

    Definition ranged_for_u_ind :=
      ranged_for_w_ind word_unsigned_of_Z_bracketed.
  End Unsigned.

  Section Signed.
    Lemma word_signed_of_Z_bracketed l h w:
      word.signed l <= w <= word.signed h ->
      word.signed (word.of_Z w) = w.
    Proof.
      pose proof word.signed_range l.
      pose proof word.signed_range h.
      intros; rewrite word.signed_of_Z, word.swrap_inrange; lia.
    Qed.

    Definition ranged_for_s :=
      ranged_for_w word_signed_of_Z_bracketed.

    Definition ranged_for_s_ind :=
      ranged_for_w_ind word_signed_of_Z_bracketed.
  End Signed.

  Definition wZ_must_pos (a: Z) :
    match Z_gt_dec a 0, Z_le_dec a (2 ^ 32 - 1) with
    | left _, left _ => word.unsigned (word.of_Z a) > 0
    | _, _ => True
    end.
  Proof.
    destruct Z_le_dec, Z_gt_dec; [ | exact I .. ].
    assert (2 ^ 32 - 1 <= 2 ^ Semantics.width - 1) by
        (destruct Semantics.width_cases as [-> | ->]; lia).
    rewrite word.unsigned_of_Z, word.wrap_small; lia.
  Qed.
End with_parameters.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Section Generic.
    Notation wbody body pr Hr :=
      (fun tok idx acc pr =>
         body tok idx acc (ranged_for_widen_bounds pr Hr)).

    Context (signed: bool).

    Lemma compile_ranged_for A {tr mem locals functions}
          (from to: Z) body (a0: A) :
      let v := ranged_for from to body a0 in
      forall {P} {pred: P v -> predicate}
        (loop_pred: Z -> A -> predicate)
        {k: nlet_eq_k P v} {k_impl} {body_impl}
        (from_var to_var: string) vars,

        let lp from tok_acc tr mem locals :=
            let frm := ExitToken.branch (fst tok_acc) (to - 1) from in
            map.get locals from_var = Some (word.of_Z frm) /\
            loop_pred (frm + 1) (snd tok_acc) tr mem
                      (map.put locals from_var (word.of_Z (frm + 1))) in

        (forall from a0 tr mem locals,
            loop_pred from a0 tr mem locals ->
            map.getmany_of_list locals [from_var; to_var] =
            Some [word.of_Z from; word.of_Z to]) ->

        loop_pred from a0 tr mem locals ->
        from <= to ->
        (if signed then
           - 2 ^ (Semantics.width - 1) <=  from /\ to < 2 ^ (Semantics.width - 1)
         else
           0 <= from /\ to < 2 ^ Semantics.width) ->

        ((* loop body *)
          let lp := lp in
          forall tr mem locals from'
            (Hl: from - 1 < from')
            (Hr: from' < to)
            (Hr': from' <= to),
            let tok := ExitToken.new false in
            let a := ranged_for' from from' (wbody body pr Hr') a0 in
            ExitToken.get (fst a) = false ->
            loop_pred from' (snd a) tr mem locals ->
            (<{ Trace := tr;
                Memory := mem;
                Locals := locals;
                Functions := functions }>
             body_impl
             <{ lp from' (body tok from' (snd a) (conj Hl Hr)) }>)) ->
        (let v := v in
         forall tr mem locals,
           loop_pred to v tr mem locals ->
           (<{ Trace := tr;
               Memory := mem;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.while
             (expr.op (if signed then bopname.lts else bopname.ltu)
                      (expr.var from_var)
                      (expr.var to_var))
             (cmd.seq
                body_impl
                (cmd.set from_var
                         (expr.op bopname.add
                                  (expr.var from_var)
                                  (expr.literal 1)))))
          k_impl
        <{ pred (nlet_eq vars v k) }>.
    Proof.
      intros * Hlocals Hinit Hfromto Hbounds Hbody Hk.
      repeat straightline'.

      pose (inv := (fun n tr mem locals =>
                     exists from' (Hr: from' <= to),
                       from <= from' /\
                       n = Z.to_nat (to - from') /\
                       let a := ranged_for' from from' (wbody body pr Hr) a0 in
                       (from' < to -> ExitToken.get (fst a) = false) /\
                       loop_pred from' (snd a) tr mem locals)).

      red. red.

      eexists nat, lt, inv; split.
      { apply lt_wf. }
      { split.
        { (* Initial invariant *)
          eexists; red.
          exists from.
          exists (ltac:(eauto): from <= to).
          split; try reflexivity.
          split; try reflexivity.
          unfold ranged_for, ranged_for';
            rewrite ranged_for_break_exit by lia.
          eauto. }
        intros niters * Hinv.
        destruct Hinv as (from' & Hl & Hr & -> & Hcontinue & Hpred).
        eexists ?[b]; split; [|split].
        { (* loop test can be eval'd *)
          eexists; split;
            [ eapply (map.getmany_of_list_get _ 0); eauto || reflexivity | ].
          eexists; split;
            [ eapply (map.getmany_of_list_get _ 1); eauto || reflexivity | ].
          [b]: destruct signed.
          destruct signed; simpl.
          - rewrite word.signed_lts, !word.signed_of_Z, !word.swrap_inrange by lia;
              reflexivity.
          - rewrite word.unsigned_ltu, !word.unsigned_of_Z, !word.wrap_small by lia;
              reflexivity. }
        all: intros Hnz; destruct (from' <? to) eqn:Hnz' in Hnz;
          try (destruct signed in *; simpl in Hnz;
               rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1 in Hnz;
               congruence).

        { (* Loop body analysis *)
          apply Z.ltb_lt in Hnz'.
          eapply compile_seq.
          { (* User-supplied loop body *)
            unshelve apply Hbody; cycle -2.
            { unshelve apply Hcontinue; eassumption. }
            { apply Hpred. }
            all: eauto with arith || lia. }
          { (* Variable increment *)
            set (body _ _ _ _) as acc_tok in *.
            set (ExitToken.branch (fst acc_tok) (to - 1) from' + 1) as from'' in *.

            subst lp; cbv beta; intros * (Hfromeq & Hlp).
            eexists; split.
            eexists; split; [exact Hfromeq|].
            eexists; red. red.
            simpl. rewrite <- word.ring_morph_add.
            eexists; split; unfold inv.

            assert (exists h,
                       acc_tok =
                       (ranged_for' from (from' + 1) (wbody body pr h) a0))
              as [? Hrefold].
            { exists (ltac:(lia): from' + 1 <= to).
              subst acc_tok.
              erewrite ranged_for'_unfold_r_nstop with (H := ?[H]).
              [H]: lia.
              f_equal; f_equal; apply range_unique.
              cbv beta; intros; f_equal; apply range_unique.
              erewrite ranged_for'_Proper; [apply Hcontinue|..];
                intros; cbv beta; f_equal; (congruence || lia || apply range_unique). }

            { (* Invariant proof *)
              eexists from''.

              unshelve eexists;
                [subst from''; destruct (fst acc_tok); simpl; lia|].
              split;
                [subst from''; destruct (fst acc_tok); simpl; lia|].

              split; [reflexivity|].

              split.
              { (* If index is < to, loop didn't exit *)
                subst from'';
                  destruct (fst acc_tok) eqn:Htok; simpl in *;
                    [intros; exfalso; lia|].
                intros; rewrite <- Htok, Hrefold by assumption.
                unfold ExitToken.get; f_equal.
                apply ranged_for'_Proper;
                  intros; cbv beta; f_equal; (congruence || lia || apply range_unique). }

              { (* Final invariant holds *)
                set (map.put _ from_var _) as locals' in *.
                subst from'';
                  destruct (fst acc_tok) eqn:Htok; simpl in *;
                    rewrite Hrefold in Hlp.
                { (* Loop exited early *)
                  erewrite ranged_for'_monotonic.
                  replace (to - 1 + 1) with to in * by lia.
                  - eassumption.
                  - lia.
                  - cbv beta; intros; f_equal; apply range_unique.
                  - rewrite <- Hrefold; assumption. }
                { (* Loop did not exit early *)
                  erewrite ranged_for'_Proper;
                  [ eapply Hlp| .. ];
                  intros; cbv beta; f_equal; (congruence || lia || apply range_unique). } } }

            { (* Variant decreased *)
              subst from''. destruct (fst acc_tok); simpl; lia. } } }

        { (* Loop end analysis *)
          apply Z.ltb_ge in Hnz'.
          cbv zeta in Hpred.
          assert (from' = to) as Hend by lia; destruct Hend.
          eapply Hk.
          subst v.
          unfold ranged_for.
          erewrite ranged_for'_Proper;
            [ eapply Hpred| .. ];
            intros; cbv beta; f_equal; (congruence || lia || apply range_unique). } }
    Qed.

    Context {to_Z: word -> Z}
            (of_Z_to_Z: forall w, word.of_Z (to_Z w) = w)
            (to_Z_of_Z: forall l h w,
                to_Z l <= w <= to_Z h ->
                to_Z (word.of_Z w) = w).

    Lemma compile_ranged_for_w A {tr mem locals functions}
          (from to: word)
          (H: if signed then
                - 2 ^ (Semantics.width - 1) <=  to_Z from /\ to_Z to < 2 ^ (Semantics.width - 1)
              else
                0 <= to_Z from /\ to_Z to < 2 ^ Semantics.width)
          body (a0: A) :
      let v := ranged_for_w from to to_Z_of_Z body a0 in
      forall {P} {pred: P v -> predicate}
        (loop_pred: word -> A -> predicate)
        {k: nlet_eq_k P v} {k_impl} {body_impl}
        (from_var to_var: string) vars,

        let lp from tok_acc tr mem locals :=
            let frm := ExitToken.branch (fst tok_acc) (word.sub to (word.of_Z 1)) from in
            map.get locals from_var = Some frm /\
            loop_pred (word.add frm (word.of_Z 1)) (snd tok_acc) tr mem
                      (map.put locals from_var (word.add frm (word.of_Z 1))) in

        (forall from a0 tr mem locals,
            loop_pred from a0 tr mem locals ->
            map.getmany_of_list locals [from_var; to_var] =
            Some [from; to]) ->

        loop_pred from a0 tr mem locals ->
        to_Z from <= to_Z to ->

        ((* loop body *)
          let lp := lp in
          forall tr mem locals from'
            (Hl: to_Z from - 1 < to_Z from')
            (Hr: to_Z from' < to_Z to)
            (Hr': to_Z from' <= to_Z to),
            let tok := ExitToken.new false in
            let a := ranged_for' (to_Z from) (to_Z from')
                                (w_body _ _ to_Z_of_Z
                                        (wbody body pr Hr')) a0 in
            ExitToken.get (fst a) = false ->

            loop_pred from' (snd a) tr mem locals ->
            (<{ Trace := tr;
                Memory := mem;
                Locals := locals;
                Functions := functions }>
             body_impl
             <{ lp from' (body tok from' (snd a) (conj Hl Hr)) }>)) ->
        (let v := v in
         forall tr mem locals,
           loop_pred to v tr mem locals ->
           (<{ Trace := tr;
               Memory := mem;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.while
             (expr.op (if signed then bopname.lts else bopname.ltu)
                      (expr.var from_var)
                      (expr.var to_var))
             (cmd.seq
                body_impl
                (cmd.set from_var
                         (expr.op bopname.add
                                  (expr.var from_var)
                                  (expr.literal 1)))))
          k_impl
        <{ pred (nlet_eq vars v k) }>.
    Proof.
      intros * Hlocals Hinit Hfromto Hbody Hk.
      apply compile_ranged_for
        with (loop_pred := fun z => loop_pred (word.of_Z z)); intros.

      - rewrite of_Z_to_Z. eauto.
      - rewrite of_Z_to_Z; eassumption.
      - eassumption.
      - eassumption.
      - assert (exists h, a = ranged_for' (to_Z from) (to_Z (word.of_Z from')) (w_body from (word.of_Z from') to_Z_of_Z (wbody body pr h)) a0) as [h eqn].
        { unshelve eexists; subst a.
          { rewrite (to_Z_of_Z from to); lia. }
          unshelve apply ranged_for'_Proper; reflexivity || eauto.
          { rewrite (to_Z_of_Z from to); try reflexivity; lia. }
          { unfold w_body; intros; f_equal.
            apply range_unique. } }

        clearbody a; subst a; unfold w_body at 1; cbv beta.
        eapply WeakestPrecondition_weaken; cycle 1.
        + unshelve (apply Hbody; eassumption);
            rewrite (to_Z_of_Z from to); lia.
        + unfold lp, lp0.
          set (ranged_for' _ _ _ _) as fr.

          set (body _ _ _ _) as b0; set (body _ _ _ _) as b1; assert (b0 = b1).
          { subst b0 b1. f_equal. apply range_unique. }
          clearbody b0; subst.

          intros * (Hm & Hlp).
          * destruct (fst b1); simpl in *;
              repeat rewrite ?word.ring_morph_add, ?word.ring_morph_sub, ?of_Z_to_Z;
              eauto.
      - eapply Hk.
        rewrite of_Z_to_Z in H0.
        eassumption.
    Qed.
  End Generic.

  Context {A: Type}
          {tr : Semantics.trace}
          {mem : Semantics.mem}
          {locals : Semantics.locals}
          {functions : list (string * (list string * list string * cmd))}
          (from to : word).

  Let unsigned_bounds:
    0 <= word.unsigned from /\
    word.unsigned to < 2 ^ Semantics.width.
  Proof.
    pose proof word.unsigned_range from;
      pose proof word.unsigned_range to.
    lia.
  Qed.

  Let signed_bounds:
    - 2 ^ (Semantics.width - 1) <= word.signed from /\
    word.signed to < 2 ^ (Semantics.width - 1).
  Proof.
    pose proof word.signed_range from;
      pose proof word.signed_range to.
    lia.
  Qed.

  Definition compile_ranged_for_u :=
    @compile_ranged_for_w false _ word.of_Z_unsigned word_unsigned_of_Z_bracketed
                          A tr mem locals functions from to unsigned_bounds.

  Definition compile_ranged_for_s :=
    @compile_ranged_for_w true _ word.of_Z_signed word_signed_of_Z_bracketed
                          A tr mem locals functions from to signed_bounds.
End with_parameters.

Require Import Rupicola.Lib.Arrays.
Require Import Rupicola.Examples.Cells.Cells.

Section Ex.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Notation "∅" := map.empty.
  Notation "m [[ k ← v ]]" :=
    (map.put m k v)
      (left associativity, at level 11,
       format "m [[ k  ←  v ]]").

  Lemma signed_lt_unsigned w:
    word.signed w <= word.unsigned w.
  Proof.
    pose proof word.unsigned_range w.
    rewrite word.signed_unsigned_dec.
    destruct Z_lt_le_dec; lia.
  Qed.

  Instance HasDefault_word : HasDefault word :=
    word.of_Z 0.

  Program Definition vect_memcpy {n1 n2} (len: word)
          (a1: VectorArray.t word n1)
          (a2: VectorArray.t word n2)
          (pr1: word.unsigned len < Z.of_nat n1)
          (pr2: word.unsigned len < Z.of_nat n2) :=
    let/n from := word.of_Z 0 in
    let/n a2 := ranged_for_u
                 from len
                 (fun tok idx a2 Hlt =>
                    let/n v := VectorArray.get a1 idx _ in
                    let/n a2 := VectorArray.put a2 idx _ v in
                    (tok, a2)) a2 in
    (a1, a2).
  Next Obligation.
    pose proof word.unsigned_range idx.
    pose proof word.unsigned_range len.
    unfold cast, Convertible_word_nat.
    lia.
  Qed.
  Next Obligation.
    pose proof word.unsigned_range idx.
    pose proof word.unsigned_range len.
    unfold cast, Convertible_word_nat.
    lia.
  Qed.

  Instance spec_of_vect_memcpy : spec_of "vect_memcpy" :=
    fnspec! "vect_memcpy" (len: word) (a1_ptr a2_ptr : address) /
          {n1} (a1: VectorArray.t word n1)
          {n2} (a2: VectorArray.t word n2)
          (pr1: word.unsigned len < Z.of_nat n1)
          (pr2: word.unsigned len < Z.of_nat n2)
          R,
    { requires tr mem :=
        (vectorarray_value AccessWord a1_ptr a1 ⋆
                           vectorarray_value AccessWord a2_ptr a2 ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        let res := vect_memcpy len a1 a2 pr1 pr2 in
        (vectorarray_value AccessWord a1_ptr (fst res) ⋆
                           vectorarray_value AccessWord a2_ptr (snd res) ⋆ R) mem' }.

  Derive vect_memcpy_body SuchThat
         (defn! "vect_memcpy"("len", "a1", "a2") { vect_memcpy_body },
          implements @vect_memcpy)
         As vect_memcpy_correct.
  Proof.
    compile_setup.

    repeat compile_step.

    simple apply compile_nlet_as_nlet_eq.
    eapply compile_ranged_for_u
      with (loop_pred := (fun idx a2 tr' mem' locals' =>
                           tr' = tr /\
                           locals' = (∅[["len" ← len]]
                                       [["a1" ← a1_ptr]][["a2" ← a2_ptr]]
                                       [["from" ← idx]]) /\
                           (vectorarray_value AccessWord a1_ptr a1 *
                            vectorarray_value AccessWord a2_ptr a2 * R)%sep mem')).

    all: repeat compile_step; compile_done.
  Qed.

  Program Definition vect_memcpy_s {n1 n2} (len: word)
          (a1: VectorArray.t word n1)
          (a2: VectorArray.t word n2)
          (pr1: word.signed len < Z.of_nat n1)
          (pr2: word.signed len < Z.of_nat n2) :=
    let/n from eq:_ := word.of_Z 0 in
    let/n := word.of_Z 1 in
    let/n a2 := ranged_for_s
                 from len
                 (fun tok idx a2 Hlt =>
                    let/n v := VectorArray.get a1 idx _ in
                    let/n a2 := VectorArray.put a2 idx _ v in
                    (tok, a2)) a2 in
    (a1, a2).
  Next Obligation.
    pose proof word.half_modulus_pos.
    unfold cast, Convertible_word_nat.
    rewrite word.signed_of_Z, word.swrap_inrange in H0 by lia.
    rewrite word.signed_gz_eq_unsigned; lia.
  Qed.
  Next Obligation.
    pose proof word.half_modulus_pos.
    unfold cast, Convertible_word_nat.
    rewrite word.signed_of_Z, word.swrap_inrange in H0 by lia.
    rewrite word.signed_gz_eq_unsigned; lia.
  Qed.


  Instance spec_of_vect_memcpy_s : spec_of "vect_memcpy_s" :=
    fnspec! "vect_memcpy_s" (len: word) (a1_ptr a2_ptr : address) /
          {n1} (a1: VectorArray.t word n1)
          {n2} (a2: VectorArray.t word n2)
          (pr1: word.signed len < Z.of_nat n1)
          (pr2: word.signed len < Z.of_nat n2)
          R,
    { requires tr mem :=
        (vectorarray_value AccessWord a1_ptr a1 ⋆
                           vectorarray_value AccessWord a2_ptr a2 ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        let res := vect_memcpy_s len a1 a2 pr1 pr2 in
        (vectorarray_value AccessWord a1_ptr (fst res) ⋆
                           vectorarray_value AccessWord a2_ptr (snd res) ⋆ R) mem' }.

  Derive vect_memcpy_s_body SuchThat
         (defn! "vect_memcpy_s"("len", "a1", "a2") { vect_memcpy_s_body },
          implements @vect_memcpy_s)
         As vect_memcpy_s_correct.
  Proof.
    compile_setup.

    repeat compile_step.

    simple apply compile_nlet_as_nlet_eq.
    unfold ranged_for_s;
      simple eapply compile_ranged_for_s with (loop_pred := (fun idx a2 tr' mem' locals' =>
                                                              tr' = tr /\
                                                              locals' = (∅[["len" ← len]][["a1" ← a1_ptr]][["a2" ← a2_ptr]]
                                                                          [["from" ← idx]][["step" ← v0]]) /\
                                                              (vectorarray_value AccessWord a1_ptr a1 * vectorarray_value AccessWord a2_ptr a2 * R)%sep mem')).

    all: repeat compile_step; compile_done.
  Qed.

  Definition sizedlist_memcpy (len: word)
             (a1: ListArray.t word)
             (a2: ListArray.t word) :=
    let/n from := word.of_Z 0 in
    let/n := word.of_Z 1 in
    let/n a2 := ranged_for_u
                 from len
                 (fun tok idx a2 Hlt =>
                    let/n v := ListArray.get a1 idx in
                    let/n a2 := ListArray.put a2 idx v in
                    (tok, a2)) a2 in
    (a1, a2).

  Instance spec_of_sizedlist_memcpy : spec_of "sizedlist_memcpy" :=
    fnspec! "sizedlist_memcpy" (len: word) (a1_ptr a2_ptr : address) /
          {n1} (a1: ListArray.t word)
          {n2} (a2: ListArray.t word)
          (pr1: word.unsigned len < Z.of_nat n1)
          (pr2: word.unsigned len < Z.of_nat n2)
          R,
    { requires tr mem :=
        (sizedlistarray_value AccessWord a1_ptr n1 a1 ⋆
                              sizedlistarray_value AccessWord a2_ptr n2 a2 ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        let res := sizedlist_memcpy len a1 a2 in
        (sizedlistarray_value AccessWord a1_ptr n1 (fst res) ⋆
                              sizedlistarray_value AccessWord a2_ptr n2 (snd res) ⋆ R) mem' }.

  Derive sizedlist_memcpy_body SuchThat
         (defn! "sizedlist_memcpy"("len", "a1", "a2") { sizedlist_memcpy_body },
          implements sizedlist_memcpy)
         As sizedlist_memcpy_correct.
  Proof.
    compile_setup.

    repeat compile_step.

    simple apply compile_nlet_as_nlet_eq.
    eapply compile_ranged_for_u with (loop_pred := (fun idx a2 tr' mem' locals' =>
                                                     tr' = tr /\
                                                     locals' = (∅[["len" ← len]][["a1" ← a1_ptr]][["a2" ← a2_ptr]]
                                                                 [["from" ← idx]][["step" ← word.of_Z 1]]) /\
                                                     (sizedlistarray_value AccessWord a1_ptr n1 a1 *
                                                      sizedlistarray_value AccessWord a2_ptr n2 a2 * R)%sep mem')).

    all: repeat compile_step; try lia; compile_done.
  Qed.

  Definition unsizedlist_memcpy (len: word)
             (a1: ListArray.t word)
             (a2: ListArray.t word) :=
    let/n from := word.of_Z 0 in
    let/n := word.of_Z 1 in
    let/n a2 := ranged_for_u
                 from len
                 (fun tok idx a2 Hlt =>
                    let/n v := ListArray.get a1 idx in
                    let/n a2 := ListArray.put a2 idx v in
                    (tok, a2)) a2 in
    (a1, a2).

  Instance spec_of_unsizedlist_memcpy : spec_of "unsizedlist_memcpy" :=
    fnspec! "unsizedlist_memcpy" (len: word) (a1_ptr a2_ptr : address) /
          (a1: ListArray.t word) (a2: ListArray.t word)
          (pr1: word.unsigned len < Z.of_nat (List.length a1))
          (pr2: word.unsigned len < Z.of_nat (List.length a2))
          R,
    { requires tr mem :=
        (listarray_value AccessWord a1_ptr a1 ⋆
                         listarray_value AccessWord a2_ptr a2 ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        let res := unsizedlist_memcpy len a1 a2 in
        (listarray_value AccessWord a1_ptr (fst res) ⋆
                         listarray_value AccessWord a2_ptr (snd res) ⋆ R) mem' }.

  Derive unsizedlist_memcpy_body SuchThat
         (defn! "unsizedlist_memcpy"("len", "a1", "a2") { unsizedlist_memcpy_body },
          implements unsizedlist_memcpy)
         As unsizedlist_memcpy_correct.
  Proof.
    compile_setup.

    repeat compile_step.

    simple apply compile_nlet_as_nlet_eq.
    eapply compile_ranged_for_u with (loop_pred := (fun idx a2 tr' mem' locals' =>
                                                     tr' = tr /\
                                                     locals' = (∅[["len" ← len]][["a1" ← a1_ptr]][["a2" ← a2_ptr]]
                                                                 [["from" ← idx]][["step" ← word.of_Z 1]]) /\
                                                     (listarray_value AccessWord a1_ptr a1 *
                                                      listarray_value AccessWord a2_ptr a2 * R)%sep mem')).

    (*  FIXME remove previous hints *)
    (* Import UnsizedListArrayCompiler. *)
    Hint Extern 1 => simple eapply @compile_word_unsizedlistarray_get; shelve : compiler.
    Hint Extern 1 => simple eapply @compile_word_unsizedlistarray_put; shelve : compiler.

    all: repeat compile_step; compile_done; unfold id.

    { lia. (* loop index in bounds + function precondition *) }
    { (* Note the call to induction.
          Without vectors or the sizedlist predicate, we need to check that the index is in bounds but we modified the array.
          Using a vector type instead keeps the inranged_for in the type and the statement of put specifies that the length is preserved.
          Putting that info in the representation predicates has a similar effect.
          Without this, we need to perranged_for induction explicitly. *)
      subst a.
      apply ranged_for_u_ind.
      - lia.
      - intros; unfold nlet; cbn.
        rewrite ListArray.put_length.
        assumption. }
  Qed.

  Program Definition incr_gallina (c: cell) : cell :=
    let/n one := word.of_Z 1 in
    let/n from := word.of_Z 3 in
    let/n to := word.of_Z 5 in
    let/n := word.of_Z 1 in
    let/n tick := word.of_Z 0 in
    let/n (tick, c) :=
       ranged_for_u (A := word * cell)
                    from to
                    (fun tok idx acc bounded =>
                       let '(tick, c) := acc in
                       let/n v := get c in
                       let/n v := word.add v idx in
                       let/n c := put v c in
                       let/n tick := word.add tick one in
                       (tok, (tick, c)))
                    (tick, c) : word * cell in
    (let/n v := get c in
     let/n v := word.add v tick in
     let/n c := put v c in
     c).

  Instance spec_of_incr : spec_of "incr" :=
    fnspec! "incr" c_ptr / (c: cell) R,
    { requires tr mem :=
        (cell_value c_ptr c ⋆ R) mem;
      ensures tr' mem' :=
        tr' = tr /\
        (cell_value c_ptr (incr_gallina c) ⋆ R) mem' }.

  Derive incr_body SuchThat
         (defn! "incr"("c") { incr_body },
          implements incr_gallina)
         As body_correct.
  Proof.
    compile_setup.

    repeat compile_step.

    simple apply compile_nlet_as_nlet_eq.
    eapply compile_ranged_for_u with (loop_pred := (fun idx acc tr' mem' locals' =>
                                                     let '(tick, c) := acc in
                                                     tr' = tr /\
                                                     (* locals' = map.put locals "tick" tick /\ *)
                                                     locals' = (∅[["c" ← c_ptr]][["one" ← v]]
                                                                 [["from" ← idx]][["to" ← v1]][["step" ← v2]]
                                                                 [["tick" ← tick]]) /\
                                                     (cell_value c_ptr c * R)%sep mem')).

    all: repeat compile_step; compile_done.
  Qed.
End Ex.

(* Require Import bedrock2.NotationsCustomEntry. *)
(* Require Import bedrock2.NotationsInConstr. *)
(* Eval cbv [sizedlist_memcpy_body unsizedlist_memcpy_body vect_memcpy_s_body fold_right noskips is_skip] in sizedlist_memcpy_body. *)

Require bedrock2.BasicC64Semantics.

Module test.
  Import BasicC64Semantics.

  Time Compute (ranged_for 0 15 3
                        (fun t idx acc _ =>
                           if Z.ltb 11 idx then
                             let t' := ExitToken.set t in
                             (t', acc)
                           else
                             let acc := idx :: acc in
                             (t, acc)) []).

  Time Compute (ranged_for_u (word.of_Z 0) (word.of_Z 15) (word.of_Z 3)
                          (fun t idx acc _ =>
                             if word.ltu (word.of_Z 11) idx then
                               let t' := ExitToken.set t in
                               (t', acc)
                             else
                               let acc := idx :: acc in
                               (t, acc)) []).
End test.
