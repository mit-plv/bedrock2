Require Coq.Vectors.Vector.
Require Import Arith PeanoNat.
Require Import Coq.Program.Wf.
Require Import Coq.Setoids.Setoid.
Require Import Coq.derive.Derive.
Require Import Coq.funind.Recdef.
Require Import Coq.micromega.Psatz.

Require coqutil.Map.SortedListString.

Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.Cells.Cells.

(* (* Set Primitive Projections. *) *)
(* Record p2 {A B} := P2 { pfst: A; psnd: B }. *)
(* (* Unset Primitive Projections. *) *)
(* Arguments P2 {A B} pfst psnd: assert. *)
(* Arguments p2: clear implicits. *)

Lemma extends_refl {p o} {map: map.map p o} m:
  map.extends m m.
Proof. firstorder. Qed.

Lemma extends_eq {p o} {map: map.map p o} m1 m2:
  m1 = m2 ->
  map.extends m1 m2.
Proof. intros * ->; apply extends_refl. Qed.

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

Class HasDefault (T: Type) := default: T.

Class Convertible (T1 T2: Type) := cast: T1 -> T2.

Fixpoint replace_nth {A} (n: nat) (l: list A) (a: A) {struct l} :=
  match l, n with
  | [], _ => []
  | _ :: t, 0 => a :: t
  | h :: t, S n => h :: replace_nth n t a
  end.

Lemma nth_replace_nth {A}:
  forall (xs: list A) idx idx' d v,
    idx' = idx ->
    idx < List.length xs ->
    nth idx' (replace_nth idx xs v) d = v.
Proof.
  intros; subst; revert dependent idx; revert dependent xs.
  induction xs; cbn; intros idx Hlt.
  - inversion Hlt.
  - destruct idx; simpl.
    + reflexivity.
    + apply IHxs; auto with arith.
Qed.

Lemma replace_nth_length {A}:
  forall (l: list A) n a,
    List.length (replace_nth n l a) = List.length l.
Proof.
  induction l; cbn; intros.
  - reflexivity.
  - destruct n; simpl; rewrite ?IHl; try reflexivity.
Qed.

Lemma Vector_to_list_length {T n}:
  forall (v: Vector.t T n),
    List.length (Vector.to_list v) = n.
Proof.
  induction v; cbn.
  - reflexivity.
  - f_equal; assumption.
Qed.

Lemma Vector_nth_hd_skipn {T n}:
  forall (f: Fin.t n) idx (v : Vector.t T n) (t0 : T),
    idx = proj1_sig (Fin.to_nat f) ->
    Vector.nth v f = List.hd t0 (List.skipn idx (Vector.to_list v)).
Proof.
  induction f; cbn; intros; rewrite (Vector.eta v).
  - subst; reflexivity.
  - subst; destruct (Fin.to_nat f); cbn.
    erewrite IHf; reflexivity.
Qed.

Lemma Vector_to_list_app {A n1 n2} :
  forall v1 v2,
    Vector.to_list (@Vector.append A n1 n2 v1 v2) =
    List.app (Vector.to_list v1) (Vector.to_list v2).
Proof.
  induction v1; cbn; intros.
  - reflexivity.
  - f_equal. apply IHv1.
Qed.

Open Scope list_scope.

Lemma List_firstn_app_l {A} :
  forall (l1 l2: list A) n,
    n = List.length l1 ->
    List.firstn n (l1 ++ l2) = l1.
Proof.
  intros; subst.
  rewrite List.firstn_app, List.firstn_all, Nat.sub_diag; simpl.
  rewrite app_nil_r; reflexivity.
Qed.

Lemma List_firstn_app_l2 {A} :
  forall (l1 l2: list A) n k,
    n = List.length l1 ->
    (List.firstn (n + k) (l1 ++ l2) = l1 ++ (List.firstn k l2)).
Proof.
  intros; subst.
  rewrite List.firstn_app, List.firstn_all2, minus_plus; simpl; (reflexivity || lia).
Qed.

Lemma List_skipn_app_r {A} :
  forall (l1 l2: list A) n,
    n = List.length l1 ->
    List.skipn n (l1 ++ l2) = l2.
Proof.
  intros; subst.
  rewrite List.skipn_app, List.skipn_all, Nat.sub_diag; simpl; reflexivity.
Qed.

Lemma List_skipn_app_r2 {A} :
  forall (l1 l2: list A) n k,
    n = List.length l1 ->
    List.skipn (n + k) (l1 ++ l2) =
    List.skipn k l2.
Proof.
  intros; subst.
  rewrite List.skipn_app, List.skipn_all, minus_plus; simpl; (reflexivity || lia).
Qed.

Lemma Vector_to_list_replace {A n}:
  forall (a: Vector.t A n) (idx: nat) (f: Fin.t n) v,
    idx = proj1_sig (Fin.to_nat f) ->
    Vector.to_list (Vector.replace a f v) =
    replace_nth idx (Vector.to_list a) v.
Proof.
  intros; subst; induction f; cbn; intros; rewrite (Vector.eta a).
  - reflexivity.
  - destruct (Fin.to_nat f); cbn in *.
    f_equal; apply IHf.
Qed.

Lemma replace_nth_eqn {A} :
  forall (xs: list A) idx x,
    idx < List.length xs ->
    replace_nth idx xs x =
    List.firstn idx xs ++ x :: List.skipn (S idx) xs.
Proof.
  induction xs; cbn; intros idx x Hlt.
  - inversion Hlt.
  - destruct idx.
    + reflexivity.
    + cbn [List.firstn List.app].
      f_equal; apply IHxs.
      auto with arith.
Qed.

Lemma Vector_nth_replace {T n}:
  forall (idx: Fin.t n) (v: Vector.t T n) (val: T),
    Vector.nth (Vector.replace v idx val) idx = val.
Proof.
  induction idx; intros; rewrite (Vector.eta v); cbn; try rewrite IHidx; reflexivity.
Qed.

Module VectorArray.
  Section VectorArray.
    Context {K V: Type}.
    Context {Conv: Convertible K nat}.

    Definition t n := Vector.t V n.
    Definition get {n} (a: t n) (k: K) (pr: cast k < n) : V :=
      Vector.nth_order a pr.
    Definition put {n} (a: t n) (k: K) (pr: cast k < n) (v: V) : t n :=
      Vector.replace_order a pr v.
    (* FIXME needs an accessor that generates a test and returns a default *)
  End VectorArray.

  Arguments t : clear implicits.
End VectorArray.

Module ListArray.
  Section ListArray.
    Context {K V: Type}.
    Context {HD: HasDefault V}.
    Context {Conv: Convertible K nat}.

    Definition t := list V.
    Definition get (a: t) (k: K) : V :=
      List.nth (cast k) a default.
    Definition put (a: t) (k: K) (v: V) : t :=
      replace_nth (cast k) a v.
    (* FIXME needs an accessor that generates a test and returns a default *)

    Lemma put_length (a: t) (k: K) (v: V) :
      List.length (put a k v) = List.length a.
    Proof. intros; apply replace_nth_length. Qed.
  End ListArray.

  Arguments t : clear implicits.
End ListArray.

Section Gallina.
  Open Scope Z_scope.

  Context {A}
          (from to step: Z)
          (body: forall (tok: ExitToken.t) (idx: Z) (acc: A),
              from <= idx < to -> (ExitToken.t * A)).

  Lemma ranged_for'_1 {idx} :
    from <= idx ->
    idx < to ->
    from <= idx < to.
  Proof. lia. Qed.

  Lemma ranged_for'_2 {idx k} :
    from <= idx ->
    from <= idx + Z.max 1 k.
  Proof. lia. Qed.

  Lemma ranged_for'_termination {idx k}:
    idx < to ->
    to - (idx + Z.max 1 k) < to - idx.
  Proof.
    intros. (* This reduces faster than a the proof generated by ‘lia’ *)
    match goal with
    | [  |- ?a < ?b ] =>
      destruct (Z.lt_decidable a b) as [Hlt | Hge];
        [ exact Hlt | exfalso; lia ]
    end.
  Defined.

  (* Require Import Equations.Equations. *)

  (* Equations ranged_for' (a0: A) idx (Hle: from <= idx) : A by wf (to - idx) lt := *)
  (*   ranged_for' a0 idx Hle with le_gt_dec to idx => { *)
  (*     ranged_for' a0 idx Hle (left _) := a0; *)
  (*     ranged_for' a0 idx Hle (right Hgt) := *)
  (*       let (tok, a0) := body (ExitToken.new false) idx a0 (ranged_for'_1 Hle Hgt) in *)
  (*       if ExitToken.get tok then a0 *)
  (*       else ranged_for' a0 (idx + S (pred step)) (ranged_for'_2 Hle) *)
  (*   }. *)
  (* Next Obligation. lia. Qed. *)

  (* Program Fixpoint ranged_for' (a0: A) idx (Hle: from <= idx) {measure (to - idx)} : A := *)
  (*   match le_gt_dec to idx with *)
  (*   | left _ => a0 *)
  (*   | right Hgt => *)
  (*     let (tok, a0) := body (ExitToken.new false) idx a0 (ranged_for'_1 Hle Hgt) in *)
  (*     if ExitToken.get tok then a0 *)
  (*     else ranged_for' a0 (idx + S (pred step)) (ranged_for'_2 Hle) *)
  (*   end. *)
  (* Next Obligation. lia. Qed. *)

  (* FIXME Is ExitToken the right API for continue?. *)
  Search (Z -> Z -> { _ } + { _ }).
  Function ranged_for' (a0: A) idx (Hle: from <= idx) {measure (fun n => Z.to_nat (to - n)) idx} : A :=
    match Z_lt_dec idx to with
    | left Hlt =>
      let '(tok, a0) := body (ExitToken.new false) idx a0 (ranged_for'_1 Hle Hlt) in
      if ExitToken.get tok then a0
      else ranged_for' a0 (idx + Z.max 1 step) (ranged_for'_2 Hle)
    | right _ => a0
    end.
  Proof. lia. Defined.   (* FIXME *)
  (* intros; apply ranged_for'_termination; assumption. Defined. *)
  Global Opaque ranged_for'.

  Definition ranged_for (a0: A) :=
    ranged_for' a0 from (Z.le_refl _).

  Definition Z_must_lt (a b: Z) : if Z_lt_dec a b then a < b else True.
  Proof. destruct Z_lt_dec; (assumption || exact I). Defined.
  Definition Z_must_gt (a b: Z) : if Z_gt_dec a b then a > b else True.
  Proof. destruct Z_gt_dec; (assumption || exact I). Defined.
  Definition Z_must_pos (a: Z) : if Z_gt_dec a 0 then a > 0 else True :=
    Z_must_gt a 0.

  Section Induction.
    Context (P: A -> Prop) (a0: A).

    Context (H0: P a0).
    Context (Hbody: forall tok idx a1 Hle, P a1 -> P (snd (body tok idx a1 Hle))).

    Lemma ranged_for'_ind' :
      forall idx Hle,
        P (ranged_for' a0 idx Hle).
    Proof.
      intros.
      revert H0 Hbody.
      apply ranged_for'_ind;
        repeat match goal with
               | _ => progress (subst || intros || cbn in * )
               | [ H: _ = _ |- _ ] => apply (f_equal snd) in H
               | _ => eauto
               end.
    Qed.

    Lemma ranged_for_ind :
      P (ranged_for a0).
    Proof. eapply ranged_for'_ind'. Qed.
  End Induction.
End Gallina.

Open Scope Z_scope.

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Context {A: Type}
          (from to step: word).

  Section Generic.
    Context {to_Z: word -> Z}
            (to_Z_of_Z: forall l h w,
                to_Z l <= w <= to_Z h ->
                to_Z (word.of_Z w) = w).

    Context (Hgt: to_Z step > 0).
    Context (body: forall (tok: ExitToken.t) (idx: word) (acc: A),
              to_Z from <= to_Z idx < to_Z to ->
              (ExitToken.t * A)).

    Program Definition ranged_for_w (a0: A) : A :=
      ranged_for (to_Z from) (to_Z to) (to_Z step)
                 (fun tok idx acc pr =>
                    body tok (word.of_Z idx) acc _)
                 a0.
    Next Obligation.
      erewrite (to_Z_of_Z from to); lia.
    Qed.

    Section Induction.
      Context (P: A -> Prop) (a0: A).
      Context (H0: P a0).
      Context (Hbody: forall tok idx a1 Hle, P a1 -> P (snd (body tok idx a1 Hle))).

      Lemma ranged_for_w_ind : P (ranged_for_w a0).
      Proof. unfold ranged_for_w; apply ranged_for_ind; auto. Qed.
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

  Section WordArray.
    Context
      {A K} (to_list: A -> list word) (to_word: K -> word)
      (get: A -> K -> word)
      (put: A -> K -> word -> A)
      (repr: address -> A -> Semantics.mem -> Prop).

    Notation to_nat idx := (Z.to_nat (word.unsigned (to_word idx))).

    Context (a : A) (a_ptr : word) (a_var : string)
            (val: word) (val_var: string)
            (idx : K) (idx_var : string).

    Context
      (Hget: forall a,
         exists default,
           get a idx =
           List.hd default (List.skipn (to_nat idx) (to_list a)))
      (Hput:
         (to_nat idx < List.length (to_list a))%nat ->
         to_list (put a idx val) =
         List.app
           (List.firstn (to_nat idx) (to_list a))
           (val :: List.skipn (S (to_nat idx)) (to_list a)))
      (Hgetput:
         (to_nat idx < List.length (to_list a))%nat ->
         get (put a idx val) idx = val)
      (Hrw:
         Lift1Prop.iff1
           (repr a_ptr a)
           (array scalar (word.of_Z (Memory.bytes_per_word Semantics.width))
                  a_ptr (to_list a)))
      (Hrw_put:
         Lift1Prop.iff1
           (repr a_ptr (put a idx val))
           (array scalar (word.of_Z (Memory.bytes_per_word Semantics.width))
                  a_ptr (to_list (put a idx val)))).

    Lemma compile_word_array_get
          {tr mem locals functions} {T} {pred: T -> predicate}
          R (k: _ -> T) (k_impl : cmd) (var : string):

      (Z.to_nat (word.unsigned (to_word idx)) < Datatypes.length (to_list a))%nat ->

      sep (repr a_ptr a) R mem ->
      map.get locals a_var = Some a_ptr ->
      map.get locals idx_var = Some (to_word idx) ->

      let v := get a idx in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.set
           var
           (expr.load
              access_size.word
              (expr.op bopname.add
                       (expr.var a_var)
                       (expr.op bopname.mul
                                (expr.literal (Memory.bytes_per_word Semantics.width))
                                (expr.var idx_var)))))
        k_impl
      <{ pred (nlet [var] v k) }>.
    Proof.
      cbn; intros Hlt *.
      pose proof word.unsigned_range (to_word idx) as (Hge & _).
      destruct (Hget a) as [default Hget0].

      exists (get a idx); split; cbn; [ | assumption ].
      exists a_ptr; split; [ eassumption | ]; cbn.
      exists (to_word idx); split; [ eassumption | ]; cbn.
      eexists; split; [ | reflexivity ].

      eapply load_word_of_sep.
      seprewrite_in Hrw H.        (* FIXME seprewrite shouldn't rename *)
      (* FIXME: BEDROCK2: Adding an extra "_" at the end shelves an inequality *)
      once (seprewrite_in open_constr:(array_index_nat_inbounds
                                         _ _ _ _ (Z.to_nat (word.unsigned (to_word idx)))) H4).
      { assumption. }

      rewrite word.ring_morph_mul, Z2Nat.id, !word.of_Z_unsigned in H3 by assumption.
      rewrite Hget0.
      ecancel_assumption.
    Qed.

    Lemma compile_word_array_put
          {tr mem locals functions} {T} {pred: T -> predicate}
          R (k: _ -> T) (k_impl: cmd) (var: string) :
      (Z.to_nat (word.unsigned (to_word idx)) < Datatypes.length (to_list a))%nat ->

      sep (repr a_ptr a) R mem ->
      map.get locals a_var = Some a_ptr ->
      map.get locals idx_var = Some (to_word idx) ->
      map.get locals val_var = Some val ->

      let a := (put a idx val) in
      (let a := a in
       forall mem',
         sep (repr a_ptr a) R mem' ->
         <{ Trace := tr;
            Memory := mem';
            Locals := locals;
            Functions := functions }>
         k_impl
         <{ pred (k a) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.store
           access_size.word
           (expr.op bopname.add
                    (expr.var a_var)
                    (expr.op bopname.mul
                             (expr.literal (Memory.bytes_per_word Semantics.width))
                             (expr.var idx_var)))
           (expr.var val_var))
        k_impl
      <{ pred (nlet [var] a k) }>.
    Proof.
      cbn; intros Hlt *.
      pose proof word.unsigned_range (to_word idx) as (Hge & _).
      destruct (Hget (put a idx val)) as [default Hget0].
      eexists; split; cbn.

      { eexists; split; [ eassumption | ]; cbn.
        eexists; split; [ eassumption | reflexivity ]. }

      { eexists; split; cbn.
        { eexists; split; [ eassumption | reflexivity ]. }
        { seprewrite_in Hrw H.
          once (seprewrite_in
                  open_constr:(array_index_nat_inbounds
                                 _ _ (default := default) _ _ (Z.to_nat (word.unsigned (to_word idx)))) H5).
          { assumption. }

          eapply store_word_of_sep.
          { rewrite word.ring_morph_mul, Z2Nat.id, !word.of_Z_unsigned in H4 by assumption.
            ecancel_assumption. }
          { intros m Hm.
            apply H3.
            seprewrite Hrw_put.
            seprewrite
              open_constr:(array_index_nat_inbounds
                             _ _ (default := default) _ _ (Z.to_nat (word.unsigned (to_word idx)))).
            { rewrite Hput by lia.
              rewrite List.app_length, List.firstn_length_le by lia.
              cbn [List.length]; rewrite List.length_skipn.
              lia. }
            { rewrite <- Hget0, Hgetput by lia.
              repeat rewrite word.ring_morph_mul, Z2Nat.id, !word.of_Z_unsigned by lia.
              rewrite Hput by lia.

              rewrite List.firstn_app.
              rewrite List.firstn_firstn, Min.min_idempotent.
              rewrite List.firstn_length_le by lia.
              rewrite Nat.sub_diag; cbn [List.firstn]; rewrite app_nil_r.

              change (val :: ?tl) with (List.app [val] tl).
              rewrite List.app_assoc, List.skipn_app, List.skipn_all, List.app_nil_l, List.skipn_skipn;
                rewrite !List.app_length, List.firstn_length_le, (Nat.add_comm _ 1) by lia.
              - rewrite Nat.sub_diag, Nat.add_0_l.
                ecancel_assumption.
              - reflexivity. } } } }
    Qed.
  End WordArray.

  Instance Convertible_word_Nat : Convertible word nat :=
    fun w => Z.to_nat (word.unsigned w).
  Instance HasDefault_word : HasDefault word :=
    word.of_Z 0.

  Section WordVectorArray.
    Definition word_vectorarray_value {n} (addr: address) (a: VectorArray.t word n) : Semantics.mem -> Prop :=
      array scalar (word.of_Z (Memory.bytes_per_word Semantics.width)) addr (Vector.to_list a).

    Notation repr := word_vectorarray_value.
    Notation to_list := Vector.to_list.
    Notation to_word := (proj1_sig (P:=fun idx0 : word => (cast idx0 < _)%nat)).
    Notation to_nat idx := (Z.to_nat (word.unsigned (to_word idx))).

    Notation get a idx := (VectorArray.get a (proj1_sig idx) (proj2_sig idx)).
    Notation put a idx v := (VectorArray.put a (proj1_sig idx) (proj2_sig idx) v).

    Lemma WordVectorArray_Hget {n}:
      forall (a: VectorArray.t word n) idx,
      exists default,
        get a idx =
        List.hd default (List.skipn (to_nat idx) (to_list a)).
    Proof.
      intros. exists (word.of_Z 0).
      apply Vector_nth_hd_skipn.
      rewrite Fin.to_nat_of_nat; reflexivity.
    Qed.

    Lemma WordVectorArray_Hput {n} :
      forall (a : VectorArray.t word n) (idx: {idx : word | (cast idx < n)%nat}) v,
        to_list (put a idx v) =
        List.app
          (List.firstn (to_nat idx) (to_list a))
          (v :: List.skipn (S (to_nat idx)) (to_list a)).
    Proof.
      unfold put.
      destruct idx as [widx pr]; cbn [proj1_sig proj2_sig].
      unfold cast, Convertible_word_Nat in *.
      set (Z.to_nat (word.unsigned widx)) as idx in *.
      intros.
      unfold Vector.replace_order; erewrite Vector_to_list_replace by reflexivity.
      rewrite <- replace_nth_eqn by (rewrite Vector_to_list_length; assumption).
      rewrite Fin.to_nat_of_nat; reflexivity.
    Qed.

    Lemma WordVectorArray_Hgetput {n} :
      forall (a : VectorArray.t word n) (idx: {idx : word | (cast idx < n)%nat}) v,
        get (put a idx v) idx = v.
    Proof.
      unfold get, put, Vector.nth_order, Vector.replace_order.
      intros; apply Vector_nth_replace.
    Qed.

    Lemma WordVectorArray_Hrw {n}:
      forall addr (a: VectorArray.t word n),
        Lift1Prop.iff1
          (repr addr a)
          (array scalar (word.of_Z (Memory.bytes_per_word Semantics.width))
                 addr (to_list a)).
    Proof. reflexivity. Qed.

    Lemma compile_word_vectorarray_get {n}
        {tr mem locals functions} {T} {pred: T -> predicate} :
      forall R (a: VectorArray.t word n) (a_ptr: address) a_var
        idx idx_var pr (k: _ -> T) k_impl var,
        (* (pr: (word.unsigned idx < Z.of_nat n)%Z), FIXME if we want this eqn, then indices need to be Z *)

        sep (word_vectorarray_value a_ptr a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some idx ->

        let v := VectorArray.get a idx pr in
        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var v;
            Functions := functions }>
         k_impl
         <{ pred (k v) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.set
             var
             (expr.load
                access_size.word
                (expr.op bopname.add
                         (expr.var a_var)
                         (expr.op bopname.mul
                                  (expr.literal (Memory.bytes_per_word Semantics.width))
                                  (expr.var idx_var)))))
          k_impl
        <{ pred (nlet [var] v k) }>.
    Proof.
      intros.
      change v with
          ((fun a idx => VectorArray.get a (proj1_sig idx) (proj2_sig idx))
             a (exist (fun idx => cast idx < n)%nat idx pr)).
      eapply (compile_word_array_get to_list to_word);
        eauto using WordVectorArray_Hget, WordVectorArray_Hrw.
      { rewrite Vector_to_list_length.
        simpl. assumption. }
    Qed.

    Lemma compile_word_vectorarray_put {n}
        {tr mem locals functions} {T} {pred: T -> predicate} :
      forall R (a: VectorArray.t word n) a_ptr a_var
        idx idx_var val val_var pr (k: _ -> T) k_impl var,

        sep (word_vectorarray_value a_ptr a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some idx ->
        map.get locals val_var = Some val ->

        let a := (VectorArray.put a idx pr val) in
        (let a := a in
         forall mem',
           sep (word_vectorarray_value a_ptr a) R mem' ->
           <{ Trace := tr;
              Memory := mem';
              Locals := locals;
              Functions := functions }>
           k_impl
           <{ pred (k a) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.store
             access_size.word
             (expr.op bopname.add
                      (expr.var a_var)
                      (expr.op bopname.mul
                               (expr.literal (Memory.bytes_per_word Semantics.width))
                               (expr.var idx_var)))
             (expr.var val_var))
          k_impl
        <{ pred (nlet [var] a k) }>.
    Proof.
      intros.
      change a0 with
          ((fun a idx val => VectorArray.put a (proj1_sig idx) (proj2_sig idx) val)
             a (exist (fun idx => cast idx < n)%nat idx pr) val).
      eapply (compile_word_array_put
                to_list to_word
                (fun a idx => get a idx)
                (fun a idx v => put a idx v));
        eauto using WordVectorArray_Hget, WordVectorArray_Hrw,
        WordVectorArray_Hgetput, WordVectorArray_Hput.
      rewrite Vector_to_list_length; assumption.
    Qed.
  End WordVectorArray.

  Section WordListArray.
    Definition word_listarray_value (addr: address) (a: ListArray.t word)
      : Semantics.mem -> Prop :=
      array scalar (word.of_Z (Memory.bytes_per_word Semantics.width)) addr a.

    Notation repr := word_listarray_value.
    Notation to_list x := x.
    Notation to_word x := x.
    Notation to_nat idx := (Z.to_nat (word.unsigned (to_word idx))).

    Notation get a idx := (ListArray.get a idx).
    Notation put a idx v := (ListArray.put a idx v).

    Lemma WordListArray_Hget:
      forall (a: ListArray.t word) idx,
      exists default,
        get a idx =
        List.hd default (List.skipn (to_nat idx) (to_list a)).
    Proof.
      intros. exists (word.of_Z 0).
      unfold get; rewrite <- List.nth_default_eq.
      apply List.hd_skipn_nth_default.
    Qed.

    Lemma WordListArray_Hput :
      forall (a : ListArray.t word) (idx: word) v,
        (to_nat idx < Datatypes.length a)%nat ->
        to_list (put a idx v) =
        List.app
          (List.firstn (to_nat idx) (to_list a))
          (v :: List.skipn (S (to_nat idx)) (to_list a)).
    Proof.
      unfold put; eauto using replace_nth_eqn.
    Qed.

    Lemma WordListArray_Hgetput :
      forall (a : ListArray.t word) (idx: word) v,
        (to_nat idx < Datatypes.length a)%nat ->
        get (put a idx v) idx = v.
    Proof.
      unfold get, put.
      intros; apply nth_replace_nth; (assumption || reflexivity).
    Qed.

    Lemma WordListArray_Hrw:
      forall addr (a: ListArray.t word),
        Lift1Prop.iff1
          (repr addr a)
          (array scalar (word.of_Z (Memory.bytes_per_word Semantics.width))
                 addr (to_list a)).
    Proof. reflexivity. Qed.

    Lemma compile_word_listarray_get
        {tr mem locals functions} {T} {pred: T -> predicate} :
      forall R (a: ListArray.t word) (a_ptr: address) a_var
        idx idx_var (k: _ -> T) k_impl var,

        sep (word_listarray_value a_ptr a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some idx ->

        word.unsigned idx < Z.of_nat (Datatypes.length (id a)) ->

        let v := ListArray.get a idx in
        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var v;
            Functions := functions }>
         k_impl
         <{ pred (k v) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.set
             var
             (expr.load
                access_size.word
                (expr.op bopname.add
                         (expr.var a_var)
                         (expr.op bopname.mul
                                  (expr.literal (Memory.bytes_per_word Semantics.width))
                                  (expr.var idx_var)))))
          k_impl
        <{ pred (nlet [var] v k) }>.
    Proof.
      intros.
      eapply (compile_word_array_get id id);
        eauto using WordListArray_Hget, WordListArray_Hrw.
      pose proof word.unsigned_range idx.
      unfold id in *; lia.
    Qed.

    Lemma compile_word_listarray_put
        {tr mem locals functions} {T} {pred: T -> predicate} :
      forall R a a_ptr a_var idx idx_var val val_var (k: _ -> T) k_impl var,

        sep (word_listarray_value a_ptr a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some idx ->
        map.get locals val_var = Some val ->

        (word.unsigned idx < Z.of_nat (List.length a))%Z ->

        let a := (ListArray.put a idx val) in
        (let a := a in
         forall mem',
           sep (word_listarray_value a_ptr a) R mem' ->
           <{ Trace := tr;
              Memory := mem';
              Locals := locals;
              Functions := functions }>
           k_impl
           <{ pred (k a) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.store
             access_size.word
             (expr.op bopname.add
                      (expr.var a_var)
                      (expr.op bopname.mul
                               (expr.literal (Memory.bytes_per_word Semantics.width))
                               (expr.var idx_var)))
             (expr.var val_var))
          k_impl
        <{ pred (nlet [var] a k) }>.
    Proof.
      intros.
      eapply (compile_word_array_put id id);
        eauto using WordListArray_Hget, WordListArray_Hput,
        WordListArray_Hgetput, WordListArray_Hrw.
      unfold id; pose proof word.unsigned_range idx.
      lia.
    Qed.
  End WordListArray.

  Section WordSizedListArray.
    Definition word_sizedlistarray_value (addr: address) (len: nat) (a: ListArray.t word)
      : Semantics.mem -> Prop :=
      sep (emp (List.length a = len)) (array scalar (word.of_Z (Memory.bytes_per_word Semantics.width)) addr a).

    Notation repr := word_sizedlistarray_value.
    Notation to_list x := x.
    Notation to_word x := x.
    Notation to_nat idx := (Z.to_nat (word.unsigned (to_word idx))).

    Notation get a idx := (ListArray.get a idx).
    Notation put a idx v := (ListArray.put a idx v).

    Lemma WordSizedListArray_Hrw:
      forall addr sz (a: ListArray.t word),
        List.length a = sz ->
        Lift1Prop.iff1
          (repr addr sz a)
          (array scalar (word.of_Z (Memory.bytes_per_word Semantics.width))
                 addr (to_list a)).
    Proof. unfold word_sizedlistarray_value.
       intros. setoid_replace (Datatypes.length a = sz) with True.
       - apply sep_emp_True_l.
       - tauto.
    Qed.

    Lemma WordSizedListArray_length :
      forall addr sz (a: ListArray.t word) mem R,
        (repr addr sz a * R)%sep mem -> List.length a = sz.
    Proof.
      intros * H; unfold repr in H.
      eapply proj1. apply sep_emp_l with (m := mem).
      ecancel_assumption.
    Qed.

    Lemma compile_word_sizedlistarray_get {sz}
        {tr mem locals functions} {T} {pred: T -> predicate} :
      forall R (a: ListArray.t word) (a_ptr: address) a_var
        idx idx_var (k: _ -> T) k_impl var,

        sep (word_sizedlistarray_value a_ptr sz a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some idx ->

        word.unsigned idx < Z.of_nat sz ->

        let v := ListArray.get a idx in
        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var v;
            Functions := functions }>
         k_impl
         <{ pred (k v) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.set
             var
             (expr.load
                access_size.word
                (expr.op bopname.add
                         (expr.var a_var)
                         (expr.op bopname.mul
                                  (expr.literal (Memory.bytes_per_word Semantics.width))
                                  (expr.var idx_var)))))
          k_impl
        <{ pred (nlet [var] v k) }>.
    Proof.
      intros.
      eapply (compile_word_array_get id id _ (fun addr a => repr addr sz a));
        eauto using WordListArray_Hget.
      - eapply WordSizedListArray_Hrw, WordSizedListArray_length.
        eassumption.
      - unfold id.
        erewrite WordSizedListArray_length by eassumption.
        pose proof word.unsigned_range idx.
        lia.
    Qed.

    Lemma compile_word_sizedlistarray_put {sz}
        {tr mem locals functions} {T} {pred: T -> predicate} :
      forall R a a_ptr a_var idx idx_var val val_var (k: _ -> T) k_impl var,

        sep (word_sizedlistarray_value a_ptr sz a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some idx ->
        map.get locals val_var = Some val ->

        (word.unsigned idx < Z.of_nat sz)%Z ->

        let a := (ListArray.put a idx val) in
        (let a := a in
         forall mem',
           sep (word_sizedlistarray_value a_ptr sz a) R mem' ->
           <{ Trace := tr;
              Memory := mem';
              Locals := locals;
              Functions := functions }>
           k_impl
           <{ pred (k a) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.store
             access_size.word
             (expr.op bopname.add
                      (expr.var a_var)
                      (expr.op bopname.mul
                               (expr.literal (Memory.bytes_per_word Semantics.width))
                               (expr.var idx_var)))
             (expr.var val_var))
          k_impl
        <{ pred (nlet [var] a k) }>.
    Proof.
      intros.
      eapply (compile_word_array_put id id _ _ (fun (addr: word) a => repr addr sz a));
        eauto using WordListArray_Hget, WordListArray_Hput,
        WordListArray_Hgetput.
      - eapply WordSizedListArray_Hrw, WordSizedListArray_length.
        eassumption.
      - eapply WordSizedListArray_Hrw.
        unfold id; rewrite ListArray.put_length.
        eapply WordSizedListArray_length.
        eassumption.
      - unfold id; pose proof word.unsigned_range idx.
        erewrite WordSizedListArray_length by eassumption.
        lia.
    Qed.
  End WordSizedListArray.

  Lemma compile_add :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
      tr functions T (pred: T -> predicate)
      x x_var y y_var (k: _ -> T) k_impl var,
      map.get locals x_var = Some x ->
      map.get locals y_var = Some y ->
      let v := word.add x y in
      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var v;
          Functions := functions }>
       k_impl
       <{ pred (k v) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.op bopname.add (expr.var x_var) (expr.var y_var)))
              k_impl
      <{ pred (nlet [var] v k) }>.
  Proof.
    intros.
    repeat straightline.
    eexists; split.
    { repeat straightline.
        exists x; split; try eassumption.
        repeat straightline.
        exists y; split; try eassumption.
        reflexivity. }
    red.
    eassumption.
  Qed.

  (* Lemma compile_ranged_for : *)
  (*   forall (locals: Semantics.locals) (mem: Semantics.mem) *)
  (*     A T *)
  (*     (loop_pred: nat -> (bool * A) -> predicate) *)
  (*     (k_pred: T -> predicate) *)
  (*     tr functions *)
  (*     vars *)
  (*     (from to step: nat) *)
  (*     (from_var to_var step_var: string) *)
  (*     body body_impl *)
  (*     (k: _ -> T) k_impl *)
  (*     (a0: A), *)
  (*     loop_pred from (true, a0) tr mem locals -> *)
  (*     (* fixme make a shorter alias for this *) *)
  (*     option_map word.unsigned (map.get locals from_var) = Some (Z.of_nat from) -> *)
  (*     option_map word.unsigned (map.get locals to_var) = Some (Z.of_nat to) -> *)
  (*     option_map word.unsigned (map.get locals step_var) = Some (Z.of_nat step) -> *)
  (*     let v := ranged_for from to step body a0 in *)
  (*     ((* loop body *) *)
  (*      forall tr mem locals from', *)
  (*        let a := ranged_for from from' step body a0 in *)
  (*        loop_pred from' (true, a) tr mem locals -> *)
  (*        (<{ Trace := tr; *)
  (*            Memory := mem; *)
  (*            Locals := locals; *)
  (*            Functions := functions }> *)
  (*         body_impl *)
  (*         <{ loop_pred from' (body from' a) }>)) -> *)
  (*     (let v := v in *)
  (*      forall tr mem locals, *)
  (*        loop_pred to (false, v) tr mem locals -> *)
  (*        (<{ Trace := tr; *)
  (*            Memory := mem; *)
  (*            Locals := locals; *)
  (*            Functions := functions }> *)
  (*         k_impl *)
  (*         <{ k_pred (k v) }>)) -> *)
  (*     (let v := v in *)
  (*      <{ Trace := tr; *)
  (*         Memory := mem; *)
  (*         Locals := locals; *)
  (*         Functions := functions }> *)
  (*      cmd.seq *)
  (*        (cmd.while *)
  (*           (expr.op bopname.ltu (expr.var from_var) (expr.var to_var)) *)
  (*           (cmd.seq *)
  (*              (cmd.set from_var *)
  (*                       (expr.op bopname.add *)
  (*                                (expr.var from_var) *)
  (*                                (expr.literal 1))) *)
  (*              body_impl)) *)
  (*        k_impl *)
  (*      <{ k_pred (nlet vars v k) }>). *)
  (* Proof. *)
  (*   cbv zeta. *)
  (*   repeat straightline'. *)
  (* Admitted. *)

  Definition ranged_for_widen_bounds {from idx from' to} :
    from <= idx < from' ->
    from' < to ->
    from <= idx < to.
  Proof. lia. Qed.

  Section Generic.
    Context {to_Z: word -> Z}
            (to_Z_of_Z: forall l h w,
                to_Z l <= w <= to_Z h ->
                to_Z (word.of_Z w) = w).

    Lemma compile_ranged_for_w {A T}:
      forall tr mem locals functions
        (loop_pred: word -> A -> predicate)
        (k_pred: T -> predicate)
        (from to step: word)
        (from_var to_var step_var: string)
        (a0: A) vars
        body body_impl
        k k_impl,
        let lp from '(tok, acc) tr mem locals :=
            loop_pred (ExitToken.branch tok (word.sub to (word.of_Z 1)) from) acc tr mem locals in
        (forall from a0 tr mem locals,
            loop_pred from a0 tr mem locals ->
            map.getmany_of_list locals [from_var; to_var; step_var] =
            Some [from; to; step]) ->
        loop_pred from a0 tr mem locals ->
        let v := ranged_for_w from to step to_Z_of_Z body a0 in
        ((* loop body *)
          let lp := lp in
          forall tr mem locals from'
            (Hle: to_Z from <= to_Z from')
            (Hlt: to_Z from' < to_Z to),
            let tok := ExitToken.new false in
            let a := ranged_for_w from from' step to_Z_of_Z
                                 (fun tok idx acc pr =>
                                    body tok idx acc (ranged_for_widen_bounds pr Hlt)) a0 in
            loop_pred from' a tr mem locals ->
            (<{ Trace := tr;
                Memory := mem;
                Locals := locals;
                Functions := functions }>
             body_impl
             <{ lp from' (body tok from' a (conj Hle Hlt)) }>)) ->
        (let v := v in
         forall tr mem locals,
           loop_pred to v tr mem locals ->
           (<{ Trace := tr;
               Memory := mem;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ k_pred (k v) }>)) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.while
             (expr.op bopname.ltu (expr.var from_var) (expr.var to_var))
             (cmd.seq
                body_impl
                (cmd.set from_var
                         (expr.op bopname.add
                                  (expr.var from_var)
                                  (expr.literal 1)))))
          k_impl
        <{ k_pred (nlet vars v k) }>.
    Proof.
      cbv zeta.
      repeat straightline'.
    Admitted.
  End Generic.

  Definition compile_ranged_for_u {A T} :=
    compile_ranged_for_w word_unsigned_of_Z_bracketed (A := A) (T := T).

  Definition compile_ranged_for_s {A T} :=
    compile_ranged_for_w word_signed_of_Z_bracketed (A := A) (T := T).

   Ltac compile_custom ::=
     first [simple eapply compile_get |
            simple eapply compile_put |
            (* simple eapply compile_sig | *)
            simple eapply compile_word_vectorarray_get |
            simple eapply compile_word_vectorarray_put |
            simple eapply compile_word_sizedlistarray_get |
            simple eapply compile_word_sizedlistarray_put ].

   Notation "∅" := map.empty.
   Notation "m [[ k ← v ]]" :=
     (map.put m k v)
       (left associativity, at level 11,
        format "m [[ k  ←  v ]]").

   Ltac try_unify x y :=
     try ((unify x y; fail 1) || fail 1 "Does not unify").

   Ltac lookup_variable m val ::=
     match m with
     | map.put _ ?k ?val' =>
       let t := type of val in
       let _ := constr:(@eq_refl t val <: val = val') in
       constr:(k)
     | map.put ?m' _ _ => lookup_variable m' val
     | _ => fail "lookup_variable: no results found"
     end.

   Lemma signed_lt_unsigned w:
     word.signed w <= word.unsigned w.
   Proof.
     pose proof word.unsigned_range w.
     rewrite word.signed_unsigned_dec.
     destruct Z_lt_le_dec; lia.
   Qed.

    Program Definition vect_memcpy {n1 n2} (len: word)
           (a1: VectorArray.t word n1)
           (a2: VectorArray.t word n2)
           (pr1: word.unsigned len < Z.of_nat n1)
           (pr2: word.unsigned len < Z.of_nat n2) :=
     let/n from := word.of_Z 0 in
     let/n step := word.of_Z 1 in
     let/n a2 := ranged_for_u
                  from len step
                  (fun tok idx a2 Hlt =>
                     let/n v := VectorArray.get a1 idx _ in
                     let/n a2 := VectorArray.put a2 idx _ v in
                     (tok, a2)) a2 in
     (a1, a2).
    Next Obligation.
      pose proof word.unsigned_range idx.
      pose proof word.unsigned_range len.
      unfold cast, Convertible_word_Nat.
      lia.
    Qed.
    Next Obligation.
      pose proof word.unsigned_range idx.
      pose proof word.unsigned_range len.
      unfold cast, Convertible_word_Nat.
      lia.
    Qed.

   Definition TwoVectArrays {n1 n2} a1_ptr a2_ptr :=
     (fun '(a1, a2) (_retvals: list word) =>
        (word_vectorarray_value (n := n1) a1_ptr a1 *
         word_vectorarray_value (n := n2) a2_ptr a2)%sep).
   Hint Unfold TwoVectArrays : compiler.

   Instance spec_of_vect_memcpy : spec_of "vect_memcpy" :=
     (forall! (len: word) (a1_ptr a2_ptr : address)
       {n1} (a1: VectorArray.t word n1)
       {n2} (a2: VectorArray.t word n2)
       (pr1: word.unsigned len < Z.of_nat n1)
       (pr2: word.unsigned len < Z.of_nat n2),
         (fun R mem =>
            sep (word_vectorarray_value a1_ptr a1 * word_vectorarray_value a2_ptr a2)%sep R mem)
         ===>
         "vect_memcpy" @ [len; a1_ptr; a2_ptr]
         ===>
         (TwoVectArrays a1_ptr a2_ptr (vect_memcpy len a1 a2 pr1 pr2))).

   Derive vect_memcpy_body SuchThat
          (let memcpy := ("vect_memcpy", (["len"; "a1"; "a2"], [], vect_memcpy_body)) in
           program_logic_goal_for
             memcpy
             (ltac:(let x := program_logic_goal_for_function
                              memcpy (@nil string) in
                    exact x)))
          As vect_memcpy_correct.
   Proof.
     compile_setup.

     repeat compile_step.

     eapply compile_ranged_for_u with (loop_pred := (fun idx a2 tr' mem' locals' =>
         tr' = tr /\
         locals' = (∅[["len" ← len]][["a1" ← a1_ptr]][["a2" ← a2_ptr]]
                     [["from" ← idx]][["step" ← v0]]) /\
         (word_vectorarray_value a1_ptr a1 * word_vectorarray_value a2_ptr a2 * R)%sep mem')).

     all: repeat compile_step; compile_done.
   Qed.

   Definition sizedlist_memcpy (len: word)
           (a1: ListArray.t word)
           (a2: ListArray.t word) :=
     let/n from := word.of_Z 0 in
     let/n step := word.of_Z 1 in
     let/n a2 := ranged_for_u
                  from len step
                  (fun tok idx a2 Hlt =>
                     let/n v := ListArray.get a1 idx in
                     let/n a2 := ListArray.put a2 idx v in
                     (tok, a2)) a2 in
     (a1, a2).

   Definition TwoSizedListArrays n1 n2 a1_ptr a2_ptr :=
     (fun '(a1, a2) (_retvals: list word) =>
        (word_sizedlistarray_value a1_ptr n1 a1 *
         word_sizedlistarray_value a2_ptr n2 a2)%sep).
   Hint Unfold TwoSizedListArrays : compiler.

   Instance spec_of_sizedlist_memcpy : spec_of "sizedlist_memcpy" :=
     (forall! (len: word) (a1_ptr a2_ptr : address)
       {n1} (a1: ListArray.t word)
       {n2} (a2: ListArray.t word)
       (pr1: word.unsigned len < Z.of_nat n1)
       (pr2: word.unsigned len < Z.of_nat n2),
         (fun R mem =>
            sep (word_sizedlistarray_value a1_ptr n1 a1 *
                 word_sizedlistarray_value a2_ptr n2 a2)%sep R mem)
         ===>
         "sizedlist_memcpy" @ [len; a1_ptr; a2_ptr]
         ===>
         (TwoSizedListArrays n1 n2 a1_ptr a2_ptr (sizedlist_memcpy len a1 a2))).

   Derive sizedlist_memcpy_body SuchThat
         (let memcpy := ("sizedlist_memcpy", (["len"; "a1"; "a2"], [], sizedlist_memcpy_body)) in
          program_logic_goal_for
            memcpy
            (ltac:(let x := program_logic_goal_for_function
                              memcpy (@nil string) in
                   exact x)))
         As sizedlist_memcpy_correct.
   Proof.
     compile_setup.

     repeat compile_step.

     eapply compile_ranged_for_u with (loop_pred := (fun idx a2 tr' mem' locals' =>
         tr' = tr /\
         locals' = (∅[["len" ← len]][["a1" ← a1_ptr]][["a2" ← a2_ptr]]
                     [["from" ← idx]][["step" ← v0]]) /\
         (word_sizedlistarray_value a1_ptr n1 a1 *
          word_sizedlistarray_value a2_ptr n2 a2 * R)%sep mem')).

     all: repeat compile_step; try lia; compile_done.
   Qed.

   Definition unsizedlist_memcpy (len: word)
           (a1: ListArray.t word)
           (a2: ListArray.t word) :=
     let/n from := word.of_Z 0 in
     let/n step := word.of_Z 1 in
     let/n a2 := ranged_for_u
                  from len step
                  (fun tok idx a2 Hlt =>
                     let/n v := ListArray.get a1 idx in
                     let/n a2 := ListArray.put a2 idx v in
                     (tok, a2)) a2 in
     (a1, a2).

   Definition TwoUnsizedListArrays a1_ptr a2_ptr :=
     (fun '(a1, a2) (_retvals: list word) =>
        (word_listarray_value a1_ptr a1 *
         word_listarray_value a2_ptr a2)%sep).
   Hint Unfold TwoUnsizedListArrays : compiler.

   Instance spec_of_unsizedlist_memcpy : spec_of "unsizedlist_memcpy" :=
     (forall! (len: word) (a1_ptr a2_ptr : address)
       (a1: ListArray.t word) (a2: ListArray.t word)
       (pr1: word.unsigned len < Z.of_nat (List.length a1))
       (pr2: word.unsigned len < Z.of_nat (List.length a2)),
         (fun R mem =>
            sep (word_listarray_value a1_ptr a1 *
                 word_listarray_value a2_ptr a2)%sep R mem)
         ===>
         "unsizedlist_memcpy" @ [len; a1_ptr; a2_ptr]
         ===>
         (TwoUnsizedListArrays a1_ptr a2_ptr (unsizedlist_memcpy len a1 a2))).

   Derive unsizedlist_memcpy_body SuchThat
         (let memcpy := ("unsizedlist_memcpy", (["len"; "a1"; "a2"], [], unsizedlist_memcpy_body)) in
          program_logic_goal_for
            memcpy
            (ltac:(let x := program_logic_goal_for_function
                              memcpy (@nil string) in
                   exact x)))
         As unsizedlist_memcpy_correct.
   Proof.
     compile_setup.

     repeat compile_step.

     eapply compile_ranged_for_u with (loop_pred := (fun idx a2 tr' mem' locals' =>
         tr' = tr /\
         locals' = (∅[["len" ← len]][["a1" ← a1_ptr]][["a2" ← a2_ptr]]
                     [["from" ← idx]][["step" ← v0]]) /\
         (word_listarray_value a1_ptr a1 *
          word_listarray_value a2_ptr a2 * R)%sep mem')).

     Ltac compile_custom ::=
       first [simple eapply compile_get |
              simple eapply compile_put |
              simple eapply compile_word_vectorarray_get |
              simple eapply compile_word_vectorarray_put |
              simple eapply compile_word_listarray_get |
              simple eapply compile_word_listarray_put ].

     all: repeat compile_step; compile_done; unfold id.

     { lia. (* loop index in bounds + function precondition *) }
     { (* Note the call to induction.
          Without vectors or the sizedlist predicate, we need to check that the index is in bounds but we modified the array.
          Using a vector type instead keeps the information in the type and the statement of put specifies that the length is preserved.
          Putting that info in the representation predicates has a similar effect.
          Without this, we need to perform induction explicitly. *)
       subst a.
       apply ranged_for_u_ind.
       - lia.
       - intros; unfold BlockedLet.nlet, with_name; cbn.
         rewrite ListArray.put_length.
         assumption. }
   Qed.

   Program Definition incr_gallina_spec (c: cell) : cell :=
      let/n one := word.of_Z 1 in
      let/n from := word.of_Z 3 in
      let/n to := word.of_Z 5 in
      let/n step := word.of_Z 1 in
      let/n tick := word.of_Z 0 in
      let/n (tick, c) :=
         ranged_for_u (A := word * cell)
                      from to step
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

  Print incr_gallina_spec.

  Instance spec_of_incr : spec_of "incr" :=
    (forall! (c_ptr : address) (c :cell),
        (sep (cell_value c_ptr c))
          ===>
          "incr" @ [c_ptr]
          ===>
          (OneCell c_ptr (incr_gallina_spec c))).

   Derive incr_body SuchThat
         (let incr := ("incr", (["c"], [], incr_body)) in
          program_logic_goal_for
            incr
            (ltac:(let x := program_logic_goal_for_function
                              incr (@nil string) in
                   exact x)))
         As body_correct.
   Proof.
     compile_setup.

     repeat compile_step.

     compile_unfold_head_binder;
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

   Program Definition vect_memcpy_s {n1 n2} (len: word)
           (a1: VectorArray.t word n1)
           (a2: VectorArray.t word n2)
           (pr1: word.signed len < Z.of_nat n1)
           (pr2: word.signed len < Z.of_nat n2) :=
     let/n from eq:_ := word.of_Z 0 in
     let/n step := word.of_Z 1 in
     let/n a2 := ranged_for_s
                  from len step
                  (fun tok idx a2 Hlt =>
                     let/n v := VectorArray.get a1 idx _ in
                     let/n a2 := VectorArray.put a2 idx _ v in
                     (tok, a2)) a2 in
     (a1, a2).
   Next Obligation.
     pose proof word.half_modulus_pos.
     unfold cast, Convertible_word_Nat.
     rewrite word.signed_of_Z, word.swrap_inrange in H0 by lia.
     rewrite word.signed_gz_eq_unsigned; lia.
   Qed.
   Next Obligation.
     pose proof word.half_modulus_pos.
     unfold cast, Convertible_word_Nat.
     rewrite word.signed_of_Z, word.swrap_inrange in H0 by lia.
     rewrite word.signed_gz_eq_unsigned; lia.
   Qed.

   Instance spec_of_vect_memcpy_s : spec_of "vect_memcpy_s" :=
     (forall! (len: word) (a1_ptr a2_ptr : address)
       {n1} (a1: VectorArray.t word n1)
       {n2} (a2: VectorArray.t word n2)
       (pr1: word.signed len < Z.of_nat n1)
       (pr2: word.signed len < Z.of_nat n2),
         (fun R mem =>
            sep (word_vectorarray_value a1_ptr a1 * word_vectorarray_value a2_ptr a2)%sep R mem)
         ===>
         "vect_memcpy_s" @ [len; a1_ptr; a2_ptr]
         ===>
         (TwoVectArrays a1_ptr a2_ptr (vect_memcpy_s len a1 a2 pr1 pr2))).

   Derive vect_memcpy_s_body SuchThat
          (let memcpy := ("vect_memcpy_s", (["len"; "a1"; "a2"], [], vect_memcpy_s_body)) in
           program_logic_goal_for
             memcpy
             (ltac:(let x := program_logic_goal_for_function
                              memcpy (@nil string) in
                    exact x)))
          As vect_memcpy_s_correct.
   Proof.
     compile_setup.

     repeat compile_step.

     unfold ranged_for_s;
       simple eapply compile_ranged_for_s with (loop_pred := (fun idx a2 tr' mem' locals' =>
         tr' = tr /\
         locals' = (∅[["len" ← len]][["a1" ← a1_ptr]][["a2" ← a2_ptr]]
                     [["from" ← idx]][["step" ← v0]]) /\
         (word_vectorarray_value a1_ptr a1 * word_vectorarray_value a2_ptr a2 * R)%sep mem')).

     all: repeat compile_step; compile_done.
   Qed.
End with_parameters.

Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.
Eval cbv [unsizedlist_memcpy_body vect_memcpy_s_body fold_right] in sizedlist_memcpy_body.

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
