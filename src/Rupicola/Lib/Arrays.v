From Coq Require Vector List.
Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.
Require Import Rupicola.Lib.Loops.
Require Export bedrock2.ArrayCasts.

Open Scope list_scope.

Module VectorArray.
  Section VectorArray.
    Context {K: Type}.
    Context {Conv: Convertible K nat}.
    Open Scope nat_scope.

    Definition t V n := Vector.t V n.
    Definition get {V n} (a: t V n) (k: K) (pr: cast k < n) : V :=
      Vector.nth_order a pr.
    Definition put {V n} (a: t V n) (k: K) (pr: cast k < n) (v: V) : t V n :=
      Vector.replace_order a pr v.
    Definition map {V V' n} (f: V -> V') (a: t V n) : t V' n :=
      Vector.map f a.
    Definition fold_left {V V' n} (f: V' -> V -> V') v0 (a: t V n) : V' :=
      Vector.fold_left f v0 a.
    (* FIXME needs an accessor that generates a test and returns a default *)
  End VectorArray.

  Arguments t : clear implicits.
End VectorArray.

Module ListArray.
Section ListArray.
  Context {K: Type} {Conv: Convertible K nat}.

  Section __.
    Context {V: Type} {HD: HasDefault V}.
    Open Scope nat_scope.

    Definition t := list V.
    Definition get (a: t) (k: K) : V :=
      List.nth (cast k) a default.
    Definition put (a: t) (k: K) (v: V) : t :=
      replace_nth (cast k) a v.
    (* FIXME needs an accessor that generates a test and returns a default *)

    Lemma put_length (a: t) (k: K) (v: V) :
      List.length (put a k v) = List.length a.
    Proof. intros; apply replace_nth_length. Qed.

    Lemma put_0 (a: t) (k: K) (v: V) :
      0 < length a -> cast k = 0 ->
      put a k v = v :: List.tl a.
    Proof.
      unfold put; intros ? ->.
      destruct a; simpl in *; reflexivity || lia.
    Qed.

    Lemma put_app_len (a1 a2: t) (k: K) (v: V) :
      0 < length a2 -> cast k = length a1 ->
      put (a1 ++ a2) k v = a1 ++ v :: List.tl a2.
    Proof.
      unfold put; intros ? -> ;
        rewrite !replace_nth_eqn by (rewrite ?app_length; lia).
      rewrite List.firstn_app_l by reflexivity.
      change (S ?x) with (1 + x); rewrite <- List.skipn_skipn.
      rewrite List.skipn_app_r by reflexivity.
      reflexivity.
    Qed.
  End __.

  Definition map {V V'} (f: V -> V') (a: t) :=
    List.map f a.
  Definition fold_left {V V'} (f: V' -> V -> V') (a: t) (v0: V') :=
    List.fold_left f a v0.
End ListArray.

Arguments t : clear implicits.
End ListArray.

Section with_parameters.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {memT: map.map word Byte.byte}.
  Context {localsT: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok memT}.
  Context {locals_ok : map.ok localsT}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Section GenericArray.
    Record access_info :=
      { ai_type : Type;
        ai_size : access_size.access_size;
        ai_repr : word -> ai_type -> memT -> Prop;
        ai_to_word : ai_type -> word;
        ai_to_truncated_word : ai_type -> word;
        ai_default : HasDefault ai_type;
        ai_width := Z.of_nat (@Memory.bytes_per width ai_size) }.

    (* FIXME it might be better to use Cyclic.ZModulo.ZModulo. for the 16 and 32
       cases, since it would avoid the truncation step (and it would make it
       possible to recognize which type of array we're working with
       unambiguously); otherwise currently the result of a 16 or 32-bits read
       does not match the result of the Gallina-level get function. *)

    Local Definition _access_info asize : access_info :=
      match asize with
      | access_size.one =>
          {| ai_size := asize;
             ai_type := byte;
             ai_repr := scalar8;
             ai_default := Byte.x00;
             ai_to_word v := word_of_byte v;
             ai_to_truncated_word v := word_of_byte v |}
      | access_size.two =>
          {| ai_size := asize;
             ai_type := word;
             ai_repr := scalar16;
             ai_default := word.of_Z 0;
             ai_to_word v := v;
             ai_to_truncated_word v := truncate_word access_size.two v |}
      | access_size.four =>
          {| ai_size := asize;
             ai_type := word;
             ai_repr := scalar32;
             ai_default := word.of_Z 0;
             ai_to_word v := v;
             ai_to_truncated_word v := truncate_word access_size.four v |}
      | access_size.word =>
          {| ai_size := access_size.word;
             ai_type := word;
             ai_repr := scalar;
             ai_default := word.of_Z 0;
             ai_to_word v := v;
             ai_to_truncated_word v := v |}
      end.

    Lemma ai_width_bounded a :
      0 < a.(ai_width) < 2 ^ width.
    Proof.
      unfold ai_width; destruct ai_size; simpl.
      all: try (destruct width_cases as [H|H]; rewrite H; simpl; lia).
    Qed.

    Context (sz: access_size.access_size).
    Notation ai := (_access_info sz).
    Notation V := ai.(ai_type).

    (* FIXME should this be a type class? *)
    Context
      {A K}
      (to_list: A -> list V)
      (K_to_nat: Convertible K nat)
      (get: A -> K -> V)
      (put: A -> K -> V -> A)
      (repr: word -> A -> memT -> Prop).

    Definition array_repr a_ptr a :=
      (array ai.(ai_repr) (word.of_Z ai.(ai_width)) a_ptr (to_list a)).

    Notation K_to_word x := (word.of_Z (Z.of_nat (K_to_nat x))).

    Context (a : A) (a_ptr : word) (a_expr : expr)
            (val: V) (val_expr : expr)
            (idx : K) (idx_expr : expr).

    Context
      (Hget: forall a,
         exists default,
           get a idx =
           List.hd default (List.skipn (K_to_nat idx) (to_list a)))
      (Hrw:
         Lift1Prop.iff1
           (repr a_ptr a)
           (array_repr a_ptr a)).

    Definition offset base idx width :=
      (expr.op bopname.add base (expr.op bopname.mul width idx)).

    (* FIXME this should be an expression lemma, not a statement one *)
    Lemma compile_array_get {tr mem locals functions}:
      let v := get a idx in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl : cmd}
        R (var : string),

        Z.of_nat (K_to_nat idx) < Z.of_nat (Datatypes.length (to_list a)) ->

        sep (repr a_ptr a) R mem ->
        WeakestPrecondition.dexpr mem locals a_expr a_ptr ->
        WeakestPrecondition.dexpr mem locals idx_expr (K_to_word idx) ->

        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var (ai.(ai_to_truncated_word) v);
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.set
             var
             (expr.load (ai.(ai_size))
                        (offset a_expr idx_expr (expr.literal ai.(ai_width)))))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      cbn; intros Hlt *. clear put.
      pose proof word.unsigned_range (K_to_word idx) as (Hge & _).
      destruct (Hget a) as [default Hget0].

      exists (ai.(ai_to_truncated_word) (get a idx)); split; cbn; [ | assumption ].
      eapply WeakestPrecondition_dexpr_expr; eauto.
      eapply WeakestPrecondition_dexpr_expr; eauto.
      eexists; split; [ | reflexivity ].

      seprewrite_in Hrw H0.        (* FIXME seprewrite shouldn't rename *)
      (* FIXME: BEDROCK2: Adding an extra "_" at the end shelves an inequality *)
      match goal with
      | [ H: (array_repr _ _ ⋆ _) ?mem |- _ ] =>
        unfold array_repr in *;
          seprewrite_in open_constr:(array_index_nat_inbounds
                                       _ _ (default := default) _ _ (K_to_nat idx)) H
      end.
      { lia. }

      match goal with
      | [ H: context[word.of_Z (_ * _)] |- _ ] =>
        rewrite word.ring_morph_mul, !word.of_Z_unsigned in H by assumption
      end.

      rewrite Hget0.

      clear Hget Hrw.
      destruct sz; cbv [_access_info ai_type ai_size ai_repr ai_to_truncated_word ai_width] in *.
      - eapply load_one_of_sep; ecancel_assumption.
      - eapply load_two_of_sep; ecancel_assumption.
      - eapply load_four_of_sep; ecancel_assumption.
      - eapply load_word_of_sep; ecancel_assumption.
    Qed.

    Context (Hput:
               (K_to_nat idx < List.length (to_list a))%nat ->
               to_list (put a idx val) =
               List.app
                 (List.firstn (K_to_nat idx) (to_list a))
                 (val :: List.skipn (S (K_to_nat idx)) (to_list a)))
            (Hgetput:
               (K_to_nat idx < List.length (to_list a))%nat ->
               get (put a idx val) idx = val)
            (Hrw_put:
               Lift1Prop.iff1
                 (repr a_ptr (put a idx val))
                 (array_repr a_ptr (put a idx val))).

    Definition map_step tmp_var vars f a (idx: K) :=
      (let/n tmp as tmp_var := get a idx in
       let/n tmp as tmp_var := f tmp in
       nlet vars (put a idx tmp) id).

    Definition foldl_step {A} tmp_var vars (f: A -> V -> A) bs acc (idx: K) :=
      (let/n tmp as tmp_var := get bs idx in
       nlet vars (f acc tmp) id).

    Local Lemma compile_array_put_length :
      (K_to_nat idx < Datatypes.length (to_list a))%nat ->
      (K_to_nat idx < List.length (to_list (put a idx val)))%nat.
    Proof.
      intros; rewrite Hput by assumption.
      rewrite List.app_length, List.firstn_length_le by lia.
      cbn [List.length]; rewrite List.length_skipn.
      lia.
    Qed.

    Local Lemma compile_array_put_firstn :
      (K_to_nat idx < Datatypes.length (to_list a))%nat ->
      List.firstn (K_to_nat idx) (to_list (put a idx val)) =
      List.firstn (K_to_nat idx) (to_list a).
    Proof.
      intros; rewrite Hput by lia.
      rewrite List.firstn_app.
      rewrite List.firstn_firstn, Min.min_idempotent.
      rewrite List.firstn_length_le by lia.
      rewrite Nat.sub_diag; cbn [List.firstn]; rewrite app_nil_r.
      reflexivity.
    Qed.

    Local Lemma compile_array_put_skipn :
      (K_to_nat idx < Datatypes.length (to_list a))%nat ->
      List.skipn (S (K_to_nat idx)) (to_list (put a idx val)) =
      List.skipn (S (K_to_nat idx)) (to_list a).
    Proof.
      intros; rewrite Hput by lia.
      change (val :: ?tl) with (List.app [val] tl).
      rewrite List.app_assoc, List.skipn_app, List.skipn_all, List.app_nil_l, List.skipn_skipn;
        rewrite !List.app_length, List.firstn_length_le, (Nat.add_comm _ 1) by lia.
      - rewrite Nat.sub_diag, Nat.add_0_l.
        reflexivity.
      - reflexivity.
    Qed.

    Lemma compile_array_put {tr mem locals functions} :
      let v := put a idx val in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl: cmd}
        R (var: string),

      (K_to_nat idx < Datatypes.length (to_list a))%nat ->

      sep (repr a_ptr a) R mem ->
      WeakestPrecondition.dexpr mem locals a_expr a_ptr ->
      WeakestPrecondition.dexpr mem locals idx_expr (K_to_word idx) ->
      WeakestPrecondition.dexpr mem locals val_expr (ai.(ai_to_word) val) ->

      (let v := v in
       forall mem',
         sep (repr a_ptr v) R mem' ->
         <{ Trace := tr;
            Memory := mem';
            Locals := locals;
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.store
           (ai.(ai_size))
           (offset a_expr idx_expr (expr.literal ai.(ai_width)))
           val_expr)
        k_impl
      <{ pred (nlet_eq [var] v k) }>.
    Proof.
      cbn; intros Hlt *.
      pose proof compile_array_put_length as Hputlen.
      pose proof compile_array_put_firstn as Hputfst.
      pose proof compile_array_put_skipn as Hputskp.
      pose proof word.unsigned_range (K_to_word idx) as (Hge & _).
      destruct (Hget (put a idx val)) as [default Hget0].
      eexists; split; cbn.

      { repeat (eapply WeakestPrecondition_dexpr_expr; eauto). }

      { eexists; split; cbn.
        { repeat (eapply WeakestPrecondition_dexpr_expr; eauto). }
        { seprewrite_in Hrw H0.

          match goal with
          | [ H: (array_repr _ _ ⋆ _) ?mem |- _ ] =>
            unfold array_repr in *;
              seprewrite_in open_constr:(array_index_nat_inbounds
                                           _ _ (default := default) _ _ (K_to_nat idx)) H
          end.
          { assumption. }

          match goal with
          | [ H: context[word.of_Z (_ * _)] |- _ ] =>
            rewrite word.ring_morph_mul, !word.of_Z_unsigned in H by assumption
          end.

          destruct sz;
            cbv [_access_info ai_type ai_size ai_repr ai_to_word ai_width] in *.

          1: eapply store_one_of_sep; [ ecancel_assumption | ].
          2: eapply store_two_of_sep; [ ecancel_assumption | ].
          3: eapply store_four_of_sep; [ ecancel_assumption | ].
          4: eapply store_word_of_sep; [ ecancel_assumption | ].

          all: intros m Hm; apply H4; seprewrite Hrw_put.
          all: seprewrite
                 open_constr:(array_index_nat_inbounds
                                _ _ (default := default)
                                _ _ (K_to_nat idx));
            [ apply Hputlen; assumption | ].
          all: rewrite <- Hget0, Hgetput, !Hputfst, !Hputskp by assumption.
          all: repeat rewrite word.ring_morph_mul, !word.of_Z_unsigned by lia.

          1: rewrite to_byte_of_byte_nowrap in Hm.
          all: try ecancel_assumption.
      } }
    Qed.
  End GenericArray.

  Section GenericVectorArray.
    Context (sz: access_size.access_size).
    Notation ai := (_access_info sz).

    Context {K: Type}
            {ConvNat: Convertible K nat}.

    Notation to_list := Vector.to_list.
    Notation K_to_nat idx := (cast (proj1_sig (P:=fun idx0 : K => (cast idx0 < _)%nat) idx)).
    Notation K_to_word x := (word.of_Z (Z.of_nat (K_to_nat x))).

    Notation get a idx := (VectorArray.get a (proj1_sig idx) (proj2_sig idx)).
    Notation put a idx v := (VectorArray.put a (proj1_sig idx) (proj2_sig idx) v).

    Definition vectorarray_value {n}
               (addr: word) (a: VectorArray.t ai.(ai_type) n)
      : memT -> Prop :=
      array ai.(ai_repr) (word.of_Z ai.(ai_width)) addr (to_list a).
    Notation repr := vectorarray_value.

    Lemma VectorArray_Hget {n}:
      forall (a: VectorArray.t ai.(ai_type) n) idx,
      exists default,
        get a idx =
        List.hd default (List.skipn (K_to_nat idx) (to_list a)).
    Proof.
      intros. exists ai.(ai_default).
      apply Vector_nth_hd_skipn.
      rewrite Fin.to_nat_of_nat; reflexivity.
    Qed.

    Lemma VectorArray_Hput {n} :
      forall (a : VectorArray.t ai.(ai_type) n) (idx: {idx : K | (cast idx < n)%nat}) v,
        to_list (put a idx v) =
        List.app
          (List.firstn (K_to_nat idx) (to_list a))
          (v :: List.skipn (S (K_to_nat idx)) (to_list a)).
    Proof.
      unfold put.
      destruct idx as [widx pr]; cbn [proj1_sig proj2_sig].
      unfold cast in *.
      intros.
      unfold Vector.replace_order; erewrite Vector_to_list_replace by reflexivity.
      rewrite <- replace_nth_eqn by (rewrite Vector_to_list_length; assumption).
      rewrite Fin.to_nat_of_nat; reflexivity.
    Qed.

    Lemma VectorArray_Hgetput {n} :
      forall (a : VectorArray.t ai.(ai_type) n) (idx: {idx : K | (cast idx < n)%nat}) v,
        get (put a idx v) idx = v.
    Proof.
      unfold get, put, Vector.nth_order, Vector.replace_order.
      intros; apply Vector_nth_replace.
    Qed.

    Lemma VectorArray_Hrw {n}:
      forall addr (a: VectorArray.t ai.(ai_type) n),
        Lift1Prop.iff1
          (repr addr a)
          (array_repr sz to_list addr a).
    Proof. reflexivity. Qed.

    Lemma compile_vectorarray_get {n} {tr mem locals functions}
          (a: VectorArray.t ai.(ai_type) n) (idx: K) pr:
      let v := VectorArray.get a idx pr in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R (a_ptr: word) a_expr idx_expr var,

        sep (vectorarray_value a_ptr a) R mem ->
        WeakestPrecondition.dexpr mem locals a_expr a_ptr ->
        WeakestPrecondition.dexpr mem locals idx_expr (word.of_Z (Z.of_nat (cast idx))) ->

        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var (ai.(ai_to_truncated_word) v);
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.set
             var
             (expr.load
                (ai.(ai_size))
                (offset a_expr idx_expr (expr.literal ai.(ai_width)))))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros.
      change v with
          ((fun a idx => VectorArray.get a (proj1_sig idx) (proj2_sig idx))
             a (exist (fun idx => cast idx < n)%nat idx pr)).
      eapply (compile_array_get sz to_list (fun x => K_to_nat x));
        eauto using VectorArray_Hget, VectorArray_Hrw.
      { rewrite Vector_to_list_length. simpl; lia. }
    Qed.

    Lemma compile_vectorarray_put {n} {tr mem locals functions}
          (a: VectorArray.t ai.(ai_type) n) (idx: K) pr val:
      let v := VectorArray.put a idx pr val in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R a_ptr a_expr idx_expr val_expr var,

        sep (vectorarray_value a_ptr a) R mem ->
        WeakestPrecondition.dexpr mem locals a_expr a_ptr ->
        WeakestPrecondition.dexpr mem locals idx_expr (word.of_Z (Z.of_nat (cast idx))) ->
        WeakestPrecondition.dexpr mem locals val_expr (ai.(ai_to_word) val) ->

        (let v := v in
         forall mem',
           sep (vectorarray_value a_ptr v) R mem' ->
           <{ Trace := tr;
              Memory := mem';
              Locals := locals;
              Functions := functions }>
           k_impl
           <{ pred (k v eq_refl) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.store
             (ai.(ai_size))
             (offset a_expr idx_expr (expr.literal ai.(ai_width)))
             val_expr)
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros.
      change v with
          ((fun v idx val => VectorArray.put a (proj1_sig idx) (proj2_sig idx) val)
             v (exist (fun idx => cast idx < n)%nat idx pr) val).
      eapply (compile_array_put sz
                to_list (fun x => K_to_nat x)
                (fun a idx => get a idx)
                (fun a idx v => put a idx v));
        eauto using VectorArray_Hget, VectorArray_Hrw,
        VectorArray_Hgetput, VectorArray_Hput.
      rewrite Vector_to_list_length; assumption.
    Qed.
  End GenericVectorArray.

  Section GenericListArray.
    Context (sz: access_size.access_size).
    Context {HD: HasDefault (_access_info sz).(ai_type)}.
    Notation ai := (_access_info sz).

    Context {K: Type}
            {ConvNat: Convertible K nat}.

    Notation to_list x := x (only parsing).
    Notation K_to_nat idx := (@cast _ _ ConvNat idx).
    Notation K_to_word x := (word.of_Z (Z.of_nat (K_to_nat x))).

    Notation get a idx := (ListArray.get a idx).
    Notation put a idx v := (ListArray.put a idx v).

    Definition listarray_value
               (addr: word) (a: ListArray.t ai.(ai_type))
      : memT -> Prop :=
      array ai.(ai_repr) (word.of_Z ai.(ai_width)) addr a.
    Notation repr := listarray_value.

    Lemma ListArray_Hget:
      forall (a: ListArray.t ai.(ai_type)) idx,
      exists default,
        get a idx =
        List.hd default (List.skipn (K_to_nat idx) (to_list a)).
    Proof.
      intros. exists default.
      unfold get; rewrite <- List.nth_default_eq.
      apply List.hd_skipn_nth_default.
    Qed.

    Lemma ListArray_Hput :
      forall (a : ListArray.t ai.(ai_type)) (idx: K) v,
        (K_to_nat idx < Datatypes.length a)%nat ->
        to_list (put a idx v) =
        List.app
          (List.firstn (K_to_nat idx) (to_list a))
          (v :: List.skipn (S (K_to_nat idx)) (to_list a)).
    Proof.
      unfold put; eauto using replace_nth_eqn.
    Qed.

    Lemma ListArray_Hgetput :
      forall (a : ListArray.t ai.(ai_type)) (idx: K) v,
        (K_to_nat idx < Datatypes.length a)%nat ->
        get (put a idx v) idx = v.
    Proof.
      unfold get, put.
      intros; apply nth_replace_nth; (assumption || reflexivity).
    Qed.

    Lemma ListArray_Hrw:
      forall addr a,
        Lift1Prop.iff1
          (repr addr a)
          (array_repr sz (fun x => to_list x) addr a).
    Proof. reflexivity. Qed.

    Lemma compile_unsizedlistarray_get {tr mem locals functions}
          (a: ListArray.t ai.(ai_type)) (idx: K):
      let v := ListArray.get a idx in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R (a_ptr: word) a_expr idx_expr var,

        sep (listarray_value a_ptr a) R mem ->
        WeakestPrecondition.dexpr mem locals a_expr a_ptr ->
        WeakestPrecondition.dexpr mem locals idx_expr (word.of_Z (Z.of_nat (cast idx))) ->

        Z.of_nat (cast idx) < Z.of_nat (Datatypes.length a) ->

        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var (ai.(ai_to_truncated_word) v);
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.set
             var
             (expr.load
                (ai.(ai_size))
                (offset a_expr idx_expr (expr.literal ai.(ai_width)))))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros.
      eapply (compile_array_get sz id (fun x => K_to_nat x));
        eauto using ListArray_Hget, ListArray_Hrw.
    Qed.

    Lemma compile_unsizedlistarray_put {tr mem locals functions}
          (a: ListArray.t ai.(ai_type)) (idx: K) val:
      let v := ListArray.put a idx val in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R (a_ptr: word) a_expr idx_expr val_expr var,

        sep (listarray_value a_ptr a) R mem ->
        WeakestPrecondition.dexpr mem locals a_expr a_ptr ->
        WeakestPrecondition.dexpr mem locals idx_expr (word.of_Z (Z.of_nat (cast idx))) ->
        WeakestPrecondition.dexpr mem locals val_expr (ai.(ai_to_word) val) ->

        Z.of_nat (K_to_nat idx) < Z.of_nat (List.length a) ->

        (let v := v in
         forall mem',
           sep (listarray_value a_ptr v) R mem' ->
           <{ Trace := tr;
              Memory := mem';
              Locals := locals;
              Functions := functions }>
           k_impl
           <{ pred (k v eq_refl) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.store
             (ai.(ai_size))
             (offset a_expr idx_expr (expr.literal ai.(ai_width)))
             val_expr)
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros.
      eapply (compile_array_put sz id (fun x => K_to_nat x));
        eauto using ListArray_Hget, ListArray_Hput,
        ListArray_Hgetput, ListArray_Hrw.
      unfold id; pose proof word.unsigned_range (K_to_word idx).
      lia.
    Qed.

    Notation map_step := (map_step sz ListArray.get ListArray.put).

    Lemma ListArray_map_step_ok {tmp_var vars f}:
      acts_as_replace_nth f (map_step tmp_var vars f).
    Proof.
      unfold acts_as_replace_nth, map_step, nlet, id, get, put, cast, Convertible_Z_nat.
      intros; rewrite Nat2Z.id, replace_nth_app_skip, nth_middle; reflexivity.
    Qed.

    Definition compile_listarray_map
               f (a: ListArray.t ai.(ai_type)) tmp_var vars :=
      compile_map f (map_step tmp_var vars f) a (ListArray.map f a) vars
                  ListArray_map_step_ok eq_refl.

    Notation foldl_step := (foldl_step sz ListArray.get).

    Lemma ListArray_foldl_step_ok {A} {tmp_var vars} {f: A -> _ -> A} bs:
      acts_as_foldl_step f (foldl_step tmp_var vars f bs) bs.
    Proof.
      unfold acts_as_foldl_step, foldl_step, nlet, id, get, put, cast, Convertible_Z_nat.
      eintros * ->%nth_error_nth; reflexivity.
    Qed.

    Definition compile_listarray_scalar_fold_left {A}
               (f: A -> _ -> A) (bs: ListArray.t ai.(ai_type)) a
               tmp_var vars :=
      compile_scalar_fold_left
        f (foldl_step tmp_var vars f bs) bs
        a (ListArray.fold_left f bs a) vars
        eq_refl (ListArray_foldl_step_ok bs).
  End GenericListArray.

  Section GenericSizedListArray.
    Context {sz: access_size.access_size}.
    Context {HD: HasDefault (_access_info sz).(ai_type)}.
    Notation ai := (_access_info sz).

    Context {K: Type}
            {ConvNat: Convertible K nat}.

    Notation to_list x := x (only parsing).
    Notation K_to_nat idx := (@cast _ _ ConvNat idx).
    Notation K_to_word x := (word.of_Z (Z.of_nat (K_to_nat x))).

    Notation get a idx := (ListArray.get a idx).
    Notation put a idx v := (ListArray.put a idx v).

    Definition sizedlistarray_value
               (len: nat) (addr: word) (a: ListArray.t ai.(ai_type))
      : memT -> Prop :=
      sep (emp (List.length a = len))
          (listarray_value sz addr a).

    Lemma sizedlistarray_value_of_array {len addr a mem} :
      List.length a = len ->
      listarray_value sz addr a mem ->
      sizedlistarray_value len addr a mem.
    Proof. intros; apply sep_emp_l; eauto. Qed.

    Lemma array_of_sizedlistarray_value {len addr a mem} :
      sizedlistarray_value len addr a mem ->
      listarray_value sz addr a mem.
    Proof. intros H; apply sep_emp_l in H; intuition. Qed.

    Lemma length_of_sizedlistarray_value {len addr a mem} :
      sizedlistarray_value len addr a mem ->
      List.length a = len.
    Proof. intros H; apply sep_emp_l in H; intuition. Qed.

    Lemma length_of_sizedlistarray_value_R {len addr a R mem} :
      (sizedlistarray_value len addr a ⋆ R) mem ->
      List.length a = len.
    Proof.
      intros (?&?&H); decompose [and] H.
      eauto using length_of_sizedlistarray_value.
    Qed.

    Lemma sizedlistarray_value_max_length {len addr a R mem} :
      (sizedlistarray_value len addr a ⋆ R) mem ->
      (ai_width ai) * Z.of_nat len <= 2 ^ width.
    Proof.
      pose proof ai_width_bounded ai.
      intros * (<- & Hmem)%sep_assoc%sep_emp_l.
      etransitivity; [ | eapply array_max_length ]; eauto.
      - rewrite word.unsigned_of_Z_nowrap by lia; reflexivity.
      - destruct sz; apply scalar8_no_aliasing || apply scalar_no_aliasing1.
      - rewrite word.unsigned_of_Z_nowrap; lia.
    Qed.

    Lemma sizedlistarray_value_app1_length {len addr a1 a2 R mem} :
      (sizedlistarray_value len addr (a1 ++ a2) ⋆ R) mem ->
      (length a1 = len - length a2)%nat.
    Proof.
      intros * Hmem.
      apply length_of_sizedlistarray_value_R in Hmem.
      rewrite app_length in Hmem; lia.
    Qed.

    Notation repr := sizedlistarray_value.

    Lemma SizedListArray_Hrw:
      forall len addr (a: ListArray.t ai.(ai_type)),
        List.length a = len ->
        Lift1Prop.iff1
          (repr len addr a)
          (array_repr sz (fun x => to_list x) addr a).
    Proof.
      unfold sizedlistarray_value.
      red; intros; rewrite sep_emp_l; tauto.
    Qed.

    Lemma SizedListArray_length :
      forall len addr (a: ListArray.t ai.(ai_type)) mem R,
        (repr len addr a * R)%sep mem -> List.length a = len.
    Proof.
      intros * H; unfold repr in H.
      eapply proj1. apply sep_emp_l with (m := mem).
      ecancel_assumption.
    Qed.

    Lemma compile_sizedlistarray_get {len} {tr mem locals functions}
          (a: ListArray.t ai.(ai_type)) (idx: K):
      let v := ListArray.get a idx in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R (a_ptr: word) a_expr idx_expr var,

        sep (sizedlistarray_value len a_ptr a) R mem ->
        WeakestPrecondition.dexpr mem locals a_expr a_ptr ->
        WeakestPrecondition.dexpr mem locals idx_expr (word.of_Z (Z.of_nat (cast idx))) ->

        Z.of_nat (cast idx) < Z.of_nat len ->

        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var (ai.(ai_to_truncated_word) v);
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.set
             var
             (expr.load
                (ai.(ai_size))
                (offset a_expr idx_expr (expr.literal ai.(ai_width)))))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros.
      eapply (compile_array_get sz id (fun x => K_to_nat idx) _ (fun (addr: word) a => repr len addr a));
        eauto using ListArray_Hget.
      - eapply SizedListArray_Hrw, SizedListArray_length.
        eassumption.
      - unfold id.
        erewrite SizedListArray_length by eassumption.
        assumption.
    Qed.

    Lemma compile_sizedlistarray_put {len} {tr mem locals functions}
          (a: ListArray.t ai.(ai_type)) (idx: K) val:
      let v := ListArray.put a idx val in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R (a_ptr: word) a_expr idx_expr val_expr var,

        sep (sizedlistarray_value len a_ptr a) R mem ->
        WeakestPrecondition.dexpr mem locals a_expr a_ptr ->
        WeakestPrecondition.dexpr mem locals idx_expr (word.of_Z (Z.of_nat (cast idx))) ->
        WeakestPrecondition.dexpr mem locals val_expr (ai.(ai_to_word) val) ->

        Z.of_nat (cast idx) < Z.of_nat len ->

        (let v := v in
         forall mem',
           sep (sizedlistarray_value len a_ptr v) R mem' ->
           <{ Trace := tr;
              Memory := mem';
              Locals := locals;
              Functions := functions }>
           k_impl
           <{ pred (k v eq_refl) }>) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd.store
             (ai.(ai_size))
             (offset a_expr idx_expr (expr.literal ai.(ai_width)))
             val_expr)
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros.
      eapply (compile_array_put sz id (fun x => K_to_nat x) _ _ (fun (addr: word) a => repr len addr a));
        eauto using ListArray_Hget, ListArray_Hput,
        ListArray_Hgetput.
      - eapply SizedListArray_Hrw, SizedListArray_length.
        eassumption.
      - eapply SizedListArray_Hrw.
        unfold id; rewrite ListArray.put_length.
        eapply SizedListArray_length.
        eassumption.
      - unfold id.
        erewrite SizedListArray_length by eassumption.
        lia.
    Qed.
  End GenericSizedListArray.

  Ltac prepare_array_lemma lemma sz := (* This makes [simple apply] work *)
    pose (lemma sz) as lem;
    cbv beta iota delta [_access_info ai_type ai_repr ai_to_word ai_to_truncated_word ai_width ai_size
                            map_step foldl_step]
      in (type of lem);
    change (let ai_width := _ in ?x) with x in (type of lem);
    cbv beta in (type of lem);
    let t := type of lem in
    exact (lem: t).

  Notation prepare_array_lemma lemma sz :=
    ltac:(prepare_array_lemma lemma sz) (only parsing).

  Definition compile_byte_vectorarray_get :=
    prepare_array_lemma (@compile_vectorarray_get) access_size.one.
  Definition compile_w16_vectorarray_get :=
    prepare_array_lemma (@compile_vectorarray_get) access_size.two.
  Definition compile_w32_vectorarray_get :=
    prepare_array_lemma (@compile_vectorarray_get) access_size.four.
  Definition compile_word_vectorarray_get :=
    prepare_array_lemma (@compile_vectorarray_get) access_size.word.
  Definition compile_byte_vectorarray_put :=
    prepare_array_lemma (@compile_vectorarray_put) access_size.one.
  Definition compile_w16_vectorarray_put :=
    prepare_array_lemma (@compile_vectorarray_put) access_size.two.
  Definition compile_w32_vectorarray_put :=
    prepare_array_lemma (@compile_vectorarray_put) access_size.four.
  Definition compile_word_vectorarray_put :=
    prepare_array_lemma (@compile_vectorarray_put) access_size.word.

  Definition compile_byte_unsizedlistarray_get :=
    prepare_array_lemma (@compile_unsizedlistarray_get) access_size.one.
  Definition compile_w16_unsizedlistarray_get :=
    prepare_array_lemma (@compile_unsizedlistarray_get) access_size.two.
  Definition compile_w32_unsizedlistarray_get :=
    prepare_array_lemma (@compile_unsizedlistarray_get) access_size.four.
  Definition compile_word_unsizedlistarray_get :=
    prepare_array_lemma (@compile_unsizedlistarray_get) access_size.word.
  Definition compile_byte_unsizedlistarray_put :=
    prepare_array_lemma (@compile_unsizedlistarray_put) access_size.one.
  Definition compile_w16_unsizedlistarray_put :=
    prepare_array_lemma (@compile_unsizedlistarray_put) access_size.two.
  Definition compile_w32_unsizedlistarray_put :=
    prepare_array_lemma (@compile_unsizedlistarray_put) access_size.four.
  Definition compile_word_unsizedlistarray_put :=
    prepare_array_lemma (@compile_unsizedlistarray_put) access_size.word.

  Definition compile_byte_sizedlistarray_get :=
    prepare_array_lemma (@compile_sizedlistarray_get) access_size.one.
  Definition compile_w16_sizedlistarray_get :=
    prepare_array_lemma (@compile_sizedlistarray_get) access_size.two.
  Definition compile_w32_sizedlistarray_get :=
    prepare_array_lemma (@compile_sizedlistarray_get) access_size.four.
  Definition compile_word_sizedlistarray_get :=
    prepare_array_lemma (@compile_sizedlistarray_get) access_size.word.
  Definition compile_byte_sizedlistarray_put :=
    prepare_array_lemma (@compile_sizedlistarray_put) access_size.one.
  Definition compile_w16_sizedlistarray_put :=
    prepare_array_lemma (@compile_sizedlistarray_put) access_size.two.
  Definition compile_w32_sizedlistarray_put :=
    prepare_array_lemma (@compile_sizedlistarray_put) access_size.four.
  Definition compile_word_sizedlistarray_put :=
    prepare_array_lemma (@compile_sizedlistarray_put) access_size.word.

  Definition compile_byte_listarray_map :=
    prepare_array_lemma (@compile_listarray_map) access_size.one.
  Definition compile_w16_listarray_map :=
    prepare_array_lemma (@compile_listarray_map) access_size.two.
  Definition compile_w32_listarray_map :=
    prepare_array_lemma (@compile_listarray_map) access_size.four.
  Definition compile_word_listarray_map :=
    prepare_array_lemma (@compile_listarray_map) access_size.word.

  Definition compile_byte_listarray_scalar_fold_left :=
    prepare_array_lemma (@compile_listarray_scalar_fold_left) access_size.one.
  Definition compile_w16_listarray_scalar_fold_left :=
    prepare_array_lemma (@compile_listarray_scalar_fold_left) access_size.two.
  Definition compile_w32_listarray_scalar_fold_left :=
    prepare_array_lemma (@compile_listarray_scalar_fold_left) access_size.four.
  Definition compile_word_listarray_scalar_fold_left :=
    prepare_array_lemma (@compile_listarray_scalar_fold_left) access_size.word.
End with_parameters.

Arguments sizedlistarray_value {width word memT} sz len addr a _ : assert.
Arguments Arrays._access_info /.
Arguments Arrays.ai_width /.

Import Rupicola.Lib.Invariants Rupicola.Lib.Gensym.

Ltac _compile_map locals to thm :=
  let idx_v := gensym locals "from" in
  let tmp_v := gensym locals "tmp" in
  let to_v := gensym locals "to" in
  let lp := infer_ranged_for_predicate idx_v to_v to in
  eapply thm with (idx_var := idx_v) (to_var := to_v)
                  (tmp_var := tmp_v) (loop_pred := lp).

Ltac compile_map :=
  lazymatch goal with
  | [ |- WeakestPrecondition.cmd _ _ _ _ ?locals (_ (nlet_eq _ ?v _)) ] =>
      lazymatch v with
      | (ListArray.map (V := Init.Byte.byte) _ ?l) =>
          _compile_map locals (Z.of_nat (List.length l)) compile_byte_listarray_map
      | (ListArray.map (V := @word.rep _ _) _ ?l) =>
          _compile_map locals (Z.of_nat (List.length l)) compile_word_listarray_map
      end
  end.

Ltac _compile_scalar_fold_left locals to thm :=
  let idx_v := gensym locals "from" in
  let tmp_v := gensym locals "tmp" in
  let to_v := gensym locals "to" in
  let lp := infer_ranged_for_predicate idx_v to_v to in
  eapply thm with (idx_var := idx_v) (to_var := to_v)
                  (tmp_var := tmp_v) (loop_pred := lp).

Ltac compile_fold_left :=
  lazymatch goal with
  | [ |- WeakestPrecondition.cmd _ _ _ _ ?locals (_ (nlet_eq _ ?v _)) ] =>
      lazymatch v with
      | (ListArray.fold_left (V := Init.Byte.byte) _ ?l _) =>
          _compile_scalar_fold_left
            locals (Z.of_nat (List.length l))
            compile_byte_listarray_scalar_fold_left
      | (ListArray.fold_left (V := @word.rep _ _) _ ?l _) =>
          _compile_scalar_fold_left
            locals (Z.of_nat (List.length l))
            compile_word_listarray_scalar_fold_left
      end
  end.

Module VectorArrayCompiler.
  #[export] Hint Extern 1 (WP_nlet_eq (VectorArray.get _ _ _)) =>
    simple eapply (@compile_byte_vectorarray_get); shelve : compiler.
  #[export] Hint Extern 1 (WP_nlet_eq (VectorArray.get _ _ _)) =>
    simple eapply (@compile_word_vectorarray_get); shelve : compiler.
  #[export] Hint Extern 1 (WP_nlet_eq (VectorArray.put _ _ _ _)) =>
    simple eapply (@compile_byte_vectorarray_put); shelve : compiler.
  #[export] Hint Extern 1 (WP_nlet_eq (VectorArray.put _ _ _ _)) =>
    simple eapply (@compile_word_vectorarray_put); shelve : compiler.
End VectorArrayCompiler.

Module UnsizedListArrayCompiler.
  #[export] Hint Extern 1 (WP_nlet_eq (ListArray.get _ _)) =>
    simple eapply (@compile_byte_unsizedlistarray_get); shelve : compiler.
  #[export] Hint Extern 1 (WP_nlet_eq (ListArray.get _ _)) =>
    simple eapply (@compile_word_unsizedlistarray_get); shelve : compiler.
  #[export] Hint Extern 1 (WP_nlet_eq (ListArray.put _ _ _)) =>
    simple eapply (@compile_byte_unsizedlistarray_put); shelve : compiler.
  #[export] Hint Extern 1 (WP_nlet_eq (ListArray.put _ _ _)) =>
    simple eapply (@compile_word_unsizedlistarray_put); shelve : compiler.
  #[export] Hint Extern 1 (WP_nlet_eq (ListArray.map _ _)) =>
    compile_map; shelve : compiler.
  #[export] Hint Extern 1 (WP_nlet_eq (ListArray.fold_left _ _ _)) =>
    compile_fold_left; shelve : compiler.
End UnsizedListArrayCompiler.

Module SizedListArrayCompiler.
  #[export] Hint Extern 1 (WP_nlet_eq (ListArray.get _ _)) =>
    simple eapply (@compile_byte_sizedlistarray_get); shelve : compiler.
  #[export] Hint Extern 1 (WP_nlet_eq (ListArray.get _ _)) =>
    simple eapply (@compile_word_sizedlistarray_get); shelve : compiler.
  #[export] Hint Extern 1 (WP_nlet_eq (ListArray.put _ _ _)) =>
    simple eapply (@compile_byte_sizedlistarray_put); shelve : compiler.
  #[export] Hint Extern 1 (WP_nlet_eq (ListArray.put _ _ _)) =>
    simple eapply (@compile_word_sizedlistarray_put); shelve : compiler.
  #[export] Hint Extern 1 (WP_nlet_eq (ListArray.map _ _)) =>
    compile_map; shelve : compiler.
  #[export] Hint Extern 1 (WP_nlet_eq (ListArray.fold_left _ _ _)) =>
    compile_fold_left; shelve : compiler.
End SizedListArrayCompiler.

Module AccessSizeCompatibilityNotations.
  Notation AccessByte := access_size.one (only parsing).
  Notation AccessWord := access_size.word (only parsing).
End AccessSizeCompatibilityNotations.

Export AccessSizeCompatibilityNotations.

Export VectorArrayCompiler.
(* UnsizedListArrayCompiler and SizedListArrayCompiler conflict, so don't export them. *)
