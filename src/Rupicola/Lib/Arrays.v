From Coq Require Vector List.
Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.
(* Require Import Arith PeanoNat. *)

Class HasDefault (T: Type) := default: T.
Instance HasDefault_byte : HasDefault byte := Byte.x00.

Class Convertible (T1 T2: Type) := cast: T1 -> T2.
Instance Convertible_self {A}: Convertible A A := id.

Open Scope list_scope.

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

    Lemma put_0 (a: list V) (k: K) (v: V) :
      0 < length a -> cast k = 0 ->
      put a k v = v :: List.tl a.
    Proof.
      unfold put; intros ? ->.
      destruct a; simpl in *; reflexivity || lia.
    Qed.

    Lemma put_app_len (a1 a2: list V) (k: K) (v: V) :
      0 < length a2 -> cast k = length a1 ->
      put (a1 ++ a2) k v = a1 ++ v :: List.tl a2.
    Proof.
      unfold put; intros ? -> ;
        rewrite !replace_nth_eqn by (rewrite ?app_length; lia).
      rewrite List_firstn_app_l by reflexivity.
      change (S ?x) with (1 + x); rewrite <- List.skipn_skipn.
      rewrite List_skipn_app_r by reflexivity.
      reflexivity.
    Qed.
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
  Open Scope Z_scope.

  Section GenericArray.
    (* No 16 or 32 to avoid depending on two more word instances. *)
    Inductive AccessSize := AccessByte | AccessWord.

    Record access_info :=
      { ai_type : Type;
        ai_size : access_size.access_size;
        ai_repr : word -> ai_type -> memT -> Prop;
        ai_to_word : ai_type -> word;
        ai_default : HasDefault ai_type;
        ai_width := Z.of_nat (@Memory.bytes_per width ai_size) }.

    Local Definition _access_info asize :=
      match asize with
      | AccessByte => {| ai_size := access_size.one;
                        ai_type := byte;
                        ai_repr := scalar8;
                        ai_default := Byte.x00;
                        ai_to_word v := word_of_byte v |}
      | AccessWord => {| ai_size := access_size.word;
                        ai_type := word;
                        ai_repr := scalar;
                        ai_default := word.of_Z 0;
                        ai_to_word v := v |}
      end.

    (* Definition awidth {T} `{ak: access_kind T} : Z := *)
    (*   Z.of_nat (@Memory.bytes_per Semantics.width a_size). *)

    Context (sz: AccessSize).
    Notation ai := (_access_info sz).
    Notation V := ai.(ai_type).

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
            Locals := map.put locals var (ai.(ai_to_word) v);
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
      cbn; intros Hlt *.
      pose proof word.unsigned_range (K_to_word idx) as (Hge & _).
      destruct (Hget a) as [default Hget0].

      exists (ai.(ai_to_word) (get a idx)); split; cbn; [ | assumption ].
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

      clear put Hget Hrw.
      destruct sz; cbv [_access_info ai_type ai_size ai_repr ai_to_word ai_width] in *.
      - eapply load_one_of_sep; ecancel_assumption.
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
          2: eapply store_word_of_sep; [ ecancel_assumption | ].

          all: intros m Hm; apply H4; seprewrite Hrw_put.
          all: seprewrite
                 open_constr:(array_index_nat_inbounds
                                _ _ (default := default)
                                _ _ (K_to_nat idx));
            [ apply Hputlen; assumption | ].
          all: rewrite <- Hget0, Hgetput, !Hputfst, !Hputskp by assumption.
          all: repeat rewrite word.ring_morph_mul, !word.of_Z_unsigned by lia.

          1: rewrite to_byte_of_byte_nowrap in Hm.
          all: try ecancel_assumption. } }
    Qed.
  End GenericArray.

  Section GenericVectorArray.
    Context (sz: AccessSize).
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
            Locals := map.put locals var (ai.(ai_to_word) v);
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
    Context (sz: AccessSize).
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
            Locals := map.put locals var (ai.(ai_to_word) v);
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
  End GenericListArray.

  Section GenericSizedListArray.
    Context {sz: AccessSize}.
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
            Locals := map.put locals var (ai.(ai_to_word) v);
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
    cbv beta iota delta [_access_info ai_type ai_repr ai_to_word ai_width ai_size] in (type of lem);
    change (let ai_width := _ in ?x) with x in (type of lem);
    cbv beta in (type of lem);
    let t := type of lem in
    exact (lem: t).

  Notation prepare_array_lemma lemma sz :=
    ltac:(prepare_array_lemma lemma sz) (only parsing).

  Definition compile_byte_vectorarray_get :=
    prepare_array_lemma (@compile_vectorarray_get) AccessByte.
  Definition compile_word_vectorarray_get :=
    prepare_array_lemma (@compile_vectorarray_get) AccessWord.
  Definition compile_byte_vectorarray_put :=
    prepare_array_lemma (@compile_vectorarray_put) AccessByte.
  Definition compile_word_vectorarray_put :=
    prepare_array_lemma (@compile_vectorarray_put) AccessWord.

  Definition compile_byte_unsizedlistarray_get :=
    prepare_array_lemma (@compile_unsizedlistarray_get) AccessByte.
  Definition compile_word_unsizedlistarray_get :=
    prepare_array_lemma (@compile_unsizedlistarray_get) AccessWord.
  Definition compile_byte_unsizedlistarray_put :=
    prepare_array_lemma (@compile_unsizedlistarray_put) AccessByte.
  Definition compile_word_unsizedlistarray_put :=
    prepare_array_lemma (@compile_unsizedlistarray_put) AccessWord.

  Definition compile_byte_sizedlistarray_get :=
    prepare_array_lemma (@compile_sizedlistarray_get) AccessByte.
  Definition compile_word_sizedlistarray_get :=
    prepare_array_lemma (@compile_sizedlistarray_get) AccessWord.
  Definition compile_byte_sizedlistarray_put :=
    prepare_array_lemma (@compile_sizedlistarray_put) AccessByte.
  Definition compile_word_sizedlistarray_put :=
    prepare_array_lemma (@compile_sizedlistarray_put) AccessWord.
End with_parameters.

Arguments sizedlistarray_value {width word memT} sz len addr a _ : assert.
Arguments Arrays._access_info /.
Arguments Arrays.ai_width /.

Ltac cbn_array :=
  cbn [Arrays._access_info
         ai_type ai_size ai_repr ai_to_word ai_width
         Memory.bytes_per] in *;
  change (Z.of_nat 1%nat) with (1%Z) in *;
  change (Z.of_nat 2%nat) with (2%Z) in *;
  change (Z.of_nat 4%nat) with (4%Z) in *;
  change (Z.of_nat 8%nat) with (8%Z) in *.

Instance Convertible_word_nat {width : Z} {word : word width} : Convertible word nat :=
  fun w => Z.to_nat (word.unsigned w).

#[export] Hint Unfold cast : compiler_cleanup.
#[export] Hint Unfold Convertible_word_nat : compiler_cleanup.

Module VectorArrayCompiler.
  #[export] Hint Extern 1 => simple eapply (@compile_byte_vectorarray_get); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@compile_word_vectorarray_get); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@compile_byte_vectorarray_put); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@compile_word_vectorarray_put); shelve : compiler.
End VectorArrayCompiler.

Module UnsizedListArrayCompiler.
  #[export] Hint Extern 1 => simple eapply (@compile_byte_unsizedlistarray_get); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@compile_word_unsizedlistarray_get); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@compile_byte_unsizedlistarray_put); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@compile_word_unsizedlistarray_put); shelve : compiler.
End UnsizedListArrayCompiler.

Module SizedListArrayCompiler.
  #[export] Hint Extern 1 => simple eapply (@compile_byte_sizedlistarray_get); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@compile_word_sizedlistarray_get); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@compile_byte_sizedlistarray_put); shelve : compiler.
  #[export] Hint Extern 1 => simple eapply (@compile_word_sizedlistarray_put); shelve : compiler.
End SizedListArrayCompiler.

Export VectorArrayCompiler.
(* UnsizedListArrayCompiler and SizedListArrayCompiler conflict, so don't export them. *)
