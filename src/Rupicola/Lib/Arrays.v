From Coq Require Vector List.
Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.
(* Require Import Arith PeanoNat. *)

Class HasDefault (T: Type) := default: T.

Class Convertible (T1 T2: Type) := cast: T1 -> T2.

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

Section with_parameters.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.

  Open Scope Z_scope.

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

    Lemma compile_word_array_get {tr mem locals functions}:
      let v := get a idx in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl : cmd}
        R (var : string),

        (Z.to_nat (word.unsigned (to_word idx)) < Datatypes.length (to_list a))%nat ->

        sep (repr a_ptr a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some (to_word idx) ->

        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var v;
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
                access_size.word
                (expr.op bopname.add
                         (expr.var a_var)
                         (expr.op bopname.mul
                                  (expr.literal (Memory.bytes_per_word Semantics.width))
                                  (expr.var idx_var)))))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      cbn; intros Hlt *.
      pose proof word.unsigned_range (to_word idx) as (Hge & _).
      destruct (Hget a) as [default Hget0].

      exists (get a idx); split; cbn; [ | assumption ].
      exists a_ptr; split; [ eassumption | ]; cbn.
      exists (to_word idx); split; [ eassumption | ]; cbn.
      eexists; split; [ | reflexivity ].

      eapply load_word_of_sep.
      seprewrite_in Hrw H0.        (* FIXME seprewrite shouldn't rename *)
      (* FIXME: BEDROCK2: Adding an extra "_" at the end shelves an inequality *)
      once (seprewrite_in open_constr:(array_index_nat_inbounds
                                         _ _ _ _ (Z.to_nat (word.unsigned (to_word idx)))) H5).
      { assumption. }

      rewrite word.ring_morph_mul, Z2Nat.id, !word.of_Z_unsigned in H4 by assumption.
      rewrite Hget0.
      ecancel_assumption.
    Qed.

    Lemma compile_word_array_put {tr mem locals functions} :
      let v := put a idx val in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl: cmd}
        R (var: string),

      (Z.to_nat (word.unsigned (to_word idx)) < Datatypes.length (to_list a))%nat ->

      sep (repr a_ptr a) R mem ->
      map.get locals a_var = Some a_ptr ->
      map.get locals idx_var = Some (to_word idx) ->
      map.get locals val_var = Some val ->

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
           access_size.word
           (expr.op bopname.add
                    (expr.var a_var)
                    (expr.op bopname.mul
                             (expr.literal (Memory.bytes_per_word Semantics.width))
                             (expr.var idx_var)))
           (expr.var val_var))
        k_impl
      <{ pred (nlet_eq [var] v k) }>.
    Proof.
      cbn; intros Hlt *.
      pose proof word.unsigned_range (to_word idx) as (Hge & _).
      destruct (Hget (put a idx val)) as [default Hget0].
      eexists; split; cbn.

      { eexists; split; [ eassumption | ]; cbn.
        eexists; split; [ eassumption | reflexivity ]. }

      { eexists; split; cbn.
        { eexists; split; [ eassumption | reflexivity ]. }
        { seprewrite_in Hrw H0.
          once (seprewrite_in
                  open_constr:(array_index_nat_inbounds
                                 _ _ (default := default) _ _ (Z.to_nat (word.unsigned (to_word idx)))) H6).
          { assumption. }

          eapply store_word_of_sep.
          { rewrite word.ring_morph_mul, Z2Nat.id, !word.of_Z_unsigned in H5 by assumption.
            ecancel_assumption. }
          { intros m Hm.
            apply H4.
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

    Lemma compile_word_vectorarray_get {n} {tr mem locals functions}
          (a: VectorArray.t word n) idx pr:
      let v := VectorArray.get a idx pr in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R (a_ptr: address) a_var idx_var var,

        sep (word_vectorarray_value a_ptr a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some idx ->

        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var v;
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
                access_size.word
                (expr.op bopname.add
                         (expr.var a_var)
                         (expr.op bopname.mul
                                  (expr.literal (Memory.bytes_per_word Semantics.width))
                                  (expr.var idx_var)))))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
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

    Lemma compile_word_vectorarray_put {n} {tr mem locals functions}
          (a: VectorArray.t word n) idx pr val:
      let v := VectorArray.put a idx pr val in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R a_ptr a_var idx_var val_var var,

        sep (word_vectorarray_value a_ptr a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some idx ->
        map.get locals val_var = Some val ->

        (let v := v in
         forall mem',
           sep (word_vectorarray_value a_ptr v) R mem' ->
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
             access_size.word
             (expr.op bopname.add
                      (expr.var a_var)
                      (expr.op bopname.mul
                               (expr.literal (Memory.bytes_per_word Semantics.width))
                               (expr.var idx_var)))
             (expr.var val_var))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros.
      change v with
          ((fun v idx val => VectorArray.put a (proj1_sig idx) (proj2_sig idx) val)
             v (exist (fun idx => cast idx < n)%nat idx pr) val).
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
    Notation to_list x := x (only parsing).
    Notation to_word x := x (only parsing).
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

    Lemma compile_word_unsizedlistarray_get {tr mem locals functions}
          (a: ListArray.t word) idx:
      let v := ListArray.get a idx in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R (a_ptr: address) a_var idx_var var,

        sep (word_listarray_value a_ptr a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some idx ->

        word.unsigned idx < Z.of_nat (Datatypes.length (id a)) ->

        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var v;
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
                access_size.word
                (expr.op bopname.add
                         (expr.var a_var)
                         (expr.op bopname.mul
                                  (expr.literal (Memory.bytes_per_word Semantics.width))
                                  (expr.var idx_var)))))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros.
      eapply (compile_word_array_get id id);
        eauto using WordListArray_Hget, WordListArray_Hrw.
      pose proof word.unsigned_range idx.
      unfold id in *; lia.
    Qed.

    Lemma compile_word_unsizedlistarray_put {tr mem locals functions}
          (a: ListArray.t word) idx val:
      let v := ListArray.put a idx val in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R (a_ptr: address) a_var idx_var val_var var,

        sep (word_listarray_value a_ptr a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some idx ->
        map.get locals val_var = Some val ->

        (word.unsigned idx < Z.of_nat (List.length a))%Z ->

        (let v := v in
         forall mem',
           sep (word_listarray_value a_ptr v) R mem' ->
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
             access_size.word
             (expr.op bopname.add
                      (expr.var a_var)
                      (expr.op bopname.mul
                               (expr.literal (Memory.bytes_per_word Semantics.width))
                               (expr.var idx_var)))
             (expr.var val_var))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
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
    Notation to_list x := x (only parsing).
    Notation to_word x := x (only parsing).
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
    Proof.
      unfold word_sizedlistarray_value.
      red; intros; rewrite sep_emp_l; tauto.
    Qed.

    Lemma WordSizedListArray_length :
      forall addr sz (a: ListArray.t word) mem R,
        (repr addr sz a * R)%sep mem -> List.length a = sz.
    Proof.
      intros * H; unfold repr in H.
      eapply proj1. apply sep_emp_l with (m := mem).
      ecancel_assumption.
    Qed.

    Lemma compile_word_sizedlistarray_get {sz} {tr mem locals functions}
          (a: ListArray.t word) idx:
      let v := ListArray.get a idx in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R (a_ptr: address) a_var idx_var var,

        sep (word_sizedlistarray_value a_ptr sz a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some idx ->

        word.unsigned idx < Z.of_nat sz ->

        (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var v;
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
                access_size.word
                (expr.op bopname.add
                         (expr.var a_var)
                         (expr.op bopname.mul
                                  (expr.literal (Memory.bytes_per_word Semantics.width))
                                  (expr.var idx_var)))))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
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

    Lemma compile_word_sizedlistarray_put {sz} {tr mem locals functions}
          (a: ListArray.t word) idx val:
      let v := ListArray.put a idx val in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
        R (a_ptr: address) a_var idx_var val_var var,

        sep (word_sizedlistarray_value a_ptr sz a) R mem ->
        map.get locals a_var = Some a_ptr ->
        map.get locals idx_var = Some idx ->
        map.get locals val_var = Some val ->

        (word.unsigned idx < Z.of_nat sz)%Z ->

        (let v := v in
         forall mem',
           sep (word_sizedlistarray_value a_ptr sz v) R mem' ->
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
             access_size.word
             (expr.op bopname.add
                      (expr.var a_var)
                      (expr.op bopname.mul
                               (expr.literal (Memory.bytes_per_word Semantics.width))
                               (expr.var idx_var)))
             (expr.var val_var))
          k_impl
        <{ pred (nlet_eq [var] v k) }>.
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
End with_parameters.

Module VectorArrayCompiler.
  Hint Extern 1 => simple eapply @compile_word_vectorarray_get; shelve : compiler.
  Hint Extern 1 => simple eapply @compile_word_vectorarray_put; shelve : compiler.
End VectorArrayCompiler.

Module UnsizedListArrayCompiler.
  Hint Extern 1 => simple eapply @compile_word_unsizedlistarray_get; shelve : compiler.
  Hint Extern 1 => simple eapply @compile_word_unsizedlistarray_put; shelve : compiler.
End UnsizedListArrayCompiler.

Module SizedListArrayCompiler.
  Hint Extern 1 => simple eapply @compile_word_sizedlistarray_get; shelve : compiler.
  Hint Extern 1 => simple eapply @compile_word_sizedlistarray_put; shelve : compiler.
End SizedListArrayCompiler.

Export VectorArrayCompiler.
(* UnsizedListArrayCompiler and SizedListArrayCompiler conflict, so don't export them. *)
