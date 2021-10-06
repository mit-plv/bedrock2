Require Import Rupicola.Lib.Api.

Section Gallina.
  Definition linkedlist A : Type := list A.

  Definition ll_hd {A} : A -> linkedlist A -> A := hd.

  Definition ll_next {A} : linkedlist A -> linkedlist A := tl.
End Gallina.

Section Separation.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {element : Type} {element_size : access_size}
          {Element : word -> element -> mem -> Prop}.

  Local Notation element_size_in_bytes :=
    (@Memory.bytes_per width element_size).
  Local Notation skip_element :=
    (fun p : word =>
       word.add p (word.of_Z (Z.of_nat element_size_in_bytes))).

  (* To have a LinkedList with elements inline, instantiate Element with
     something like [scalar] or [ptsto], and set the element_size to word or one
     respectively.

     To have a LinkedList that holds pointers to its elements, set the
     element_size to word and give Element an indirection. For example, to do a
     LinkedList of scalars but with pointer-indirection, do:

     element := word
     Element := (fun (p : address) (x : word) =>
                  Lift1Prop.ex1
                    (fun px : address =>
                      (scalar p px * scalar px x)%sep)) *)
  Fixpoint LinkedList (end_ptr pl : word) (l : list element)
    : mem -> Prop :=
    match l with
    | [] => emp (pl = end_ptr)
    | e :: l' =>
      Lift1Prop.ex1
        (fun pl' =>
           (Element pl e
            * scalar (skip_element pl) pl'
            * LinkedList end_ptr pl' l')%sep)
    end.
End Separation.

Section Compile.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  (* TODO: generalize
  Context {element : Type}
          {Element : address -> element -> Semantics.mem -> Prop}.
  Context {element_eqb : element -> element -> bool}
          {element_eqb_spec :
             forall x y : element,
               BoolSpec (x = y) (x <> y) (element_eqb x y)}.
  Local Notation LinkedList :=
    (@LinkedList semantics element Element).
   *)
  Local Notation LinkedList :=
    (@LinkedList _ word mem word access_size.word scalar) (only parsing).
  Local Notation word_size_in_bytes :=
    (@Memory.bytes_per width access_size.word).
  Local Notation next_word :=
    (fun p : word =>
       word.add p (word.of_Z (Z.of_nat word_size_in_bytes))).

  (* TODO: these should probably use Owned/Reserved/Borrowed annotations *)

  Lemma compile_ll_hd : forall {tr mem locals functions} d ll,
    let v := ll_hd d ll in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      R end_ptr ll_expr ll_ptr ll'_ptr var,

      (scalar ll_ptr (ll_hd d ll)
       * scalar (next_word ll_ptr) ll'_ptr
       * LinkedList end_ptr ll'_ptr (ll_next ll)
       * R)%sep mem ->

      WeakestPrecondition.dexpr mem locals ll_expr ll_ptr ->

      (let v := v in
       forall m,
         let ll' := ll_next ll in
         (scalar ll_ptr v
          * scalar (next_word ll_ptr) ll'_ptr
          * LinkedList end_ptr ll'_ptr ll'
          * R)%sep m ->
         <{ Trace := tr;
            Memory := m;
            Locals := map.put locals var v;
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq (cmd.set var (expr.load access_size.word ll_expr)) k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof.
    cbn [LinkedList ll_hd hd]; intros.
    sepsimpl. repeat straightline'.
    eexists; split; repeat straightline.
    eapply WeakestPrecondition_dexpr_expr; eauto.
    all: repeat straightline'.
    use_hyp_with_matching_cmd; eauto;
      ecancel_assumption.
  Qed.

  (* this version assumes you've run hd already, so it doesn't do any
     manipulations of separation logic predicates *)
  Lemma compile_ll_next : forall {tr mem locals functions} ll,
    let v := ll_next ll in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      dummy R end_ptr ll_expr ll_ptr ll'_ptr var,

      (scalar ll_ptr (ll_hd dummy ll)
       * scalar (next_word ll_ptr) ll'_ptr
       * LinkedList end_ptr ll'_ptr (ll_next ll)
       * R)%sep mem ->

      WeakestPrecondition.dexpr mem locals ll_expr ll_ptr ->

      (let v := v in
       <{ Trace := tr;
          Memory := mem;
          Locals := map.put locals var ll'_ptr;
          Functions := functions }>
       k_impl
       <{ pred (k v eq_refl) }>) ->
      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      cmd.seq
        (cmd.set var
                 (expr.load
                    access_size.word
                    (expr.op bopname.add
                             ll_expr
                             (expr.literal
                                (Z.of_nat word_size_in_bytes)))))
        k_impl
      <{ pred (nlet_eq [var] v k) }>.
  Proof.
    repeat first [straightline |
                  eexists; split; [ eauto | ] |
                  eapply WeakestPrecondition_dexpr_expr; eauto];
      eauto.
  Qed.
End Compile.

Section Helpers.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {element : Type} {element_size : access_size}
          {Element : word -> element -> mem -> Prop}.

  Local Notation element_size_in_bytes :=
    (@Memory.bytes_per width element_size).
  Local Notation skip_element :=
    (fun p : word =>
       word.add p (word.of_Z (Z.of_nat element_size_in_bytes))).
  Local Notation LinkedList :=
    (@LinkedList _ word mem element element_size Element).

  Lemma LinkedList_snoc_iff1 :
    forall l pl x end_ptr,
      Lift1Prop.iff1
        (LinkedList end_ptr pl (l ++ [x])%list)
        (liftexists px,
            LinkedList px pl l
            * Element px x
            * scalar (skip_element px) end_ptr)%sep.
  Proof.
    induction l; cbn [LinkedList List.app]; intros.
    { intros; split; intros; sepsimpl.
      all:lift_eexists; sepsimpl; subst.
      all:try ecancel_assumption.
      all:reflexivity. }
    { intros; split; intros.
      { sepsimpl.
        match goal with H : sep _ _ _ |- _ =>
                        seprewrite_in IHl H end.
        sepsimpl_hyps.
        repeat (lift_eexists; sepsimpl; subst).
        ecancel_assumption. }
      { sepsimpl.
        lift_eexists.
        seprewrite IHl.
        repeat (lift_eexists; sepsimpl; subst).
        ecancel_assumption. } }
  Qed.

  Lemma LinkedList_append_impl1 :
    forall l1 l2 p1 p2 end_ptr,
      Lift1Prop.impl1
        (LinkedList p2 p1 l1 * LinkedList end_ptr p2 l2)%sep
        (LinkedList end_ptr p1 (l1 ++ l2)%list).
  Proof.
    induction l1; cbn [LinkedList List.app]; intros.
    { intro; intros.
      sepsimpl; subst; eauto. }
    { (* TODO: this proof would be nicer if impl1 automation was better *)
      rewrite !sep_ex1_l.
      eapply Lift1Prop.impl1_ex1_l.
      intros.
      eapply Lift1Prop.impl1_ex1_r.
      erewrite <-IHl1 with (p2 := p2).
      repeat intro.
      ecancel_assumption. }
  Qed.

  Lemma ll_next_eq {A} (ll ll' : linkedlist A) (x : A) :
    ll = x :: ll' -> ll_next ll = ll'.
  Proof. intros; subst; reflexivity. Qed.

  Lemma ll_hd_next_eq {A} (ll : linkedlist A) (d : A) :
    ll <> nil ->
    ll = ll_hd d ll :: ll_next ll.
  Proof. intros; subst; destruct ll; cbn; congruence. Qed.
End Helpers.
