Require Import Rupicola.Lib.Api.

Section Gallina.
  Definition linkedlist A : Type := list A.

  Definition ll_hd {A} : A -> linkedlist A -> A := hd.

  Definition ll_next {A} : linkedlist A -> linkedlist A := tl.
End Gallina.

Section Separation.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {element : Type} {element_size : access_size}
          {Element : address -> element -> Semantics.mem -> Prop}.

  Local Notation element_size_in_bytes :=
    (@Memory.bytes_per Semantics.width element_size).
  Local Notation skip_element :=
    (fun p : address =>
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
  Fixpoint LinkedList (end_ptr pl : address) (l : list element)
    : Semantics.mem -> Prop :=
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
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
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
    (@LinkedList semantics word access_size.word scalar) (only parsing).
  Local Notation word_size_in_bytes :=
    (@Memory.bytes_per Semantics.width access_size.word).
  Local Notation next_word :=
    (fun p : address =>
       word.add p (word.of_Z (Z.of_nat word_size_in_bytes))).

  (* TODO: these should probably use Owned/Reserved/Borrowed annotations *)

  Lemma compile_ll_hd :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr retvars R' R functions T (pred: T -> _ -> _ -> Prop)
      d end_ptr ll ll_var ll_ptr ll'_ptr k k_impl var,
      map.get locals ll_var = Some ll_ptr ->
      (scalar ll_ptr (ll_hd d ll)
       * scalar (next_word ll_ptr) ll'_ptr
       * LinkedList end_ptr ll'_ptr (ll_next ll)
       * R')%sep mem ->
      let v := ll_hd d ll in
      (let head := v in
       forall m,
         let ll' := ll_next ll in
         (scalar ll_ptr head
          * scalar (next_word ll_ptr) ll'_ptr
          * LinkedList end_ptr ll'_ptr ll'
          * R')%sep m ->
         find k_impl
         implementing (pred (k head))
         and-returning retvars
         and-locals-post locals_ok
         with-locals (map.put locals var head)
         and-memory m and-trace tr and-rest R
         and-functions functions) ->
      (let head := v in
       find (cmd.seq
               (cmd.set var
                        (expr.load access_size.word (expr.var ll_var)))
               k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    cbn [LinkedList ll_hd hd]; intros.
    sepsimpl. repeat straightline'.
    use_hyp_with_matching_cmd; eauto;
      ecancel_assumption.
  Qed.

  (* this version assumes you've run hd already, so it doesn't do any
     manipulations of separation logic predicates *)
  Lemma compile_ll_next :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr retvars R' R functions T (pred: T -> _ -> _ -> Prop)
      end_ptr (ll ll' : linkedlist word) ll_var ll_ptr ll'_ptr
      dummy k k_impl var,
      map.get locals ll_var = Some ll_ptr ->
      (scalar ll_ptr (ll_hd dummy ll)
       * scalar (next_word ll_ptr) ll'_ptr
       * LinkedList end_ptr ll'_ptr (ll_next ll)
       * R')%sep mem ->
      let v := ll_next ll in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-returning retvars
       and-locals-post locals_ok
       with-locals (map.put locals var ll'_ptr)
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq
               (cmd.set var
                        (expr.load
                           access_size.word
                           (expr.op bopname.add
                                    (expr.var ll_var)
                                    (expr.literal
                                       (Z.of_nat word_size_in_bytes)))))
               k_impl)
       implementing (pred (dlet head k))
       and-returning retvars
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'. eauto.
  Qed.
End Compile.

Section Helpers.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {element : Type} {element_size : access_size}
          {Element : address -> element -> Semantics.mem -> Prop}.

  Local Notation element_size_in_bytes :=
    (@Memory.bytes_per Semantics.width element_size).
  Local Notation skip_element :=
    (fun p : address =>
       word.add p (word.of_Z (Z.of_nat element_size_in_bytes))).
  Local Notation LinkedList :=
    (@LinkedList semantics element element_size Element).

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
