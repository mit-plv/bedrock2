Require Import Rupicola.Lib.Api.

Section Gallina.
  Definition linkedlist A : Type := list A.

  Definition ll_hd {A} : A -> linkedlist A -> A := hd.

  Definition ll_next {A} : linkedlist A -> linkedlist A := tl.

  Definition ll_empty {A} : linkedlist A -> bool :=
    fun l => (length l =? 0)%nat.
End Gallina.

Section Separation.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {NULL : address -> Semantics.mem -> Prop}.
  Context {element : Type}
          {Element : address -> element -> Semantics.mem -> Prop}.

  Local Notation word_size_in_bytes :=
    (@Memory.bytes_per Semantics.width access_size.word).
  Local Notation next_word :=
    (fun p : address =>
       word.add p (word.of_Z (Z.of_nat word_size_in_bytes))).

  Fixpoint LinkedList (pl : address) (l : list element)
    : Semantics.mem -> Prop :=
    match l with
    | [] => NULL pl
    | e :: l' =>
      Lift1Prop.ex1
        (fun pe =>
           Lift1Prop.ex1
             (fun pl' =>
                (scalar pl pe
                 * scalar (next_word pl) pl'
                 * LinkedList pl' l'
                 * Element pe e)%sep))
    end.
End Separation.

Section Compile.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  (* TODO: generalize
  Context {NULL : address -> Semantics.mem -> Prop}.
  Context {element : Type}
          {Element : address -> element -> Semantics.mem -> Prop}.
  Context {element_eqb : element -> element -> bool}
          {element_eqb_spec :
             forall x y : element,
               BoolSpec (x = y) (x <> y) (element_eqb x y)}.
  Local Notation LinkedList :=
    (@LinkedList semantics NULL element Element).
   *)
  Local Notation NULL :=
    (fun p : address => emp (map:=Semantics.mem)
                            (word.eqb p (word.of_Z 0) = true)).
  Local Notation LinkedList :=
    (@LinkedList semantics NULL word scalar) (only parsing).
  Local Notation word_size_in_bytes :=
    (@Memory.bytes_per Semantics.width access_size.word).
  Local Notation next_word :=
    (fun p : address =>
       word.add p (word.of_Z (Z.of_nat word_size_in_bytes))).

  (* TODO: these should probably use Owned/Reserved/Borrowed annotations *)

  Lemma compile_ll_hd :
    forall (locals: Semantics.locals) (mem: Semantics.mem)
           (locals_ok : Semantics.locals -> Prop)
      tr R' R functions T (pred: T -> _ -> Prop)
      d ll ll_var ll_ptr k k_impl var,
      map.get locals ll_var = Some ll_ptr ->
      (LinkedList ll_ptr ll * R')%sep mem ->
      ll <> nil ->
      let v := ll_hd d ll in
      (let head := v in
       forall m ll' px pll',
         ll = head :: ll' ->
         (scalar ll_ptr px
          * scalar px head
          * scalar (next_word ll_ptr) pll'
          * LinkedList pll' ll'
          * R')%sep m ->
         find k_impl
         implementing (pred (k head))
         and-locals-post locals_ok
         with-locals (map.put locals var px)
         and-memory mem and-trace tr and-rest R
         and-functions functions) ->
      (let head := v in
       find (cmd.seq
               (cmd.set var
                        (expr.load access_size.word (expr.var ll_var)))
               k_impl)
       implementing (pred (dlet head k))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    destruct ll; [ congruence | ].
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
      tr R functions T (pred: T -> _ -> Prop)
      (ll : linkedlist word) ll_var ll_ptr k k_impl var,
      map.get locals ll_var = Some ll_ptr ->
      let v := ll_next ll in
      (let head := v in
       find k_impl
       implementing (pred (k head))
       and-locals-post locals_ok
       with-locals (map.put locals var (next_word ll_ptr))
       and-memory mem and-trace tr and-rest R
       and-functions functions) ->
      (let head := v in
       find (cmd.seq
               (cmd.set var
                        (expr.op bopname.add
                                 (expr.var ll_var)
                                 (expr.literal
                                    (Z.of_nat word_size_in_bytes))))
               k_impl)
       implementing (pred (dlet head k))
       and-locals-post locals_ok
       with-locals locals and-memory mem and-trace tr and-rest R
       and-functions functions).
  Proof.
    repeat straightline'. eauto.
  Qed.
End Compile.
